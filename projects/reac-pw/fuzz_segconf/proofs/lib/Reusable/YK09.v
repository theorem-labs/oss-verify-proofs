(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK09.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK0c YK0d.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.
Module APC.
Import AX2. Import AX2B.
Definition CEIL : Z := 0x7fff7f800000.
Definition KHI : Z := 0x10007fff8000.
Definition FLOOR : Z := 0x2aaaaaaab000.
Definition MBASE_MIN : Z := 0x154555557000.
Definition PID_MAX : Z := 4194304.
Record atable : Type := AT {
img_lo : Z; img_hi : Z;
n_res : nat;
shadow_off : Z;
a_entry : Z;
rw_lo : Z; rw_len : Z;
ph_addr_z : Z; ph_ent_z : Z; ph_num_z : Z;
x_imemset : Z; x_imemcpy : Z; x_memset : Z; x_memcpy : Z; x_memiszero : Z;
x_istrncpy : Z; x_sealed : Z; x_popfree : Z;
x_sniff : Z; sniff_tab : Z; sniff_cell : Z;
x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
stops_more : list Z
}.
Section q.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Inductive spiece : Type := SPLit (bs : list Z) | SPBlob (k : nat).
Inductive shape : Type :=
| SNil
| SExit (code : Z)
| SEmitP (fd : Z) (ps : list spiece) (s : shape)
| SAlt2 (a b : shape)
| SCase (e : expr) (mid : Z) (s1 s2 : shape)
| SHole (h : nat)
| SNext.
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
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.
Definition mkind_eqb (a b : mkind) : bool :=
match a, b with
| KRW, KRW | KRWLAZY, KRWLAZY | KNONE, KNONE | KNONELAZY, KNONELAZY | KFOG, KFOG | KHOLE, KHOLE => true
| _, _ => false
end.
Record amap : Type := AM {
am_base : expr;
am_len  : expr;
am_kind : mkind
}.
Definition is_tok_kind (k : mkind) : bool := match k with KFOG | KHOLE => true | _ => false end.
Definition is_hole (m : amap) : bool := mkind_eqb (am_kind m) KHOLE.
Definition is_fog (m : amap) : bool := is_tok_kind (am_kind m).
Definition no_fog (ms : list amap) : bool := forallb (fun m => negb (is_fog m)) ms.
Definition no_holes (ms : list amap) : bool := forallb (fun m => negb (is_hole m)) ms.
Inductive afd : Type :=
| FdStd
| FdFile (k : nat) (len off : expr)
| FdDir.
Record acs : Type := ACS {
a_ss    : sym_state;
a_maps  : list amap;
a_totsz : Z;
a_ylo   : Z;
a_eager : Z;
a_vis   : list (expr * expr);
a_ghost : list (expr * expr);
a_abytes : Z;
a_brk   : expr;
a_fd    : afd;
a_tidset : bool
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
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition esub (a b : expr) : expr := mkAlu ALU_SUB a b.
Definition escale (c : Z) (e : expr) : expr := mkMd M_MUL (ELit c) e.
Definition eaddz (a : expr) (z : Z) : expr := mkAlu ALU_ADD a (ELit z).
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
Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
match e with
| ELit _ => true
| EVar n => Nat.ltb n b
| EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
| EExt _ _ _ x => expr_vars_lt b x
| EBlob _ _ _ _ => true
end.
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).
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
Definition fresh_ok (cs : acs) : bool :=
let v := nxt cs in
sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
&& maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
&& expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v.
Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
if fresh_ok cs then
let ss := a_ss cs in
let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
match carry (s_log ss') (s_know ss') [] with
| (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
| _ => None
end
else None.
Definition run_block (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
if fresh_ok cs then
let ss := a_ss cs in
let bc := mkbc (facts_of (s_know ss)) in
let kx := mk_kix (s_know ss) in
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
Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
let sp := mk_sprepB bc ub uk un in
List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).
Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof. intros. bcfe. unfold kn_havocB, kn_havoc. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.
Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc. Proof. apply functional_extensionality; intros k. unfold kn_havocM. apply kn_havocB_eqf. Qed.
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
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
match K with
| KImg lo hi =>
if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
| _ => [K]
end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.
Definition kimg_clip (k : list kentry) : list kentry :=
List.filter (fun K => match K with KImg lo hi => Z.leb (img_lo A) lo && Z.leb lo hi && Z.leb hi (img_hi A) | _ => true end) k.
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
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).
Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
ranges_apart_xB bc b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).
Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof. intros. bcfe. unfold off_image_xB, off_image_x. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.
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
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := xlo k e.
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).
Definition len_eqbB (bc : bctx) (n m : expr) : bool :=
expr_eqb n m || (lin_ge0B bc [(n, 0%Z)] [(m, 0%Z)] && lin_ge0B bc [(m, 0%Z)] [(n, 0%Z)]).
Lemma len_eqbB_eqf : forall fk, len_eqbB (mkbc fk) = len_eqb fk.
Proof. intros. bcfe. unfold len_eqbB, len_eqb. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite len_eqbB_eqf : bceq.
Definition lit_diff (e f : expr) : option Z :=
match esub e f with ELit z => Some (z mod two64) | _ => None end.
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
Definition after_call (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) : option acs :=
let ss := a_ss cs in
let nx := s_next ss in
let sr1 := sr_fresh (s_regs ss) caller_saved nx in
let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
if (fresh_ok cs && kn_vars_lt nx k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS)))
else None.
Definition after_call2 (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) (extra : nat) : option acs :=
let ss := a_ss cs in
let nx := s_next ss in
let sr1 := sr_fresh (s_regs ss) caller_saved nx in
let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
if (fresh_ok cs && kn_vars_lt (nx + NCS + extra) k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS + extra)))
else None.
Definition page_up (len : Z) : Z := ((len + 4095) / 4096) * 4096.
Definition is_ecall_at (cs : acs) : bool :=
(Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
match fetch_word segs (Z_to_bv 64 (pc cs)) with
| Some w => is_ecall w
| None => false
end)%bool.
Definition xlo1 (k : list kentry) (e : expr) : option Z :=
match e with
| ELit z => Some (zlit64 z)
| _ => match erange k e, lin_brange k e with
| Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
| Some (lo, _), None => Some lo
| None, Some (lo', _) => Some lo'
| None, None => match lin_srange k e with Some (lo, _) => Some lo | None => None end
end
end.
Definition xlo1B (bc : bctx) (e : expr) : option Z :=
match e with
| ELit z => Some (zlit64 z)
| _ => match erangeB bc e, lin_brangeB bc e with
| Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
| Some (lo, _), None => Some lo
| None, Some (lo', _) => Some lo'
| None, None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end
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
| None, None => match lin_srange k e with Some (_, hi) => Some hi | None => None end
end
end.
Definition xhi1B (bc : bctx) (e : expr) : option Z :=
match e with
| ELit z => Some (zlit64 z)
| _ => match erangeB bc e, lin_brangeB bc e with
| Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
| Some (_, hi), None => Some hi
| None, Some (_, hi') => Some hi'
| None, None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end
end
end.
Lemma xhi1B_eqf : forall fk, xhi1B (mkbc fk) = xhi1 fk.
Proof. intros. bcfe. unfold xhi1B, xhi1. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xhi1B_eqf : bceq.
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
Definition node_droprange (cs : acs) (b n : expr) : acs :=
let '(bb, bk) := split_lit b in set_kn cs (kn_havoc (kn cs) bb bk n).
Definition node_bump (cs : acs) (m : nat) : option acs :=
if Nat.leb (nxt cs) m then Some (bump cs (m - nxt cs)) else None.
Definition node_havoc (cs : acs) (rs : list nat) : option acs :=
if (fresh_ok cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool then
let ss := a_ss cs in
Some (with_ss cs (mk_ss (s_pc ss) (sr_fresh (s_regs ss) rs (s_next ss)) (s_know ss) (s_next ss + length rs)))
else None.
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
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside k b off n (am_base m) 0 (am_len m)) ms.
Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideB bc b off n (am_base m) 0 (am_len m)) ms.
Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. intros. bcfe. unfold find_containingB, find_containing. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).
Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).
Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. intros. bcfe. unfold shadow_ofB, shadow_of. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
let '(sb, sk, sn) := shadow_of k b n in
match find_containing k ms [KRWLAZY] sb sk sn with
| Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
| None => []
end.
Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
let '(sb, sk, sn) := shadow_ofB bc b n in
match find_containingB bc ms [KRWLAZY] sb sk sn with
| Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
| None => []
end.
Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof. intros. bcfe. unfold shadow_factsB, shadow_facts. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.
Definition vis_cost (nhi : Z) : Z := nhi + nhi / 8 + 16384.
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
&& forallb (fun p => let '(pb, pk) := split_lit (fst p) in
flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs)
&& Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts k0 (a_maps cs) b n ++ k) (nxt cs))
(a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| None => None
end.
Definition vis_add (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
let k0 := kn cs in let bc := mkbc k0 in
let '(bb, bk) := split_lit b in
let '(sb, sk, sn) := shadow_ofB bc b n in
match xhiB bc n with
| Some nhi =>
if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
&& expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
&& forallb (fun p => let '(pb, pk) := split_lit (fst p) in
flat_xB bc pb pk (snd p)
&& ranges_apart_xB bc bb bk n pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs)
&& forallb (fun p => let '(pb, pk) := split_lit (fst p) in
flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs)
&& Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
(a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| None => None
end.
Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof. intros. unfold vis_add, vis_add_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_factsB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf. reflexivity. Qed.
Fixpoint find_disj (k : list kentry) (b1 b2 : expr) : option (expr * Z * expr * expr * Z * expr) :=
match k with
| [] => None
| KDisj (SA c1 o1) n1 (SA c2 o2) n2 :: r =>
if (expr_eqb c1 b1 && expr_eqb c2 b2)%bool then Some (c1, o1, n1, c2, o2, n2)
else if (expr_eqb c1 b2 && expr_eqb c2 b1)%bool then Some (c2, o2, n2, c1, o1, n1)
else find_disj r b1 b2
| _ :: r => find_disj r b1 b2
end.
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
Definition node_shdisj (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
let k := kn cs in let bc := mkbc k in
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
Definition mmap_len (cs : acs) : option (expr * Z * Z) :=
match reg_lit cs 11 with
| Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
| None =>
let le := reg cs 11 in let k := kn cs in let bc := mkbc k in
match xloB bc le, xhiB bc le with
| Some lo, Some hi =>
if (Z.ltb 0 lo && Z.leb 12 (ealignB bc le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
| _, _ => None
end
end.
Lemma mmap_len_eq : forall cs, mmap_len cs = mmap_len_ref cs.
Proof. intros. unfold mmap_len, mmap_len_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?xhiB_eqf, ?xloB_eqf. reflexivity. Qed.
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
Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
((match xhi k len, base_range k b with
| Some lh, Some (lo, hi) =>
(Z.leb CEIL (lo + off) && Z.leb (hi + off + lh) two64)
|| (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))
| _, _ => false
end) || inside_maps k ms b off len)%bool.
Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
((match xhiB bc len, base_rangeB bc b with
| Some lh, Some (lo, hi) =>
(Z.leb CEIL (lo + off) && Z.leb (hi + off + lh) two64)
|| (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))
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
Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
kimg_clip (List.filter (grant_keep_bB bc ms) (bc_fk bc)).
Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof. intros. bcfe. unfold kn_grant_filterB, kn_grant_filter. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.
Definition budget_ok (cs : acs) (extra : Z) : bool :=
Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
flat_map (fun m => if is_fog m then [] else
match am_base m with
| ELit _ => []
| mb => [KDisj (SA mb 0) (am_len m) (SA nb 0) ne]
end) ms.
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
(m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
ACS (mk_ss (pc cs + 4) sr k' nx')
(m :: a_maps cs) (a_totsz cs + nhi) ylo'
(if eager then a_eager cs + nhi else a_eager cs)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
match ne with
| ELit _ => []
| _ => [KRange (eadd base ne) (4096 * (KHI / 4096 + 1) + nlo) CEIL]
end.
Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
match mmap_len cs with
| Some (ne, nlo, nhi) =>
if (fresh_ok cs && expr_vars_lt (nxt cs) ne
&& gap_ok cs nhi && (negb eager || budget_ok cs nhi)
&& Z.leb (KHI + 2 * nhi) (a_ylo cs) && Z.leb (a_ylo cs) FLOOR
&& no_holes (a_maps cs))%bool then
let v := nxt cs in
let base := escale 4096 (EVar v) in
let kfacts := KRange (EVar v) (KHI / 4096 + 1) ((CEIL - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_new (a_maps cs) base ne in
let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
let k' := kfacts ++ kn_grant_filter (kn cs) (a_maps cs) in
let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs - 2 * nhi) in
if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
else None
| None => None
end.
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
let k := kn cs in let a := reg cs 10 in
let '(b, off) := split_lit a in
match mmap_len cs, xlo k a, xhi k a with
| Some (ne, nlo, nhi), Some alo, Some ahi =>
if (page_aligned k a && Z.ltb 0 alo && Z.leb (img_hi A) alo && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
| _, _, _ => None
end.
Definition same_val (k : list kentry) (a b : expr) : bool :=
if expr_eqb a b then true
else (if lin_ge0 k [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 k [(b, 0%Z)] [(a, 0%Z)] else false).
Definition find_hole (k : list kentry) (ms : list amap) (a ne : expr) : option amap :=
List.find (fun m => is_hole m && same_val k a (am_base m) && same_val k ne (am_len m)) ms.
Definition unhole (ms : list amap) (h : amap) : list amap :=
List.map (fun m => if (is_hole m && amap_eqb m h)%bool then AM (am_base m) (am_len m) KFOG else m) ms.
Definition mmap_fixed_grant (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
(kind : mkind) (eager visible : bool) : option acs :=
let k := kn cs in
let a := reg cs 10 in
let m := AM a ne kind in
let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
let k' := ksh ++ kn_grant_filter k ms0 in
let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.
Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
let k := kn cs in
let a := reg cs 10 in
match fixed_args cs KHI with
| Some (b, off, ne, nlo, nhi) =>
if (no_fog (a_maps cs)
&& forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
&& (negb eager || budget_ok cs nhi)
&& expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
else None
| None =>
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
Definition rekind (ms : list amap) (m : amap) : list amap :=
map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.
Inductive fixed_in_arm := ArmE | ArmF | ArmG.
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
match fixed_args cs CEIL with
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
Definition fixed_in_args (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
match fixed_args cs CEIL with
| Some (b, off, ne, nlo, nhi) =>
let k := kn cs in let bc := mkbc k in
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
Definition mmap_fixed_in (cs : acs) (arm : fixed_in_arm) : option acs :=
match fixed_in_args cs arm with
| Some (b, off, ne, nlo, nhi, m) =>
let k := kn cs in let bc := mkbc k in
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
Definition ENOMEM_RET : Z := two64 - 12.
Definition refuse (cs : acs) : acs := set_pc (set_reg cs 10 (ELit ENOMEM_RET)) (pc cs + 4).
Definition replace_entry (ms : list amap) (m : amap) (pieces : list amap) : list amap :=
flat_map (fun m' => if amap_eqb m' m then pieces else [m']) ms.
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
let hp := if hole then [AM a ne KHOLE] else [] in
let ss := a_ss cs in
ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
(dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutout k b off ne)) (s_next ss))
(hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition mmap_destroyed_with (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
let k := kn cs in let bc := mkbc k in
let a := reg cs 10 in
let mb := am_base m in let ml := am_len m in
let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
let hp := if hole then [AM a ne KHOLE] else [] in
let ss := a_ss cs in
ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
(dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutoutB bc b off ne)) (s_next ss))
(hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Lemma mmap_destroyed_with_eq : forall hole cs b off ne m lne rne, mmap_destroyed_with hole cs b off ne m lne rne = mmap_destroyed_with_ref hole cs b off ne m lne rne.
Proof. intros. unfold mmap_destroyed_with, mmap_destroyed_with_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf. reflexivity. Qed.
Definition dest_cases (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
let k := kn cs in
let a := reg cs 10 in
let mb := am_base m in let ml := am_len m in
let ls := if lin_ge0 k [(a, -1)] [(mb, 0)] then [true]
else if (expr_eqb a mb || lin_ge0 k [(mb, 0)] [(a, 0)])%bool then [false]
else [true; false] in
let rs := if lin_ge0 k [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]
else if lin_ge0 k [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]
else [true; false] in
flat_map (fun l => map (fun r => (l, r)) rs) ls.
Definition mmap_destroyed (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs :=
map (fun lr => mmap_destroyed_with hole cs b off ne m (fst lr) (snd lr)) (dest_cases cs ne m).
Definition mmap_gate (cs : acs) : option (Z * Z * bool) :=
match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
| Some 222, Some prot, Some flags, Some m1, Some 0 =>
if negb (Z.eqb m1 (two64 - 1)) then None
else Some (prot, flags, match reg_lit cs 10 with Some 0 => true | _ => false end)
| _, _, _, _, _ => None
end.
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
| _, _ => None
end in
match g with Some csG => Some (refuse cs, csG) | None => None end
| None => None
end.
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
Definition node_mprotect_ref (cs : acs) : option acs :=
match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEIL with
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
match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEIL with
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
Proof. intros. unfold node_mprotect, node_mprotect_ref. unfold ehi, elo. rewrite ?find_containingB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.
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
&& xinside k pb pk (snd p) bb bk ne && kzero_x k k sb sk sn)
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
&& xinsideB bc pb pk (snd p) bb bk ne && kzero_xB bc k sb sk sn)
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
let k := kn cs in let '(bb, bk) := split_lit (a_brk cs) in
(brk_base_ok cs d && no_fog (a_maps cs)
&& forallb (fun m => ranges_apart_x k bb bk (ELit (d + 4096)) (am_base m) 0 (am_len m)) (a_maps cs)
&& budget_ok cs d)%bool.
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
if (brk_grow_possible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
let k' := kn_grant_filter k (a_maps cs) in
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
if (negb (is_fog m) && Z.leb 0 sz && Z.ltb sz two64
&& match xhi (kn cs) (am_len m) with Some h => Z.leb h sz | None => false end)%bool
then Some (with_maps cs (list_set_nth i (fog_token sz) (a_maps cs)))
else None
| None => None
end.
Definition node_fognew (cs : acs) (i : nat) (sz : Z) : option acs :=
if (Nat.leb i (length (a_maps cs)) && Z.leb 0 sz && Z.ltb sz two64)%bool
then Some (with_maps cs (list_insert_nth i (fog_token sz) (a_maps cs)))
else None.
Definition node_ghost (cs : acs) (b n : expr) : option acs :=
match xhi (kn cs) n with
| Some nhi =>
if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs ++ [(b, n)])
(a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| None => None
end.
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
Definition node_unvis (cs : acs) (b n : expr) : option acs :=
let k := kn cs in let bc := mkbc k in
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
Definition node_intro (cs : acs) (lo hi : Z) : option acs :=
if (fresh_ok cs && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool then
let v := nxt cs in let ss := a_ss cs in
Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v)))
else None.
Definition SPIN_WORD : Z := 0x6f.
Definition node_spin (cs : acs) : bool :=
(Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
match fetch_word segs (Z_to_bv 64 (pc cs)) with
| Some w => Z.eqb (bv_unsigned w) SPIN_WORD
| None => false
end)%bool.
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
Definition summary_fill (cs : acs) (entry : Z) (cmax : Z) : option acs :=
let k := kn cs in let bc := mkbc k in
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
else if Z.leb 1 n then
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
else if Z.leb 1 n then
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
Definition summary_copy (cs : acs) (entry : Z) : option acs :=
let k := kn cs in let bc := mkbc k in
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
Definition summary_miz (cs : acs) : option acs :=
let k := kn cs in let bc := mkbc k in
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
Definition img_cov (k : list kentry) (a b : Z) : bool :=
existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.
Definition img_covB (bc : bctx) (a b : Z) : bool :=
existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) (bc_fk bc).
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof. intros. bcfe. unfold img_covB, img_cov. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite img_covB_eqf : bceq.
Definition SEALED_W : Z := 0x3e64656c6165733c.
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
Definition summary_istrncpy (cs : acs) : option acs :=
let k := kn cs in let bc := mkbc k in
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
|| kn_readable_x k bb bk ne)
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
let v := extK k v0 in
match erange k v with
| Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
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
Definition summary_sniff (cs : acs) : option acs :=
let k := kn cs in let bc := mkbc k in
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
|| kn_readable_x k bb bk ne)
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
let v := extKB bc v0 in
match erangeB bc v with
| Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
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
Definition V_S1 : nat := 0.
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.
Definition V_W : nat := 4.
Definition V_BRK : nat := 5.
Definition V_S2 : nat := 6.
Definition V_L1 : nat := 7.
Definition V_UID : nat := 8.
Definition e_sp0 : expr := eadd (escale 32768 (EVar V_S1)) (escale 16 (EVar V_S2)).
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
Definition e_atr8 : expr :=
eadd (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.
Definition node_envscan (cs : acs) : option acs :=
let k := kn cs in
if (Z.eqb (pc cs) (x_envscan A) && len_eqb k (reg cs 9) e_envp)%bool then
Some (set_pc (set_reg (set_reg cs 9 (eadd (reg cs 9) (eadd (escale 8 (EVar V_ENVC)) (ELit 8)))) 10 (ELit 0)) (x_envscan_k A))
else None.
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
Definition inst (inv : acs) (J : nat) (e : expr) : acs :=
ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
(map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
(map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
(esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).
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
Fixpoint mk_fwd (m : list (nat * nat)) : option (list (option nat)) :=
match m with
| [] => Some []
| (s, d) :: rest =>
match mk_fwd rest with
| Some t => match nt_get t s with None => Some (nt_set t s d) | Some _ => None end
| None => None
end
end.
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
Fixpoint bt_set (t : list bool) (i : nat) {struct i} : list bool :=
match i, t with
| O, [] => [true]
| O, _ :: rest => true :: rest
| S j, [] => false :: bt_set [] j
| S j, x :: rest => x :: bt_set rest j
end.
Definition bt_get (t : list bool) (i : nat) : bool := nth i t false.
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
Definition saddr_eqb_h (x y : saddr) : bool :=
saddr_eqb x y || expr_eqb (eaddz (a_base x) (a_off x)) (eaddz (a_base y) (a_off y)).
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
Definition kflat_h (k : list kentry) (K : kentry) : bool :=
match K with
| KWord (SA b o) w _ => flat_x k b o (ELit (Z.of_nat w))
| KZero (SA b o) n | KBlob (SA b o) n _ | KWr (SA b o) n | KFill (SA b o) n _ | KUnk (SA b o) n => flat_x k b o n
| _ => true
end.
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
&& expr_vars_lt lo (a_brk ch) && fd_vars_lt lo (a_fd ch)
&& list_eqb amap_eqb (a_maps cs) (a_maps ch)
&& list_eqb pair_eqb (a_vis cs) (a_vis ch)
&& list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
&& expr_eqb (a_brk cs) (a_brk ch)
&& afd_eqb (a_fd cs) (a_fd ch)
&& Bool.eqb (a_tidset cs) (a_tidset ch)
&& Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
&& Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).
Definition lc_bnd (c : loopctx) : nat := match c with LC _ _ _ hi => hi | JC _ _ _ b _ => b end.
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
Definition loop_body_state (J : nat) (N : expr) (nhi : Z) (inv : acs) : acs :=
add_kn inv [KRange (EVar J) 0 (nhi - 1); KRange (esub N (EVar J)) 1 nhi].
Definition branch_probe (cs : acs) : option expr :=
match itab_lookup IT (pc cs) with
| Some (Branch c rs1 rs2 _) =>
Some (fst (cond_probe c (sr_get (s_regs (a_ss cs)) rs1) (sr_get (s_regs (a_ss cs)) rs2)))
| _ => None
end.
Fixpoint diff_regs (i : nat) (ra rb : list expr) : list nat :=
match ra, rb with
| a :: ra', b :: rb' => if expr_eqb a b then diff_regs (S i) ra' rb' else i :: diff_regs (S i) ra' rb'
| _, _ => []
end.
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
Definition via_ok (cs js : acs) (lo : nat) : bool :=
(match s_log (a_ss js) with [] => true | _ => false end
&& Nat.eqb (length (s_regs (a_ss js))) 32
&& Nat.leb nx0 (nxt cs) && Nat.leb (nxt cs) lo && Nat.leb lo (nxt js))%bool.
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
let '(bb, bo) := split_lit b in
let K := KUnk (SA bb bo) (ELit n) in
if kunk_covered (kn cs) K then Some (set_kn cs (K :: kn_cutout (kn cs) bb bo (ELit n))) else None.
Definition respell_ok (k : list kentry) (a e : expr) : bool :=
match decide_branch k BC_EQ a e with
| Some true => true
| _ =>
match erange k (mkAlu ALU_SUB a e) with
| Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
| None => false
end
end.
Definition node_respell (cs : acs) (r : nat) (e : expr) : option acs :=
if (Nat.ltb 0 r && Nat.ltb r 32 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool
then Some (set_reg cs r e) else None.
Definition sa_of (b : expr) : saddr := let '(bb, bo) := split_lit b in SA bb bo.
Fixpoint hw_apply (k : list kentry) (a : saddr) (x : nat) (found : bool) : list kentry :=
match k with
| [] => []
| KWord a' w v :: r =>
if saddr_eqb a' a then (if found then hw_apply r a x true else KWord a' w (EVar x) :: hw_apply r a x true)
else KWord a' w v :: hw_apply r a x found
| K :: r => K :: hw_apply r a x found
end.
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
Definition STOPS : list Z :=
[x_imemset A; x_imemcpy A; x_memset A; x_memcpy A; x_memiszero A; x_envscan A; x_pnscan A] ++ stops_more A.
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
match rs with
| [] => t
| (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
end.
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := mk_itab_ranges_acc rs PTLeaf.
End q.
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : nat := 9.
Definition K_RND : nat := 25.
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := split_lit e_atrandom.
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
[KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].
Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
[KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 2047;
KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE9;
KRange e_sp0 0x7fff80000000 0x7fffffffff40;
KRange (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) 0xFFFF0000000 0xFFFFFFFFFE8;
KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
KRange (EVar V_UID) 0 0xFFFFFFFE;
KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 4 6 (ELit 4096)
++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
++ [atr;
KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.
Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
Definition init_vis (A : atable) : list (expr * expr) :=
[(ELit (img_lo A), ELit (img_hi A - img_lo A)); (ELit CEIL, ELit (2^47 - CEIL))].
Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
(vis_cost (img_hi A - img_lo A) + vis_cost (2^47 - CEIL)) (escale 4096 (EVar V_BRK)) FdStd false.
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.
Definition ASAN : atable :=
{| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x4ba64; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0xe1ea4; x_imemcpy := 0xe1e28; x_memset := 0x116934; x_memcpy := 0x116530; x_memiszero := 0xe2508;
x_istrncpy := 0xe23b8; x_sealed := 0x1205f; x_popfree := 0x52a70;
x_sniff := 0x1414dc; sniff_tab := 0x24f40; sniff_cell := 0x14bf00;
x_envscan := 0x10d5e4; x_envscan_k := 0x10d5f0; x_pnscan := 0x10d6a8; x_pnscan_k := 0x10d6b4;
stops_more := [0x506e4; 0x51d08; 0xddd88; 0xee070; 0xee200]    |}.
Definition ASAN_TEXT_LO : Z := 0x4ba64.
Definition ASAN_TEXT_N : nat := 252263.
Definition asan_init : acs := init_acs_of ASAN.
Definition BOTH : atable :=
{| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x4ba54; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0xe1e94; x_imemcpy := 0xe1e18; x_memset := 0x116924; x_memcpy := 0x116520; x_memiszero := 0xe24f8;
x_istrncpy := 0xe23a8; x_sealed := 0x1205f; x_popfree := 0x52a60;
x_sniff := 0x1414cc; sniff_tab := 0x24f40; sniff_cell := 0x14bf80;
x_envscan := 0x10d5d4; x_envscan_k := 0x10d5e0; x_pnscan := 0x10d698; x_pnscan_k := 0x10d6a4;
stops_more := [0x506d4; 0x51cf8; 0xddd78; 0xee060; 0xee1f0] |}.
Definition BOTH_TEXT_LO : Z := 0x4ba54.
Definition BOTH_TEXT_N : nat := 252267.
Definition both_init : acs := init_acs_of BOTH.
End APC.
