(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From Stdlib Require Uint63.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B.
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

Module DigI.
Import Stdlib.Numbers.Cyclic.Int63.Uint63.   (* [comment removed for export] *)
Definition imix (h x : int) : int := PrimInt63.land (PrimInt63.lxor (PrimInt63.lsl h 5%uint63) x) 1073741823%uint63.
Fixpoint pos_low (p : positive) (n : nat) (acc bit : int) : int :=
  match n, p with
  | O, _ => acc
  | S _, xH => PrimInt63.lor acc bit
  | S m, xO q => pos_low q m acc (PrimInt63.lsl bit 1%uint63)
  | S m, xI q => pos_low q m (PrimInt63.lor acc bit) (PrimInt63.lsl bit 1%uint63)
  end.
Definition zdg (z : Z) : int :=
  match z with
  | Z0 => 0%uint63
  | Zpos p => pos_low p 24%nat 0%uint63 1%uint63
  | Zneg p => PrimInt63.lxor (pos_low p 24%nat 0%uint63 1%uint63) 16777216%uint63
  end.
Definition ndg (n : nat) : int := pos_low (Pos.of_succ_nat n) 24%nat 0%uint63 1%uint63.   (* [comment removed for export] *)
Definition vdg (n : N) : int := pos_low (pos_fast n) 24%nat 0%uint63 1%uint63.   (* [comment removed for export] *)
Fixpoint edigI (e : expr) (h : int) : int :=
  match e with
  | ELit z => imix (imix h 1%uint63) (zdg z)
  | EVar n => imix (imix h 2%uint63) (vdg n)
  | EAlu o a b => edigI b (edigI a (imix (imix h 3%uint63) (ndg (aluop_ix o))))
  | EAluw o a b => edigI b (edigI a (imix (imix h 4%uint63) (ndg (aluop_ix o))))
  | EMd o a b => edigI b (edigI a (imix (imix h 5%uint63) (ndg (mulop_ix o))))
  | EMdw o a b => edigI b (edigI a (imix (imix h 6%uint63) (ndg (mulop_ix o))))
  | EExt sx lo n a => edigI a (imix (imix (imix (imix h 7%uint63) (ndg (bool_ix sx))) (ndg lo)) (ndg n))
  | EBlob sx k i n => imix (imix (imix (imix (imix h 8%uint63) (ndg (bool_ix sx))) (ndg k)) (zdg i)) (ndg n)
  end.
Definition adigI (a : saddr) (h : int) : int := imix (edigI (a_base a) h) (zdg (a_off a)).
Fixpoint rsdigI (rs : list (saddr * expr)) (h : int) : int :=
  match rs with [] => h | (a, n) :: rest => rsdigI rest (edigI n (adigI a h)) end.
Fixpoint esdigI (es : list expr) (h : int) : int :=
  match es with [] => h | e :: rest => esdigI rest (edigI e h) end.
Definition kdigI (K : kentry) : int :=
  match K with
  | KWord a w v => edigI v (imix (adigI a 11%uint63) (ndg w))
  | KZero a n => edigI n (adigI a 12%uint63)
  | KBlob a n k => imix (edigI n (adigI a 13%uint63)) (ndg k)
  | KImg lo hi => imix (imix 14%uint63 (zdg lo)) (zdg hi)
  | KAlign e m => imix (edigI e 15%uint63) (zdg m)
  | KRange e lo hi => imix (imix (edigI e 16%uint63) (zdg lo)) (zdg hi)
  | KWr a n => edigI n (adigI a 17%uint63)
  | KDisj a1 n1 a2 n2 => edigI n2 (adigI a2 (edigI n1 (adigI a1 18%uint63)))
  | KFill a n c => imix (edigI n (adigI a 19%uint63)) (zdg c)
  | KUnk a n => edigI n (adigI a 20%uint63)
  | KPriv t rs args k => imix (esdigI args (rsdigI rs (imix 21%uint63 (ndg t)))) (zdg k)
  end.
Definition ikey (h : int) : positive := match Stdlib.Numbers.Cyclic.Int63.Uint63.to_Z h with Zpos p => xO p | Zneg p => xI p | Z0 => xH end.
End DigI.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : N.       (* [comment removed for export] *)
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
Definition salt2 (a b : shape) : shape :=
  match a, b with SNil, _ => b | _, SNil => a | _, _ => if shape_eqb a b then a else SAlt2 a b end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.    

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
Definition nxt (cs : acs) : N := s_next (a_ss cs).

Definition with_ss (cs : acs) (ss : sym_state) : acs :=
  ACS ss (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition mk_ss (p : Z) (sr : list expr) (k : list kentry) (nx : N) : sym_state := SS p sr [] k nx.
Definition set_reg (cs : acs) (n : nat) (e : expr) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (sr_upd (s_regs ss) n e) (s_know ss) (s_next ss)).
Definition set_pc (cs : acs) (p : Z) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss p (s_regs ss) (s_know ss) (s_next ss)).
Definition set_kn (cs : acs) (k : list kentry) : acs :=
  let ss := a_ss cs in with_ss cs (mk_ss (s_pc ss) (s_regs ss) k (s_next ss)).
Definition add_kn (cs : acs) (k : list kentry) : acs := set_kn cs (k ++ kn cs).
Definition bump (cs : acs) (d : N) : acs :=
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
Definition V_S1 : N := 0.     (* [comment removed for export] *)
Definition V_ARGC : N := 1.
Definition V_ENVC : N := 2.
Definition V_L0 : N := 3.     (* [comment removed for export] *)
Definition V_W : N := 4.      (* [comment removed for export] *)
Definition V_BRK : N := 5.    (* [comment removed for export] *)
Definition V_S2 : N := 6.     (* [comment removed for export] *)
Definition V_L1 : N := 7.     (* [comment removed for export] *)
Definition V_UID : N := 8.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sp0 : expr := eadd (escale 32768 (EVar V_S1)) (escale 16 (EVar V_S2)).

(* [comment removed for export] *)
Definition STK : Z := 8388608.                 (* [comment removed for export] *)
Definition e_top : expr := eaddz e_sp0 (- STK).
Definition TOPMAX : Z := 0x800000000000 - STK.  (* [comment removed for export] *)
Definition LOWTOP : Z := 0x7fff7000.           (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint expr_vars (e : expr) (acc : list N) : list N :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (N.eqb n) acc then acc else n :: acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars x (expr_vars y acc)
  | EExt _ _ _ x => expr_vars x acc
  | EBlob _ _ _ _ => acc
  end.

Definition live_vars (cs : acs) : list N :=
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

Definition all_live (live : list N) (e : expr) : bool :=
  forallb (fun v => N.ltb v nx0 || existsb (N.eqb v) live) (expr_vars e []).

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list N) (K : kentry) : bool :=
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

(* [comment removed for export] *)
Definition expr_any_live (live : list N) (e : expr) : bool :=
  existsb (fun v => existsb (N.eqb v) live) (expr_vars e []).
Definition live_close1 (k : list kentry) (live : list N) : list N :=
  fold_right (fun K acc => match K with KRange e _ _ => if expr_any_live live e then expr_vars e acc else acc | _ => acc end) live k.

Definition cs_gc_ref (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_close1 (kn cs) (live_close1 (kn cs) (live_vars cs)) in
  set_kn cs (List.filter (kn_gc_entry spb spk live) (kn cs)).

Definition vkey (n : N) : positive := pos_fast n.   (* [comment removed for export] *)
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
Definition in_live_t (t : ptree unit) (v : N) : bool :=
  match pt_get t (vkey v) with Some _ => true | None => false end.
Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if N.ltb n nx0 then true else in_live_t t n
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
Fixpoint expr_any_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_any_live_t t x then true else expr_any_live_t t y
  | EExt _ _ _ x => expr_any_live_t t x
  | EBlob _ _ _ _ => false
  end.
Definition live_close1_t (k : list kentry) (t : ptree unit) : ptree unit :=
  fold_right (fun K acc => match K with KRange e _ _ => if expr_any_live_t t e then expr_vars_t e acc else acc | _ => acc end) t k.
Definition cs_gc (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_close1_t (kn cs) (live_close1_t (kn cs) (live_vars_t cs)) in
  set_kn cs (List.filter (kn_gc_entry_t spb spk live) (kn cs)).

(* [comment removed for export] *)
Definition live_agree (acc : list N) (t : ptree unit) : Prop :=
  forall v, existsb (N.eqb v) acc = in_live_t t v.
Lemma vkey_inj : forall a b, vkey a = vkey b -> a = b.
Proof. intros a b H. unfold vkey in H. apply pos_fast_inj. exact H. Qed.
Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (N.eqb n) acc then acc else n :: acc) (pt_set (vkey n) tt t).
Proof.
  intros acc t n H v. unfold in_live_t.
  destruct (N.eq_dec v n) as [->|NE].
  - rewrite pt_gss. destruct (existsb (N.eqb n) acc) eqn:E; [exact E|]. cbn [existsb]. rewrite N.eqb_refl. reflexivity.
  - rewrite pt_gso by (intros HK; apply NE; apply vkey_inj; exact HK).
    fold (in_live_t t v). rewrite <- (H v).
    destruct (existsb (N.eqb n) acc); [reflexivity|]. cbn [existsb].
    destruct (N.eqb_spec v n); [contradiction|]. reflexivity.
Qed.
Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof.
  induction e; intros acc t H; cbn [expr_vars expr_vars_t]; try exact H; try (apply live_agree_var; exact H); auto.
Qed.
Lemma live_agree_fold : forall (X : Type) (f : X -> list N -> list N) (g : X -> ptree unit -> ptree unit) (l : list X) acc t,
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
  apply live_agree_fold; [intros a acc t H; destruct a as [[] ? ?|[] ?|[] ? ?| | | |[] ?| |[] ? ?|[] ?|? ? ? ?]; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  exact A0.
Qed.
Lemma forallb_expr_vars : forall P e acc,
  forallb P (expr_vars e acc) = (forallb P (expr_vars e []) && forallb P acc)%bool.
Proof.
  intros P e. induction e; intros acc; cbn [expr_vars]; try reflexivity.
  - destruct (existsb (N.eqb n) acc) eqn:E; cbn [existsb forallb].
    + rewrite Bool.andb_true_r. destruct (P n) eqn:Pn; [reflexivity|]. cbn [andb].
      destruct (forallb P acc) eqn:F; [|reflexivity]. exfalso.
      apply existsb_exists in E as [x [Hx Ex]]. apply N.eqb_eq in Ex. subst x.
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
  - rewrite <- (H n). cbn. rewrite Bool.andb_true_r. destruct (N.ltb n nx0); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - rewrite forallb_expr_vars, IHe1, IHe2. destruct (forallb _ (expr_vars e1 [])); reflexivity.
  - exact IHe.
Qed.
Lemma existsb_expr_vars : forall P e acc,
  existsb P (expr_vars e acc) = (existsb P (expr_vars e []) || existsb P acc)%bool.
Proof.
  intros P e. induction e; intros acc; cbn [expr_vars]; try reflexivity.
  - destruct (existsb (N.eqb n) acc) eqn:E; cbn [existsb].
    + rewrite Bool.orb_false_r. destruct (P n) eqn:Pn; [|reflexivity]. cbn [orb].
      apply existsb_exists in E as [x [Hx Ex]]. apply N.eqb_eq in Ex. subst x.
      apply existsb_exists. exists n. split; [exact Hx | exact Pn].
    + rewrite Bool.orb_false_r. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - rewrite IHe1, IHe2, (IHe1 (expr_vars e2 [])). rewrite Bool.orb_assoc. reflexivity.
  - apply IHe.
Qed.
Lemma expr_any_live_t_eq : forall acc t e, live_agree acc t -> expr_any_live_t t e = expr_any_live acc e.
Proof.
  intros acc t e H. unfold expr_any_live. induction e; cbn [expr_any_live_t expr_vars existsb]; try reflexivity.
  - rewrite <- (H n). cbn. rewrite Bool.orb_false_r. reflexivity.
  - rewrite existsb_expr_vars, IHe1, IHe2. destruct (existsb _ (expr_vars e1 [])); reflexivity.
  - rewrite existsb_expr_vars, IHe1, IHe2. destruct (existsb _ (expr_vars e1 [])); reflexivity.
  - rewrite existsb_expr_vars, IHe1, IHe2. destruct (existsb _ (expr_vars e1 [])); reflexivity.
  - rewrite existsb_expr_vars, IHe1, IHe2. destruct (existsb _ (expr_vars e1 [])); reflexivity.
  - exact IHe.
Qed.
Lemma live_close1_agree : forall k acc t, live_agree acc t -> live_agree (live_close1 k acc) (live_close1_t k t).
Proof.
  intros k acc t H. unfold live_close1, live_close1_t.
  apply live_agree_fold; [|exact H].
  intros K acc' t' H'. destruct K as [| | | | |e lo hi| | | | |pt prs pargs pk]; try exact H'.
  rewrite (expr_any_live_t_eq acc t e H). destruct (expr_any_live acc e); [apply live_agree_expr; exact H' | exact H'].
Qed.
Lemma cs_gc_eq : forall cs, cs_gc cs = cs_gc_ref cs.
Proof.
  intros cs. unfold cs_gc, cs_gc_ref. destruct (split_lit (reg cs 2)) as [spb spk].
  f_equal. apply filter_ext. intros K.
  pose proof (live_close1_agree (kn cs) _ _ (live_close1_agree (kn cs) _ _ (live_vars_agree cs))) as H.
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2|[b kk] l c|[b kk] l |pt prs pargs pk]; cbn [kn_gc_entry kn_gc_entry_t];
    rewrite ?(expr_all_live_t_eq _ _ _ H); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_vars_lt (b : N) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => N.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.
Definition saddr_vars_lt (b : N) (a : saddr) : bool := expr_vars_lt b (a_base a).

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : N) (s : shape) : bool :=
  match s with
  | SNil | SExit _ | SHole _ | SNext => true
  | SEmitP _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.
Fixpoint sr_vars_lt (b : N) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Definition kentry_vars_lt (b : N) (K : kentry) : bool :=
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
  | KPriv _ rs args _ =>   (* [comment removed for export] *)
      forallb (fun r : saddr * expr => saddr_vars_lt b (fst r) && expr_vars_lt b (snd r)) rs && sr_vars_lt b args
  end.
Fixpoint kn_vars_lt (b : N) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition pairs_vars_lt (b : N) (l : list (expr * expr)) : bool :=
  forallb (fun p => expr_vars_lt b (fst p) && expr_vars_lt b (snd p)) l.
Definition maps_vars_lt (b : N) (ms : list amap) : bool :=
  forallb (fun m => expr_vars_lt b (am_base m) && expr_vars_lt b (am_len m)) ms.
Definition fd_vars_lt (b : N) (f : afd) : bool :=
  match f with FdStd => true | FdFile _ l o => expr_vars_lt b l && expr_vars_lt b o | FdDir => true end.
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && N.leb nx0 v.

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
(* [comment removed for export] *)
Lemma forallb_ext36 : forall (T : Type) (f g : T -> bool), (forall x, f x = g x) -> forall l, forallb f l = forallb g l.
Proof. intros T f g H. induction l as [|x l IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.
Definition nlt_p (bp : positive) (n : N) : bool := Pos.ltb (pos_fast n) bp.
Lemma nlt_p_eq : forall v n, nlt_p (pos_fast v) n = N.ltb n v.
Proof. intros v n. unfold nlt_p. apply pos_fast_ltb. Qed.
Fixpoint expr_vars_ltP (bp : positive) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => nlt_p bp n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_vars_ltP bp x then expr_vars_ltP bp y else false
  | EExt _ _ _ x => expr_vars_ltP bp x
  | EBlob _ _ _ _ => true
  end.
Lemma expr_vars_ltP_eq : forall v e, expr_vars_ltP (pos_fast v) e = expr_vars_lt v e.
Proof.
  intros v e. induction e; cbn [expr_vars_ltP expr_vars_lt]; try reflexivity.
  all: try (rewrite IHe1, IHe2; reflexivity). all: try (rewrite IHe; reflexivity). apply nlt_p_eq.
Qed.
Fixpoint sr_vars_ltP (bp : positive) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => if expr_vars_ltP bp e then sr_vars_ltP bp r else false end.
Lemma sr_vars_ltP_eq : forall v sr, sr_vars_ltP (pos_fast v) sr = sr_vars_lt v sr.
Proof. intros v sr. induction sr as [|e r IH]; [reflexivity|]. cbn [sr_vars_ltP sr_vars_lt]. rewrite expr_vars_ltP_eq, IH. reflexivity. Qed.
Definition kentry_vars_ltP (bp : positive) (K : kentry) : bool :=
  match K with
  | KWord a _ v => if expr_vars_ltP bp (a_base a) then expr_vars_ltP bp v else false
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => if expr_vars_ltP bp (a_base a) then expr_vars_ltP bp n else false
  | KImg _ _ => true
  | KAlign e _ | KRange e _ _ => expr_vars_ltP bp e
  | KDisj a1 n1 a2 n2 =>
      if expr_vars_ltP bp (a_base a1) then if expr_vars_ltP bp n1 then if expr_vars_ltP bp (a_base a2) then expr_vars_ltP bp n2
      else false else false else false
  | KPriv _ rs args _ =>
      if forallb (fun r : saddr * expr => if expr_vars_ltP bp (a_base (fst r)) then expr_vars_ltP bp (snd r) else false) rs
      then sr_vars_ltP bp args else false
  end.
Lemma kentry_vars_ltP_eq : forall v K, kentry_vars_ltP (pos_fast v) K = kentry_vars_lt v K.
Proof.
  intros v K. destruct K; cbn [kentry_vars_ltP kentry_vars_lt]; unfold saddr_vars_lt; rewrite ?expr_vars_ltP_eq; try reflexivity.
  - destruct (expr_vars_lt v (a_base a1)), (expr_vars_lt v n1), (expr_vars_lt v (a_base a2)); reflexivity.
  - rewrite sr_vars_ltP_eq.
    rewrite (forallb_ext36 _ _ (fun r : saddr * expr => saddr_vars_lt v (fst r) && expr_vars_lt v (snd r))%bool).
    + destruct (forallb _ rs); reflexivity.
    + intros [a n]. cbn [fst snd]. unfold saddr_vars_lt. rewrite !expr_vars_ltP_eq. reflexivity.
Qed.
Fixpoint kn_vars_ltP (bp : positive) (k : list kentry) : bool :=
  match k with [] => true | K :: r => if kentry_vars_ltP bp K then kn_vars_ltP bp r else false end.
Lemma kn_vars_ltP_eq : forall v k, kn_vars_ltP (pos_fast v) k = kn_vars_lt v k.
Proof. intros v k. induction k as [|K r IH]; [reflexivity|]. cbn [kn_vars_ltP kn_vars_lt]. rewrite kentry_vars_ltP_eq, IH. reflexivity. Qed.
Definition pairs_vars_ltP (bp : positive) (l : list (expr * expr)) : bool :=
  forallb (fun p => if expr_vars_ltP bp (fst p) then expr_vars_ltP bp (snd p) else false) l.
Lemma pairs_vars_ltP_eq : forall v l, pairs_vars_ltP (pos_fast v) l = pairs_vars_lt v l.
Proof. intros v l. unfold pairs_vars_ltP, pairs_vars_lt. apply forallb_ext36. intros p. rewrite !expr_vars_ltP_eq. reflexivity. Qed.
Definition maps_vars_ltP (bp : positive) (ms : list amap) : bool :=
  forallb (fun m => if expr_vars_ltP bp (am_base m) then expr_vars_ltP bp (am_len m) else false) ms.
Lemma maps_vars_ltP_eq : forall v ms, maps_vars_ltP (pos_fast v) ms = maps_vars_lt v ms.
Proof. intros v ms. unfold maps_vars_ltP, maps_vars_lt. apply forallb_ext36. intros m. rewrite !expr_vars_ltP_eq. reflexivity. Qed.
Definition fd_vars_ltP (bp : positive) (f : afd) : bool :=
  match f with FdStd => true | FdFile _ l o => if expr_vars_ltP bp l then expr_vars_ltP bp o else false | FdDir => true end.
Lemma fd_vars_ltP_eq : forall v f, fd_vars_ltP (pos_fast v) f = fd_vars_lt v f.
Proof. intros v f. destruct f; cbn [fd_vars_ltP fd_vars_lt]; rewrite ?expr_vars_ltP_eq; reflexivity. Qed.
Definition fresh_okP (cs : acs) : bool :=
  let bp := pos_fast (nxt cs) in
  if sr_vars_ltP bp (s_regs (a_ss cs)) then if kn_vars_ltP bp (kn cs) then
  if maps_vars_ltP bp (a_maps cs) then if pairs_vars_ltP bp (a_vis cs) then if pairs_vars_ltP bp (a_ghost cs) then
  if expr_vars_ltP bp (a_brk cs) then if fd_vars_ltP bp (a_fd cs) then N.leb nx0 (nxt cs)
  else false else false else false else false else false else false else false.
Lemma fresh_okP_eq : forall cs, fresh_okP cs = fresh_ok cs.
Proof.
  intros cs. unfold fresh_okP, fresh_ok. cbv zeta.
  rewrite sr_vars_ltP_eq, kn_vars_ltP_eq, maps_vars_ltP_eq, !pairs_vars_ltP_eq, expr_vars_ltP_eq, fd_vars_ltP_eq.
  destruct (sr_vars_lt _ _), (kn_vars_lt _ _), (maps_vars_lt _ _), (pairs_vars_lt _ (a_vis cs)), (pairs_vars_lt _ (a_ghost cs)),
           (expr_vars_lt _ (a_brk cs)), (fd_vars_lt _ _); reflexivity.
Qed.

Definition run_block (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_okP cs then   (* [comment removed for export] *)
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in                 (* [comment removed for export] *)
    let ss0 := clr (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    (* [comment removed for export] *)
    match sym_execTXS_go segs bc kx IT K fuel true stops ss0 [] [] ss0 [] with
    | (ss', sps, tab) =>
        match carryKS bc (s_log ss') sps tab (s_know ss') with
        | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
        | _ => None
        end
    end
  else None.
Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof.
  intros K fuel stops cs. unfold run_block, run_block_ref. rewrite fresh_okP_eq. destruct (fresh_ok cs); [|reflexivity]. cbv zeta.
  set (ss0 := clr (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))).
  assert (Hk0 : s_know ss0 = s_know (a_ss cs)) by reflexivity.
  destruct (sym_execTXS_go_eq segs IT K fuel true stops ss0 [] [] ss0 [] eq_refl eq_refl (Forall_nil _)) as (E1 & E2 & E3).
  rewrite Hk0 in E1, E2, E3.
  destruct (sym_execTXS_go segs (mkbc (facts_of (s_know (a_ss cs)))) (mk_kix (s_know (a_ss cs))) IT K fuel true stops ss0 [] [] ss0 [])
    as [[ss' sps] tab] eqn:Hr.
  cbn [fst snd] in E1, E2, E3.
  assert (Hss : sym_execTX segs IT K fuel true stops (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs))) = ss')
    by (unfold sym_execTX; exact (eq_sym E1)).
  rewrite Hss.
  assert (Hk' : s_know ss' = s_know (a_ss cs)).
  { rewrite <- Hss. rewrite sym_execTX_know. reflexivity. }
  rewrite E2, <- E1. rewrite Hk'. rewrite carryKS_eq by exact E3. rewrite carryK_eq. reflexivity.
Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.

(* [comment removed for export] *)
Fixpoint exprs_eqb (xs ys : list expr) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => expr_eqb x y && exprs_eqb xs' ys'
  | _, _ => false
  end.
Fixpoint rs_eqb (xs ys : list (saddr * expr)) : bool :=
  match xs, ys with
  | [], [] => true
  | (a, n) :: xs', (a', n') :: ys' => saddr_eqb a a' && expr_eqb n n' && rs_eqb xs' ys'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition kentry_eqb (x y : kentry) : bool :=
  match x, y with
  | KWord a w v, KWord a' w' v' => if Nat.eqb w w' then (if saddr_eqb a a' then expr_eqb v v' else false) else false
  | KZero a n, KZero a' n' => if saddr_eqb a a' then expr_eqb n n' else false
  | KBlob a n k, KBlob a' n' k' => if Nat.eqb k k' then (if saddr_eqb a a' then expr_eqb n n' else false) else false
  | KImg lo hi, KImg lo' hi' => if Z.eqb lo lo' then Z.eqb hi hi' else false
  | KAlign e m, KAlign e' m' => if Z.eqb m m' then expr_eqb e e' else false
  | KRange e lo hi, KRange e' lo' hi' => if Z.eqb lo lo' then (if Z.eqb hi hi' then expr_eqb e e' else false) else false
  | KWr a n, KWr a' n' => if saddr_eqb a a' then expr_eqb n n' else false
  | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' =>
      if saddr_eqb a1 a1' then (if saddr_eqb a2 a2' then (if expr_eqb n1 n1' then expr_eqb n2 n2' else false) else false) else false
  | KFill a n c, KFill a' n' c' => if Z.eqb c c' then (if saddr_eqb a a' then expr_eqb n n' else false) else false
  | KUnk a n, KUnk a' n' => if saddr_eqb a a' then expr_eqb n n' else false
  | KPriv t rs args k, KPriv t' rs' args' k' =>
      if Nat.eqb t t' then (if Z.eqb k k' then (if rs_eqb rs rs' then exprs_eqb args args' else false) else false) else false   (* [comment removed for export] *)
  | _, _ => false
  end.

Definition amap_eqb (x y : amap) : bool :=
  if mkind_eqb (am_kind x) (am_kind y) then (if expr_eqb (am_base x) (am_base y) then expr_eqb (am_len x) (am_len y) else false) else false.

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => if eqb a b then list_eqb eqb x' y' else false
  | _, _ => false
  end.

Definition pair_eqb (x y : expr * expr) : bool := if expr_eqb (fst x) (fst y) then expr_eqb (snd x) (snd y) else false.

Definition afd_eqb (x y : afd) : bool :=
  match x, y with
  | FdStd, FdStd => true
  | FdDir, FdDir => true
  | FdFile k l o, FdFile k' l' o' => if Nat.eqb k k' then (if expr_eqb l l' then expr_eqb o o' else false) else false
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition zmix (h x : Z) : Z := Z.land (Z.lxor (Z.shiftl h 5) x) 1073741823.
Fixpoint edig (e : expr) (h : Z) : Z :=
  match e with
  | ELit z => zmix (zmix h 1) z
  | EVar n => zmix (zmix h 2) (Zpos (pos_fast n))   (* [comment removed for export] *)
  | EAlu o a b => edig b (edig a (zmix (zmix h 3) (Z.of_nat (aluop_ix o))))
  | EAluw o a b => edig b (edig a (zmix (zmix h 4) (Z.of_nat (aluop_ix o))))
  | EMd o a b => edig b (edig a (zmix (zmix h 5) (Z.of_nat (mulop_ix o))))
  | EMdw o a b => edig b (edig a (zmix (zmix h 6) (Z.of_nat (mulop_ix o))))
  | EExt sx lo n a => edig a (zmix (zmix (zmix (zmix h 7) (Z.of_nat (bool_ix sx))) (Z.of_nat lo)) (Z.of_nat n))
  | EBlob sx k i n => zmix (zmix (zmix (zmix (zmix h 8) (Z.of_nat (bool_ix sx))) (Z.of_nat k)) i) (Z.of_nat n)
  end.
Definition adig (a : saddr) (h : Z) : Z := zmix (edig (a_base a) h) (a_off a).
Fixpoint rsdig (rs : list (saddr * expr)) (h : Z) : Z :=
  match rs with [] => h | (a, n) :: rest => rsdig rest (edig n (adig a h)) end.
Fixpoint esdig (es : list expr) (h : Z) : Z :=
  match es with [] => h | e :: rest => esdig rest (edig e h) end.
Definition kdig (K : kentry) : Z :=
  match K with
  | KWord a w v => edig v (zmix (adig a 11) (Z.of_nat w))
  | KZero a n => edig n (adig a 12)
  | KBlob a n k => zmix (edig n (adig a 13)) (Z.of_nat k)
  | KImg lo hi => zmix (zmix 14 lo) hi
  | KAlign e m => zmix (edig e 15) m
  | KRange e lo hi => zmix (zmix (edig e 16) lo) hi
  | KWr a n => edig n (adig a 17)
  | KDisj a1 n1 a2 n2 => edig n2 (adig a2 (edig n1 (adig a1 18)))
  | KFill a n c => zmix (edig n (adig a 19)) c
  | KUnk a n => edig n (adig a 20)
  | KPriv t rs args k => zmix (esdig args (rsdig rs (zmix 21 (Z.of_nat t)))) k
  end.
(* [comment removed for export] *)
Definition kkey (K : kentry) : positive := DigI.ikey (DigI.kdigI K).   (* [comment removed for export] *)
Definition kix : Type := ptree (list kentry).
Definition kix_bucket (t : kix) (p : positive) : list kentry := match pt_get t p with Some l => l | None => [] end.
Fixpoint kn_ix (k : list kentry) : kix :=
  match k with
  | [] => PTLeaf
  | X :: rest => let t := kn_ix rest in let p := kkey X in pt_set p (X :: kix_bucket t p) t
  end.
(* [comment removed for export] *)
Definition kn_memI (t : kix) (K : kentry) : bool := existsb (fun X => kentry_eqb X K) (kix_bucket t (kkey K)).
(* [comment removed for export] *)
Definition kn_memI2 (t : kix) (K : kentry) : bool := existsb (kentry_eqb K) (kix_bucket t (kkey K)).

Lemma p_saddr_eqb_eq : forall a b, saddr_eqb a b = true -> a = b.
Proof.
  intros [ab ak] [bb bk] H. unfold saddr_eqb in H. cbn [a_base a_off] in H.
  destruct (Z.eqb ak bk) eqn:H2; [|discriminate H]. apply p_expr_eqb_eq in H. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma p_exprs_eqb_eq : forall xs ys, exprs_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; cbn [exprs_eqb]; intros H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply p_expr_eqb_eq in H1. rewrite (IH ys H2). subst. reflexivity.
Qed.
Lemma p_rs_eqb_eq : forall xs ys, rs_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|[a n] xs IH]; destruct ys as [|[a' n'] ys]; cbn [rs_eqb]; intros H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply p_saddr_eqb_eq in H1. apply p_expr_eqb_eq in H2. rewrite (IH ys H3). subst. reflexivity.
Qed.
Lemma p_kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof.
  intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
  repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
    | H : (if ?c then _ else false) = true |- _ => let E := fresh "E" in destruct c eqn:E; [|discriminate H]
    end;
  repeat match goal with
    | H : saddr_eqb _ _ = true |- _ => apply p_saddr_eqb_eq in H
    | H : expr_eqb _ _ = true |- _ => apply p_expr_eqb_eq in H
    | H : exprs_eqb _ _ = true |- _ => apply p_exprs_eqb_eq in H
    | H : rs_eqb _ _ = true |- _ => apply p_rs_eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    end; subst; reflexivity.
Qed.
Lemma kix_bucket_cons : forall X rest p,
  kix_bucket (kn_ix (X :: rest)) p = if Pos.eqb p (kkey X) then X :: kix_bucket (kn_ix rest) p else kix_bucket (kn_ix rest) p.
Proof.
  intros X rest p. cbn [kn_ix]. unfold kix_bucket at 1.
  destruct (Pos.eqb p (kkey X)) eqn:E.
  - apply Pos.eqb_eq in E. subst p. rewrite pt_gss. reflexivity.
  - apply Pos.eqb_neq in E. rewrite pt_gso by exact E. reflexivity.
Qed.
Lemma kn_memI_eq : forall k K, kn_memI (kn_ix k) K = existsb (fun X => kentry_eqb X K) k.
Proof.
  induction k as [|X rest IH]; intros K.
  - unfold kn_memI, kix_bucket. cbn [kn_ix]. rewrite pt_get_leaf. reflexivity.
  - unfold kn_memI. rewrite kix_bucket_cons. cbn [existsb].
    destruct (Pos.eqb (kkey K) (kkey X)) eqn:E.
    + cbn [existsb]. f_equal. exact (IH K).
    + destruct (kentry_eqb X K) eqn:EQ.
      * apply p_kentry_eqb_eq in EQ. subst X. rewrite Pos.eqb_refl in E. discriminate.
      * cbn [orb]. exact (IH K).
Qed.
Lemma forallb_exteq : forall (T : Type) (f g : T -> bool), (forall x, f x = g x) -> forall l, forallb f l = forallb g l.
Proof. intros T f g H. induction l as [|x l IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.
Lemma filter_exteq : forall (T : Type) (f g : T -> bool), (forall x, f x = g x) -> forall l, List.filter f l = List.filter g l.
Proof. intros T f g H. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. rewrite H, IH. reflexivity. Qed.
Lemma kn_memI2_eq : forall k K, kn_memI2 (kn_ix k) K = existsb (kentry_eqb K) k.
Proof.
  induction k as [|X rest IH]; intros K.
  - unfold kn_memI2, kix_bucket. cbn [kn_ix]. rewrite pt_get_leaf. reflexivity.
  - unfold kn_memI2. rewrite kix_bucket_cons. cbn [existsb].
    destruct (Pos.eqb (kkey K) (kkey X)) eqn:E.
    + cbn [existsb]. f_equal. exact (IH K).
    + destruct (kentry_eqb K X) eqn:EQ.
      * apply p_kentry_eqb_eq in EQ. subst X. rewrite Pos.eqb_refl in E. discriminate.
      * cbn [orb]. exact (IH K).
Qed.

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
  | KPriv _ rs _ _ => priv_apart_x allkn ub uk un rs   (* [comment removed for export] *)
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
  | KPriv _ rs _ _ => priv_apart_xB bc ub uk un rs   (* [comment removed for export] *)
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
  | KPriv _ rs _ _ => priv_apart_p allkn sp ub uk un rs   (* [comment removed for export] *)
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
  | KPriv _ rs _ _ => priv_apart_pB bc sp ub uk un rs   (* [comment removed for export] *)
  end.

Lemma kentry_apart_bpB_eqf : forall fk, kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk.
Proof. intros. bcfe. unfold kentry_apart_bpB, kentry_apart_bp. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.
(* [comment removed for export] *)
Definition ranges_apart_num (bc : bctx) (sp : sprep) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      match sp_rng sp, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + zlit64 z1) (lo2 + k2) || Z.leb (hi2 + k2 + zlit64 z2) (lo1 + k1))%bool
      | _, _ => false
      end
  | _, _ =>
      match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
      | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 => (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool
      | _, _, _, _ => false
      end
  end.
Lemma ranges_apart_num_pB : forall bc sp b1 k1 n1 b2 k2 n2,
  ranges_apart_num bc sp k1 n1 b2 k2 n2 = true -> ranges_apart_pB bc sp b1 k1 n1 b2 k2 n2 = true.
Proof.
  intros bc sp b1 k1 n1 b2 k2 n2 H. unfold ranges_apart_num in H. unfold ranges_apart_pB. cbv zeta.
  destruct n1 as [z1| | | | | | |]; destruct n2 as [z2| | | | | | |];
    destruct (sp_rng sp) as [[lo1 hi1]|]; try discriminate H; destruct (base_rangeB bc b2) as [[lo2 hi2]|]; try discriminate H;
    try (rewrite H; reflexivity);
    destruct (sp_h1 sp) as [h1|]; try discriminate H; destruct (xhiB bc _) as [h2|]; try discriminate H; rewrite H; reflexivity.
Qed.
Definition num_pre (bc : bctx) (sp : sprep) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => if Nat.leb w 8 then ranges_apart_num bc sp uk un b k (ELit (Z.of_nat w)) else false
  | KZero (SA b k) l | KBlob (SA b k) l _ | KWr (SA b k) l | KFill (SA b k) l _ | KUnk (SA b k) l => ranges_apart_num bc sp uk un b k l
  | _ => false
  end.
Lemma num_pre_apart : forall bc sp ub uk un K, num_pre bc sp uk un K = true -> kentry_apart_bpB bc sp ub uk un K = true.
Proof.
  intros bc sp ub uk un K H.
  destruct K as [[b k] w v|[b k] l|[b k] l bk|lo hi|e mm|e lo hi|[b k] l|a1 n1 a2 n2|[b k] l fc|[b k] l|pt prs pargs pk];
    cbn [num_pre] in H; try discriminate H; cbn [kentry_apart_bpB]; try (apply ranges_apart_num_pB; exact H).
  destruct (Nat.leb w 8); [|discriminate H]. cbn [andb]. apply ranges_apart_num_pB; exact H.
Qed.



Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => if kimg_b K then true else kentry_apart_bpB bc sp ub uk un K) (bc_fk bc).   (* [comment removed for export] *)

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof. intros. bcfe. unfold kn_unfillB, kn_unfill. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill. Proof. apply functional_extensionality; intros k. unfold kn_unfillM. apply kn_unfillB_eqf. Qed.



(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition kpriv_b (K : kentry) : bool := match K with KPriv _ _ _ _ => true | _ => false end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition kpriv_geb (X K : kentry) : bool :=
  match X, K with
  | KPriv t rs args k, KPriv t' rs' args' k' => Nat.eqb t t' && rs_eqb rs rs' && exprs_eqb args args' && Z.leb 0 k' && Z.leb k' k
  | _, _ => false
  end.
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
  if (if kwr_b K then true else kentry_apart_bpB bc sp ub uk un K) then [K]   (* [comment removed for export] *)
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof. intros. bcfe. unfold havoc1pB, havoc1p. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc_ref (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.

Definition kn_havocB0 (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).

(* [comment removed for export] *)
Definition hstate : Type := (list (xkey * xpre) * (expr * option (Z * Z)))%type.   (* [comment removed for export] *)
Definition hstate_ok (bc : bctx) (st : hstate) : Prop := table_ok bc (fst st) /\ snd (snd st) = base_rangeB bc (fst (snd st)).
Definition hstate0 (bc : bctx) : hstate := ([], (ELit 0, base_rangeB bc (ELit 0))).
Lemma hstate0_ok : forall bc, hstate_ok bc (hstate0 bc).
Proof. intros bc. split; [constructor | reflexivity]. Qed.
Definition apart_st (bc : bctx) (sp : sprep) (st : hstate) (ub : expr) (uk : Z) (un : expr) (b : expr) (k : Z) (n : expr) : bool * hstate :=
  let '(tab, (cb, cr)) := st in
  let br := if expr_eqb cb b then cr else base_rangeB bc b in
  let '(x, tab') := ranges_apart_pBtr bc sp br tab ub uk un b k n in
  (x, (tab', (b, br))).
Lemma apart_st_eq : forall bc sp st ub uk un b k n, hstate_ok bc st ->
  fst (apart_st bc sp st ub uk un b k n) = ranges_apart_pB bc sp ub uk un b k n /\ hstate_ok bc (snd (apart_st bc sp st ub uk un b k n)).
Proof.
  intros bc sp [tab [cb cr]] ub uk un b k n [Ht Hc]. cbn [fst snd] in Ht, Hc. unfold apart_st.
  assert (Hbr : (if expr_eqb cb b then cr else base_rangeB bc b) = base_rangeB bc b).
  { destruct (expr_eqb cb b) eqn:He; [apply expr_eqb_eqB in He; subst cb; exact Hc | reflexivity]. }
  rewrite Hbr, ranges_apart_pBtr_eq.
  destruct (ranges_apart_pBt_eq bc sp tab ub uk un b k n Ht) as [E O].
  destruct (ranges_apart_pBt bc sp tab ub uk un b k n) as [x tab']. cbn [fst snd] in E, O |- *.
  split; [exact E | split; [exact O | reflexivity]].
Qed.
Definition kentry_apart_bpBt (bc : bctx) (sp : sprep) (st : hstate) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool * hstate :=
  match K with
  | KWord (SA b k) w _ => if Nat.leb w 8 then apart_st bc sp st ub uk un b k (ELit (Z.of_nat w)) else (false, st)
  | KZero (SA b k) l => apart_st bc sp st ub uk un b k l
  | KBlob (SA b k) l _ => apart_st bc sp st ub uk un b k l
  | KImg lo hi => if (Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64)%bool
                  then apart_st bc sp st ub uk un (ELit 0) lo (ELit (hi - lo)) else (false, st)
  | KAlign _ _ => (true, st)
  | KRange _ _ _ => (true, st)
  | KDisj _ _ _ _ => (true, st)
  | KWr (SA b k) n => apart_st bc sp st ub uk un b k n
  | KFill (SA b k) l _ => apart_st bc sp st ub uk un b k l
  | KUnk (SA b k) l => apart_st bc sp st ub uk un b k l
  | KPriv _ rs _ _ => (priv_apart_pB bc sp ub uk un rs, st)
  end.
Lemma kentry_apart_bpBt_eq : forall bc sp st ub uk un K, hstate_ok bc st ->
  fst (kentry_apart_bpBt bc sp st ub uk un K) = kentry_apart_bpB bc sp ub uk un K
  /\ hstate_ok bc (snd (kentry_apart_bpBt bc sp st ub uk un K)).
Proof.
  intros bc sp st ub uk un K Hok. unfold kentry_apart_bpBt, kentry_apart_bpB.
  destruct K as [[b k] w v|[b k] l|[b k] l bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2|[b k] l c|[b k] l|t rs args z];
    try (split; [reflexivity | exact Hok]); try (apply apart_st_eq; exact Hok).
  - destruct (Nat.leb w 8); cbn [andb]; [apply apart_st_eq; exact Hok | split; [reflexivity | exact Hok]].
  - destruct (Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64)%bool; cbn [andb]; [apply apart_st_eq; exact Hok | split; [reflexivity | exact Hok]].
Qed.
Definition havoc1pBt (bc : bctx) (sp : sprep) (st : hstate) (ub : expr) (uk : Z) (un : expr) (K : kentry)
  : list kentry * hstate :=
  if kwr_b K then ([K], st)
  else let '(a, st') := kentry_apart_bpBt bc sp st ub uk un K in
       if a then ([K], st')
       else (match K with
             | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
             | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
             | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
             | _ => []
             end, st').
Lemma havoc1pBt_eq : forall bc sp st ub uk un K, hstate_ok bc st ->
  fst (havoc1pBt bc sp st ub uk un K) = havoc1pB bc sp ub uk un K /\ hstate_ok bc (snd (havoc1pBt bc sp st ub uk un K)).
Proof.
  intros bc sp st ub uk un K Hok. unfold havoc1pBt, havoc1pB.
  destruct (kwr_b K); [split; [reflexivity | exact Hok]|].
  destruct (kentry_apart_bpBt_eq bc sp st ub uk un K Hok) as [E O].
  destruct (kentry_apart_bpBt bc sp st ub uk un K) as [a st']. cbn [fst snd] in E, O. rewrite <- E.
  destruct a; (split; [reflexivity | exact O]).
Qed.
Fixpoint kn_havoc_goBt (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (st : hstate) (l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => let '(o, st') := havoc1pBt bc sp st ub uk un K in o ++ kn_havoc_goBt bc sp ub uk un st' r
  end.
Lemma kn_havoc_goBt_eq : forall bc sp ub uk un l st, hstate_ok bc st ->
  kn_havoc_goBt bc sp ub uk un st l = List.flat_map (havoc1pB bc sp ub uk un) l.
Proof.
  intros bc sp ub uk un l. induction l as [|K r IH]; intros st Hok; [reflexivity|].
  cbn [kn_havoc_goBt List.flat_map]. destruct (havoc1pBt_eq bc sp st ub uk un K Hok) as [E O].
  destruct (havoc1pBt bc sp st ub uk un K) as [o st']. cbn [fst snd] in E, O. rewrite <- E, (IH st' O). reflexivity.
Qed.
Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  kn_havoc_goBt bc sp ub uk un (hstate0 bc) (bc_fk bc).
Lemma kn_havocB_eq0 : forall bc ub uk un, kn_havocB bc ub uk un = kn_havocB0 bc ub uk un.
Proof. intros. unfold kn_havocB, kn_havocB0. cbv zeta. apply kn_havoc_goBt_eq. apply hstate0_ok. Qed.

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc_ref fk.
Proof. intros. bcfe. rewrite kn_havocB_eq0. unfold kn_havocB0, kn_havoc_ref. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havoc (k : list kentry) : expr -> Z -> expr -> list kentry := kn_havocB (mkbc k).
Lemma kn_havoc_eq : kn_havoc = kn_havoc_ref. Proof. apply functional_extensionality; intros k. unfold kn_havoc. apply kn_havocB_eqf. Qed.
Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc. Proof. reflexivity. Qed.



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
Definition kn_keepm (k : list kentry) (ws : list (expr * expr)) (vs : list N) : list kentry :=
  let wss := map (fun w => (split_lit (fst w), xlo k (snd w))) ws in
  let vt := fold_right (fun v t => pt_set (vkey v) tt t) PTLeaf vs in
  let meets (b : expr) (o : Z) (n : option Z) : bool :=
    existsb (fun w => if expr_eqb (fst (fst w)) b then
                        let wk := snd (fst w) in
                        match snd w with
                        | Some wl => Z.ltb 0 wl && Z.ltb wk (match n with Some n => o + n | None => wk + 1 end) && Z.ltb o (wk + wl)
                        | None => true
                        end
                      else false) wss in
  List.filter (fun K => match K with
                        | KWord (SA b o) w _ => meets b o (Some (Z.of_nat w))
                        | KZero (SA b o) n => meets b o (xhi k n)
                        | KBlob (SA b o) n _ => meets b o (xhi k n)
                        | KFill (SA b o) n _ => meets b o (xhi k n)
                        | KUnk (SA b o) n => meets b o (xhi k n)
                        | KWr (SA b o) n => meets b o (xhi k n)
                        | KImg lo hi => meets (ELit 0) lo (Some (hi - lo))
                        | KRange e _ _ => expr_all_live_t vt e
                        | KAlign e _ => expr_all_live_t vt e
                        | KDisj a1 n1 a2 n2 => expr_all_live_t vt (a_base a1) && expr_all_live_t vt n1
                                               && expr_all_live_t vt (a_base a2) && expr_all_live_t vt n2
                        | KPriv _ _ _ _ => true   (* [comment removed for export] *)
                        end%bool) k.

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
Definition know_lookupBX (bc : bctx) (kx : AX2B.kix) (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool)
           (acc : list sidecond) : lres :=
  know_lookupABI bc kx segs (AX2B.kx_kn kx) rb rk n sx hints acc.
Lemma know_lookupBX_eq : forall fk rb rk n sx hints acc,
  know_lookupBX (mkbc fk) (AX2B.mk_kix fk) rb rk n sx hints acc = know_lookupB segs (mkbc fk) rb rk n sx hints acc.
Proof.
  intros. unfold know_lookupBX, know_lookupB. change (AX2B.kx_kn (AX2B.mk_kix fk)) with fk.
  rewrite know_lookupABI_eq. reflexivity.
Qed.
Definition kreadZBX (bc : bctx) (kx : AX2B.kix) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookupBX bc kx b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.
Lemma kreadZBX_eq : forall fk b off n, kreadZBX (mkbc fk) (AX2B.mk_kix fk) b off n = kreadZ fk b off n.
Proof. intros. rewrite <- kreadZB_eqf. unfold kreadZBX, kreadZB. rewrite know_lookupBX_eq. reflexivity. Qed.
Lemma kreadZBX_eqf : forall fk, kreadZBX (mkbc fk) (AX2B.mk_kix fk) = kreadZ fk.
Proof. intros. bcfe. apply kreadZBX_eq. Qed.
Definition kread8eBX (bc : bctx) (kx : AX2B.kix) (b : expr) (off : Z) : option expr :=
  match know_lookupBX bc kx b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.
Lemma kread8eBX_eq : forall fk b off, kread8eBX (mkbc fk) (AX2B.mk_kix fk) b off = kread8e fk b off.
Proof. intros. rewrite <- kread8eB_eqf. unfold kread8eBX, kread8eB. rewrite know_lookupBX_eq. reflexivity. Qed.
Lemma kread8eBX_eqf : forall fk, kread8eBX (mkbc fk) (AX2B.mk_kix fk) = kread8e fk.
Proof. intros. bcfe. apply kread8eBX_eq. Qed.



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
      else if (if Z.eqb (c' mod 256) (c mod 256) then xinsideB bc b off n zb zk zn else false) then true   (* [comment removed for export] *)
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
  if expr_eqb n m then true else if lin_ge0B bc [(n, 0%Z)] [(m, 0%Z)] then lin_ge0B bc [(m, 0%Z)] [(n, 0%Z)] else false.   (* [comment removed for export] *)

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

Fixpoint sr_fresh (sr : list expr) (ixs : list nat) (nx : N) : list expr :=
  match ixs with
  | [] => sr
  | i :: t => sr_fresh (sr_upd sr i (EVar nx)) t (N.succ nx)
  end.

Definition NCS : N := 16.

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
Definition after_call2 (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) (extra : N) : option acs :=
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
Definition var_range_ok0 (k : list kentry) (v : N) (lo hi : Z) : bool :=
  existsb (fun f : sfact =>
    match fst f with
    | [(c, EVar v')] => (N.eqb v' v && Z.ltb 0 c && Z.leb lo ((fst (snd f) + c - 1) / c) && Z.leb (snd (snd f) / c) hi)%bool
    | _ => false
    end) (sum_facts k k).
(* [comment removed for export] *)
Definition sf_vlo (v : N) (f : sfact) : option Z :=
  match fst f with
  | [(c, EVar v')] => if N.eqb v' v then
                        if Z.ltb 0 c then Some ((fst (snd f) + c - 1) / c)
                        else if Z.ltb c 0 then Some ((- snd (snd f) + (- c) - 1) / (- c)) else None
                      else None
  | _ => None
  end.
Definition sf_vhi (v : N) (f : sfact) : option Z :=
  match fst f with
  | [(c, EVar v')] => if N.eqb v' v then
                        if Z.ltb 0 c then Some (snd (snd f) / c)
                        else if Z.ltb c 0 then Some ((- fst (snd f)) / (- c)) else None
                      else None
  | _ => None
  end.
Definition var_range_ok (k : list kentry) (v : N) (lo hi : Z) : bool :=
  let fs := sum_facts k k in
  if (if Z.leb lo 0 then true else existsb (fun f => match sf_vlo v f with Some l => Z.leb lo l | None => false end) fs)
  then (if Z.leb (two64 - 1) hi then true else existsb (fun f => match sf_vhi v f with Some h => Z.leb h hi | None => false end) fs)
  else false.

(* [comment removed for export] *)
Definition kr_lo_ok (k : list kentry) (e : expr) (lo : Z) : bool :=
  existsb (fun K => match K with KRange e' l _ => if Z.leb lo l then expr_eqb e' e else false | _ => false end) k.
Definition kr_hi_ok (k : list kentry) (e : expr) (hi : Z) : bool :=
  existsb (fun K => match K with KRange e' _ h => if Z.leb h hi then expr_eqb e' e else false | _ => false end) k.
(* [comment removed for export] *)
Definition lin_test_q2 (er : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool)
           (f : sfact) (q : Z) : bool :=
  lin_test_rel0 er fs c (sub_fact q (fst f) ts)
    (fun lo hi => if Z.leb 0 q then test (lo + q * fst (snd f))%Z (hi + q * snd (snd f))%Z
                  else test (lo + q * snd (snd f))%Z (hi + q * fst (snd f))%Z).
Definition lin_test_relq2 (er : expr -> option (Z * Z)) (fs : list sfact) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
  existsb (fun f => existsb (fun q => lin_test_q2 er fs c ts test f q) (nodup Z.eq_dec (fact_quots (fst f) ts))) fs.
Definition lin2_lo_ok (k : list kentry) (e : expr) (lo : Z) : bool :=
  let l := lin_of e in
  lin_test_relq2 (erange k) (sum_facts k k) (fst l) (snd l) (fun lo' hi' => (Z.leb lo lo' && Z.leb 0 lo' && Z.ltb hi' two64)%bool).
(* [comment removed for export] *)
Definition lin2_ok (k : list kentry) (e : expr) (lo hi : Z) : bool :=
  let l := lin_of e in
  lin_test_relq2 (erange k) (sum_facts k k) (fst l) (snd l)
    (fun lo' hi' => (Z.leb lo lo' && Z.leb 0 lo' && Z.leb hi' hi && Z.ltb hi' two64)%bool).
Definition range_lo_ok (k : list kentry) (e : expr) (lo : Z) : bool :=
  if Z.leb lo 0 then true
  else if kr_lo_ok k e lo then true
  else if (match xlo2 k e with Some l => Z.leb lo l | None => false end) then true
  else if (match e with EVar v => existsb (fun f => match sf_vlo v f with Some l => Z.leb lo l | None => false end) (sum_facts k k) | _ => false end) then true
  else lin2_lo_ok k e lo.   (* [comment removed for export] *)
Definition range_hi_ok (k : list kentry) (e : expr) (hi : Z) : bool :=
  if Z.leb (two64 - 1) hi then true
  else if kr_hi_ok k e hi then true
  else if (match xhi2 k e with Some h => Z.leb h hi | None => false end) then true
  else match e with EVar v => existsb (fun f => match sf_vhi v f with Some h => Z.leb h hi | None => false end) (sum_facts k k) | _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lin_ge0_deep (k : list kentry) (pos neg : xterms) : bool :=
  if lin_ge0 k pos neg then true else
  if (if xt_nowrap k pos then xt_nowrap k neg else false) then
    let '(c2, t2) := srl_expand k (lsub_e (xt_lin pos) (xt_lin neg)) in
    lin_ge0_scaled k (xt_const pos - xt_const neg + c2)%Z t2
  else false.
Definition lin_ge0_deepB (bc : bctx) (pos neg : xterms) : bool :=
  if lin_ge0B bc pos neg then true else
  if (if xt_nowrapB bc pos then xt_nowrapB bc neg else false) then
    let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
    lin_ge0_scaledB bc (xt_const pos - xt_const neg + c2)%Z t2
  else false.
Lemma lin_ge0_deepB_eqf : forall fk, lin_ge0_deepB (mkbc fk) = lin_ge0_deep fk.
Proof. intros. bcfe. unfold lin_ge0_deepB, lin_ge0_deep. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite lin_ge0_deepB_eqf : bceq.
Definition xinside0_deep (k : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if xinside_refuted k b1 k1 b2 k2 n2 then false
  else if lin_ge0_deep k [(b1, k1)] [(b2, k2)] then lin_ge0_deep k [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Definition xinside0_deepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if xinside_refutedB bc b1 k1 b2 k2 n2 then false
  else if lin_ge0_deepB bc [(b1, k1)] [(b2, k2)] then lin_ge0_deepB bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Lemma xinside0_deepB_eqf : forall fk, xinside0_deepB (mkbc fk) = xinside0_deep fk.
Proof. intros. bcfe. unfold xinside0_deepB, xinside0_deep. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite xinside0_deepB_eqf : bceq.

Definition in_side_l (k : list kentry) (b : expr) (o : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if (match n, m with
      | ELit z, ELit zm => expr_eqb b (a_base c) && Z.leb (a_off c) o && Z.leb 0 z && Z.ltb z two64 && Z.leb 0 zm && Z.ltb zm two64
                           && Z.leb (o + z) (a_off c + zm)
      | _, _ => false
      end)%bool then true   (* [comment removed for export] *)
  else if xinside k b o n (a_base c) (a_off c) m then true
  else if novars (a_base c) then xinside0 k b o n (a_base c) (a_off c) m else false.
Definition kdisj_lin2 (k : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  existsb (fun D => match D with
                    | KDisj c1 m1 c2 m2 =>   (* [comment removed for export] *)
                        if (if in_side_l k b2 k2 n2 c2 m2 then in_side_l k b1 k1 n1 c1 m1 else false) then true
                        else if in_side_l k b2 k2 n2 c1 m1 then in_side_l k b1 k1 n1 c2 m2 else false
                    | _ => false
                    end) k.
(* [comment removed for export] *)
Definition in_side_lB (bc : bctx) (b : expr) (o : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if (match n, m with
      | ELit z, ELit zm => expr_eqb b (a_base c) && Z.leb (a_off c) o && Z.leb 0 z && Z.ltb z two64 && Z.leb 0 zm && Z.ltb zm two64
                           && Z.leb (o + z) (a_off c + zm)
      | _, _ => false
      end)%bool then true
  else if xinsideB bc b o n (a_base c) (a_off c) m then true
  else if novars (a_base c) then xinside0B bc b o n (a_base c) (a_off c) m else false.
Lemma in_side_lB_eqf : forall fk, in_side_lB (mkbc fk) = in_side_l fk.
Proof. intros. bcfe. unfold in_side_lB, in_side_l. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite in_side_lB_eqf : bceq.
Definition kdisj_lin2B0 (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  existsb (fun D => match D with
                    | KDisj c1 m1 c2 m2 =>
                        if (if in_side_lB bc b2 k2 n2 c2 m2 then in_side_lB bc b1 k1 n1 c1 m1 else false) then true
                        else if in_side_lB bc b2 k2 n2 c1 m1 then in_side_lB bc b1 k1 n1 c2 m2 else false
                    | _ => false
                    end) (bc_fk bc).
Lemma kdisj_lin2B0_eqf : forall fk, kdisj_lin2B0 (mkbc fk) = kdisj_lin2 fk.
Proof. intros. bcfe. unfold kdisj_lin2B0, kdisj_lin2. autorewrite with bceq. reflexivity. Qed.
(* [comment removed for export] *)
Lemma in_side_lB_cand : forall bc b o n c m, in_side_lB bc b o n c m = true -> novars (a_base c) = true \/ shares_var b (a_base c) = true.
Proof.
  intros bc b o n c m H. unfold in_side_lB in H.
  destruct (match n, m with
            | ELit z, ELit zm => expr_eqb b (a_base c) && Z.leb (a_off c) o && Z.leb 0 z && Z.ltb z two64 && Z.leb 0 zm && Z.ltb zm two64
                                 && Z.leb (o + z) (a_off c + zm)
            | _, _ => false
            end)%bool eqn:E1.
  - destruct n; try discriminate E1. destruct m; try discriminate E1.
    destruct (expr_eqb b (a_base c)) eqn:He; [|discriminate E1].
    apply p_expr_eqb_eq in He. subst b. destruct (novars (a_base c)) eqn:Hn; [left; reflexivity|]. right.
    apply shares_var_self_gen; [intros v Hv; exact Hv | exact Hn].
  - destruct (xinsideB bc b o n (a_base c) (a_off c) m) eqn:E2; [exact (xinsideB_cand _ _ _ _ _ _ _ E2)|].
    destruct (novars (a_base c)) eqn:Hn; [left; reflexivity | discriminate H].
Qed.
Lemma in_side_lB_guard : forall bc b o n c m,
  (if cand (ekeys b []) (ekeys (a_base c) []) (novars (a_base c)) then in_side_lB bc b o n c m else false) = in_side_lB bc b o n c m.
Proof.
  intros bc b o n c m. destruct (cand _ _ _) eqn:Hc; [reflexivity|]. destruct (cand_false _ _ Hc) as [H1 H2].
  destruct (in_side_lB bc b o n c m) eqn:Hs; [|reflexivity]. destruct (in_side_lB_cand _ _ _ _ _ _ Hs); congruence.
Qed.
Fixpoint kdisj_lin2BX (bc : bctx) (ds : list kdx) (kb1 kb2 : list positive) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match ds with
  | [] => false
  | d :: rest =>
      if (if cand kb2 (kd_k2 d) (kd_l2 d) then if cand kb1 (kd_k1 d) (kd_l1 d) then
            (if in_side_lB bc b2 k2 n2 (kd_c2 d) (kd_m2 d) then in_side_lB bc b1 k1 n1 (kd_c1 d) (kd_m1 d) else false)
          else false else false) then true
      else if (if cand kb2 (kd_k1 d) (kd_l1 d) then if cand kb1 (kd_k2 d) (kd_l2 d) then
            (if in_side_lB bc b2 k2 n2 (kd_c1 d) (kd_m1 d) then in_side_lB bc b1 k1 n1 (kd_c2 d) (kd_m2 d) else false)
          else false else false) then true
      else kdisj_lin2BX bc rest kb1 kb2 b1 k1 n1 b2 k2 n2
  end.
Lemma kdisj_lin2BX_eq : forall bc kn b1 k1 n1 b2 k2 n2,
  kdisj_lin2BX bc (mk_kdx kn) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2
  = existsb (fun D => match D with
                      | KDisj c1 m1 c2 m2 =>
                          if (if in_side_lB bc b2 k2 n2 c2 m2 then in_side_lB bc b1 k1 n1 c1 m1 else false) then true
                          else if in_side_lB bc b2 k2 n2 c1 m1 then in_side_lB bc b1 k1 n1 c2 m2 else false
                      | _ => false
                      end) kn.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [mk_kdx existsb]; try exact IH.
  cbn [kdisj_lin2BX kd_c1 kd_m1 kd_c2 kd_m2 kd_k1 kd_l1 kd_k2 kd_l2].
  rewrite (guard2 _ _ _ _ (in_side_lB_guard bc b2 k2 n2 _ _) (in_side_lB_guard bc b1 k1 n1 _ _)).
  rewrite (guard2 _ _ _ _ (in_side_lB_guard bc b2 k2 n2 _ _) (in_side_lB_guard bc b1 k1 n1 _ _)).
  rewrite IH. match goal with |- (if ?x then _ else _) = _ => destruct x end; [reflexivity|].
  match goal with |- (if ?x then _ else _) = _ => destruct x end; reflexivity.
Qed.
Definition kdisj_lin2B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  kdisj_lin2BX bc (bc_kd bc) (ekeys b1 []) (ekeys b2 []) b1 k1 n1 b2 k2 n2.
Lemma kdisj_lin2B_eqf : forall fk, kdisj_lin2B (mkbc fk) = kdisj_lin2 fk.
Proof.
  intros fk. rewrite <- kdisj_lin2B0_eqf. bcfe. unfold kdisj_lin2B, kdisj_lin2B0. rewrite bc_kd_mkbc, kdisj_lin2BX_eq, bc_fk_mkbc. reflexivity.
Qed.
#[local] Hint Rewrite kdisj_lin2B_eqf : bceq.
(* [comment removed for export] *)
Definition in_side_ld (k : list kentry) (b : expr) (o : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if in_side_l k b o n c m then true
  else if novars (a_base c) then xinside0_deep k b o n (a_base c) (a_off c) m else false.
Definition in_side_ldB (bc : bctx) (b : expr) (o : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  if in_side_lB bc b o n c m then true
  else if novars (a_base c) then xinside0_deepB bc b o n (a_base c) (a_off c) m else false.
Lemma in_side_ldB_eqf : forall fk, in_side_ldB (mkbc fk) = in_side_ld fk.
Proof. intros. bcfe. unfold in_side_ldB, in_side_ld. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite in_side_ldB_eqf : bceq.
Definition kdisj_lin2d (k : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  existsb (fun D => match D with
                    | KDisj c1 m1 c2 m2 =>
                        if (if in_side_ld k b2 k2 n2 c2 m2 then in_side_ld k b1 k1 n1 c1 m1 else false) then true
                        else if in_side_ld k b2 k2 n2 c1 m1 then in_side_ld k b1 k1 n1 c2 m2 else false
                    | _ => false
                    end) k.
Definition kdisj_lin2dB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  existsb (fun D => match D with
                    | KDisj c1 m1 c2 m2 =>
                        if (if in_side_ldB bc b2 k2 n2 c2 m2 then in_side_ldB bc b1 k1 n1 c1 m1 else false) then true
                        else if in_side_ldB bc b2 k2 n2 c1 m1 then in_side_ldB bc b1 k1 n1 c2 m2 else false
                    | _ => false
                    end) (bc_fk bc).
Lemma kdisj_lin2dB_eqf : forall fk, kdisj_lin2dB (mkbc fk) = kdisj_lin2d fk.
Proof. intros. bcfe. unfold kdisj_lin2dB, kdisj_lin2d. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kdisj_lin2dB_eqf : bceq.

(* [comment removed for export] *)
Definition kfoot_kdisj (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => if Nat.leb w 8 then kdisj_lin2B bc ub uk un kb kk (ELit (Z.of_nat w)) else false
  | KBlob (SA kb kk) l _ | KZero (SA kb kk) l | KFill (SA kb kk) l _ | KUnk (SA kb kk) l | KWr (SA kb kk) l => kdisj_lin2B bc ub uk un kb kk l
  | _ => false
  end.
Definition havoc1pK (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kwr_b K then [K]
  else if kentry_apart_bpB bc sp ub uk un K then [K]
  else if kfoot_kdisj bc ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.
Definition kn_havocK0 (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let bc := mkbc k in let sp := mk_sprepB bc ub uk un in List.flat_map (havoc1pK bc sp ub uk un) k.
(* [comment removed for export] *)
Definition havoc1pKt (bc : bctx) (sp : sprep) (st : hstate) (ub : expr) (uk : Z) (un : expr) (K : kentry)
  : list kentry * hstate :=
  if kwr_b K then ([K], st)
  else let '(a, st') := kentry_apart_bpBt bc sp st ub uk un K in
       if a then ([K], st')
       else ((if kfoot_kdisj bc ub uk un K then [K]
              else match K with
                   | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
                   | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
                   | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
                   | _ => []
                   end), st').
Lemma havoc1pKt_eq : forall bc sp st ub uk un K, hstate_ok bc st ->
  fst (havoc1pKt bc sp st ub uk un K) = havoc1pK bc sp ub uk un K /\ hstate_ok bc (snd (havoc1pKt bc sp st ub uk un K)).
Proof.
  intros bc sp st ub uk un K Hok. unfold havoc1pKt, havoc1pK.
  destruct (kwr_b K); [split; [reflexivity | exact Hok]|].
  destruct (kentry_apart_bpBt_eq bc sp st ub uk un K Hok) as [E O].
  destruct (kentry_apart_bpBt bc sp st ub uk un K) as [a st']. cbn [fst snd] in E, O. rewrite <- E.
  destruct a; (split; [reflexivity | exact O]).
Qed.
Fixpoint kn_havoc_goKt (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (st : hstate) (l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => let '(o, st') := havoc1pKt bc sp st ub uk un K in o ++ kn_havoc_goKt bc sp ub uk un st' r
  end.
Lemma kn_havoc_goKt_eq : forall bc sp ub uk un l st, hstate_ok bc st ->
  kn_havoc_goKt bc sp ub uk un st l = List.flat_map (havoc1pK bc sp ub uk un) l.
Proof.
  intros bc sp ub uk un l. induction l as [|K r IH]; intros st Hok; [reflexivity|].
  cbn [kn_havoc_goKt List.flat_map]. destruct (havoc1pKt_eq bc sp st ub uk un K Hok) as [E O].
  destruct (havoc1pKt bc sp st ub uk un K) as [o st']. cbn [fst snd] in E, O. rewrite <- E, (IH st' O). reflexivity.
Qed.
Definition kn_havocK (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let bc := mkbc k in let sp := mk_sprepB bc ub uk un in kn_havoc_goKt bc sp ub uk un (hstate0 bc) k.
Lemma kn_havocK_eq0 : forall k ub uk un, kn_havocK k ub uk un = kn_havocK0 k ub uk un.
Proof. intros. unfold kn_havocK, kn_havocK0. cbv zeta. apply kn_havoc_goKt_eq. apply hstate0_ok. Qed.

(* [comment removed for export] *)
Definition fact_ok_ref (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      if (match xlo2 k e, xhi2 k e with
          | Some l, Some h => Z.leb lo l && Z.leb h hi
          | _, _ => false
          end)%bool then true
      else if (if range_lo_ok k e lo then range_hi_ok k e hi else false) then true   (* [comment removed for export] *)
      else lin2_ok k e lo hi   (* [comment removed for export] *)
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (ealign k e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => if ranges_apart_x k b1 k1 n1 b2 k2 n2 then true else if kdisj_lin2 k b1 k1 n1 b2 k2 n2 then true else kdisj_lin2d k b1 k1 n1 b2 k2 n2   (* [comment removed for export] *)
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => (Z.leb lo' lo && Z.leb hi hi')%bool | _ => false end) k   (* [comment removed for export] *)
  | KPriv _ _ _ _ => existsb (fun X => kpriv_geb X K) k   (* [comment removed for export] *)
  | _ => false
  end.
(* [comment removed for export] *)
Definition range_lo_okB (bc : bctx) (k : list kentry) (e : expr) (lo : Z) : bool :=
  if Z.leb lo 0 then true
  else if kr_lo_ok k e lo then true
  else if (match xlo2B bc e with Some l => Z.leb lo l | None => false end) then true
  else if (match e with EVar v => existsb (fun f => match sf_vlo v f with Some l => Z.leb lo l | None => false end) (bc_fs bc) | _ => false end) then true
  else lin2_lo_ok k e lo.   (* [comment removed for export] *)
Definition range_hi_okB (bc : bctx) (k : list kentry) (e : expr) (hi : Z) : bool :=
  if Z.leb (two64 - 1) hi then true
  else if kr_hi_ok k e hi then true
  else if (match xhi2B bc e with Some h => Z.leb h hi | None => false end) then true
  else match e with EVar v => existsb (fun f => match sf_vhi v f with Some h => Z.leb h hi | None => false end) (bc_fs bc) | _ => false end.
Definition fact_okB (bc : bctx) (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      if (match xlo2B bc e, xhi2B bc e with
          | Some l, Some h => Z.leb lo l && Z.leb h hi
          | _, _ => false
          end)%bool then true
      else if (if range_lo_okB bc k e lo then range_hi_okB bc k e hi else false) then true
      else lin2_ok k e lo hi   (* [comment removed for export] *)
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (ealignB bc e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => if ranges_apart_xB bc b1 k1 n1 b2 k2 n2 then true else if kdisj_lin2B bc b1 k1 n1 b2 k2 n2 then true else kdisj_lin2dB bc b1 k1 n1 b2 k2 n2
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => (Z.leb lo' lo && Z.leb hi hi')%bool | _ => false end) k
  | KPriv _ _ _ _ => existsb (fun X => kpriv_geb X K) k   (* [comment removed for export] *)
  | _ => false
  end.
Definition fact_ok (k : list kentry) (K : kentry) : bool := fact_okB (mkbc k) k K.
Lemma fact_ok_eq : forall k K, fact_ok k K = fact_ok_ref k K.
Proof.
  intros k K. unfold fact_ok, fact_okB, fact_ok_ref, range_lo_okB, range_hi_okB, range_lo_ok, range_hi_ok.
  rewrite ?xlo2B_eqf, ?xhi2B_eqf, ?ealignB_eqf, ?ranges_apart_xB_eqf, ?kdisj_lin2B_eqf, ?kdisj_lin2dB_eqf, ?bc_fs_mkbc. reflexivity.
Qed.

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

(* [comment removed for export] *)
Fixpoint kread_bytesBX (bc : bctx) (kx : AX2B.kix) (fuel : nat) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZBX bc kx b off 1 with
           | Some z => match kread_bytesBX bc kx f b (off + 1) with
                       | Some rest => Some (z :: rest)
                       | None => None
                       end
           | None => None
           end
  end.
Lemma kread_bytesBX_eq : forall fk fuel b off, kread_bytesBX (mkbc fk) (AX2B.mk_kix fk) fuel b off = kread_bytes fuel fk b off.
Proof.
  intros fk fuel. induction fuel as [|f IH]; intros b off; [reflexivity|].
  cbn [kread_bytesBX kread_bytes]. rewrite kreadZBX_eq, IH.
  destruct (kreadZ fk b off 1); [|reflexivity]. destruct (kread_bytes f fk b (off + 1)); reflexivity.
Qed.
Lemma kread_bytesBX_eqf : forall fk, kread_bytesBX (mkbc fk) (AX2B.mk_kix fk) = (fun fuel => kread_bytes fuel fk).
Proof. intros fk. bcfe. apply kread_bytesBX_eq. Qed.


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
Fixpoint drop_by (f : nat -> bool) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if f i then drop_by f (S i) r else K :: drop_by f (S i) r
  end.
Fixpoint mark_pos (i : nat) (m : list bool) : list bool :=
  match m with [] => [] | b :: r => match i with O => true :: r | S j => b :: mark_pos j r end end.
Definition mask_of (ixs : list nat) (n : nat) : list bool := List.fold_left (fun m i => mark_pos i m) ixs (List.repeat false n).
Fixpoint drop_mask (m : list bool) (k : list kentry) : list kentry :=
  match k, m with
  | [], _ => []
  | K :: r, b :: m' => if b then drop_mask m' r else K :: drop_mask m' r
  | K :: r, [] => K :: r
  end.
Definition drop_ixsM (ixs : list nat) (k : list kentry) : list kentry := drop_mask (mask_of ixs (length k)) k.
Lemma drop_ixs_by : forall ixs i k, drop_ixs ixs i k = drop_by (fun j => existsb (Nat.eqb j) ixs) i k.
Proof. intros ixs i k. revert i. induction k as [|K r IH]; intros i; cbn [drop_ixs drop_by]; [reflexivity|]. rewrite !IH. reflexivity. Qed.
Lemma drop_mask_by : forall f k m i, length m = length k -> (forall j, (j < length k)%nat -> nth j m false = f (i + j)%nat) ->
  drop_mask m k = drop_by f i k.
Proof.
  intros f k. induction k as [|K r IH]; intros m i HL Hn; [destruct m; reflexivity|].
  destruct m as [|b m']; [discriminate HL|]. cbn [drop_mask drop_by].
  assert (Hb : b = f i) by (rewrite <- (Nat.add_0_r i); exact (Hn O ltac:(cbn; lia))).
  assert (IH' : drop_mask m' r = drop_by f (S i) r).
  { apply IH; [cbn in HL; lia|]. intros j Hj. specialize (Hn (S j) ltac:(cbn; lia)). cbn [nth] in Hn. rewrite Hn. f_equal. lia. }
  rewrite Hb, IH'. reflexivity.
Qed.
Lemma mark_pos_length : forall i m, length (mark_pos i m) = length m.
Proof. intros i m. revert i. induction m as [|b r IH]; intros [|j]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma mark_pos_nth : forall i m j, (j < length m)%nat -> nth j (mark_pos i m) false = (nth j m false || Nat.eqb j i)%bool.
Proof.
  intros i m. revert i. induction m as [|b r IH]; intros i j Hj; [cbn in Hj; lia|].
  destruct i as [|i']; destruct j as [|j']; cbn [mark_pos nth Nat.eqb].
  - rewrite orb_true_r. reflexivity.
  - destruct (Nat.eqb (S j') 0) eqn:E; [discriminate E|]. rewrite orb_false_r. reflexivity.
  - rewrite orb_false_r. reflexivity.
  - apply IH. cbn in Hj. lia.
Qed.
Lemma fold_mark_length : forall ixs m, length (List.fold_left (fun m i => mark_pos i m) ixs m) = length m.
Proof. induction ixs as [|x xs IH]; intros m; cbn [List.fold_left]; [reflexivity|]. rewrite IH. apply mark_pos_length. Qed.
Lemma fold_mark_nth : forall ixs m j, (j < length m)%nat ->
  nth j (List.fold_left (fun m i => mark_pos i m) ixs m) false = (nth j m false || existsb (Nat.eqb j) ixs)%bool.
Proof.
  induction ixs as [|x xs IH]; intros m j Hj; cbn [List.fold_left existsb]; [rewrite orb_false_r; reflexivity|].
  rewrite IH by (rewrite mark_pos_length; exact Hj). rewrite mark_pos_nth by exact Hj. rewrite orb_assoc. reflexivity.
Qed.
Lemma drop_ixsM_eq : forall ixs k, drop_ixsM ixs k = drop_ixs ixs 0 k.
Proof.
  intros ixs k. unfold drop_ixsM, mask_of. rewrite drop_ixs_by. apply drop_mask_by.
  - rewrite fold_mark_length, repeat_length. reflexivity.
  - intros j Hj. rewrite fold_mark_nth by (rewrite repeat_length; exact Hj). rewrite nth_repeat. reflexivity.
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

Definition node_fresh_ref (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs :=
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
        (* [comment removed for export] *)
        let kj := match xlo2 k (reg cs r), xhi2 k (reg cs r) with
                  | Some rlo, Some rhi =>
                      if Z.leb logc (ealign k b) then [KRange (eadd b ne) (((rlo + c - 1) / c) * c) ((rhi / c) * c)]
                      else [KRange (eadd b ne) rlo rhi]
                  | _, _ => []
                  end in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: kres ++ kj in
        Some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => None
    end
  else None.
(* [comment removed for export] *)
Definition residue_factB (bc : bctx) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1B bc e', xhi1B bc e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].
Definition node_fresh (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs :=
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
        let kj := match xlo2B bc (reg cs r), xhi2B bc (reg cs r) with
                  | Some rlo, Some rhi =>
                      if Z.leb logc (ealignB bc b) then [KRange (eadd b ne) (((rlo + c - 1) / c) * c) ((rhi / c) * c)]
                      else [KRange (eadd b ne) rlo rhi]
                  | _, _ => []
                  end in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: kres ++ kj in
        Some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => None
    end
  else None.
Lemma node_fresh_eq : forall cs r logc base, node_fresh cs r logc base = node_fresh_ref cs r logc base.
Proof.
  intros. unfold node_fresh, node_fresh_ref, residue_factB, residue_fact. cbv zeta.
  rewrite ?ealignB_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?xlo1B_eqf, ?xhi1B_eqf. reflexivity.
Qed.

(* [comment removed for export] *)
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havoc (kn cs) bb bk n).

(* [comment removed for export] *)
Definition node_bump (cs : acs) (m : N) : option acs :=
  if N.leb (nxt cs) m then Some (bump cs (m - nxt cs)) else None.

(* [comment removed for export] *)
Definition node_havoc (cs : acs) (rs : list nat) : option acs :=
  if (fresh_ok cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (sr_fresh (s_regs ss) rs (s_next ss)) (s_know ss) (s_next ss + N.of_nat (length rs))))
  else None.

(* [comment removed for export] *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  | _ => 1%nat
  end.
Definition bigb (K : nat) (e : expr) : bool := Nat.ltb K (esize e).
Fixpoint kn_bigsubst (K : nat) (k : list kentry) (nx : N) : list kentry * N :=
  match k with
  | [] => ([], 0%N)
  | KWord a w v :: r =>
      if bigb K v then let '(r', c) := kn_bigsubst K r (N.succ nx) in (KWord a w (EVar nx) :: r', N.succ c)
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
  List.find (fun m => if (negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds)%bool then xinsideB bc b off n (am_base m) 0 (am_len m) else false) ms.   (* [comment removed for export] *)

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. intros. bcfe. unfold find_containingB, find_containing. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.


(* [comment removed for export] *)
Definition find_containing2 (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  match find_containing k ms kinds b off n with
  | Some m => Some m
  | None =>
      match List.find (fun m => if (negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && novars (am_base m))%bool
                                then xinside0 k b off n (am_base m) 0 (am_len m) else false) ms with   (* [comment removed for export] *)
      | Some m => Some m
      | None => List.find (fun m => if (negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && novars (am_base m))%bool
                                    then xinside0_deep k b off n (am_base m) 0 (am_len m) else false) ms   (* [comment removed for export] *)
      end
  end.
Definition find_containing2B (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  match find_containingB bc ms kinds b off n with
  | Some m => Some m
  | None =>
      match List.find (fun m => if (negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && novars (am_base m))%bool
                                then xinside0B bc b off n (am_base m) 0 (am_len m) else false) ms with   (* [comment removed for export] *)
      | Some m => Some m
      | None => List.find (fun m => if (negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && novars (am_base m))%bool
                                    then xinside0_deepB bc b off n (am_base m) 0 (am_len m) else false) ms   (* [comment removed for export] *)
      end
  end.
Lemma find_containing2B_eqf : forall fk, find_containing2B (mkbc fk) = find_containing2 fk.
Proof. intros. bcfe. unfold find_containing2B, find_containing2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite find_containing2B_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. intros. bcfe. unfold shadow_ofB, shadow_of. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
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
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof. intros. unfold vis_add, vis_add_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_factsB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf. reflexivity. Qed.


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
Definition disj_side_fact2 (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : list kentry :=
  match nA, base_range k cB with
  | ELit _, _ => []
  | _, Some (_, bhi) => if Z.leb 0 (bhi + oB) then [KRange (esub (esub (eaddz cB oB) (eaddz cA oA)) nA) 0 (bhi + oB)] else []
  | _, None => []
  end.
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) :=
  let k := kn cs in
  match find_disj k b1 b2 with
  | Some (c1, o1, n1, c2, o2, n2) =>
      match flat_x k c1 o1 n1, flat_x k c2 o2 n2, disj_side_fact k c1 o1 n1 c2 o2, disj_side_fact k c2 o2 n2 c1 o1 with
      | true, true, Some K1, Some K2 => Some (add_kn cs (K1 :: disj_side_fact2 k c1 o1 n1 c2 o2), add_kn cs (K2 :: disj_side_fact2 k c2 o2 n2 c1 o1))
      | _, _, _, _ => None
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
  | m :: rest => (negb (is_fog m) && xinside k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => if (if is_fog m then false else xinsideB bc b off len (am_base m) 0 (am_len m)) then true else inside_mapsB bc rest b off len   (* [comment removed for export] *)
  end.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros b. apply functional_extensionality; intros off. apply functional_extensionality; intros len. 
  revert b off len. induction ms as [|m rest IH]; intros; bcfe; [reflexivity|].
  cbn [inside_mapsB inside_maps]. rewrite IH. autorewrite with bceq. destruct (is_fog m); reflexivity.   (* [comment removed for export] *)
Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint covered_b (fuel : nat) (ms : list amap) (lo hi : Z) : bool :=
  if Z.leb hi lo then true else
  match fuel with
  | O => false
  | S f =>
      match List.find (fun m => match am_base m, am_len m with
                                | ELit b, ELit l => negb (is_fog m) && Z.leb b lo && Z.ltb lo (b + l) && Z.leb 0 b && Z.leb 0 l && Z.ltb (b + l) two64
                                | _, _ => false
                                end) ms with
      | Some m => match am_base m, am_len m with
                  | ELit b, ELit l => covered_b f ms (b + l) hi
                  | _, _ => false
                  end
      | None => false
      end
  end.
Definition band_cover (ms : list amap) : bool := covered_b (length ms) ms LOWTOP KHI.

Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (lin_ge0 k [(b, off)] [(e_top, 0)] && Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
        || (Z.leb LOWTOP (lo + off) && Z.leb (hi + off + lh) KHI && band_cover ms)   (* [comment removed for export] *)
    | _, _ => false
    end) || inside_maps k ms b off len)%bool.

(* [comment removed for export] *)
Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match xhiB bc len, base_rangeB bc b with
  | Some lh, Some (lo, hi) =>
      if (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))%bool then true    (* [comment removed for export] *)
      else if inside_mapsB bc ms b off len then true
      else if (Z.leb LOWTOP (lo + off) && Z.leb (hi + off + lh) KHI && band_cover ms)%bool then true   (* [comment removed for export] *)
      else if (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)%bool then lin_ge0B bc [(b, off)] [(e_top, 0)]   (* [comment removed for export] *)
      else false
  | _, _ => inside_mapsB bc ms b off len
  end.

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros b.
  apply functional_extensionality; intros off. apply functional_extensionality; intros len.
  unfold safe_rangeB, safe_range. autorewrite with bceq.
  destruct (xhi fk len) as [lh|]; [|reflexivity]. destruct (base_range fk b) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))%bool; [rewrite !orb_true_r; reflexivity|rewrite orb_false_r].
  destruct (inside_maps fk ms b off len); [rewrite orb_true_r; reflexivity|rewrite orb_false_r].
  destruct (Z.leb LOWTOP (lo + off) && Z.leb (hi + off + lh) KHI && band_cover ms)%bool; [rewrite !orb_true_r; reflexivity|rewrite orb_false_r].
  destruct (lin_ge0 fk [(b, off)] [(e_top, 0)]); cbn [andb];
    destruct (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)%bool; reflexivity.
Qed.
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
  | KPriv _ rs _ _ => forallb (fun r : saddr * expr => safe_range k ms (a_base (fst r)) (a_off (fst r)) (snd r)) rs   (* [comment removed for export] *)
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
  | KPriv _ rs _ _ => forallb (fun r : saddr * expr => safe_rangeB bc ms (a_base (fst r)) (a_off (fst r)) (snd r)) rs   (* [comment removed for export] *)
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
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m with
                     | ELit _ => []
                     | mb => [KDisj (SA mb 0) (am_len m) (SA nb 0) ne]
                     end) ms.

(* [comment removed for export] *)
Definition kdisj_all (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA nb 0) ne]) ms.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_band_lit (m : amap) : bool :=
  match am_base m, am_len m with
  | ELit b, ELit l => (Z.leb LOWTOP b && Z.leb (b + l) KHI)%bool
  | _, _ => false
  end.
Definition kdisj_grant (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  KDisj (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A)) (SA nb 0) ne
  :: KDisj (SA e_sp0 (- STK)) (esub (ELit (2 ^ 47)) e_top) (SA nb 0) ne   (* [comment removed for export] *)
  :: kdisj_all (if band_cover ms then List.filter (fun m => negb (in_band_lit m)) ms else ms) nb ne.

(* [comment removed for export] *)
Definition band_entries (ms : list amap) : list amap :=
  List.filter (fun m => match am_base m, am_len m with
                        | ELit b, ELit l => (negb (is_fog m) && Z.ltb b KHI && Z.ltb LOWTOP (b + l))%bool
                        | _, _ => false
                        end) ms.

(* [comment removed for export] *)
Definition off_band (k : list kentry) (ms : list amap) (b : expr) (off : Z) (n : expr) : bool :=
  (band_cover ms && inside_maps k ms b off n
   && forallb (fun m => ranges_apart_x k b off n (am_base m) 0 (am_len m)) (band_entries ms))%bool.
(* [comment removed for export] *)
Fixpoint inside_mapsL (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => if (if negb (is_fog m) then xinsideB bc b off len (am_base m) 0 (am_len m) else false) then true
                 else inside_mapsL bc rest b off len
  end.
Lemma inside_mapsL_eq : forall bc ms b off len, inside_mapsL bc ms b off len = inside_mapsB bc ms b off len.
Proof. intros bc ms. induction ms as [|m rest IH]; intros; [reflexivity|]. cbn [inside_mapsL inside_mapsB]. rewrite IH. destruct (is_fog m); reflexivity. Qed.   (* [comment removed for export] *)
Definition off_bandB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (n : expr) : bool :=
  if (if band_cover ms then inside_mapsL bc ms b off n else false)
  then forallb (fun m => ranges_apart_xB bc b off n (am_base m) 0 (am_len m)) (band_entries ms) else false.
Lemma off_bandB_eqf : forall fk, off_bandB (mkbc fk) = off_band fk.
Proof.
  intros. bcfe. unfold off_bandB, off_band. rewrite inside_mapsL_eq. autorewrite with bceq. reflexivity.
Qed.
(* [comment removed for export] *)
Definition off_bandL (k : list kentry) (ms : list amap) (b : expr) (off : Z) (n : expr) (pre : bool) : bool :=
  if pre then true else off_bandB (mkbc k) ms b off n.
Lemma off_bandL_or : forall k ms b off n pre, off_bandL k ms b off n pre = (pre || off_band k ms b off n)%bool.
Proof. intros. unfold off_bandL. rewrite off_bandB_eqf. destruct pre; reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : N)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 + nlo) TOPMAX]
  end.

(* [comment removed for export] *)
Definition vis_add_banded (cs1 : acs) (b n : expr) (kmem : list kentry) (kL kH : list kentry) : option acs :=
  match vis_add (set_kn cs1 (kL ++ kn cs1)) b n (kmem ++ kL ++ kn cs1),
        vis_add (set_kn cs1 (kH ++ kn cs1)) b n (kmem ++ kH ++ kn cs1) with
  | Some cL, Some cH =>
      let shL := shadow_facts (kL ++ kn cs1) (a_maps cs1) b n in
      let shH := shadow_facts (kH ++ kn cs1) (a_maps cs1) b n in
      if (list_eqb kentry_eqb shL shH && Z.eqb (a_abytes cL) (a_abytes cH))%bool
      then Some (set_kn cL (shL ++ kmem ++ kn cs1)) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition null_vlo (cs : acs) (nlo : Z) : Z :=
  if (band_cover (a_maps cs) && Z.ltb (LOWTOP - 4096) nlo)%bool then KHI / 4096
  else if Z.ltb (img_lo A - 4096) nlo then img_hi A / 4096 else 1.
(* [comment removed for export] *)
Definition null_band (ms : list amap) (base ne : expr) : list kentry :=
  if band_cover ms then [KDisj (SA (ELit LOWTOP) 0) (ELit (KHI - LOWTOP)) (SA base 0) ne] else [].

(* [comment removed for export] *)
Definition base_var (e : expr) : option N :=
  match e with EMd M_MUL (ELit 4096) (EVar v) => Some v | _ => None end.
Definition entry_band (k : list kentry) (m : amap) : option (N * Z) :=
  match base_var (am_base m), xlo k (am_len m) with
  | Some v, Some nlo =>
      match xhi k (EVar v) with
      | Some vh =>
          if (Z.leb vh (2 ^ 51) && Z.leb 0 nlo
              && existsb (kentry_eqb (KDisj (SA (ELit LOWTOP) 0) (ELit (KHI - LOWTOP)) (SA (am_base m) 0) (am_len m))) k)%bool
          then Some (v, nlo) else None
      | None => None
      end
  | _, _ => None
  end.
Definition vis_add_in (cs cs1 : acs) (m : amap) (a ne : expr) (b : expr) (off : Z) : option acs :=
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  match entry_band (kn cs) m with
  | Some (v, nlo) =>
      match vis_add_banded cs1 a ne kmem [KRange (EVar v) 0 ((LOWTOP - nlo) / 4096)]
                                         [KRange (EVar v) (KHI / 4096) ((TOPMAX - nlo) / 4096)] with
      | Some c => Some c
      | None => vis_add cs1 a ne (kmem ++ kn cs1)
      end
  | None => vis_add cs1 a ne (kmem ++ kn cs1)
  end.

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && Z.leb 0 nlo && Z.leb nhi TOPMAX
          && no_holes (a_maps cs))%bool then      
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := KRange (EVar v) (null_vlo cs nlo) ((TOPMAX - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_grant (a_maps cs) base ne
                      ++ null_band (a_maps cs) base ne ++ [KRange (esub e_top (eadd base ne)) 0 TOPMAX] in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterB (mkbc (kn cs)) (a_maps cs) in   (* [comment removed for export] *)
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (N.succ v) (AM base ne kind) nhi eager (a_ylo cs) in
        if visible then
          if band_cover (a_maps cs) then
            vis_add_banded cs1 base ne kmem
              [KRange (EVar v) 1 ((LOWTOP - nlo) / 4096); KRange (eadd base ne) (4096 + nlo) LOWTOP]   (* [comment removed for export] *)
              [KRange (EVar v) (KHI / 4096) ((TOPMAX - nlo) / 4096)]                                (* [comment removed for export] *)
          else None
        else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && Z.leb (img_hi A) alo && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition fixed_args_in (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

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
  match fixed_args cs CEIL with      (* [comment removed for export] *)
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else
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
  end.

(* [comment removed for export] *)
Definition kn_rezero (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ | KPriv _ _ _ _ => kentry_apart_bp k sp ub uk un K
                        | _ => true
                        end) k.

Definition kn_rezeroB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ | KPriv _ _ _ _ => kentry_apart_bpB bc sp ub uk un K
                        | _ => true
                        end) (bc_fk bc).

Lemma kn_rezeroB_eqf : forall fk, kn_rezeroB (mkbc fk) = kn_rezero fk.
Proof. intros. bcfe. unfold kn_rezeroB, kn_rezero. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.

Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Lemma kn_rezeroM_eq : kn_rezeroM = kn_rezero. Proof. apply functional_extensionality; intros k. unfold kn_rezeroM. apply kn_rezeroB_eqf. Qed.

(* [comment removed for export] *)
Definition in_other_map (k : list kentry) (ms : list amap) (m : amap) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                         else xinside k kb kk (ELit (Z.of_nat w)) (am_base m') 0 (am_len m')) ms
  | KBlob (SA kb kk) l _ | KFill (SA kb kk) l _ | KZero (SA kb kk) l | KUnk (SA kb kk) l | KWr (SA kb kk) l =>   (* [comment removed for export] *)
      existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                         else xinside k kb kk l (am_base m') 0 (am_len m')) ms
  | KPriv _ rs _ _ =>   (* [comment removed for export] *)
      forallb (fun r => match r with
                        | (SA kb kk, l) => existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                                                               else xinside k kb kk l (am_base m') 0 (am_len m')) ms
                        end) rs
  | _ => false
  end.
Definition in_other_mapB0 (bc : bctx) (ms : list amap) (m : amap) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                         else xinsideB bc kb kk (ELit (Z.of_nat w)) (am_base m') 0 (am_len m')) ms
  | KBlob (SA kb kk) l _ | KFill (SA kb kk) l _ | KZero (SA kb kk) l | KUnk (SA kb kk) l | KWr (SA kb kk) l =>
      existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                         else xinsideB bc kb kk l (am_base m') 0 (am_len m')) ms
  | KPriv _ rs _ _ =>
      forallb (fun r => match r with
                        | (SA kb kk, l) => existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                                                               else xinsideB bc kb kk l (am_base m') 0 (am_len m')) ms
                        end) rs
  | _ => false
  end.
Lemma in_other_mapB0_eqf : forall fk, in_other_mapB0 (mkbc fk) = in_other_map fk.
Proof. intros. bcfe. unfold in_other_mapB0, in_other_map. autorewrite with bceq. reflexivity. Qed.
(* [comment removed for export] *)
Definition xinsideB_r (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then (if xinside_numBr bc br1 k1 n1 b2 k2 n2 then true
                           else match n1 with ELit _ => false | _ => xinside0B bc b1 k1 n1 b2 k2 n2 end) else false.
Definition in_other_mapB (bc : bctx) (ms : list amap) (m : amap) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      let br := base_rangeB bc kb in
      existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                         else xinsideB_r bc br kb kk (ELit (Z.of_nat w)) (am_base m') 0 (am_len m')) ms
  | KBlob (SA kb kk) l _ | KFill (SA kb kk) l _ | KZero (SA kb kk) l | KUnk (SA kb kk) l | KWr (SA kb kk) l =>
      let br := base_rangeB bc kb in
      existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                         else xinsideB_r bc br kb kk l (am_base m') 0 (am_len m')) ms
  | KPriv _ rs _ _ =>
      forallb (fun r => match r with
                        | (SA kb kk, l) => let br := base_rangeB bc kb in
                                           existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                                                              else xinsideB_r bc br kb kk l (am_base m') 0 (am_len m')) ms
                        end) rs
  | _ => false
  end.
Lemma in_other_mapB_r : forall bc ms m K, in_other_mapB bc ms m K = in_other_mapB0 bc ms m K.
Proof.
  intros bc ms m K.
  destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk|lo hi|e mm|e lo hi|[kb kk] l|a1 n1 a2 n2|[kb kk] l fc|[kb kk] l|pt prs pargs pk]; reflexivity.
Qed.
Lemma in_other_mapB_eqf : forall fk, in_other_mapB (mkbc fk) = in_other_map fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros m.
  apply functional_extensionality; intros K. rewrite in_other_mapB_r, in_other_mapB0_eqf. reflexivity.
Qed.
#[local] Hint Rewrite in_other_mapB_eqf : bceq.
(* [comment removed for export] *)
Definition priv_mix (k : list kentry) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (rs : list (saddr * expr)) : bool :=
  forallb (fun r => match r with
                    | (SA kb kk, l) => if ranges_apart_p k sp ub uk un kb kk l then true
                                       else existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                                                               else xinside k kb kk l (am_base m') 0 (am_len m')) ms
                    end) rs.
Definition priv_mixB (bc : bctx) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (rs : list (saddr * expr)) : bool :=
  forallb (fun r => match r with
                    | (SA kb kk, l) => if ranges_apart_pB bc sp ub uk un kb kk l then true
                                       else existsb (fun m' => if is_fog m' then false else if amap_eqb m' m then false
                                                               else xinsideB bc kb kk l (am_base m') 0 (am_len m')) ms
                    end) rs.
Lemma priv_mixB_eqf : forall fk, priv_mixB (mkbc fk) = priv_mix fk.
Proof. intros. bcfe. unfold priv_mixB, priv_mix. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite priv_mixB_eqf : bceq.
Definition in_other_mapR (k : list kentry) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  if in_other_map k ms m K then true
  else match K with KPriv _ rs _ _ => priv_mix k ms m sp ub uk un rs | _ => false end.
Definition in_other_mapRB (bc : bctx) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  if in_other_mapB bc ms m K then true
  else match K with KPriv _ rs _ _ => priv_mixB bc ms m sp ub uk un rs | _ => false end.
Lemma in_other_mapRB_eqf : forall fk, in_other_mapRB (mkbc fk) = in_other_mapR fk.
Proof. intros. bcfe. unfold in_other_mapRB, in_other_mapR. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite in_other_mapRB_eqf : bceq.
Definition kn_rezero2 (k : list kentry) (ms : list amap) (m : amap) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => if kentry_apart_bp k sp ub uk un K then true else in_other_mapR k ms m sp ub uk un K
                        | KPriv _ _ _ _ => if kentry_apart_bp k sp ub uk un K then true else in_other_mapR k ms m sp ub uk un K   (* [comment removed for export] *)
                        | _ => true
                        end) k.
Definition kn_rezero2B (bc : bctx) (ms : list amap) (m : amap) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ | KPriv _ _ _ _ =>   (* [comment removed for export] *)
                            if num_pre bc sp uk un K then true else if in_other_mapRB bc ms m sp ub uk un K then true else kentry_apart_bpB bc sp ub uk un K
                        | _ => true
                        end) (bc_fk bc).
Lemma kn_rezero2B_eqf : forall fk, kn_rezero2B (mkbc fk) = kn_rezero2 fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros m.
  apply functional_extensionality; intros ub. apply functional_extensionality; intros uk. apply functional_extensionality; intros un.
  unfold kn_rezero2B, kn_rezero2. rewrite bc_fk_mkbc, mk_sprepB_eqf. cbv zeta.
  apply filter_ext. intros K. rewrite kentry_apart_bpB_eqf, in_other_mapRB_eqf.
  destruct K; try reflexivity;
    (destruct (num_pre (mkbc fk) (mk_sprep fk ub uk un) uk un _) eqn:Hn;
     [ lazymatch goal with |- context [kentry_apart_bp fk ?sp ?ub' ?uk' ?un' ?K'] =>
         assert (Hap0 : kentry_apart_bp fk sp ub' uk' un' K' = true) by (rewrite <- kentry_apart_bpB_eqf; apply num_pre_apart; exact Hn);
         rewrite Hap0; reflexivity end
     | destruct (kentry_apart_bp fk (mk_sprep fk ub uk un) ub uk un _); destruct (in_other_mapR fk ms m (mk_sprep fk ub uk un) ub uk un _); reflexivity ]).
Qed.
#[local] Hint Rewrite kn_rezero2B_eqf : bceq.
(* [comment removed for export] *)
Definition cutout1p2 (k : list kentry) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kentry_apart_bp k sp ub uk un K then [K]
  else if in_other_mapR k ms m sp ub uk un K then [K]   (* [comment removed for export] *)
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cut k ub uk un kb kk len
       | _ => []
       end.
Definition cutout1p2B (bc : bctx) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if num_pre bc sp uk un K then [K]   (* [comment removed for export] *)
  else if in_other_mapRB bc ms m sp ub uk un K then [K]   (* [comment removed for export] *)
  else if kentry_apart_bpB bc sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | KWr (SA kb kk) len => kwr_cutB bc ub uk un kb kk len
       | _ => []
       end.
Lemma cutout1p2B_eqf : forall fk, cutout1p2B (mkbc fk) = cutout1p2 fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros m.
  apply functional_extensionality; intros sp. apply functional_extensionality; intros ub.
  apply functional_extensionality; intros uk. apply functional_extensionality; intros un. apply functional_extensionality; intros K.
  unfold cutout1p2B, cutout1p2.
  destruct (num_pre (mkbc fk) sp uk un K) eqn:Hn.
  { assert (Hap0 : kentry_apart_bp fk sp ub uk un K = true) by (rewrite <- kentry_apart_bpB_eqf; apply num_pre_apart; exact Hn).
    rewrite Hap0. reflexivity. }
  rewrite kentry_apart_bpB_eqf, in_other_mapRB_eqf.
  destruct (kentry_apart_bp fk sp ub uk un K); destruct (in_other_mapR fk ms m sp ub uk un K); try reflexivity.
  autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite cutout1p2B_eqf : bceq.
Definition kn_cutout2 (k : list kentry) (ms : list amap) (m : amap) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (cutout1p2 k ms m sp ub uk un) k.
Definition kn_cutout2B (bc : bctx) (ms : list amap) (m : amap) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1p2B bc ms m sp ub uk un) (bc_fk bc).
Lemma kn_cutout2B_eqf : forall fk, kn_cutout2B (mkbc fk) = kn_cutout2 fk.
Proof. intros. bcfe. unfold kn_cutout2B, kn_cutout2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_cutout2B_eqf : bceq.
(* [comment removed for export] *)
Definition led_kinds : list mkind := [KRW; KRWLAZY; KNONE; KNONELAZY].
Definition havoc1p2 (k : list kentry) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bp k sp ub uk un K)%bool then [K]
  else if in_other_mapR k ms m sp ub uk un K then [K]   (* [comment removed for export] *)
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cut c k ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cut k ub uk un kb kk len
       | _ => []
       end.
Definition havoc1p2B (bc : bctx) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if kwr_b K then [K]
  else if num_pre bc sp uk un K then [K]   (* [comment removed for export] *)
  else if in_other_mapRB bc ms m sp ub uk un K then [K]   (* [comment removed for export] *)
  else if kentry_apart_bpB bc sp ub uk un K then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
       | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
       | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
       | _ => []
       end.
Lemma havoc1p2B_eqf : forall fk, havoc1p2B (mkbc fk) = havoc1p2 fk.
Proof.
  intros fk. apply functional_extensionality; intros ms. apply functional_extensionality; intros m.
  apply functional_extensionality; intros sp. apply functional_extensionality; intros ub.
  apply functional_extensionality; intros uk. apply functional_extensionality; intros un. apply functional_extensionality; intros K.
  unfold havoc1p2B, havoc1p2.
  destruct (kwr_b K); [reflexivity|]. cbn [orb].
  destruct (num_pre (mkbc fk) sp uk un K) eqn:Hn.
  { assert (Hap0 : kentry_apart_bp fk sp ub uk un K = true) by (rewrite <- kentry_apart_bpB_eqf; apply num_pre_apart; exact Hn).
    rewrite Hap0. reflexivity. }
  rewrite kentry_apart_bpB_eqf, in_other_mapRB_eqf.
  destruct (kentry_apart_bp fk sp ub uk un K); destruct (in_other_mapR fk ms m sp ub uk un K); try reflexivity.
  autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite havoc1p2B_eqf : bceq.
Definition kn_havoc_led (k : list kentry) (ms : list amap) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  match find_containing2 k ms led_kinds ub uk un with
  | Some m => let sp := mk_sprep k ub uk un in List.flat_map (havoc1p2 k ms m sp ub uk un) k
  | None => kn_havoc k ub uk un
  end.
(* [comment removed for export] *)
Definition havoc1p2Bt (bc : bctx) (ms : list amap) (m : amap) (sp : sprep) (st : hstate) (ub : expr) (uk : Z) (un : expr) (K : kentry)
  : list kentry * hstate :=
  if kwr_b K then ([K], st)
  else if num_pre bc sp uk un K then ([K], st)
  else if in_other_mapRB bc ms m sp ub uk un K then ([K], st)
  else let '(a, st') := kentry_apart_bpBt bc sp st ub uk un K in
       if a then ([K], st')
       else (match K with
             | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
             | KFill (SA kb kk) len c => kfill_cutB bc c ub uk un kb kk len
             | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
             | _ => []
             end, st').
Lemma havoc1p2Bt_eq : forall bc ms m sp st ub uk un K, hstate_ok bc st ->
  fst (havoc1p2Bt bc ms m sp st ub uk un K) = havoc1p2B bc ms m sp ub uk un K
  /\ hstate_ok bc (snd (havoc1p2Bt bc ms m sp st ub uk un K)).
Proof.
  intros bc ms m sp st ub uk un K Hok. unfold havoc1p2Bt, havoc1p2B.
  destruct (kwr_b K); [split; [reflexivity | exact Hok]|].
  destruct (num_pre bc sp uk un K); [split; [reflexivity | exact Hok]|].
  destruct (in_other_mapRB bc ms m sp ub uk un K); [split; [reflexivity | exact Hok]|].
  destruct (kentry_apart_bpBt_eq bc sp st ub uk un K Hok) as [E O].
  destruct (kentry_apart_bpBt bc sp st ub uk un K) as [a st']. cbn [fst snd] in E, O. rewrite <- E.
  destruct a; (split; [reflexivity | exact O]).
Qed.
Fixpoint kn_havoc_go2Bt (bc : bctx) (ms : list amap) (m : amap) (sp : sprep) (ub : expr) (uk : Z) (un : expr)
         (st : hstate) (l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => let '(o, st') := havoc1p2Bt bc ms m sp st ub uk un K in o ++ kn_havoc_go2Bt bc ms m sp ub uk un st' r
  end.
Lemma kn_havoc_go2Bt_eq : forall bc ms m sp ub uk un l st, hstate_ok bc st ->
  kn_havoc_go2Bt bc ms m sp ub uk un st l = List.flat_map (havoc1p2B bc ms m sp ub uk un) l.
Proof.
  intros bc ms m sp ub uk un l. induction l as [|K r IH]; intros st Hok; [reflexivity|].
  cbn [kn_havoc_go2Bt List.flat_map]. destruct (havoc1p2Bt_eq bc ms m sp st ub uk un K Hok) as [E O].
  destruct (havoc1p2Bt bc ms m sp st ub uk un K) as [o st']. cbn [fst snd] in E, O. rewrite <- E, (IH st' O). reflexivity.
Qed.
Definition kn_havoc_ledB (bc : bctx) (ms : list amap) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  match find_containing2B bc ms led_kinds ub uk un with
  | Some m => let sp := mk_sprepB bc ub uk un in kn_havoc_go2Bt bc ms m sp ub uk un (hstate0 bc) (bc_fk bc)
  | None => kn_havocB bc ub uk un
  end.
Lemma kn_havoc_ledB_eqf : forall fk, kn_havoc_ledB (mkbc fk) = kn_havoc_led fk.
Proof.
  intros. bcfe. unfold kn_havoc_ledB, kn_havoc_led. rewrite find_containing2B_eqf. unfold kn_havoc.
  destruct (find_containing2 fk _ led_kinds _ _ _); [|reflexivity]. cbv zeta. rewrite kn_havoc_go2Bt_eq by apply hstate0_ok.
  autorewrite with bceq. reflexivity.
Qed.
#[local] Hint Rewrite kn_havoc_ledB_eqf : bceq.
(* [comment removed for export] *)
Definition fact_led (cs : acs) (K : kentry) : bool :=
  match K with
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 =>
      match find_containing2 (kn cs) (a_maps cs) led_kinds b1 k1 n1 with
      | Some m1 => match find_containing2 (kn cs) (a_maps cs) led_kinds b2 k2 n2 with
                   | Some m2 => negb (amap_eqb m1 m2)
                   | None => false
                   end
      | None => false
      end
  | _ => false
  end.
(* [comment removed for export] *)
Definition fact_okc (cs : acs) (K : kentry) : bool := if fact_ok (kn cs) K then true else fact_led cs K.
(* [comment removed for export] *)
Definition kfoot_of (K : kentry) : option (saddr * expr) :=
  match K with
  | KWord a w _ => Some (a, ELit (Z.of_nat w))
  | KBlob a n _ | KZero a n | KFill a n _ | KUnk a n | KWr a n => Some (a, n)
  | _ => None
  end.
Definition disj_nth (cs : acs) (b1 n1 : expr) (i : nat) : option kentry :=
  match nth_error (kn cs) i with
  | Some K => match kfoot_of K with Some (a, n) => Some (KDisj (SA b1 0) n1 a n) | None => None end
  | None => None
  end.



(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args_in cs TOPMAX with   (* [comment removed for export] *)
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containing2 k (a_maps cs) kinds b off ne with   (* [comment removed for export] *)
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition fixed_in_args (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args_in cs TOPMAX with   (* [comment removed for export] *)
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containing2B bc (a_maps cs) kinds b off ne with   (* [comment removed for export] *)
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.

Lemma fixed_in_args_eq : forall cs arm, fixed_in_args cs arm = fixed_in_args_ref cs arm.
Proof. intros. unfold fixed_in_args, fixed_in_args_ref. unfold ehi, elo. rewrite ?find_containing2B_eqf. reflexivity. Qed.


(* [comment removed for export] *)
Definition rezero_kn (k : list kentry) (b : expr) (off : Z) (ne : expr) (k0 : list kentry) : list kentry :=
  if kwritable_x k k b off ne then KZero (SA b off) ne :: k0 else k0.

(* [comment removed for export] *)
Definition mmap_fixed_in_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfill k b off ne)
                  | ArmF => rezero_kn k b off ne (kimg_clip (kn_rezero2 k (a_maps cs) m b off ne))   (* [comment removed for export] *)
                  | ArmG => kimg_clip (kn_cutout k b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add_in cs cs1 m (reg cs 10) ne b off | _ => Some cs1 end   (* [comment removed for export] *)
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
                  | ArmF => rezero_kn k b off ne (kimg_clip (kn_rezero2B bc (a_maps cs) m b off ne))   (* [comment removed for export] *)
                  | ArmG => kimg_clip (kn_cutoutB bc b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add_in cs cs1 m (reg cs 10) ne b off | _ => Some cs1 end   (* [comment removed for export] *)
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition mmap_fixed_in_x (cs : acs) (arm : fixed_in_arm) : option ((expr * Z * expr * Z * Z * amap) * acs) :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfillB bc b off ne)
                  | ArmF => rezero_kn k b off ne (kimg_clip (kn_rezero2B bc (a_maps cs) m b off ne))   (* [comment removed for export] *)
                  | ArmG => kimg_clip (kn_cutoutB bc b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        option_map (fun c => ((b, off, ne, nlo, nhi, m), c))
                   (match arm with ArmE => vis_add_in cs cs1 m (reg cs 10) ne b off | _ => Some cs1 end)
      else None
  | None => None
  end.

Lemma mmap_fixed_in_eq : forall cs arm, mmap_fixed_in cs arm = mmap_fixed_in_ref cs arm.
Proof. intros. unfold mmap_fixed_in, mmap_fixed_in_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf, ?kn_rezeroB_eqf, ?kn_rezero2B_eqf, ?kn_unfillB_eqf. reflexivity. Qed.
Lemma mmap_fixed_in_x_spec : forall cs arm a csO, mmap_fixed_in_x cs arm = Some (a, csO) ->
  fixed_in_args cs arm = Some a /\ mmap_fixed_in cs arm = Some csO.
Proof.
  intros cs arm a csO H. unfold mmap_fixed_in_x in H. unfold mmap_fixed_in.
  destruct (fixed_in_args cs arm) as [[[[[[b off] ne] nlo] nhi] m]|]; [|discriminate H]. cbv zeta in H |- *.
  destruct (match arm with ArmE => budget_ok cs nhi | _ => true end); [|discriminate H].
  match type of H with option_map _ ?X = _ => destruct X as [c|] eqn:HX end; [|discriminate H].
  cbn [option_map] in H. injection H as <- <-. split; reflexivity.
Qed.



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
  let hp := if hole then [AM a ne KHOLE] else [] in       
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutout2 k (a_maps cs) m b off ne)) (s_next ss))   (* [comment removed for export] *)
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
(* [comment removed for export] *)
Definition mmap_destroyed_with (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in       
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutout2B bc (a_maps cs) m b off ne)) (s_next ss))   (* [comment removed for export] *)
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Lemma mmap_destroyed_with_eq : forall hole cs b off ne m lne rne, mmap_destroyed_with hole cs b off ne m lne rne = mmap_destroyed_with_ref hole cs b off ne m lne rne.
Proof. intros. unfold mmap_destroyed_with, mmap_destroyed_with_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf, ?kn_cutout2B_eqf. reflexivity. Qed.


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
Definition dest_casesB (bc : bctx) (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let ls := if lin_ge0B bc [(a, -1)] [(mb, 0)] then [true]
            else if (if expr_eqb a mb then true else lin_ge0B bc [(mb, 0)] [(a, 0)]) then [false]
            else [true; false] in
  let rs := if lin_ge0B bc [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]
            else if lin_ge0B bc [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]
            else [true; false] in
  flat_map (fun l => map (fun r => (l, r)) rs) ls.
Definition mmap_destroyed_kc (hole : bool) (cs : acs) (ne : expr) (m : amap) (kc : list kentry) (lne rne : bool) : acs :=
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kc) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
Definition mmap_destroyed_f (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs :=
  let bc := mkbc (kn cs) in
  let kc := kimg_clip (kn_cutout2B bc (a_maps cs) m b off ne) in
  map (fun lr => mmap_destroyed_kc hole cs ne m kc (fst lr) (snd lr)) (dest_casesB bc cs ne m).
Lemma mmap_destroyed_f_eqf : mmap_destroyed_f = mmap_destroyed.
Proof.
  apply functional_extensionality; intros hole. apply functional_extensionality; intros cs.
  apply functional_extensionality; intros b. apply functional_extensionality; intros off.
  apply functional_extensionality; intros ne. apply functional_extensionality; intros m.
  unfold mmap_destroyed_f, mmap_destroyed. cbv zeta.
  assert (DC : dest_casesB (mkbc (kn cs)) cs ne m = dest_cases cs ne m).
  { unfold dest_casesB, dest_cases. rewrite !lin_ge0B_eqf. reflexivity. }
  rewrite DC. apply map_ext. intros [l r]. cbn [fst snd]. rewrite mmap_destroyed_with_eq.
  unfold mmap_destroyed_kc, mmap_destroyed_with_ref. rewrite kn_cutout2B_eqf. reflexivity.
Qed.

(* [comment removed for export] *)
Definition kn_cheapcutB (bc : bctx) (ms : list amap) (m : amap) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => match K with
                        | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
                        | KImg _ _ => kentry_apart_bpB bc sp ub uk un K
                        | _ => if num_pre bc sp uk un K then true else in_other_mapRB bc ms m sp ub uk un K
                        end) (bc_fk bc).
Definition mmap_destroyedS (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs :=
  let bc := mkbc (kn cs) in
  let kc := kimg_clip (kn_cheapcutB bc (a_maps cs) m b off ne) in
  map (fun lr => mmap_destroyed_kc false cs ne m kc (fst lr) (snd lr)) (dest_casesB bc cs ne m).
Lemma cheapcut_sub : forall k ms m b off ne K,
  In K (kimg_clip (kn_cheapcutB (mkbc k) ms m b off ne)) -> In K (kimg_clip (kn_cutout2B (mkbc k) ms m b off ne)).
Proof.
  intros k ms m b off ne K H. unfold kimg_clip in *. apply filter_In in H as [H Hc]. apply filter_In. split; [|exact Hc].
  unfold kn_cheapcutB in H. apply filter_In in H as [Hin Hf]. rewrite bc_fk_mkbc in Hin.
  unfold kn_cutout2B. rewrite bc_fk_mkbc. apply in_flat_map. exists K. split; [exact Hin|].
  unfold cutout1p2B. cbv beta in Hf.
  destruct (num_pre (mkbc k) (mk_sprepB (mkbc k) b off ne) off ne K) eqn:Hn; [left; reflexivity|].
  destruct (in_other_mapRB (mkbc k) ms m (mk_sprepB (mkbc k) b off ne) b off ne K) eqn:Hi; [left; reflexivity|].
  destruct (kentry_apart_bpB (mkbc k) (mk_sprepB (mkbc k) b off ne) b off ne K) eqn:Ha; [left; reflexivity|].
  exfalso. destruct K; cbn iota in Hf; rewrite ?Hn, ?Hi, ?Ha in Hf; cbn in Hf; try discriminate Hf.
  all: cbn [kentry_apart_bpB] in Ha; discriminate Ha.
Qed.

(* [comment removed for export] *)
Definition EEXIST_RET : Z := two64 - 17.
Definition refuse_e (cs : acs) (ret : Z) : acs := set_pc (set_reg cs 10 (ELit ret)) (pc cs + 4).

(* [comment removed for export] *)
Definition mmap_nr_occ_ref (cs : acs) : option (acs * acs) :=
  match fixed_args_in cs TOPMAX with
  | Some (b, off, ne, nlo, nhi) =>
      match find_containing (kn cs) (a_maps cs) [KRW; KRWLAZY; KNONE; KNONELAZY] b off ne with
      | Some _ => Some (refuse cs, refuse_e cs EEXIST_RET)
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition mmap_nr_occ (cs : acs) : option (acs * acs) :=
  match fixed_args_in cs TOPMAX with
  | Some (b, off, ne, nlo, nhi) =>
      match find_containingB (mkbc (kn cs)) (a_maps cs) [KRW; KRWLAZY; KNONE; KNONELAZY] b off ne with
      | Some _ => Some (refuse cs, refuse_e cs EEXIST_RET)
      | None => None
      end
  | None => None
  end.
Lemma mmap_nr_occ_eq : forall cs, mmap_nr_occ cs = mmap_nr_occ_ref cs.
Proof. intros. unfold mmap_nr_occ, mmap_nr_occ_ref. rewrite ?find_containingB_eqf. reflexivity. Qed.

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
                 | 3, 0x104022 | 3, 0x104032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x100022 | 3, 0x100032 => mmap_fixed_free cs KRW true true        (* [comment removed for export] *)
                 | 0, 0x104022 | 0, 0x104032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x100022 | 0, 0x100032 => mmap_fixed_free cs KNONE false false    (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with
      | Some csG => Some (refuse cs, csG)
      | None =>   (* [comment removed for export] *)
          if isnull then None else
          match prot, flags with
          | 0, 0x104022 => mmap_nr_occ cs
          | _, _ => None
          end
      end
  | None => None
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
          match mmap_fixed_in_x cs arm with   (* [comment removed for export] *)
          | Some ((b, off, ne, nlo, nhi, m), csO) => Some (refuse cs, csO, mmap_destroyed_f hole cs b off ne m)   (* [comment removed for export] *)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_mmapinS (cs : acs) : option (acs * acs * list acs) :=
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
          match mmap_fixed_in_x cs arm with   (* [comment removed for export] *)
          | Some ((b, off, ne, nlo, nhi, m), csO) => Some (refuse cs, csO, mmap_destroyedS cs b off ne m)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args_in cs TOPMAX with   (* [comment removed for export] *)
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
            vis_add_in cs cs1 m (reg cs 10) ne b off   (* [comment removed for export] *)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args_in cs TOPMAX with   (* [comment removed for export] *)
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add_in cs cs1 m (reg cs 10) ne b off   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
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
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_grow_possible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kn_grant_filterB (mkbc k) (a_maps cs) in   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition node_brk2s (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kdisj_all (a_maps cs) b (ELit (d + 4096)) ++ kn_grant_filterB (mkbc k) (a_maps cs) in   (* [comment removed for export] *)
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

(* [comment removed for export] *)

Definition node_settid (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 96 =>
      if (negb (a_tidset cs) && fresh_ok cs)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) (KRange (EVar v) 1 (PID_MAX - 1) :: s_know ss) (N.succ v))
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
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
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
Fixpoint ghost_dedup (gs : list (expr * expr)) : list (expr * expr) :=
  match gs with
  | [] => []
  | p :: rest => if existsb (pair_eqb p) rest then ghost_dedup rest else p :: ghost_dedup rest
  end.
Definition node_ghostdedup (cs : acs) : acs :=
  ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (ghost_dedup (a_ghost cs))
      (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition vis_here (b n : expr) (p : expr * expr) : bool := (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool.

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  match xhi k b, xhi k n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) TOPMAX   (* [comment removed for export] *)
          && flat_x k sb sk sn && kzero_x k k sb sk sn)%bool
      then
        let k1 := kn_cutout k bb bk n in     (* [comment removed for export] *)
        let k2 := kn_cutout k1 sb sk sn in
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
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) TOPMAX   (* [comment removed for export] *)
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
      then
        let k1 := kn_cutoutB bc bb bk n in   (* [comment removed for export] *)
        let k2 := kn_cutoutM k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_unvis_eq : forall cs b n, node_unvis cs b n = node_unvis_ref cs b n.
Proof. intros. unfold node_unvis, node_unvis_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?kn_cutoutB_eqf, ?kzero_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?kn_cutoutM_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition ghost_covers (k : list kentry) (gs : list (expr * expr)) (bb : expr) (bk : Z) (n : expr) : bool :=
  existsb (fun g => let '(gb, gk) := split_lit (fst g) in (flat_x k gb gk (snd g) && xinside k bb bk n gb gk (snd g))%bool) gs.
(* [comment removed for export] *)
Definition kentry_apart_lin (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => if Nat.leb w 8 then (if shares_var b ub then false else kdisj_lin2 k ub uk un b o (ELit (Z.of_nat w))) else false
  | KZero (SA b o) l | KBlob (SA b o) l _ | KWr (SA b o) l | KFill (SA b o) l _ | KUnk (SA b o) l =>
      if shares_var b ub then false else kdisj_lin2 k ub uk un b o l
  | _ => false
  end.
Definition kentry_apart_linB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => if Nat.leb w 8 then (if shares_var b ub then false else kdisj_lin2B bc ub uk un b o (ELit (Z.of_nat w))) else false
  | KZero (SA b o) l | KBlob (SA b o) l _ | KWr (SA b o) l | KFill (SA b o) l _ | KUnk (SA b o) l =>
      if shares_var b ub then false else kdisj_lin2B bc ub uk un b o l
  | _ => false
  end.
Lemma kentry_apart_linB_eqf : forall fk, kentry_apart_linB (mkbc fk) = kentry_apart_lin fk.
Proof. intros. bcfe. unfold kentry_apart_linB, kentry_apart_lin. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kentry_apart_linB_eqf : bceq.
Definition kn_unfill2 (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => if kimg_b K then true else if kentry_apart_bp k sp ub uk un K then true else kentry_apart_lin k ub uk un K) k.
Definition kn_unfill2B (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => if kimg_b K then true else if kentry_apart_bpB bc sp ub uk un K then true else kentry_apart_linB bc ub uk un K) (bc_fk bc).
Lemma kn_unfill2B_eqf : forall fk, kn_unfill2B (mkbc fk) = kn_unfill2 fk.
Proof. intros. bcfe. unfold kn_unfill2B, kn_unfill2. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite kn_unfill2B_eqf : bceq.
Definition kn_unfill2M (k : list kentry) := kn_unfill2B (mkbc k).
Lemma kn_unfill2M_eq : kn_unfill2M = kn_unfill2. Proof. apply functional_extensionality; intros k. unfold kn_unfill2M. apply kn_unfill2B_eqf. Qed.

Definition node_visabsorb_ref (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  match xhi k b, xhi k n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) TOPMAX
          && flat_x k sb sk sn && ghost_covers k (a_ghost cs) bb bk n && ghost_covers k (a_ghost cs) sb sk sn)%bool
      then
        let k1 := kn_unfill2 k bb bk n in   (* [comment removed for export] *)
        let k2 := kn_unfill2 k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs)
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition ghost_coversB (bc : bctx) (gs : list (expr * expr)) (bb : expr) (bk : Z) (n : expr) : bool :=
  existsb (fun g => let '(gb, gk) := split_lit (fst g) in (flat_xB bc gb gk (snd g) && xinsideB bc bb bk n gb gk (snd g))%bool) gs.
Lemma ghost_coversB_eqf : forall fk, ghost_coversB (mkbc fk) = ghost_covers fk.
Proof. intros. bcfe. unfold ghost_coversB, ghost_covers. autorewrite with bceq. reflexivity. Qed.
#[local] Hint Rewrite ghost_coversB_eqf : bceq.
Definition node_visabsorb (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc b, xhiB bc n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) TOPMAX
          && flat_xB bc sb sk sn && ghost_coversB bc (a_ghost cs) bb bk n && ghost_coversB bc (a_ghost cs) sb sk sn)%bool
      then
        let k1 := kn_unfill2B bc bb bk n in   (* [comment removed for export] *)
        let k2 := kn_unfill2M k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs)
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
Lemma node_visabsorb_eq : forall cs b n, node_visabsorb cs b n = node_visabsorb_ref cs b n.
Proof.
  intros. unfold node_visabsorb, node_visabsorb_ref. cbv zeta.
  rewrite ?ealignB_eqf, ?flat_xB_eqf, ?kn_unfill2B_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?ghost_coversB_eqf, ?kn_unfill2M_eq. reflexivity.
Qed.



(* [comment removed for export] *)
Definition node_vissplit (cs : acs) (b : expr) (n d : Z) : option acs :=
  match xhi (kn cs) b with
  | Some bh =>
      if (existsb (vis_here b (ELit n)) (a_vis cs) && Z.ltb 0 d && Z.ltb d n && Z.leb (bh + n) TOPMAX
          && Z.leb (a_eager cs + a_abytes cs + 8192) LIMIT)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                     ((b, ELit d) :: (eaddz b d, ELit (n - d)) :: List.filter (fun p => negb (vis_here b (ELit n) p)) (a_vis cs))
                     (a_ghost cs) (a_abytes cs + 8192) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.



(* [comment removed for export] *)
Definition aligned_below_top (k : list kentry) (pb pn : expr) : bool :=
  (Z.leb 12 (ealign k pb) && Z.leb 12 (ealign k pn) && lin_ge0 k [(e_top, 0%Z)] [(pb, 0%Z); (pn, 0%Z)])%bool.

(* [comment removed for export] *)
Definition vishead_cover (k : list kentry) (z : bool) (tb : expr) (tk : Z) (sb : expr) (sk : Z) (L : expr) : bool :=
  existsb (fun K => match K with
                    | KWr wa wn => (negb z && expr_eqb (a_base wa) tb && Z.eqb (a_off wa) tk
                                    && lin_ge0 k [(tb, tk); (wn, 0%Z)] [(sb, sk); (L, 0%Z)])%bool
                    | KZero wa wn => (z && expr_eqb (a_base wa) tb && Z.eqb (a_off wa) tk
                                      && lin_ge0 k [(tb, tk); (wn, 0%Z)] [(sb, sk); (L, 0%Z)])%bool
                    | _ => false
                    end) k.
Definition vishead_long (k : list kentry) (tb : expr) (tk : Z) (sb : expr) (sk : Z) (L : expr) : bool :=
  (vishead_cover k false tb tk sb sk L && vishead_cover k true tb tk sb sk L)%bool.

Definition node_vishead (cs : acs) (b : expr) (m : Z) (L : expr) : option acs :=
  let k := kn cs in
  let n := ELit (8 * m) in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  let '(tb, tk, tn) := shadow_of k e_top (ELit 8) in
  match xhi k b, xhi k L with
  | Some bh, Some lh =>
      if (Z.ltb 0 m && Z.leb (8 * m) 4095 && Z.leb 12 (ealign k b) && flat_x k bb bk n && flat_x k sb sk sn && flat_x k sb sk L
          && flat_x k tb tk tn
          && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) L && Z.leb (bh + 8 * m) (2 ^ 47) && Z.leb lh (2 ^ 40)   (* [comment removed for export] *)
          && lin_ge0 k [(b, 8 * m)] [(e_top, 0%Z)]          (* [comment removed for export] *)
          && lin_ge0 k [(e_top, 4096)] [(b, 0%Z)]            (* [comment removed for export] *)
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               flat_x k pb pk (snd p)
                               && (ranges_apart_x k bb bk n pb pk (snd p) || expr_eqb (fst p) e_top || aligned_below_top k (fst p) (snd p))
                               && ranges_apart_x k sb sk sn pb pk (snd p)) (a_vis cs)
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               flat_x k pb pk (snd p) && ranges_apart_x k sb sk sn pb pk (snd p)) (a_ghost cs)
          && match find_containing k (a_maps cs) [KRWLAZY] sb sk sn with Some _ => true | None => false end
          && (if Z.leb lh 4096 then kwritable_x k k tb tk (ELit (512 + lh)) else vishead_long k tb tk sb sk L)
          && Z.leb (a_eager cs + a_abytes cs + vis_cost (8 * m)) LIMIT)%bool
      then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs))
                            (KWr (SA sb sk) L :: (if Z.leb lh 4096 then kimg_clip k else KZero (SA sb sk) L :: kimg_clip k)) (nxt cs))
                     (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                     ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost (8 * m)) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.



(* [comment removed for export] *)
Definition stack_elem : expr * expr := (e_top, esub (ELit (2 ^ 47)) e_top).
Definition node_unvishead (cs : acs) (b : expr) (m : Z) : option acs :=
  let k := kn cs in
  let n := ELit (8 * m) in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  let '(tb, tk, tn) := shadow_of k e_top (ELit 8) in
  match xhi k b with
  | Some bh =>
      if (existsb (vis_here b n) (a_vis cs) && existsb (vis_here (fst stack_elem) (snd stack_elem)) (a_vis cs)
          && Z.ltb 0 m && Z.leb (8 * m) 4095 && Z.leb 12 (ealign k b) && flat_x k bb bk n && Z.leb (bh + 8 * m) (2 ^ 47)   (* [comment removed for export] *)
          && flat_x k sb sk sn && flat_x k tb tk tn
          && lin_ge0 k [(b, 8 * m)] [(e_top, 0%Z)]          (* [comment removed for export] *)
          && kzero_x k k sb sk sn)%bool
      then
        let sp1 := mk_sprep k sb sk sn in
        let sp2 := mk_sprep k tb (tk - m) (ELit m) in
        let k2 := List.filter (fun K => (kimg_b K || kentry_apart_bp k sp1 sb sk sn K || kentry_apart_bp k sp2 tb (tk - m) (ELit m) K)%bool) k in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.



(* [comment removed for export] *)
Definition node_havocbrk (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (N.succ v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_havocbrkp (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb 12 (ealign (kn cs) (a_brk cs)) && Z.leb (4096 * lo) l && Z.leb h (4096 * hi))%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (N.succ v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (escale 4096 (EVar v))
                  (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_fdhavoc (cs : acs) (lo hi : Z) : option acs :=
  match a_fd cs with
  | FdFile kb len off =>
      match xlo (kn cs) off, xhi (kn cs) off with
      | Some l, Some h =>
          if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
            let v := nxt cs in let ss := a_ss cs in
            Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (N.succ v))
                      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs)
                      (FdFile kb len (EVar v)) (a_tidset cs))
          else None
      | _, _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_intro (cs : acs) (lo hi : Z) : option acs :=
  if (fresh_ok cs && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool then
    let v := nxt cs in let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (N.succ v)))
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
Proof. intros. unfold summary_fill, summary_fill_ref. unfold ehi, elo. rewrite ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq, ?kn_havoc_eq. reflexivity. Qed.


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
Definition kblob_prefix0 (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) (ELit n0) _ => expr_eqb b sb && Z.eqb o sk && Z.ltb 0 n0 && Z.leb n0 nlo
                             | _ => false
                             end) k with
  | Some (KBlob _ (ELit n0) j) => [KBlob (SA db dk) (ELit n0) j]
  | _ => []
  end.
(* [comment removed for export] *)
Definition blob_within (k : list kentry) (n ne : expr) (nlo : Z) : bool :=
  if expr_eqb n ne then true else match xhi k n with Some h => Z.leb h nlo | None => false end.
Definition kblob_prefix1 (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) (ne : expr) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) n _ => (expr_eqb b sb && Z.eqb o sk && blob_within k n ne nlo)%bool
                             | _ => false
                             end) k with
  | Some (KBlob _ n j) => [KBlob (SA db dk) n j]
  | _ => []
  end.
Definition kblob_prefix (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) (ne : expr) : list kentry :=
  match kblob_prefix0 k sb sk db dk nlo with [] => kblob_prefix1 k sb sk db dk nlo ne | l => l end.

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
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + N.of_nat i)%N)) (seq 0 words) in
              let havoc_src := if (kwritable_x k k sb sk ne && flat_x k sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) (N.of_nat words) else None in
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
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := kn_havocM k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + N.of_nat i)%N)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) (N.of_nat words) else None in
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
Proof. intros. unfold summary_copy, summary_copy_ref. unfold ehi, elo. rewrite ?copy_factsB_eqf, ?flat_xB_eqf, ?kwritable_xB_eqf, ?kzero_xB_eqf, ?off_image_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havocM_eq, ?kn_havoc_eq. reflexivity. Qed.


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
Proof. intros. unfold summary_miz, summary_miz_ref. unfold ehi, elo. rewrite ?kn_havocB_eqf, ?kwritableB_eqf, ?kzero_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havoc_eq. reflexivity. Qed.


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
Proof. intros. unfold summary_istrncpy, summary_istrncpy_ref. unfold ehi, elo. rewrite ?kwritable_xB_eqf, ?off_image_xB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?kn_havocM_eq, ?kn_havoc_eq. reflexivity. Qed.


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
Proof. intros. unfold summary_sniff, summary_sniff_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?erangeB_eqf, ?extKB_eqf, ?flat_xB_eqf, ?img_covB_eqf, ?kn_havocB_eqf, ?kn_readableB_eqf, ?know_lookupB_eqf, ?kwritableB_eqf, ?lin_ge0B_eqf, ?mkSrlB_eqf, ?ranges_apart_xB_eqf, ?xhiB_eqf, ?xloB_eqf, ?kn_havoc_eq. reflexivity. Qed.


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
        Some (with_ss cs (mk_ss (x_pnscan_k A) (sr_upd (sr_upd (s_regs ss) 11 (EVar v)) 13 (ELit 0)) k' (N.succ v)))
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
Definition entails_ref (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && forallb (fun K => existsb (kentry_eqb K) (kn cs) || existsb (fun X => kpriv_geb X K) (kn cs)) (kn ch)   (* [comment removed for export] *)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.
Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && (let t := kn_ix (kn cs) in forallb (fun K => if kn_memI2 t K then true    
                                                   else existsb (fun X => kpriv_geb X K) (kn cs)) (kn ch))   (* [comment removed for export] *)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.
Lemma entails_memI2_forallb : forall k tk,
  forallb (fun K => if kn_memI2 (kn_ix k) K then true else existsb (fun X => kpriv_geb X K) k)%bool tk
  = forallb (fun K => existsb (kentry_eqb K) k || existsb (fun X => kpriv_geb X K) k)%bool tk.
Proof. intros k tk. apply forallb_exteq. intros K. rewrite kn_memI2_eq. reflexivity. Qed.
Lemma entails_eq : forall cs ch, entails cs ch = entails_ref cs ch.
Proof.
  intros cs ch. unfold entails, entails_ref. cbv zeta. rewrite entails_memI2_forallb. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint esubst (J : N) (e : expr) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => if N.eqb n J then e else x
  | EAlu op a b => mkAlu op (esubst J e a) (esubst J e b)
  | EAluw op a b => mkAluw op (esubst J e a) (esubst J e b)
  | EMd op a b => mkMd op (esubst J e a) (esubst J e b)
  | EMdw op a b => mkMdw op (esubst J e a) (esubst J e b)
  | EExt sx lo n a => EExt sx lo n (esubst J e a)
  | EBlob _ _ _ _ => x
  end.
(* [comment removed for export] *)
Definition asubst (J : N) (e : expr) (a : saddr) : saddr := SA (esubst J e (a_base a)) (a_off a).
Definition ksubst (J : N) (e : expr) (K : kentry) : kentry :=
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
  | KPriv t rs args k => KPriv t (map (fun r => (asubst J e (fst r), esubst J e (snd r))) rs) (map (esubst J e) args) k   (* [comment removed for export] *)
  end.
Definition psubst (J : N) (e : expr) (p : expr * expr) : expr * expr := (esubst J e (fst p), esubst J e (snd p)).
Definition msubst (J : N) (e : expr) (m : amap) : amap := AM (esubst J e (am_base m)) (esubst J e (am_len m)) (am_kind m).
Definition fsubst (J : N) (e : expr) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (esubst J e l) (esubst J e o) | _ => f end.
(* [comment removed for export] *)
Definition inst (inv : acs) (J : N) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nt_set (t : ptree N) (i : N) (d : N) : ptree N := pt_set (pos_fast i) d t.
Definition nt_get (t : ptree N) (i : N) : option N := pt_get t (pos_fast i).
Lemma nt_get_set : forall t i d j, nt_get (nt_set t i d) j = if N.eqb j i then Some d else nt_get t j.
Proof.
  intros t i d j. unfold nt_get, nt_set. destruct (N.eqb_spec j i) as [->|NE]; [apply pt_gss|].
  apply pt_gso. intros E. apply NE. apply pos_fast_inj. exact E.
Qed.
Lemma nt_get_empty : forall i, nt_get PTLeaf i = None.
Proof. intros i. unfold nt_get. apply pt_get_leaf. Qed.
(* [comment removed for export] *)
Fixpoint mk_fwd (m : list (N * N)) : option (ptree N) :=
  match m with
  | [] => Some PTLeaf
  | (s, d) :: rest =>
      match mk_fwd rest with
      | Some t => match nt_get t s with None => Some (nt_set t s d) | Some _ => None end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint mk_bwd (m : list (N * N)) : option (ptree N) :=
  match m with
  | [] => Some PTLeaf
  | (s, d) :: rest =>
      match mk_bwd rest with
      | Some t => match nt_get t d with None => Some (nt_set t d s) | Some _ => None end
      | None => None
      end
  end.

Fixpoint erename (t : ptree N) (e : expr) : expr :=
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
Definition arename (t : ptree N) (a : saddr) : saddr := SA (erename t (a_base a)) (a_off a).
Definition krename (t : ptree N) (K : kentry) : kentry :=
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
  | KPriv tg rs args k => KPriv tg (map (fun r => (arename t (fst r), erename t (snd r))) rs) (map (erename t) args) k   (* [comment removed for export] *)
  end.
Definition prename (t : ptree N) (p : expr * expr) : expr * expr := (erename t (fst p), erename t (snd p)).
Definition mrename (t : ptree N) (m : amap) : amap := AM (erename t (am_base m)) (erename t (am_len m)) (am_kind m).
Definition frename (t : ptree N) (f : afd) : afd :=
  match f with FdFile k l o => FdFile k (erename t l) (erename t o) | _ => f end.

(* [comment removed for export] *)
Fixpoint evars_all (ok : N -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => ok v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_all ok a && evars_all ok b
  | EExt _ _ _ a => evars_all ok a
  | EBlob _ _ _ _ => true
  end.
Definition kvars_all (ok : N -> bool) (K : kentry) : bool :=
  match K with
  | KWord a _ v => evars_all ok (a_base a) && evars_all ok v
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_all ok (a_base a) && evars_all ok n
  | KImg _ _ => true
  | KAlign x _ | KRange x _ _ => evars_all ok x
  | KDisj a1 n1 a2 n2 => evars_all ok (a_base a1) && evars_all ok n1 && evars_all ok (a_base a2) && evars_all ok n2
  | KPriv _ rs args _ =>   (* [comment removed for export] *)
      forallb (fun r : saddr * expr => evars_all ok (a_base (fst r)) && evars_all ok (snd r)) rs && forallb (evars_all ok) args
  end%bool.
Definition csvars_all (ok : N -> bool) (cs : acs) : bool :=
  (forallb (evars_all ok) (s_regs (a_ss cs)) && forallb (kvars_all ok) (kn cs)
   && forallb (fun m => evars_all ok (am_base m) && evars_all ok (am_len m)) (a_maps cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_vis cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_ghost cs)
   && evars_all ok (a_brk cs)
   && match a_fd cs with FdFile _ l o => evars_all ok l && evars_all ok o | _ => true end)%bool.

(* [comment removed for export] *)
Fixpoint emaxv (e : expr) (acc : N) : N :=
  match e with
  | ELit _ => acc
  | EVar v => N.max acc (N.succ v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => emaxv a (emaxv b acc)
  | EExt _ _ _ a => emaxv a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kmaxv (K : kentry) (acc : N) : N :=
  match K with
  | KWord a _ v => emaxv (a_base a) (emaxv v acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => emaxv (a_base a) (emaxv n acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => emaxv x acc
  | KDisj a1 n1 a2 n2 => emaxv (a_base a1) (emaxv n1 (emaxv (a_base a2) (emaxv n2 acc)))
  | KPriv _ rs args _ =>   (* [comment removed for export] *)
      fold_right (fun (r : saddr * expr) acc' => emaxv (a_base (fst r)) (emaxv (snd r) acc')) (fold_right emaxv acc args) rs
  end.
Definition csmaxv (cs : acs) : N :=
  let acc := fold_right emaxv 0%N (s_regs (a_ss cs)) in
  let acc := fold_right kmaxv acc (kn cs) in
  let acc := fold_right (fun m acc => emaxv (am_base m) (emaxv (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => emaxv l (emaxv o acc) | _ => acc end in
  emaxv (a_brk cs) acc.

Definition rename_cs (t : ptree N) (cs : acs) (nx : N) : acs :=
  ACS (mk_ss (pc cs) (map (erename t) (s_regs (a_ss cs))) (map (krename t) (kn cs)) nx)
      (map (mrename t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prename t) (a_vis cs)) (map (prename t) (a_ghost cs)) (a_abytes cs)
      (erename t (a_brk cs)) (frename t (a_fd cs)) (a_tidset cs).

(* [comment removed for export] *)
Definition node_rename (gb : N) (cs : acs) (m : list (N * N)) : option acs :=
  if forallb (fun p => N.leb gb (fst p) && N.leb gb (snd p)) m then
    match mk_fwd m, mk_bwd m with
    | Some fw, Some bw =>
        let ok (v : N) := match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end in
        if (csvars_all ok cs && match s_log (a_ss cs) with [] => true | _ => false end)%bool then
          let cs1 := rename_cs fw cs 0%N in
          Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) (kn cs1) (N.max gb (csmaxv cs1))))
        else None
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Definition bt_set (t : ptree unit) (i : N) : ptree unit := pt_set (pos_fast i) tt t.   (* [comment removed for export] *)
Definition bt_get (t : ptree unit) (i : N) : bool := match pt_get t (pos_fast i) with Some _ => true | None => false end.
(* [comment removed for export] *)
Fixpoint evars_fo (gb : N) (e : expr) (acc : list N * ptree unit) : list N * ptree unit :=
  match e with
  | ELit _ => acc
  | EVar v => if N.ltb v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_fo gb b (evars_fo gb a acc)
  | EExt _ _ _ a => evars_fo gb a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kvars_fo (gb : N) (K : kentry) (acc : list N * ptree unit) : list N * ptree unit :=
  match K with
  | KWord a _ v => evars_fo gb v (evars_fo gb (a_base a) acc)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_fo gb n (evars_fo gb (a_base a) acc)
  | KImg _ _ => acc
  | KAlign x _ | KRange x _ _ => evars_fo gb x acc
  | KDisj a1 n1 a2 n2 => evars_fo gb n2 (evars_fo gb (a_base a2) (evars_fo gb n1 (evars_fo gb (a_base a1) acc)))
  | KPriv _ rs args _ =>   (* [comment removed for export] *)
      fold_left (fun acc' e => evars_fo gb e acc') args
                (fold_left (fun acc' (r : saddr * expr) => evars_fo gb (snd r) (evars_fo gb (a_base (fst r)) acc')) rs acc)
  end.
Definition csvars_fo (gb : N) (cs : acs) : list N :=
  let acc := fold_left (fun acc e => evars_fo gb e acc) (s_regs (a_ss cs)) ([], PTLeaf) in
  let acc := fold_left (fun acc K => kvars_fo gb K acc) (kn cs) acc in
  let acc := fold_left (fun acc m => evars_fo gb (am_len m) (evars_fo gb (am_base m) acc)) (a_maps cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_vis cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_ghost cs) acc in
  let acc := match a_fd cs with FdFile _ l o => evars_fo gb o (evars_fo gb l acc) | _ => acc end in
  let acc := evars_fo gb (a_brk cs) acc in
  rev (fst acc).
Fixpoint number_from (i : N) (l : list N) : list (N * N) :=
  match l with [] => [] | v :: rest => (v, i) :: number_from (N.succ i) rest end.
Definition compact_map (gb : N) (cs : acs) : list (N * N) := number_from gb (csvars_fo gb cs).
Definition node_compact (gb : N) (cs : acs) : option acs := node_rename gb cs (compact_map gb cs).

(* [comment removed for export] *)
Fixpoint regs_match_h (lo hi : N) (seen : list N) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' =>
      match t with
      | EVar v => if (N.leb lo v && N.ltb v hi)%bool
                  then (negb (existsb (N.eqb v) seen) && regs_match_h lo hi (v :: seen) rs' ts')%bool
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
Definition kimg_sub_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k
  | _ => false
  end.
Definition kn_incl1_h (k : list kentry) (K : kentry) : bool :=
  if existsb (fun X => kentry_eqb X K) k then true
  else if existsb (fun X => kpriv_geb X K) k then true   (* [comment removed for export] *)
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool := forallb (kn_incl1_h k) tk.
Definition kn_incl1_hI (k : list kentry) (t : kix) (K : kentry) : bool :=
  if kn_memI t K then true
  else if existsb (fun X => kpriv_geb X K) k then true
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl_hI (k : list kentry) (tk : list kentry) : bool := let t := kn_ix k in forallb (kn_incl1_hI k t) tk.
Lemma kn_incl_hI_eq : forall k tk, kn_incl_hI k tk = kn_incl_h k tk.
Proof.
  intros k tk. unfold kn_incl_hI, kn_incl_h. apply forallb_exteq. intros K.
  unfold kn_incl1_hI, kn_incl1_h. rewrite kn_memI_eq. reflexivity.
Qed.

Definition entails_h (lo hi : N) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_hI (kn cs) (kn ch)    
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
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : N)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : N)
| MC (mc_b : N) (mc_v : N) (mc_h : nat) (mc_st : acs).
Definition lc_bnd (c : loopctx) : N := match c with LC _ _ _ hi => hi | JC _ _ _ b _ => b | MC b _ _ _ => b end.

(* [comment removed for export] *)
Fixpoint find_src (m : list (N * N)) (v : N) : option N :=
  match m with [] => None | (s, d) :: r => if N.eqb d v then Some s else find_src r v end.

(* [comment removed for export] *)
Definition loop_ok (cs0 : acs) (J : BinNums.N) (N : expr) (inv : acs) : option Z :=
  let lo := N.succ J in let hi := nxt inv in
  if (fresh_ok cs0 && N.leb (nxt cs0) J && N.ltb J hi && fresh_ok inv
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
Definition loop_body_state (J : BinNums.N) (N : expr) (nhi : Z) (inv : acs) : acs :=
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
Definition node_diamond_join (nx : N) (joinpc : Z) (rs : list nat) (ca cb : acs) : option acs :=
  let hv := nodup Nat.eq_dec (diff_regs 0 (s_regs (a_ss ca)) (s_regs (a_ss cb)) ++ rs) in
  let v0 := N.max nx (N.max (nxt ca) (nxt cb)) in
  let hi := (v0 + N.of_nat (length hv))%N in
  let regsJ := sr_fresh (s_regs (a_ss ca)) hv v0 in
  let knJ := (let t := kn_ix (kn cb) in List.filter (fun K => kn_memI t K) (kn ca)) in    
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && N.leb nx0 v0
      && entails_h v0 hi ca csJ && entails_h v0 hi cb csJ)%bool
  then Some csJ else None.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint nj_arms (lo hi : Z) (cuts : list Z) : list (Z * Z) :=
  match cuts with
  | [] => [(lo, hi)]
  | c :: rest => if (Z.leb lo c && Z.ltb c hi)%bool then (lo, c) :: nj_arms (c + 1) hi rest else nj_arms lo hi rest
  end.

(* [comment removed for export] *)
Fixpoint omap_all {X Y : Type} (f : X -> option Y) (l : list X) : option (list Y) :=
  match l with
  | [] => Some []
  | x :: r => match f x, omap_all f r with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.

(* [comment removed for export] *)
Definition nj_starts (cs : acs) (e : expr) (arms : list (Z * Z)) : list acs :=
  List.filter (fun csa => negb (kn_contra (kn csa)))
              (map (fun lh : Z * Z => set_kn cs (KRange e (fst lh) (snd lh) :: kn cs)) arms).

(* [comment removed for export] *)
Fixpoint nj_ends (run : acs -> option acs) (joinpc : Z) (starts : list acs) : option (list acs) :=
  match starts with
  | [] => Some []
  | csa :: rest =>
      match run csa with
      | Some ca => if Z.eqb (pc ca) joinpc then
                     match nj_ends run joinpc rest with Some l => Some (ca :: l) | None => None end
                   else None
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition nj_gen1 (cs : acs) (b : expr) (off : Z) (n : nat) (lo hi : Z) (x : N) : option acs :=
  if (fresh_ok cs && N.leb (nxt cs) x && expr_vars_lt (nxt cs) b)%bool then
    match node_join cs b off n with
    | Some cs1 =>
        match kn cs1 with
        | KWord a w (ELit c) :: rest =>
            if (Z.leb lo c && Z.leb c hi && Z.leb 0 lo && Z.ltb hi two64)%bool
            then Some (set_kn (bump cs1 (N.succ x - nxt cs1)) (KWord a w (EVar x) :: KRange (EVar x) lo hi :: rest))
            else None
        | _ => None
        end
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition nj_val (cs : acs) (w : expr * Z * nat) : option Z :=
  match node_join cs (fst (fst w)) (snd (fst w)) (snd w) with
  | Some cs1 => match kn cs1 with KWord _ _ (ELit c) :: _ => Some c | _ => None end
  | None => None
  end.

Fixpoint zmin_list (z : Z) (l : list Z) : Z := match l with [] => z | y :: r => zmin_list (Z.min z y) r end.
Fixpoint zmax_list (z : Z) (l : list Z) : Z := match l with [] => z | y :: r => zmax_list (Z.max z y) r end.

(* [comment removed for export] *)
Definition nj_bounds (ends : list acs) (w : expr * Z * nat) : option (Z * Z) :=
  match omap_all (fun c => nj_val c w) ends with
  | Some (v :: vs) => Some (zmin_list v vs, zmax_list v vs)
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint nj_gen (cs : acs) (ws : list (expr * Z * nat)) (bs : list (Z * Z)) (x : N) : option acs :=
  match ws, bs with
  | [], [] => Some cs
  | w :: ws', lh :: bs' =>
      match nj_gen1 cs (fst (fst w)) (snd (fst w)) (snd w) (fst lh) (snd lh) x with
      | Some cs1 => nj_gen cs1 ws' bs' (N.succ x)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint nat_max_list (n : N) (l : list N) : N := match l with [] => n | m :: r => nat_max_list (N.max n m) r end.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint nj_fold (nx : N) (joinpc : Z) (rs : list nat) (acc : acs) (rest : list acs) : option acs :=
  match rest with
  | [] => Some acc
  | cb :: rest' =>
      match node_diamond_join nx joinpc rs acc cb with
      | Some csj => nj_fold nx joinpc rs csj rest'
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition nj_prep (c : acs) (ws : list (expr * Z * nat)) (bs : list (Z * Z)) (rs : list nat) (v0 : N) : option acs :=
  match nj_gen (bump c (v0 - nxt c)) ws bs v0 with
  | Some c1 => node_havoc c1 rs
  | None => None
  end.

Definition node_joinN (nx : N) (joinpc : Z) (rs : list nat) (ws : list (expr * Z * nat)) (ends : list acs) : option acs :=
  let v0 := nat_max_list nx (map nxt ends) in
  match omap_all (nj_bounds ends) ws with
  | Some bs =>
      match omap_all (fun c => nj_prep c ws bs rs v0) ends with
      | Some (c1 :: rest) =>
          if (N.leb nx0 nx && forallb (fun c => Z.eqb (pc c) joinpc) (c1 :: rest))%bool
          then (if match rest with [] => true | _ => false end
                then node_diamond_join (v0 + N.of_nat (length ws) + N.of_nat (length rs)) joinpc [] c1 c1   (* [comment removed for export] *)
                else nj_fold (v0 + N.of_nat (length ws) + N.of_nat (length rs)) joinpc [] c1 rest)
          else None
      | _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition via_ok (cs js : acs) (lo : N) : bool :=
  (match s_log (a_ss js) with [] => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss js))) 32
   && N.leb nx0 (nxt cs) && N.leb (nxt cs) lo && N.leb lo (nxt js))%bool.

(* [comment removed for export] *)
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let K := KUnk (SA bb bo) (ELit n) in
  if kunk_covered (kn cs) K then Some (set_kn cs (K :: kn_cutoutB (mkbc (kn cs)) bb bo (ELit n))) else None.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition M64 : Z := Z.ones 64.
Definition kb_lit (z : Z) : Z * Z := (M64, z mod 2 ^ 64).
Definition kb_range (k : list kentry) (e : expr) : Z * Z :=
  match erange k e with
  | Some (lo, hi) =>
      if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2 ^ 64))%bool then
        if Z.eqb lo hi then (M64, lo)
        else let m := Z.land M64 (Z.lnot (Z.ones (Z.log2 (Z.lxor lo hi) + 1))) in (m, Z.land lo m)
      else (0, 0)
  | None => (0, 0)
  end.
Definition kb_merge (a b : Z * Z) : Z * Z := (Z.lor (fst a) (fst b), Z.lor (snd a) (snd b)).
Definition kb_or (a b : Z * Z) : Z * Z :=
  (Z.lor (Z.land (fst a) (fst b)) (Z.lor (snd a) (snd b)), Z.lor (snd a) (snd b)).
Definition kb_and (a b : Z * Z) : Z * Z :=
  (Z.lor (Z.land (fst a) (fst b)) (Z.lor (Z.land (fst a) (Z.lnot (snd a))) (Z.land (fst b) (Z.lnot (snd b)))),
   Z.land (snd a) (snd b)).
Definition kb_srl (a : Z * Z) (s : Z) : Z * Z :=
  (Z.lor (Z.shiftr (fst a) s) (Z.land M64 (Z.lnot (Z.shiftr M64 s))), Z.shiftr (snd a) s).
Fixpoint kbits (k : list kentry) (e : expr) : Z * Z :=
  kb_merge (kb_range k e)
    (match e with
     | ELit z => kb_lit z
     | EAlu op a b =>
         let ka := kbits k a in let kb := kbits k b in
         if (Z.eqb (fst ka) M64 && Z.eqb (fst kb) M64)%bool
         then kb_lit (bv_unsigned (alu64 op (Z_to_bv 64 (snd ka)) (Z_to_bv 64 (snd kb))))
         else match op with
              | ALU_OR => kb_or ka kb
              | ALU_AND => kb_and ka kb
              | ALU_SRL => if Z.eqb (fst kb) M64 then kb_srl ka (Z.land (snd kb) 63) else (0, 0)
              | _ => (0, 0)
              end
     | EMd op a b =>
         let ka := kbits k a in let kb := kbits k b in
         if (Z.eqb (fst ka) M64 && Z.eqb (fst kb) M64)%bool
         then kb_lit (bv_unsigned (mul_div op (Z_to_bv 64 (snd ka)) (Z_to_bv 64 (snd kb)))) else (0, 0)
     | _ => (0, 0)
     end).

(* [comment removed for export] *)
Fixpoint renormK (k : list kentry) (e : expr) : expr :=
  match e with
  | EAlu op a b => mkAluK k op (renormK k a) (renormK k b)
  | EAluw op a b => mkAluwK k op (renormK k a) (renormK k b)
  | EMd op a b => foldK k (mkMdK k op (renormK k a) (renormK k b))
  | EMdw op a b => foldK k (mkMdw op (renormK k a) (renormK k b))
  | EExt sx lo n x => if Nat.leb n 8 then extK k (mkExt sx lo n (renormK k x)) else EExt sx lo n (renormK k x)
  | _ => foldK k e
  end.
Definition respell_ok (k : list kentry) (a e : expr) : bool :=
  match decide_branch k BC_EQ a e with
  | Some true => true
  | _ => (* [comment removed for export] *)
      if (match erange k (mkAlu ALU_SUB a e) with
          | Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
          | None => false
          end) then true
      else if (match e with   (* [comment removed for export] *)
           | ELit z => let r := kbits k a in (Z.eqb (fst r) M64 && Z.eqb (snd r) (z mod 2 ^ 64))%bool
           | _ => false
           end) then true
      else expr_eqb (renormK k a) (renormK k e)   (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition respell_okB (bc : bctx) (k : list kentry) (a e : expr) : bool :=
  match decide_branchB bc BC_EQ a e with
  | Some true => true
  | _ =>
      if (match erangeB bc (mkAlu ALU_SUB a e) with
          | Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
          | None => false
          end) then true
      else if (match e with
           | ELit z => let r := kbits k a in (Z.eqb (fst r) M64 && Z.eqb (snd r) (z mod 2 ^ 64))%bool
           | _ => false
           end) then true
      else expr_eqb (renormK k a) (renormK k e)
  end.
Lemma respell_okB_eqf : forall k a e, respell_okB (mkbc k) k a e = respell_ok k a e.
Proof. intros. unfold respell_okB, respell_ok. rewrite decide_branchB_eqf, erangeB_eqf. reflexivity. Qed.
Lemma respell_okB_eqfun : forall k, respell_okB (mkbc k) k = respell_ok k.
Proof. intros k. apply functional_extensionality; intros a. apply functional_extensionality; intros e. apply respell_okB_eqf. Qed.
Definition node_respell (cs : acs) (r : nat) (e : expr) : option acs :=
  if (Nat.ltb 0 r && Nat.ltb r 32 && expr_vars_lt (nxt cs) e && respell_okB (mkbc (kn cs)) (kn cs) (reg cs r) e)%bool   (* [comment removed for export] *)
  then Some (set_reg cs r e) else None.

(* [comment removed for export] *)
Definition memfact_ok_ref (k : list kentry) (K : kentry) : bool :=
  match K with
  | KZero (SA b o) n => (flat_x k b o n && kzero_x k k b o n)%bool
  | KWr (SA b o) n => (flat_x k b o n && kwritable_x k k b o n)%bool
  | KUnk (SA b o) e =>   (* [comment removed for export] *)
      if kunk_covered k K then true
      else match xlo k e, xhi k e with Some a, Some a' => if Z.eqb a a' then kunk_covered k (KUnk (SA b o) (ELit a)) else false | _, _ => false end
  | KWord (SA b o) w v =>   (* [comment removed for export] *)
      if (Nat.leb 1 w && Nat.leb w 8 && flat_x k b o (ELit (Z.of_nat w)))%bool then
        match know_lookup segs k b o w false [] [] with
        | LHit e [] _ => if respell_ok k e v then true else respell_ok k e (EExt false 0 w v)   (* [comment removed for export] *)
        | _ => false
        end
      else false
  | _ => false
  end.

(* [comment removed for export] *)
Definition memfact_okB (bc : bctx) (k : list kentry) (K : kentry) : bool :=
  match K with
  | KZero (SA b o) n => if flat_xB bc b o n then kzero_xB bc k b o n else false
  | KWr (SA b o) n => if flat_xB bc b o n then kwritable_xB bc k b o n else false
  | KUnk (SA b o) e =>
      if kunk_covered k K then true
      else match xloB bc e, xhiB bc e with Some a, Some a' => if Z.eqb a a' then kunk_covered k (KUnk (SA b o) (ELit a)) else false | _, _ => false end
  | KWord (SA b o) w v =>
      if (Nat.leb 1 w && Nat.leb w 8 && flat_xB bc b o (ELit (Z.of_nat w)))%bool then
        match know_lookupB segs bc b o w false [] [] with
        | LHit e [] _ => if respell_okB bc k e v then true else respell_okB bc k e (EExt false 0 w v)
        | _ => false
        end
      else false
  | _ => false
  end.
Definition memfact_ok (k : list kentry) (K : kentry) : bool := memfact_okB (mkbc k) k K.
Lemma memfact_ok_eq : forall k K, memfact_ok k K = memfact_ok_ref k K.
Proof.
  intros k K. unfold memfact_ok, memfact_okB, memfact_ok_ref.
  destruct K as [[b o] w v|[b o] n| | | | |[b o] n| | |[b o] n|]; try reflexivity;
    rewrite ?flat_xB_eqf, ?kzero_xB_eqf, ?kwritable_xB_eqf, ?xloB_eqf, ?xhiB_eqf, ?know_lookupB_eqf, ?respell_okB_eqfun; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition flat0 (k : list kentry) (b : expr) (o : Z) : bool :=
  match xlo k b, xhi k b with Some lo, Some hi => (Z.leb 0 (lo + o) && Z.ltb (hi + o) two64)%bool | _, _ => false end.
Definition memfact_fd (k : list kentry) (f : afd) (K : kentry) : bool :=
  match K with
  | KBlob (SA b o) n kj =>
      match f with
      | FdFile kb len _ =>
          (Nat.leb kb kj && Nat.ltb kj (kb + 1024) && flat0 k b o
           && match xhi k len, xhi k n with Some 0, Some 0 => true | _, _ => false end)%bool
      | _ => false
      end
  | KUnk (SA b o) n => (flat0 k b o && match xhi k n with Some 0 => true | _ => false end)%bool
  | KZero (SA b o) n => (flat0 k b o && match xhi k n with Some 0 => true | _ => false end)%bool   (* [comment removed for export] *)
  | _ => false
  end.

(* [comment removed for export] *)
Definition node_fdrespell (cs : acs) (len off : expr) : option acs :=
  match a_fd cs with
  | FdFile kb l o =>
      let bc := mkbc (kn cs) in
      if (expr_vars_lt (nxt cs) len && expr_vars_lt (nxt cs) off && respell_okB bc (kn cs) l len && respell_okB bc (kn cs) o off)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs)
                     (FdFile kb len off) (a_tidset cs))
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint nodupb_nat (l : list nat) : bool := match l with [] => true | x :: r => if existsb (Nat.eqb x) r then false else nodupb_nat r end.
Definition perm_ok (n : nat) (perm : list nat) : bool := (Nat.eqb (length perm) n && forallb (fun i => Nat.ltb i n) perm && nodupb_nat perm)%bool.
Definition node_visperm (cs : acs) (perm : list nat) : option acs :=
  let v := a_vis cs in
  if perm_ok (length v) perm then
    Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (map (fun i => nth i v (ELit 0, ELit 0)) perm) (a_ghost cs)
              (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None.

(* [comment removed for export] *)
Definition visrespell1 (b n b' n' : expr) (p : expr * expr) : expr * expr := if vis_here b n p then (b', n') else p.
Definition node_visrespell (cs : acs) (b n b' n' : expr) : option acs :=
  let bc := mkbc (kn cs) in   (* [comment removed for export] *)
  if (existsb (vis_here b n) (a_vis cs) && expr_vars_lt (nxt cs) b' && expr_vars_lt (nxt cs) n'
      && respell_okB bc (kn cs) b b' && respell_okB bc (kn cs) n n')%bool
  then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (map (visrespell1 b n b' n') (a_vis cs)) (a_ghost cs)
                 (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None.

(* [comment removed for export] *)
Definition map_here (b n : expr) (m : amap) : bool := (expr_eqb (am_base m) b && expr_eqb (am_len m) n)%bool.
Definition maprespell1 (b n b' n' : expr) (m : amap) : amap := if map_here b n m then AM b' n' (am_kind m) else m.
Definition node_maprespell (cs : acs) (b n b' n' : expr) : option acs :=
  let bc := mkbc (kn cs) in   (* [comment removed for export] *)
  if (existsb (map_here b n) (a_maps cs) && expr_vars_lt (nxt cs) b' && expr_vars_lt (nxt cs) n'
      && respell_okB bc (kn cs) b b' && respell_okB bc (kn cs) n n')%bool
  then Some (ACS (a_ss cs) (map (maprespell1 b n b' n') (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs)
                 (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None.

(* [comment removed for export] *)
Fixpoint find_srl (s : Z) (ts : list (Z * expr)) : option (Z * expr) :=
  match ts with
  | [] => None
  | (q, EAlu ALU_SRL x (ELit s')) :: r => if Z.eqb s' s then Some (q, x) else find_srl s r
  | _ :: r => find_srl s r
  end.
Definition srl_split (kn : list kentry) (x : expr) (s : Z) : option expr :=
  let l := lin_of x in
  let m := (2 ^ s)%Z in
  match (if (negb (lin_trivial l) && lin_nowrap kn x)%bool then lsplit_divc m (snd l) else ([], [])) with
  | ((_ :: _) as dts, (_ :: _) as rts) =>
      if lin_nowrap_l kn (fst l mod m) rts   (* [comment removed for export] *)
      then Some (mkAlu ALU_ADD (unlin (fst l / m, ldiv_terms m dts)) (mkAlu ALU_SRL (unlin (fst l mod m, rts)) (ELit s)))
      else None
  | _ => None
  end.
Definition node_srlsplit (cs : acs) (r : nat) (s : Z) : option acs :=
  match find_srl s (snd (lin_of (reg cs r))) with
  | Some (q, x) =>
      match srl_split (kn cs) x s with
      | Some e' =>
          let e := mkAlu ALU_ADD (mkAlu ALU_SUB (reg cs r) (mkMd M_MUL (ELit q) (EAlu ALU_SRL x (ELit s)))) (mkMd M_MUL (ELit q) e') in
          if (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 s && Z.ltb s 64 && expr_vars_lt (nxt cs) e)%bool
          then Some (set_reg cs r e) else Some cs
      | None => Some cs     (* [comment removed for export] *)
      end
  | None => Some cs
  end.

(* [comment removed for export] *)
Definition srl_split2 (kn : list kentry) (x : expr) (s : Z) : option expr :=
  let l := lin_of x in
  let m := (2 ^ s)%Z in
  match (if (negb (lin_trivial l) && lin_nowrap kn x)%bool then lsplit_divc m (snd l) else ([], [])) with
  | (dts, (_ :: _) as rts) =>
      if ((match dts with [] => negb (Z.eqb (fst l / m) 0) | _ :: _ => true end) && lin_nowrap_l kn (fst l mod m) rts)%bool
      then Some (mkAlu ALU_ADD (unlin (fst l / m, ldiv_terms m dts)) (mkAlu ALU_SRL (unlin (fst l mod m, rts)) (ELit s)))
      else None
  | _ => None
  end.
Definition srl_atom (s : Z) (a : expr) : option expr :=
  match a with EAlu ALU_SRL x (ELit s') => if Z.eqb s' s then Some x else None | _ => None end.
Fixpoint srl_all (kn : list kentry) (s : Z) (ts : list (Z * expr)) (e : expr) : expr :=
  match ts with
  | [] => e
  | (q, a) :: r =>
      match srl_atom s a with
      | Some x =>
          match srl_split2 kn x s with
          | Some e' => srl_all kn s r (mkAlu ALU_ADD (mkAlu ALU_SUB e (mkMd M_MUL (ELit q) (EAlu ALU_SRL x (ELit s)))) (mkMd M_MUL (ELit q) e'))
          | None => srl_all kn s r e
          end
      | None => srl_all kn s r e
      end
  end.
Definition node_srlsplitall (cs : acs) (r : nat) (s : Z) : option acs :=
  let e := srl_all (kn cs) s (snd (lin_of (reg cs r))) (reg cs r) in
  if (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 s && Z.ltb s 64 && expr_vars_lt (nxt cs) e)%bool
  then Some (set_reg cs r e) else Some cs.

(* [comment removed for export] *)
Definition node_andrange (cs : acs) (r : nat) (logc : Z) (ub : expr) : option acs :=
  let c := (2 ^ logc)%Z in
  let e1 := mkAluK (kn cs) ALU_AND ub (ELit (- c)) in
  if (Z.leb 0 logc && Z.ltb logc 64 && (expr_eqb (reg cs r) e1 || respell_ok (kn cs) (reg cs r) e1))%bool then
    match xlo2 (kn cs) ub, xhi2 (kn cs) ub with
    | Some lo, Some hi => Some (add_kn cs [KRange (reg cs r) ((lo / c) * c) ((hi / c) * c)])
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Definition respell_sa (b : expr) (lo hi : Z) (b' : expr) (d : Z) (a : saddr) : saddr :=
  if (expr_eqb (a_base a) b && Z.leb lo (a_off a) && Z.ltb (a_off a) hi)%bool then SA b' (a_off a + d) else a.
Definition memrespell1 (b : expr) (lo hi : Z) (b' : expr) (d : Z) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (respell_sa b lo hi b' d a) w v
  | KZero a n => KZero (respell_sa b lo hi b' d a) n
  | KBlob a n kk => KBlob (respell_sa b lo hi b' d a) n kk
  | KWr a n => KWr (respell_sa b lo hi b' d a) n
  | KFill a n c => KFill (respell_sa b lo hi b' d a) n c
  | KUnk a n => KUnk (respell_sa b lo hi b' d a) n
  | _ => K
  end.
Definition node_memrespell (cs : acs) (b : expr) (lo hi : Z) (b' : expr) (d : Z) : option acs :=
  let bc := mkbc (kn cs) in   (* [comment removed for export] *)
  match xloB bc b', xhiB bc b' with
  | Some l, Some h =>
      if (expr_vars_lt (nxt cs) b' && respell_okB bc (kn cs) b (eaddz b' d) && Z.leb 0 (l + d) && Z.ltb (h + d) two64)%bool
      then Some (set_kn cs (map (memrespell1 b lo hi b' d) (kn cs)))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition sa_of (b : expr) : saddr := let '(bb, bo) := split_lit b in SA bb bo.
Fixpoint hw_apply (k : list kentry) (a : saddr) (x : N) (found : bool) : list kentry :=
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
Fixpoint hw_go (k : list kentry) (bs : list expr) (x : N) : list kentry :=
  match bs with
  | [] => k
  | b :: r => hw_go (hw_apply k (sa_of b) x false) r (N.succ x)
  end.
Definition node_havocwords (cs : acs) (bs : list expr) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (hw_go (s_know ss) bs (s_next ss)) (s_next ss + N.of_nat (length bs))))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition img_readable (bb : expr) (bo : Z) (n : nat) : bool :=
  match bb with
  | ELit 0 => (Z.leb 0 bo && Z.leb (bo + Z.of_nat n) (2 ^ 64)
               && forallb (fun j => match seg_rom segs (Z_to_bv 64 (bo + Z.of_nat j)) with Some _ => true | None => false end) (seq 0 n))%bool
  | _ => false
  end.

Definition node_freshcell (cs : acs) (b : expr) (n : nat) : option acs :=
  let '(bb, bo) := split_lit b in
  (* [comment removed for export] *)
  if (Nat.leb 1 n && Nat.leb n 8 && fresh_ok cs && expr_vars_lt (nxt cs) bb
      && (if kn_readable segs (kn cs) (kn cs) bb bo n then true else img_readable bb bo n))%bool then
    let v := nxt cs in let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KWord (SA bb bo) n (EVar v) :: kn_cutoutB (mkbc (kn cs)) bb bo (ELit (Z.of_nat n))) (N.succ v)))   (* [comment removed for export] *)
  else None.

(* [comment removed for export] *)
Definition is_kwr (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition kn_cutout_keepwr (k : list kentry) (b : expr) (o : Z) (n : expr) : list kentry :=
  List.filter (fun K => negb (is_kwr K)) (kn_cutout k b o n) ++ List.filter is_kwr k.
Definition kn_cutout_keepwrB (k : list kentry) (b : expr) (o : Z) (n : expr) : list kentry :=   (* [comment removed for export] *)
  List.filter (fun K => negb (is_kwr K)) (kn_cutoutB (mkbc k) b o n) ++ List.filter is_kwr k.
Lemma kn_cutout_keepwrB_eq : forall k b o n, kn_cutout_keepwrB k b o n = kn_cutout_keepwr k b o n.
Proof. intros. unfold kn_cutout_keepwrB, kn_cutout_keepwr. rewrite kn_cutoutB_eqf. reflexivity. Qed.
Definition node_freshcellk (cs : acs) (b : expr) (n : nat) : option acs :=
  let '(bb, bo) := split_lit b in
  (* [comment removed for export] *)
  if (Nat.leb 1 n && Nat.leb n 8 && fresh_ok cs && expr_vars_lt (nxt cs) bb
      && (if kn_readable segs (kn cs) (kn cs) bb bo n then true else img_readable bb bo n))%bool then
    let v := nxt cs in let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KWord (SA bb bo) n (EVar v) :: kn_cutout_keepwrB (kn cs) bb bo (ELit (Z.of_nat n))) (N.succ v)))
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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : N := 9.
(* [comment removed for export] *)
Definition vN (n : nat) : N := N.of_nat n.
Definition vNm (m : list (nat * nat)) : list (N * N) := map (fun p => (N.of_nat (fst p), N.of_nat (snd p))) m.
#[global] Arguments vN : simpl never.
#[global] Arguments vNm : simpl never.   (* [comment removed for export] *)

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
   KRange (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  (* [comment removed for export] *)
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 4 6 (ELit 4096)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A));
      (* [comment removed for export] *)
      KWord (SA (fst e_auxb) (snd e_auxb + 48)) 8 (ELit 16); KUnk (SA (fst e_auxb) (snd e_auxb + 56)) (ELit 8)].

Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
(* [comment removed for export] *)
Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.

Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
(* [comment removed for export] *)
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (e_top, esub (ELit (2^47)) e_top)].   (* [comment removed for export] *)

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost (2^47 - CEIL)) (escale 4096 (EVar V_BRK)) FdStd false.
Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.        (* [comment removed for export] *)
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x608000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x32730; rw_lo := 0xaa000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x661bc; x_imemcpy := 0x66140; x_memset := 0xa45b0; x_memcpy := 0xa41ac; x_memiszero := 0x666ec;
     x_istrncpy := 0x665e8; x_sealed := 0x11a1f; x_popfree := 0x38b1c;
     x_sniff := 0x82ce4; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x99f20; x_envscan_k := 0x99f2c; x_pnscan := 0x99fe4; x_pnscan_k := 0x99ff0;
     stops_more := [0x36790; 0x37db4; 0x564c8; 0x5c880; 0x5c894; 0x5c8a8; 0x62238; 0x62308; 0x6f834; 0x70740; 0x708d0; 0x70a40; 0x7a628] |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x32730.
Definition ASAN_TEXT_N : nat := 121965.
Definition asan_init : acs := init_acs_of ASAN.

Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x607000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x32720; rw_lo := 0xa8000; rw_len := 0x55f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x661ac; x_imemcpy := 0x66130; x_memset := 0xa2bec; x_memcpy := 0xa27e8; x_memiszero := 0x666dc;
     x_istrncpy := 0x665d8; x_sealed := 0x11961; x_popfree := 0x38b0c;
     x_sniff := 0x82cd4; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x9855c; x_envscan_k := 0x98568; x_pnscan := 0x98620; x_pnscan_k := 0x9862c;
     stops_more := [0x36780; 0x37da4; 0x564b8; 0x5c870; 0x5c884; 0x5c898; 0x62228; 0x622f8; 0x6f824; 0x70730; 0x708c0; 0x70a30; 0x7a618] |}.
Definition BOTH_TEXT_LO : Z := 0x32720.
Definition BOTH_TEXT_N : nat := 120320.
Definition both_init : acs := init_acs_of BOTH.

End APC.
