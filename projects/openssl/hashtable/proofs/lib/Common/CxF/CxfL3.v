(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AsanPlanCore CxfLeaf CxfNat CxfL1 CxfL2.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module APCL.
Import APC.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import AX2B.
Import AX2BL.
Definition CEIL : Z := 0x7fff7f800000.
Lemma L_APCL_CEIL : @CEIL = @APC.CEIL.
Proof. unfold CEIL. reflexivity. Qed.

Definition KHI : Z := 0x10007fff8000.
Lemma L_APCL_KHI : @KHI = @APC.KHI.
Proof. unfold KHI. reflexivity. Qed.

Definition FLOOR : Z := 0x2aaaaaaab000.
Lemma L_APCL_FLOOR : @FLOOR = @APC.FLOOR.
Proof. unfold FLOOR. reflexivity. Qed.

Definition MBASE_MIN : Z := 0x154555557000.
Lemma L_APCL_MBASE_MIN : @MBASE_MIN = @APC.MBASE_MIN.
Proof. unfold MBASE_MIN. reflexivity. Qed.

Definition PID_MAX : Z := 4194304.
Lemma L_APCL_PID_MAX : @PID_MAX = @APC.PID_MAX.
Proof. unfold PID_MAX. reflexivity. Qed.

Definition TOPMAX : Z := 0x7fffff800000.
Lemma L_APCL_TOPMAX : @TOPMAX = @APC.TOPMAX.
Proof. unfold TOPMAX. reflexivity. Qed.

Definition STKSPAN : Z := 8388608 + 4194304.
Lemma L_APCL_STKSPAN : @STKSPAN = @APC.STKSPAN.
Proof. unfold STKSPAN. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Definition salt2 (a b : shape) : shape :=
  match a, b with SNil, _ => b | _, SNil => a | _, _ => SAlt2 a b end.
Fixpoint listZ_eqb (x y : list Z) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => Z.eqb a b && listZ_eqb x' y' | _, _ => false end.
Definition spiece_eqb (x y : spiece) : bool :=
  match x, y with SPLit a, SPLit b => listZ_eqb a b | SPBlob k, SPBlob k' => CXNAT.eqbF k k' | _, _ => false end.
Fixpoint spieces_eqb (x y : list spiece) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => spiece_eqb a b && spieces_eqb x' y' | _, _ => false end.
Fixpoint shape_eqb (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb a a' && shape_eqb b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb a a' && shape_eqb b b'
  | SHole h, SHole h' => CXNAT.eqbF h h'
  | SNext, SNext => true
  | _, _ => false
  end.
Fixpoint sleaves (s : shape) (acc : list shape) : list shape :=
  match s with
  | SAlt2 a b => sleaves a (sleaves b acc)
  | SNil => acc
  | _ => s :: acc
  end.
Definition sleaves_in (l1 l2 : list shape) : bool := forallb (fun x => existsb (shape_eqb x) l2) l1.
Definition shape_seteq (a b : shape) : bool := sleaves_in (sleaves a []) (sleaves b []) && sleaves_in (sleaves b []) (sleaves a []).
Definition mkind_eqb (a b : mkind) : bool :=
  match a, b with
  | KRW, KRW | KRWLAZY, KRWLAZY | KNONE, KNONE | KNONELAZY, KNONELAZY | KFOG, KFOG | KHOLE, KHOLE => true
  | _, _ => false
  end.
Definition is_tok_kind (k : mkind) : bool := match k with KFOG | KHOLE => true | _ => false end.
Definition is_hole (m : amap) : bool := mkind_eqb (am_kind m) KHOLE.
Definition is_fog (m : amap) : bool := is_tok_kind (am_kind m).
Definition no_fog (ms : list amap) : bool := forallb (fun m => negb (is_fog m)) ms.
Definition no_holes (ms : list amap) : bool := forallb (fun m => negb (is_hole m)) ms.
Definition reg (cs : acs) (n : nat) : expr := CXNAT.nthF n (s_regs (a_ss cs)) (ELit 0).
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
Definition lit_of (e : expr) : option Z := match e with ELit z => Some (CXLF.zm64 z) | _ => None end.
Definition reg_lit (cs : acs) (n : nat) : option Z := lit_of (reg cs n).
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition esub (a b : expr) : expr := mkAlu ALU_SUB a b.
Definition escale (c : Z) (e : expr) : expr := mkMd M_MUL (ELit c) e.
Definition eaddz (a : expr) (z : Z) : expr := mkAlu ALU_ADD a (ELit z).
Definition e_pgsp : expr := eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10)).
Definition pgdown (z : Z) : Z := z - z mod 4096.
Definition e_spw : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 4096) (EVar 10))).
Definition sa_stk : saddr := SA e_pgsp (-8388608).
Definition en_stk : expr := ELit STKSPAN.
Definition sa_stk0 : saddr := SA e_spw (-8388608).
Definition lit_entry (m : amap) (lo hi : Z) : bool :=
  negb (is_fog m) &&
  match lit_of (am_base m), lit_of (am_len m) with
  | Some b, Some n => Z.eqb b lo && Z.eqb (b + n) hi
  | _, _ => false
  end.
Definition has_entry (ms : list amap) (lo hi : Z) : bool := existsb (fun m => lit_entry m lo hi) ms.
Definition has_entry_k (ms : list amap) (lo hi : Z) (kd : mkind) : bool :=
  existsb (fun m => lit_entry m lo hi && mkind_eqb (am_kind m) kd) ms.
Definition zone_reserved (ms : list amap) : bool :=
  has_entry ms (zone_lo A) (lowsh_hi A) && has_entry ms (lowsh_hi A) (highsh_lo A) && has_entry ms (highsh_lo A) (zone_hi A).
Definition shadows_ready (ms : list amap) : bool :=
  has_entry_k ms (zone_lo A) (lowsh_hi A) KRWLAZY && has_entry ms (lowsh_hi A) (highsh_lo A)
  && has_entry_k ms (highsh_lo A) (zone_hi A) KRWLAZY.
Definition sa_hull : saddr := SA (ELit 0) (img_lo A).
Definition en_hull : expr := ELit (img_hi A - img_lo A).
Definition sa_zone : saddr := SA (ELit 0) (zone_lo A).
Definition en_zone : expr := ELit (zone_hi A - zone_lo A).
Fixpoint expr_vars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (CXNAT.eqbF n) acc then acc else n :: acc
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
  forallb (fun v => CXNAT.ltbF v nx0 || existsb (CXNAT.eqbF v) live) (expr_vars e []).
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
Definition vkey (n : nat) : positive := CXNAT.of_succ_natF n.
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
  | EVar n => if CXNAT.ltbF n nx0 then true else in_live_t t n
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
  forall v, existsb (CXNAT.eqbF v) acc = in_live_t t v.
Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => CXNAT.ltbF n b
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
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && CXNAT.lebF nx0 v.
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
Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block K fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.
Definition kentry_eqb (x y : kentry) : bool :=
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && CXNAT.eqbF w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && CXNAT.eqbF k k'
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
  | FdFile k l o, FdFile k' l' o' => CXNAT.eqbF k k' && expr_eqb l l' && expr_eqb o o'
  | _, _ => false
  end.
Definition zkey (z : Z) : Z := if Z.leb 0 z then 2 * z else 1 - 2 * z.
Definition lkey (e : expr) : Z := match e with ELit z => zkey z | _ => 0 end.
Definition kkeyZ (K : kentry) : Z :=
  match K with
  | KWord a w _ => 1 + 16 * (zkey (a_off a) + 8 * Z.of_nat w)
  | KZero a n => 2 + 16 * (zkey (a_off a) + 4 * lkey n)
  | KBlob a n _ => 3 + 16 * (zkey (a_off a) + 4 * lkey n)
  | KImg lo hi => 4 + 16 * (zkey lo + 4 * zkey (hi - lo))
  | KAlign e m => 5 + 16 * zkey m
  | KRange e lo hi => 6 + 16 * (zkey lo + 4 * zkey (hi - lo))
  | KWr a n => 7 + 16 * (zkey (a_off a) + 4 * lkey n)
  | KDisj a1 n1 a2 n2 => 8 + 16 * (zkey (a_off a1) + 4 * (lkey n1 + 4 * (zkey (a_off a2) + 4 * lkey n2)))
  | KFill a n c => 9 + 16 * (zkey (a_off a) + 4 * (lkey n + 4 * zkey c))
  | KUnk a n => 10 + 16 * (zkey (a_off a) + 4 * lkey n)
  end%Z.
Definition kkey (K : kentry) : positive := Z.to_pos (1 + Z.abs (kkeyZ K)).
Definition kset : Type := ptree (list kentry).
Definition kset_bucket (s : kset) (p : positive) : list kentry :=
  match pt_get s p with Some l => l | None => [] end.
Definition kset_add (K : kentry) (s : kset) : kset := pt_set (kkey K) (K :: kset_bucket s (kkey K)) s.
Definition kset_of (k : list kentry) : kset := List.fold_right kset_add PTLeaf k.
Definition kset_mem (s : kset) (K : kentry) : bool := existsb (fun X => kentry_eqb X K) (kset_bucket s (kkey K)).
Definition kn_isect (k1 k2 : list kentry) : list kentry :=
  let s := kset_of k2 in List.filter (kset_mem s) k1.
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => CXNAT.lebF w 8 && ranges_apart_x allkn ub uk un b k (ELit (Z.of_nat w))
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
  | KWord (SA b k) w _ => CXNAT.lebF w 8 && ranges_apart_xB bc ub uk un b k (ELit (Z.of_nat w))
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
Definition kentry_apart_bp (allkn : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => CXNAT.lebF w 8 && ranges_apart_p allkn sp ub uk un b k (ELit (Z.of_nat w))
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
  | KWord (SA b k) w _ => CXNAT.lebF w 8 && ranges_apart_pBF bc sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_pBF bc sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_pBF bc sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_pBF bc sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_pBF bc sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_pBF bc sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_pBF bc sp ub uk un b k l
  end.
Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.
Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bpB bc sp ub uk un K) (bc_fk bc).
Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
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
Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (havoc1p k sp ub uk un) k.
Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (havoc1pB bc sp ub uk un) (bc_fk bc).
Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.
Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcutB bc KWr ub uk un kb kk len.
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
Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.flat_map (cutout1p k sp ub uk un) k.
Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  List.flat_map (cutout1pB bc sp ub uk un) (bc_fk bc).
Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
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
Definition gcdisj_keep (lv lg : list expr) (K : kentry) : bool :=
  match K with
  | KDisj c1 _ c2 _ =>
      let l1 := existsb (expr_eqb (a_base c1)) lv in
      let l2 := existsb (expr_eqb (a_base c2)) lv in
      if l1 then (if l2 then true else existsb (expr_eqb (a_base c2)) lg)
      else if l2 then existsb (expr_eqb (a_base c1)) lg else false
  | _ => true
  end.
Definition ledger_bases (cs : acs) : list expr :=
  List.map (fun m => fst (split_lit (am_base m))) (a_maps cs)
  ++ List.map (fun pr : expr * expr => fst (split_lit (fst pr))) (a_vis cs)
  ++ List.map (fun pr : expr * expr => fst (split_lit (fst pr))) (a_ghost cs).
Definition kn_gcdisj (cs : acs) (live : list expr) : list kentry :=
  let lv := List.map (fun e => fst (split_lit e)) live in
  List.filter (gcdisj_keep lv (ledger_bases cs)) (kn cs).
Fixpoint evars_cnt (e : expr) (t : ptree nat) : ptree nat :=
  match e with
  | ELit _ => t
  | EVar v => let key := CXNAT.of_succ_natF v in pt_set key (S (match pt_get t key with Some n => n | None => 0%nat end)) t
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_cnt b (evars_cnt a t)
  | EExt _ _ _ a => evars_cnt a t
  | EBlob _ _ _ _ => t
  end.
Definition kvars_cnt (K : kentry) (t : ptree nat) : ptree nat :=
  match K with
  | KWord a _ v => evars_cnt v (evars_cnt (a_base a) t)
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_cnt n (evars_cnt (a_base a) t)
  | KImg _ _ => t
  | KAlign x _ | KRange x _ _ => evars_cnt x t
  | KDisj a1 n1 a2 n2 => evars_cnt n2 (evars_cnt (a_base a2) (evars_cnt n1 (evars_cnt (a_base a1) t)))
  end.
Definition pvars_cnt (ps : list (expr * expr)) (t : ptree nat) : ptree nat :=
  List.fold_right (fun pr acc => evars_cnt (snd pr) (evars_cnt (fst pr) acc)) t ps.
Definition csvars_cnt (cs : acs) : ptree nat :=
  let t1 := List.fold_right evars_cnt PTLeaf (s_regs (a_ss cs)) in
  let t2 := List.fold_right kvars_cnt t1 (kn cs) in
  let t3 := List.fold_right (fun m acc => evars_cnt (am_len m) (evars_cnt (am_base m) acc)) t2 (a_maps cs) in
  let t4 := pvars_cnt (a_vis cs) (pvars_cnt (a_ghost cs) t3) in
  let t5 := evars_cnt (a_brk cs) t4 in
  match a_fd cs with FdFile _ l o => evars_cnt o (evars_cnt l t5) | _ => t5 end.
Definition var_lonely (t : ptree nat) (v : nat) : bool :=
  match pt_get t (CXNAT.of_succ_natF v) with Some (S O) => true | _ => false end.
Definition gcrange_keep (t : ptree nat) (K : kentry) : bool :=
  match K with
  | KRange (EVar v) _ _ | KAlign (EVar v) _ => if CXNAT.lebF nx0 v then negb (var_lonely t v) else true
  | _ => true
  end.
Definition kn_gcrange (cs : acs) : list kentry := List.filter (gcrange_keep (csvars_cnt cs)) (kn cs).
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
  | LHit (ELit z) [] _ => Some (CXLF.zm64 z)
  | _ => None
  end.
Definition kreadZB (bc : bctx) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookupB segs bc b off n false [] [] with
  | LHit (ELit z) [] _ => Some (CXLF.zm64 z)
  | _ => None
  end.
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
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).
Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_xB bc b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).
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
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := xlo k e.
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).
Definition len_eqbB (bc : bctx) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0B bc [(n, 0%Z)] [(m, 0%Z)] && lin_ge0B bc [(m, 0%Z)] [(n, 0%Z)]).
Definition lit_diff (e f : expr) : option Z :=
  match esub e f with ELit z => Some (CXLF.zm64 z) | _ => None end.
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
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := CXLF.zm64 m in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (CXLF.zpow2 j) && Z.leb j 48)%bool
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
Definition xlo2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (lo, _) => Some lo | None => None end.
Definition xlo2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (lo, _) => Some lo | None => None end.
Definition xhi2 (k : list kentry) (e : expr) : option Z := match xb2 k e with Some (_, hi) => Some hi | None => None end.
Definition xhi2B (bc : bctx) (e : expr) : option Z := match xb2B bc e with Some (_, hi) => Some hi | None => None end.
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
Definition node_join (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  if (CXNAT.lebF 1 n && CXNAT.lebF n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool then
    match kread_bytes n (kn cs) b off with
    | Some bs => Some (add_kn cs [KWord (SA b off) n (ELit (zbytes_le_to_Z bs))])
    | None => None
    end
  else None.
Fixpoint drop_ixs (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (CXNAT.eqbF i) ixs then drop_ixs ixs (S i) r else K :: drop_ixs ixs (S i) r
  end.
Definition residue_fact (k : list kentry) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1 k e', xhi1 k e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].
Definition mask_fact1 (k : list kentry) (x ne : expr) : list kentry :=
  match x with
  | ELit _ => []
  | _ => match xhi1 k x with Some hx => [KRange (esub x ne) 0 hx] | None => [] end
  end.
Definition mask_fact (k : list kentry) (base : option expr) (er ne : expr) : list kentry :=
  match base, er with
  | None, EAlu ALU_AND x y => mask_fact1 k x ne ++ mask_fact1 k y ne
  | _, _ => []
  end.
Definition node_fresh (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs :=
  let k := kn cs in let c := 2 ^ logc in
  let b := match base with Some b => b | None => ELit 0 end in
  let e := esub (reg cs r) b in
  if (CXNAT.ltbF 0 r && CXNAT.ltbF r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign k e)
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) e && fresh_ok cs)%bool then
    match xlo2 k e, xhi2 k e with
    | Some lo, Some hi =>
        let v := nxt cs in
        let ne := escale c (EVar v) in
        let kres := residue_fact k e ne ++ mask_fact k base (reg cs r) ne in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: kres in
        Some (bump (set_reg (add_kn cs kf) r (eadd b ne)) 1)
    | _, _ => None
    end
  else None.
Definition node_joinx (cs : acs) (b : expr) (off : Z) (n : nat) : option acs :=
  if (CXNAT.lebF 1 n && CXNAT.lebF n 8 && fresh_ok cs && expr_vars_lt (nxt cs) b
      && kn_readable segs (kn cs) (kn cs) b off n)%bool then
    let v := nxt cs in
    Some (bump (add_kn cs [KWord (SA b off) n (EVar v)]) 1)
  else None.
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havoc (kn cs) bb bk n).
Definition node_bump (cs : acs) (m : nat) : option acs :=
  if CXNAT.lebF (nxt cs) m then Some (bump cs (m - nxt cs)) else None.
Definition node_havoc (cs : acs) (rs : list nat) : option acs :=
  if (fresh_ok cs && forallb (fun r => CXNAT.ltbF 0 r && CXNAT.ltbF r 32) rs)%bool then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (sr_fresh (s_regs ss) rs (s_next ss)) (s_know ss) (s_next ss + length rs)))
  else None.
Fixpoint esize (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  | _ => 1%nat
  end.
Definition bigb (K : nat) (e : expr) : bool := CXNAT.ltbF K (esize e).
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
Definition xinside_joint (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xlo kn b2, xhi kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_range kn b1, xhi kn n1, xlo kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 =>
            Z.leb (lo2 + k2) (lo1 + k1) &&
            match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some eh => Z.leb eh (lo2 + k2 + l2) | None => false end
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinside_jointB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 =>
            Z.leb (lo2 + k2) (lo1 + k1) &&
            match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some eh => Z.leb eh (lo2 + k2 + l2) | None => false end
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinsideJ (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  xinside kn b1 k1 n1 b2 k2 n2 || xinside_joint kn b1 k1 n1 b2 k2 n2.
Definition xinsideJB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  xinsideB bc b1 k1 n1 b2 k2 n2 || xinside_jointB bc b1 k1 n1 b2 k2 n2.
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideJ k b off n (am_base m) 0 (am_len m)) ms.
Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinsideJB bc b off n (am_base m) 0 (am_len m)) ms.
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).
Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).
Definition TASK : Z := 0x800000000000.
Definition sh_covered (k : list kentry) (ms : list amap) (bb : expr) (bk : Z) (n : expr) (sb : expr) (sk : Z) (sn : expr) : bool :=
  shadows_ready ms && flat_x k sb sk sn &&
  ranges_apart_x k bb bk n (a_base sa_zone) (a_off sa_zone) en_zone &&
  match base_range k bb, xhi k n with
  | Some (lo, hi), Some nh => Z.leb 0 (lo + bk) &&
      (Z.leb (hi + bk + nh) TASK   
       || match end_hi k bb bk n lo hi nh with Some eh => Z.leb eh TASK | None => false end)
  | _, _ => false
  end.
Definition sh_coveredB (bc : bctx) (ms : list amap) (bb : expr) (bk : Z) (n : expr) (sb : expr) (sk : Z) (sn : expr) : bool :=
  shadows_ready ms && flat_xB bc sb sk sn &&
  ranges_apart_xB bc bb bk n (a_base sa_zone) (a_off sa_zone) en_zone &&
  match base_rangeB bc bb, xhiB bc n with
  | Some (lo, hi), Some nh => Z.leb 0 (lo + bk) &&
      (Z.leb (hi + bk + nh) TASK
       || match end_hiB bc bb bk n lo hi nh with Some eh => Z.leb eh TASK | None => false end)
  | _, _ => false
  end.
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  let '(bb, bk) := split_lit b in
  if (match find_containing k ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
      || sh_covered k ms bb bk n sb sk sn)%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].
Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  let '(bb, bk) := split_lit b in
  if (match find_containingB bc ms [KRWLAZY] sb sk sn with Some _ => true | None => false end
      || sh_coveredB bc ms bb bk n sb sk sn)%bool
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].
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
Fixpoint find_zone_disj (k : list kentry) (b : expr) : option expr :=
  match k with
  | [] => None
  | KDisj (SA c1 o1) n1 (SA c2 o2) n2 :: r =>
      if (expr_eqb c1 (ELit 0) && Z.eqb o1 (zone_lo A) && expr_eqb n1 en_zone && expr_eqb c2 b && Z.eqb o2 0)%bool then Some n2
      else find_zone_disj r b
  | _ :: r => find_zone_disj r b
  end.
Definition node_band_at (cs : acs) (v : nat) : option (acs * acs) :=
  let k := kn cs in
  let b := escale 4096 (EVar v) in
  match find_zone_disj k b, xlo2 k (EVar v), xhi2 k (EVar v) with
  | Some n2, Some lo, Some hi =>
      match xlo k n2 with
      | Some nlo =>
          if (Z.leb 0 (zone_lo A) && Z.leb (zone_lo A) (zone_hi A) && Z.ltb (zone_hi A) two64
              && Z.leb 0 lo && Z.leb hi (2 ^ 51) && flat_x k b 0 n2)%bool
          then
            let hi1 := Z.min hi ((zone_lo A - nlo) / 4096) in
            let lo2 := Z.max lo ((zone_hi A + 4095) / 4096) in
            let csl := add_kn cs [KRange (EVar v) lo hi1] in
            let csh := add_kn cs [KRange (EVar v) lo2 hi] in
            
            Some (if Z.ltb hi1 lo then csh else csl, if Z.ltb hi lo2 then csl else csh)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Definition band_var (cs : acs) (v : nat) : nat :=
  if CXNAT.eqbF v 0 then match lin_of (reg cs 10) with (0%Z, [(4096%Z, EVar w)]) => w | _ => v end else v.
Definition node_band (cs : acs) (v : nat) : option (acs * acs) := node_band_at cs (band_var cs v).
Definition node_shdisj_ref (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
  if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      
      && ranges_apart_x k c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.
Definition node_shdisj (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_ofB bc b1 n1 in let '(sb2, sk2, sn2) := shadow_ofB bc b2 n2 in
  if (Z.leb 3 (ealignB bc b1) && Z.leb 3 (ealignB bc n1) && Z.leb 3 (ealignB bc b2) && Z.leb 3 (ealignB bc n2)
      && flat_xB bc c1 o1 n1 && flat_xB bc c2 o2 n2 && flat_xB bc sb1 sk1 sn1 && flat_xB bc sb2 sk2 sn2
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.
Definition mmap_len_ref (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in
      match xlo k le, xhi k le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealign k le) && Z.leb hi (CXLF.p46))%bool then Some (le, lo, hi) else None
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
          if (Z.ltb 0 lo && Z.leb 12 (ealignB bc le) && Z.leb hi (CXLF.p46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.
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
Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))       
    | _, _ => false
    end) || xinside k b off len (a_base sa_stk) (a_off sa_stk) en_stk              
        || (zone_reserved ms && xinside k b off len (a_base sa_zone) (a_off sa_zone) en_zone)   
        || inside_maps k ms b off len)%bool.
Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))       
    | _, _ => false
    end) || xinsideB bc b off len (a_base sa_stk) (a_off sa_stk) en_stk
        || (zone_reserved ms && xinsideB bc b off len (a_base sa_zone) (a_off sa_zone) en_zone)
        || inside_mapsB bc ms b off len)%bool.
Definition grant_keep_b (k : list kentry) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => CXNAT.lebF w 8 && safe_range k ms b o (ELit (Z.of_nat w))
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
  | KWord (SA b o) w _ => CXNAT.lebF w 8 && safe_rangeB bc ms b o (ELit (Z.of_nat w))
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
Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_b k ms) k).
Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry :=
  kimg_clip (List.filter (grant_keep_bB bc ms) (bc_fk bc)).
Definition safe_rangeBF (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  if (match xhiB bc len, base_rangeB bc b with
      | Some lh, Some (lo, hi) => (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))
      | _, _ => false
      end)%bool then true
  else if xinsideB bc b off len (a_base sa_stk) (a_off sa_stk) en_stk then true
  else if (if zone_reserved ms then xinsideB bc b off len (a_base sa_zone) (a_off sa_zone) en_zone else false) then true
  else inside_mapsB bc ms b off len.
Definition grant_keep_bBF (bc : bctx) (ms : list amap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => if CXNAT.lebF w 8 then safe_rangeBF bc ms b o (ELit (Z.of_nat w)) else false
  | KZero (SA b o) l => safe_rangeBF bc ms b o l
  | KBlob (SA b o) l _ => safe_rangeBF bc ms b o l
  | KImg lo hi => true
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_rangeBF bc ms b o n
  | KFill (SA b o) l _ => safe_rangeBF bc ms b o l
  | KUnk (SA b o) l => safe_rangeBF bc ms b o l
  end.
Definition kn_grant_filterF (k : list kentry) (ms : list amap) : list kentry :=
  let bc := mkbc k in kimg_clip (List.filter (grant_keep_bBF bc ms) k).
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.
Definition budget_ok (cs : acs) (extra : Z) : bool :=
  Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.
Definition kdisj_maps (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA nb 0) ne]) ms.
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  KDisj sa_hull en_hull (SA nb 0) ne
  :: KDisj sa_stk en_stk (SA nb 0) ne
  :: KDisj sa_stk0 en_stk (SA nb 0) ne    
  :: (if zone_reserved ms then [KDisj sa_zone en_zone (SA nb 0) ne] else [])
  ++ kdisj_maps ms nb ne.
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
  | _ => [KRange (eadd base ne) (4096 + nlo) TOPMAX]
  end.
Definition null_lo (ms : list amap) (nlo : Z) : Z :=
  if Z.ltb (img_lo A - 4096) nlo
  then if (zone_reserved ms && Z.ltb (zone_lo A - img_hi A) nlo)%bool
       then (zone_hi A + 4095) / 4096
       else img_hi A / 4096
  else 1.
Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && Z.leb nhi TOPMAX
          && no_holes (a_maps cs))%bool then     
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        
        let kfacts := KRange (EVar v) (null_lo (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      
      if (page_aligned k a && Z.ltb 0 alo && (Z.leb (img_hi A) alo || Z.leb (ahi + nhi) (img_lo A)) && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool
      then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.
Definition fixed_args_base (cs : acs) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a with
  | Some (ne, nlo, nhi), Some alo =>
      if (page_aligned k a && Z.ltb 0 alo && flat_x k b off ne)%bool
      then Some (b, off, ne, nlo, nhi) else None
  | _, _ => None
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
  
  match fixed_args cs CEIL with
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
Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args_base cs with
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
  match fixed_args_base cs with
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
                 
                 | 3, 0x104022 | 3, 0x104032 => mmap_fixed_free cs KRWLAZY false false   
                 | 0, 0x104022 | 0, 0x104032 => mmap_fixed_free cs KNONELAZY false false 
                 | _, _ => None
                 end in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | None => None
  end.
Definition mmap_nullF (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && Z.leb nhi TOPMAX
          && no_holes (a_maps cs))%bool then     
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        
        let kfacts := KRange (EVar v) (null_lo (a_maps cs) nlo) ((TOPMAX - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterF (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.
Definition mmap_fixed_grantF (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
           (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let m := AM a ne kind in
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filterF k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.
Definition mmap_fixed_freeF (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  
  match fixed_args cs CEIL with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grantF cs (a_maps cs) b off ne nhi kind eager visible
      else
      
          match find_hole k (a_maps cs) a ne with
          | Some h =>
              let ms0 := unhole (a_maps cs) h in
              if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
                  && (negb eager || budget_ok cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
              then mmap_fixed_grantF cs ms0 b off ne nhi kind eager visible
              else None
          | None => None
          end
  | None => None
  end.
Definition node_mmap2F (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_nullF cs KRW true true               
                 | 3, 0x4022 => mmap_nullF cs KRWLAZY false true        
                 | 0, 0x22 => mmap_nullF cs KNONE false false           
                 | 0, 0x4022 => mmap_nullF cs KNONELAZY false false     
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_freeF cs KRWLAZY false false  
                 | 3, 0x32 => mmap_fixed_freeF cs KRW true true          
                 | 0, 0x4032 => mmap_fixed_freeF cs KNONELAZY false false 
                 | 0, 0x32 => mmap_fixed_freeF cs KNONE false false      
                 
                 | 3, 0x104022 | 3, 0x104032 => mmap_fixed_freeF cs KRWLAZY false false   
                 | 0, 0x104022 | 0, 0x104032 => mmap_fixed_freeF cs KNONELAZY false false 
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
  match reg_lit cs 17, reg_lit cs 12, fixed_args_base cs with
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
  match reg_lit cs 17, reg_lit cs 12, fixed_args_base cs with
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
Definition node_mprotect2 (cs : acs) : option (acs * acs) :=
  match node_mprotect cs with Some csG => Some (refuse cs, csG) | None => None end.
Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.
Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%bool.
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
Definition brk_req (cs : acs) : option Z :=
  match lit_diff (reg cs 10) (a_brk cs) with
  | Some d => if (Z.ltb 0 d && Z.eqb (d mod 4096) 0 && Z.leb d (CXLF.p40))%bool then Some d else None
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
                        && lin_ge0 k [(b, d + 4096 - 1)] [(am_base m, 0)])        
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
  if (CXNAT.lebF i (length (a_maps cs)) && Z.leb 0 sz && Z.ltb sz two64)%bool
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
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) TOPMAX   
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
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) TOPMAX
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
Definition introg_witness (lo hi n w : Z) : bool :=
  (Z.leb lo w && Z.leb w hi && Z.leb 1 w && Z.ltb 0 n && Z.leb (4096 * w + n) (img_lo A) && Z.leb (4096 * w + n) (zone_lo A) && Z.leb (4096 * w + n) CEIL)%bool.
Definition node_introg (cs : acs) (lo hi n : Z) : option acs :=
  let w := if introg_witness lo hi n 1 then Some 1 else if introg_witness lo hi n lo then Some lo else None in
  match w with
  | Some _ =>
      if (fresh_ok cs && Z.leb 0 lo && Z.ltb hi two64)%bool then
        let v := nxt cs in let hb := escale 4096 (EVar v) in let ss := a_ss cs in
        let kz := if zone_reserved (a_maps cs) then KDisj sa_zone en_zone (SA hb 0) (ELit n) :: s_know ss else s_know ss in
        Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss)
                              (KRange (EVar v) lo hi :: KDisj sa_hull en_hull (SA hb 0) (ELit n) :: KDisj sa_stk en_stk (SA hb 0) (ELit n)
                               :: KDisj sa_stk0 en_stk (SA hb 0) (ELit n) :: kz) (S v)))
      else None
  | None => None
  end.
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
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_x k k db dk ne && kwritable_x k k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (CXLF.zm64 d) n) | _, _ => None end) with
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
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (CXLF.zm64 d) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := if off_image_xB bc db dk ne then kn_havocB bc db dk ne else kn_havocM k0 db dk ne in   
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.
Definition summary_fill_b (bc : bctx) (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in   
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xloB bc ne, xhiB bc ne, xhiB bc dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (CXLF.zm64 d) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := if off_image_xB bc db dk ne then kn_havocB bc db dk ne else kn_havocM k0 db dk ne in   
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.
Lemma summary_fill_b_ok : forall cs entry cmax, summary_fill_b (mkbc (kn cs)) cs entry cmax = summary_fill cs entry cmax.
Proof. reflexivity. Qed.

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
Definition kblob_prefix (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) (ne : expr) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) n0 _ =>
                                 expr_eqb b sb && Z.eqb o sk &&
                                 match n0 with
                                 | ELit z => Z.ltb 0 z && Z.leb z nlo
                                 | _ => Z.ltb 0 nlo && expr_eqb n0 ne
                                 end
                             | _ => false
                             end) k with
  | Some (KBlob _ n0 j) => [KBlob (SA db dk) n0 j]
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
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (CXLF.zm64 d) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne)%bool then
              let k1 := kn_havoc k0 db dk ne in
              
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
Definition summary_copy (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (CXLF.zm64 d) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := if off_image_xB bc db dk ne then kn_havocB bc db dk ne else kn_havocM k0 db dk ne in   
              
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
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
Definition summary_copy_b (bc : bctx) (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in   
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (CXLF.zm64 d) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := if off_image_xB bc db dk ne then kn_havocB bc db dk ne else kn_havocM k0 db dk ne in   
              
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ne ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
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
Lemma summary_copy_b_ok : forall cs entry, summary_copy_b (mkbc (kn cs)) cs entry = summary_copy cs entry.
Proof. reflexivity. Qed.

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
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.leb (bhi + nhi + 8) two64
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
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritableB bc k qb qk 16
              && ranges_apart_xB bc qb qk (ELit 16) bb bk ne && kzero_xB bc k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havocB bc qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.
Definition summary_miz_b (bc : bctx) (cs : acs) : option acs :=
  let k := kn cs in   
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xloB bc ne, xhiB bc ne, xhiB bc beg, xloB bc sp, xhiB bc sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (CXLF.p40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritableB bc k qb qk 16
              && ranges_apart_xB bc qb qk (ELit 16) bb bk ne && kzero_xB bc k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havocB bc qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.
Lemma summary_miz_b_ok : forall cs, summary_miz_b (mkbc (kn cs)) cs = summary_miz cs.
Proof. reflexivity. Qed.

Definition img_cov (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.
Definition img_covB (bc : bctx) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) (bc_fk bc).
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
                 else match dst with ELit d => Some (kimg_cut k (CXLF.zm64 d) 4095) | _ => None end) with
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
                 else match dst with ELit d => Some (kimg_cut k (CXLF.zm64 d) 4095) | _ => None end) with
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
Definition V_S1 : nat := 0.
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.
Definition V_W : nat := 4.
Definition V_BRK : nat := 5.
Definition V_S2 : nat := 6.
Definition V_P : nat := 10.
Definition V_Q : nat := 11.
Definition V_HW : nat := 9.
Definition V_L1 : nat := 7.
Definition V_UID : nat := 8.
Definition e_sp0 : expr := eadd (eadd (escale 32768 (EVar V_S1)) (escale 4096 (EVar V_P))) (escale 16 (EVar V_S2)).
Definition e_sp8 : expr := eadd (eadd (escale 4096 (EVar V_S1)) (escale 512 (EVar V_P))) (escale 2 (EVar V_S2)).
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := eadd e_envp (eadd (escale 8 (EVar V_ENVC)) (ELit 8)).
Definition e_str0 : expr := eaddz e_auxv 160.
Definition e_str1 : expr := eadd e_str0 (eaddz (EVar V_L0) 1).
Definition e_atrandom : expr := eadd e_str0 (escale 8 (EVar V_W)).
Definition e_atr8 : expr :=
  eadd e_sp8 (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).
Definition e_Xsh : expr := eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (eadd (EVar V_W) (escale 2 (EVar V_S2)))).
Definition e_Xm : expr := mkAlu ALU_AND e_Xsh (ELit (-8)).
Definition e_atr8m : expr := eadd (eadd (escale 4096 (EVar V_S1)) (escale 512 (EVar V_P))) e_Xm.
Definition e_vis3b : expr := escale 32768 (EVar V_S1).
Definition e_vis3n : expr := eadd (escale 4096 (EVar V_P)) (escale 4096 (EVar V_Q)).
Definition e_pgslack : expr := esub (esub (escale 4096 (EVar V_Q)) (escale 16 (EVar V_S2)))
                                    (escale 8 (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W)))).
Definition e_pgslack8 : expr := esub (esub (escale 512 (EVar V_Q)) (escale 2 (EVar V_S2)))
                                     (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).
Definition e_top8 : expr := eadd (escale 4096 (EVar V_S1)) (eadd (escale 512 (EVar V_P)) (escale 512 (EVar V_Q))).
Definition e_top : expr := eadd (escale 32768 (EVar V_S1)) (eadd (escale 4096 (EVar V_P)) (escale 4096 (EVar V_Q))).
Definition e_blk0 : expr := esub (esub (escale 4096 (EVar V_Q)) (escale 16 (EVar V_S2))) (escale 8 (eadd (EVar V_ARGC) (EVar V_ENVC))).
Definition e_blk08 : expr := esub (esub (escale 512 (EVar V_Q)) (escale 2 (EVar V_S2))) (eadd (EVar V_ARGC) (EVar V_ENVC)).
Definition e_blkL0 : expr := esub e_blk0 (EVar V_L0).
Definition e_blkL01 : expr := esub (esub e_blk0 (EVar V_L0)) (EVar V_L1).
Definition e_strW0 : expr := esub (escale 8 (EVar V_W)) (EVar V_L0).
Definition e_strW01 : expr := esub (esub (escale 8 (EVar V_W)) (EVar V_L0)) (EVar V_L1).
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
Definition kimg_sub_covered0 (k : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k
  | _ => false
  end.
Definition kn_incl1_eF (s : kset) (k : list kentry) (K : kentry) : bool :=
  if kset_mem s K then true else kimg_sub_covered0 k K.
Definition kn_incl_e (k tk : list kentry) : bool := let s := kset_of k in forallb (kn_incl1_eF s k) tk.
Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_e (kn cs) (kn ch)   
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
  | EVar n => if CXNAT.eqbF n J then e else x
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
Definition brk_vis (cs : acs) (hb : expr) (d : Z) : option acs :=
  if Z.ltb 4096 d then
    match vis_add cs hb (ELit 4096) (kn cs) with
    | Some cs1 => 
                   vis_add cs1 (eaddz hb 4096) (ELit (d - 4096))
                           (KWr (SA hb 0) (ELit 4096) :: KZero (SA hb 0) (ELit 4096)
                            :: KWr (SA hb 4096) (ELit (d - 4096)) :: KZero (SA hb 4096) (ELit (d - 4096)) :: kn cs1)
    | None => None
    end
  else vis_add cs hb (ELit d) (KWr (SA hb 0) (ELit d) :: KZero (SA hb 0) (ELit d) :: kn cs).
Definition brk_var (b : expr) : option nat :=
  match b with EMd M_MUL (ELit 4096) (EVar j) => Some j | _ => None end.
Definition node_brk2 (cs : acs) : option (bool * acs * acs) :=
  match reg_lit cs 17, brk_req cs, brk_var (a_brk cs) with
  | Some 214, Some d, Some j =>
      let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
      if (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d && flat_x k bb bk (ELit (d + 4096)) && fresh_ok cs
          && expr_vars_lt (nxt cs) (reg cs 10) && expr_vars_lt (nxt cs) b)%bool then
        let poss := forallb (fun m => ranges_apart_x k bb bk (ELit (d + 4096)) (am_base m) 0 (am_len m)) (a_maps cs) in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kdisj_new (a_maps cs) b (ELit d) ++ kn_grant_filter k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match brk_vis csB b d with
        | Some csB' => Some (poss, csA, bump (inst csB' j (EVar (nxt cs))) 1)
        | None => None
        end
      else None
  | _, _, _ => None
  end.
Definition node_brk2F (cs : acs) : option (bool * acs * acs) :=
  match reg_lit cs 17, brk_req cs, brk_var (a_brk cs) with
  | Some 214, Some d, Some j =>
      let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
      if (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d && flat_x k bb bk (ELit (d + 4096)) && fresh_ok cs
          && expr_vars_lt (nxt cs) (reg cs 10) && expr_vars_lt (nxt cs) b)%bool then
        let poss := forallb (fun m => ranges_apart_x k bb bk (ELit (d + 4096)) (am_base m) 0 (am_len m)) (a_maps cs) in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kdisj_new (a_maps cs) b (ELit d) ++ kn_grant_filterF k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match brk_vis csB b d with
        | Some csB' => Some (poss, csA, bump (inst csB' j (EVar (nxt cs))) 1)
        | None => None
        end
      else None
  | _, _, _ => None
  end.
Fixpoint nt_set (t : list (option nat)) (i : nat) (d : nat) {struct i} : list (option nat) :=
  match i, t with
  | O, [] => [Some d]
  | O, _ :: rest => Some d :: rest
  | S j, [] => None :: nt_set [] j d
  | S j, x :: rest => x :: nt_set rest j d
  end.
Definition nt_get (t : list (option nat)) (i : nat) : option nat := CXNAT.nthF i t None.
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
  if forallb (fun p => CXNAT.lebF gb (fst p) && CXNAT.lebF gb (snd p)) m then
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
Definition bt_get (t : list bool) (i : nat) : bool := CXNAT.nthF i t false.
Fixpoint evars_fo (gb : nat) (e : expr) (acc : list nat * list bool) : list nat * list bool :=
  match e with
  | ELit _ => acc
  | EVar v => if CXNAT.ltbF v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
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
      | EVar v => if (CXNAT.lebF lo v && CXNAT.ltbF v hi)%bool
                  then (negb (existsb (CXNAT.eqbF v) seen) && regs_match_h lo hi (v :: seen) rs' ts')%bool
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
      (Z.ltb 0 n && Z.leb n (CXLF.p40) && Z.leb (img_lo A) (img_hi A) && flat_x k b o (ELit n) && off_image_x k b o (ELit n) && cover_x (S (length k)) k b o (o + n))%bool
  | _ => false
  end.
Definition kentry_eqb_h (x y : kentry) : bool :=
  kentry_eqb x y ||
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb_h a a' && CXNAT.eqbF w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb_h a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb_h a a' && expr_eqb n n' && CXNAT.eqbF k k'
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
Definition kn_incl1_hF (s : kset) (k : list kentry) (K : kentry) : bool :=
  if kset_mem s K then true
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered k K.
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool := let s := kset_of k in forallb (kn_incl1_hF s k) tk.
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
Definition kzero_sub_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KZero (SA b o) (ELit n) =>
      Z.ltb 0 n && Z.ltb n two64 &&
      existsb (fun X => match X with
                         | KZero (SA b' o') (ELit n') =>
                             expr_eqb b b' && Z.leb 0 n' && Z.ltb n' two64 && Z.leb o' o && Z.leb (o + n) (o' + n')
                         | _ => false
                         end) k
  | _ => false
  end%bool.
Definition krange_implied (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi => match erange k e with
                      | Some (lo', hi') => Z.leb lo lo' && Z.leb hi' hi
                      | None => false
                      end
  | _ => false
  end%bool.
Definition kn_incl1_x (cs : acs) (K : kentry) : bool :=
  let k := kn cs in
  if existsb (kentry_eqb K) k then true
  else if kimg_sub_covered0 k K then true
  else if kzero_sub_covered k K then true
  else if krange_implied k K then true
  else kunk_covered k K.
Definition kn_incl1_xF (s : kset) (cs : acs) (K : kentry) : bool :=
  let k := kn cs in
  if kset_mem s K then true
  else if kimg_sub_covered0 k K then true
  else if kzero_sub_covered k K then true
  else if krange_implied k K then true
  else kunk_covered k K.
Definition kn_incl_x0 (cs : acs) (tk : list kentry) : bool := let s := kset_of (kn cs) in forallb (kn_incl1_xF s cs) tk.
Definition entails0 (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_x0 cs (kn ch)   
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.
Fixpoint hx_cell (k : list kentry) (a : saddr) (w : nat) : option expr :=
  match k with
  | [] => None
  | KWord a' w' v :: r => if (saddr_eqb a' a && CXNAT.eqbF w' w)%bool then Some v else hx_cell r a w
  | _ :: r => hx_cell r a w
  end.
Definition hx_cellv (k : list kentry) (a : saddr) (w : nat) : option expr :=
  match hx_cell k a w with
  | Some v => Some v
  | None => match kread_bytes w k (a_base a) (a_off a) with
            | Some bs => Some (ELit (zbytes_le_to_Z bs))
            | None => None
            end
  end.
Definition hx_bound (v : nat) (s : list (nat * expr)) : bool := existsb (fun p => CXNAT.eqbF (fst p) v) s.
Definition hx_add (vb : nat) (v : nat) (e : expr) (s : list (nat * expr)) : list (nat * expr) :=
  if (hx_bound v s || CXNAT.ltbF v vb || expr_eqb e (EVar v))%bool then s else (v, e) :: s.
Fixpoint hx_infer_regs (vb : nat) (rc rh : list expr) (s : list (nat * expr)) : list (nat * expr) :=
  match rc, rh with
  | e :: rc', EVar v :: rh' => hx_infer_regs vb rc' rh' (hx_add vb v e s)
  | _ :: rc', _ :: rh' => hx_infer_regs vb rc' rh' s
  | _, _ => s
  end.
Fixpoint hx_infer_kn (vb : nat) (k hk : list kentry) (s : list (nat * expr)) : list (nat * expr) :=
  match hk with
  | [] => s
  | KWord a w (EVar v) :: r =>
      hx_infer_kn vb k r (if (hx_bound v s || CXNAT.ltbF v vb)%bool then s
                          else match hx_cellv k a w with Some e => hx_add vb v e s | None => s end)
  | _ :: r => hx_infer_kn vb k r s
  end.
Definition hx_infer_b (vb : nat) (cs ch : acs) : list (nat * expr) :=
  hx_infer_kn vb (kn cs) (kn ch) (hx_infer_regs vb (s_regs (a_ss cs)) (s_regs (a_ss ch)) []).
Definition hx_infer (cs ch : acs) : list (nat * expr) := hx_infer_b nx0 cs ch.
Fixpoint inst_list (ch : acs) (s : list (nat * expr)) : acs :=
  match s with
  | [] => ch
  | (J, e) :: r => inst (inst_list ch r) J e
  end.
Definition entails_xb (vb : nat) (cs : acs) (ch : acs) : bool :=
  match s_log (a_ss ch) with
  | [] => let s := hx_infer_b vb cs ch in
          (CXNAT.lebF nx0 vb && forallb (fun p => CXNAT.lebF vb (fst p)) s && entails0 cs (inst_list ch s))%bool
  | _ => false
  end.
Definition entails_x (cs : acs) (ch : acs) : bool := entails_xb nx0 cs ch.
Definition lc_bnd (c : loopctx) : nat := match c with LC _ _ _ hi => hi | JC _ _ _ b _ => b end.
Definition loop_ok (cs0 : acs) (J : nat) (N : expr) (inv : acs) : option Z :=
  let lo := S J in let hi := nxt inv in
  if (fresh_ok cs0 && CXNAT.lebF (nxt cs0) J && CXNAT.ltbF J hi && fresh_ok inv
      && expr_vars_lt (nxt cs0) N
      && match s_log (a_ss inv) with [] => true | _ => false end
      && CXNAT.eqbF (length (s_regs (a_ss inv))) 32
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
  let knJ := kn_isect (kn ca) (kn cb) in   
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => CXNAT.ltbF 0 r && CXNAT.ltbF r 32) hv
      && CXNAT.eqbF (length regsJ) 32
      && CXNAT.lebF nx0 v0
      && entails_h v0 hi ca csJ && entails_h v0 hi cb csJ)%bool
  then Some csJ else None.
Fixpoint diamond_join_all (nx : nat) (joinpc : Z) (rs : list nat) (acc : acs) (ls : list acs) : option acs :=
  match ls with
  | [] => if Z.eqb (pc acc) joinpc then Some acc else None
  | x :: r => match node_diamond_join nx joinpc rs acc x with
              | Some acc' => diamond_join_all nx joinpc rs acc' r
              | None => None
              end
  end.
Definition via_ok (cs js : acs) (lo : nat) : bool :=
  (match s_log (a_ss js) with [] => true | _ => false end
   && CXNAT.eqbF (length (s_regs (a_ss js))) 32
   && CXNAT.lebF nx0 (nxt cs) && CXNAT.lebF (nxt cs) lo && CXNAT.lebF lo (nxt js))%bool.
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
  if (CXNAT.ltbF 0 r && CXNAT.ltbF r 32 && expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool
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
End WithSegs.
Lemma L_APCL_salt2 : @salt2 = @APC.salt2.
Proof. unfold salt2. reflexivity. Qed.

Lemma L_APCL_listZ_eqb : @listZ_eqb = @APC.listZ_eqb.
Proof. unfold listZ_eqb. reflexivity. Qed.

Lemma L_APCL_spiece_eqb : @spiece_eqb = @APC.spiece_eqb.
Proof. unfold spiece_eqb. rewrite ?L_APCL_listZ_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_spieces_eqb : @spieces_eqb = @APC.spieces_eqb.
Proof. unfold spieces_eqb. rewrite ?L_APCL_spiece_eqb. reflexivity. Qed.

Lemma L_APCL_shape_eqb : @shape_eqb = @APC.shape_eqb.
Proof. unfold shape_eqb. rewrite ?L_APCL_spieces_eqb, ?AX2L.L_AX2L_expr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_sleaves : @sleaves = @APC.sleaves.
Proof. unfold sleaves. reflexivity. Qed.

Lemma L_APCL_sleaves_in : @sleaves_in = @APC.sleaves_in.
Proof. unfold sleaves_in. rewrite ?L_APCL_shape_eqb. reflexivity. Qed.

Lemma L_APCL_shape_seteq : @shape_seteq = @APC.shape_seteq.
Proof. unfold shape_seteq. rewrite ?L_APCL_sleaves, ?L_APCL_sleaves_in. reflexivity. Qed.

Lemma L_APCL_mkind_eqb : @mkind_eqb = @APC.mkind_eqb.
Proof. unfold mkind_eqb. reflexivity. Qed.

Lemma L_APCL_is_tok_kind : @is_tok_kind = @APC.is_tok_kind.
Proof. unfold is_tok_kind. reflexivity. Qed.

Lemma L_APCL_is_hole : @is_hole = @APC.is_hole.
Proof. unfold is_hole. rewrite ?L_APCL_mkind_eqb. reflexivity. Qed.

Lemma L_APCL_is_fog : @is_fog = @APC.is_fog.
Proof. unfold is_fog. rewrite ?L_APCL_is_tok_kind. reflexivity. Qed.

Lemma L_APCL_no_fog : @no_fog = @APC.no_fog.
Proof. unfold no_fog. rewrite ?L_APCL_is_fog. reflexivity. Qed.

Lemma L_APCL_no_holes : @no_holes = @APC.no_holes.
Proof. unfold no_holes. rewrite ?L_APCL_is_hole. reflexivity. Qed.

Lemma L_APCL_reg : @reg = @APC.reg.
Proof. unfold reg. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kn : @kn = @APC.kn.
Proof. unfold kn. reflexivity. Qed.

Lemma L_APCL_pc : @pc = @APC.pc.
Proof. unfold pc. reflexivity. Qed.

Lemma L_APCL_nxt : @nxt = @APC.nxt.
Proof. unfold nxt. reflexivity. Qed.

Lemma L_APCL_with_ss : @with_ss = @APC.with_ss.
Proof. unfold with_ss. reflexivity. Qed.

Lemma L_APCL_mk_ss : @mk_ss = @APC.mk_ss.
Proof. unfold mk_ss. reflexivity. Qed.

Lemma L_APCL_set_reg : @set_reg = @APC.set_reg.
Proof. unfold set_reg. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_set_pc : @set_pc = @APC.set_pc.
Proof. unfold set_pc. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss. reflexivity. Qed.

Lemma L_APCL_set_kn : @set_kn = @APC.set_kn.
Proof. unfold set_kn. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss. reflexivity. Qed.

Lemma L_APCL_add_kn : @add_kn = @APC.add_kn.
Proof. unfold add_kn. rewrite ?L_APCL_kn, ?L_APCL_set_kn. reflexivity. Qed.

Lemma L_APCL_bump : @bump = @APC.bump.
Proof. unfold bump. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss. reflexivity. Qed.

Lemma L_APCL_set_regs : @set_regs = @APC.set_regs.
Proof. unfold set_regs. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss. reflexivity. Qed.

Lemma L_APCL_lit_of : @lit_of = @APC.lit_of.
Proof. unfold lit_of. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_reg_lit : @reg_lit = @APC.reg_lit.
Proof. unfold reg_lit. rewrite ?L_APCL_reg, ?L_APCL_lit_of. reflexivity. Qed.

Lemma L_APCL_eadd : @eadd = @APC.eadd.
Proof. unfold eadd. rewrite ?AX2L.L_AX2L_mkAlu. reflexivity. Qed.

Lemma L_APCL_esub : @esub = @APC.esub.
Proof. unfold esub. rewrite ?AX2L.L_AX2L_mkAlu. reflexivity. Qed.

Lemma L_APCL_escale : @escale = @APC.escale.
Proof. unfold escale. rewrite ?AX2L.L_AX2L_mkMd. reflexivity. Qed.

Lemma L_APCL_eaddz : @eaddz = @APC.eaddz.
Proof. unfold eaddz. rewrite ?AX2L.L_AX2L_mkAlu. reflexivity. Qed.

Lemma L_APCL_e_pgsp : @e_pgsp = @APC.e_pgsp.
Proof. unfold e_pgsp. rewrite ?L_APCL_eadd, ?L_APCL_escale. reflexivity. Qed.

Lemma L_APCL_pgdown : @pgdown = @APC.pgdown.
Proof. unfold pgdown. reflexivity. Qed.

Lemma L_APCL_e_spw : @e_spw = @APC.e_spw.
Proof. unfold e_spw. reflexivity. Qed.

Lemma L_APCL_sa_stk : @sa_stk = @APC.sa_stk.
Proof. unfold sa_stk. rewrite ?L_APCL_e_pgsp. reflexivity. Qed.

Lemma L_APCL_en_stk : @en_stk = @APC.en_stk.
Proof. unfold en_stk. rewrite ?L_APCL_STKSPAN. reflexivity. Qed.

Lemma L_APCL_sa_stk0 : @sa_stk0 = @APC.sa_stk0.
Proof. unfold sa_stk0. rewrite ?L_APCL_e_spw. reflexivity. Qed.

Lemma L_APCL_lit_entry : @lit_entry = @APC.lit_entry.
Proof. unfold lit_entry. rewrite ?L_APCL_is_fog, ?L_APCL_lit_of. reflexivity. Qed.

Lemma L_APCL_has_entry : @has_entry = @APC.has_entry.
Proof. unfold has_entry. rewrite ?L_APCL_lit_entry. reflexivity. Qed.

Lemma L_APCL_has_entry_k : @has_entry_k = @APC.has_entry_k.
Proof. unfold has_entry_k. rewrite ?L_APCL_mkind_eqb, ?L_APCL_lit_entry. reflexivity. Qed.

Lemma L_APCL_zone_reserved : @zone_reserved = @APC.zone_reserved.
Proof. unfold zone_reserved. rewrite ?L_APCL_has_entry. reflexivity. Qed.

Lemma L_APCL_shadows_ready : @shadows_ready = @APC.shadows_ready.
Proof. unfold shadows_ready. rewrite ?L_APCL_has_entry, ?L_APCL_has_entry_k. reflexivity. Qed.

Lemma L_APCL_sa_hull : @sa_hull = @APC.sa_hull.
Proof. unfold sa_hull. reflexivity. Qed.

Lemma L_APCL_en_hull : @en_hull = @APC.en_hull.
Proof. unfold en_hull. reflexivity. Qed.

Lemma L_APCL_sa_zone : @sa_zone = @APC.sa_zone.
Proof. unfold sa_zone. reflexivity. Qed.

Lemma L_APCL_en_zone : @en_zone = @APC.en_zone.
Proof. unfold en_zone. reflexivity. Qed.

Lemma L_APCL_expr_vars : @expr_vars = @APC.expr_vars.
Proof. unfold expr_vars. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_live_vars : @live_vars = @APC.live_vars.
Proof. unfold live_vars. rewrite ?L_APCL_kn, ?L_APCL_expr_vars. reflexivity. Qed.

Lemma L_APCL_all_live : @all_live = @APC.all_live.
Proof. unfold all_live. rewrite ?L_APCL_expr_vars, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kn_gc_entry : @kn_gc_entry = @APC.kn_gc_entry.
Proof. unfold kn_gc_entry. rewrite ?L_APCL_all_live, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_cs_gc_ref : @cs_gc_ref = @APC.cs_gc_ref.
Proof. unfold cs_gc_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_set_kn, ?L_APCL_live_vars, ?L_APCL_kn_gc_entry, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_vkey : @vkey = @APC.vkey.
Proof. unfold vkey. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_expr_vars_t : @expr_vars_t = @APC.expr_vars_t.
Proof. unfold expr_vars_t. rewrite ?L_APCL_vkey, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Lemma L_APCL_live_vars_t : @live_vars_t = @APC.live_vars_t.
Proof. unfold live_vars_t. rewrite ?L_APCL_kn, ?L_APCL_expr_vars_t. reflexivity. Qed.

Lemma L_APCL_in_live_t : @in_live_t = @APC.in_live_t.
Proof. unfold in_live_t. rewrite ?L_APCL_vkey, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Lemma L_APCL_expr_all_live_t : @expr_all_live_t = @APC.expr_all_live_t.
Proof. unfold expr_all_live_t. rewrite ?L_APCL_in_live_t, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kn_gc_entry_t : @kn_gc_entry_t = @APC.kn_gc_entry_t.
Proof. unfold kn_gc_entry_t. rewrite ?L_APCL_expr_all_live_t, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_cs_gc : @cs_gc = @APC.cs_gc.
Proof. unfold cs_gc. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_set_kn, ?L_APCL_live_vars_t, ?L_APCL_kn_gc_entry_t, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_live_agree : @live_agree = @APC.live_agree.
Proof. unfold live_agree. rewrite ?L_APCL_in_live_t, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_expr_vars_lt : @expr_vars_lt = @APC.expr_vars_lt.
Proof. unfold expr_vars_lt. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_saddr_vars_lt : @saddr_vars_lt = @APC.saddr_vars_lt.
Proof. unfold saddr_vars_lt. rewrite ?L_APCL_expr_vars_lt. reflexivity. Qed.

Lemma L_APCL_shape_vars_lt : @shape_vars_lt = @APC.shape_vars_lt.
Proof. unfold shape_vars_lt. rewrite ?L_APCL_expr_vars_lt. reflexivity. Qed.

Lemma L_APCL_kentry_vars_lt : @kentry_vars_lt = @APC.kentry_vars_lt.
Proof. unfold kentry_vars_lt. rewrite ?L_APCL_expr_vars_lt, ?L_APCL_saddr_vars_lt. reflexivity. Qed.

Lemma L_APCL_sr_vars_lt : @sr_vars_lt = @APC.sr_vars_lt.
Proof. unfold sr_vars_lt. rewrite ?L_APCL_expr_vars_lt. reflexivity. Qed.

Lemma L_APCL_kn_vars_lt : @kn_vars_lt = @APC.kn_vars_lt.
Proof. unfold kn_vars_lt. rewrite ?L_APCL_kentry_vars_lt. reflexivity. Qed.

Lemma L_APCL_pairs_vars_lt : @pairs_vars_lt = @APC.pairs_vars_lt.
Proof. unfold pairs_vars_lt. rewrite ?L_APCL_expr_vars_lt. reflexivity. Qed.

Lemma L_APCL_maps_vars_lt : @maps_vars_lt = @APC.maps_vars_lt.
Proof. unfold maps_vars_lt. rewrite ?L_APCL_expr_vars_lt. reflexivity. Qed.

Lemma L_APCL_fd_vars_lt : @fd_vars_lt = @APC.fd_vars_lt.
Proof. unfold fd_vars_lt. rewrite ?L_APCL_expr_vars_lt. reflexivity. Qed.

Lemma L_APCL_fresh_ok : @fresh_ok = @APC.fresh_ok.
Proof. unfold fresh_ok. rewrite ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_expr_vars_lt, ?L_APCL_sr_vars_lt, ?L_APCL_kn_vars_lt, ?L_APCL_pairs_vars_lt, ?L_APCL_maps_vars_lt, ?L_APCL_fd_vars_lt, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_run_block_ref : @run_block_ref = @APC.run_block_ref.
Proof. unfold run_block_ref. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_fresh_ok, ?AX2L.L_AX2L_carry, ?AX2L.L_AX2L_sym_execTX. reflexivity. Qed.

Lemma L_APCL_run_block : @run_block = @APC.run_block.
Proof. unfold run_block. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_fresh_ok, ?AX2BL.L_AX2BL_carryK, ?AX2L.L_AX2L_facts_of, ?AX2BL.L_AX2BL_mk_kix, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_sym_execTXBI. reflexivity. Qed.

Lemma L_APCL_run_block_gc : @run_block_gc = @APC.run_block_gc.
Proof. unfold run_block_gc. rewrite ?L_APCL_cs_gc, ?L_APCL_run_block. reflexivity. Qed.

Lemma L_APCL_kentry_eqb : @kentry_eqb = @APC.kentry_eqb.
Proof. unfold kentry_eqb. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_saddr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_amap_eqb : @amap_eqb = @APC.amap_eqb.
Proof. unfold amap_eqb. rewrite ?L_APCL_mkind_eqb, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_list_eqb : @list_eqb = @APC.list_eqb.
Proof. unfold list_eqb. reflexivity. Qed.

Lemma L_APCL_pair_eqb : @pair_eqb = @APC.pair_eqb.
Proof. unfold pair_eqb. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_afd_eqb : @afd_eqb = @APC.afd_eqb.
Proof. unfold afd_eqb. rewrite ?AX2L.L_AX2L_expr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_zkey : @zkey = @APC.zkey.
Proof. unfold zkey. reflexivity. Qed.

Lemma L_APCL_lkey : @lkey = @APC.lkey.
Proof. unfold lkey. rewrite ?L_APCL_zkey. reflexivity. Qed.

Lemma L_APCL_kkeyZ : @kkeyZ = @APC.kkeyZ.
Proof. unfold kkeyZ. rewrite ?L_APCL_zkey, ?L_APCL_lkey. reflexivity. Qed.

Lemma L_APCL_kkey : @kkey = @APC.kkey.
Proof. unfold kkey. rewrite ?L_APCL_kkeyZ. reflexivity. Qed.

Lemma L_APCL_kset : @kset = @APC.kset.
Proof. unfold kset. reflexivity. Qed.

Lemma L_APCL_kset_bucket : @kset_bucket = @APC.kset_bucket.
Proof. unfold kset_bucket. rewrite ?L_APCL_kset, ?AX2L.L_AX2L_pt_get. reflexivity. Qed.

Lemma L_APCL_kset_add : @kset_add = @APC.kset_add.
Proof. unfold kset_add. rewrite ?L_APCL_kkey, ?L_APCL_kset, ?L_APCL_kset_bucket, ?AX2L.L_AX2L_pt_set. reflexivity. Qed.

Lemma L_APCL_kset_of : @kset_of = @APC.kset_of.
Proof. unfold kset_of. rewrite ?L_APCL_kset, ?L_APCL_kset_add. reflexivity. Qed.

Lemma L_APCL_kset_mem : @kset_mem = @APC.kset_mem.
Proof. unfold kset_mem. rewrite ?L_APCL_kentry_eqb, ?L_APCL_kkey, ?L_APCL_kset, ?L_APCL_kset_bucket. reflexivity. Qed.

Lemma L_APCL_kn_isect : @kn_isect = @APC.kn_isect.
Proof. unfold kn_isect. rewrite ?L_APCL_kset_of, ?L_APCL_kset_mem. reflexivity. Qed.

Lemma L_APCL_kentry_apart_b : @kentry_apart_b = @APC.kentry_apart_b.
Proof. unfold kentry_apart_b. rewrite ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kentry_apart_bB : @kentry_apart_bB = @APC.kentry_apart_bB.
Proof. unfold kentry_apart_bB. rewrite ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kentry_apart_bp : @kentry_apart_bp = @APC.kentry_apart_bp.
Proof. unfold kentry_apart_bp. rewrite ?AX2L.L_AX2L_ranges_apart_p, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kentry_apart_bpB : @kentry_apart_bpB = @APC.kentry_apart_bpB.
Proof. unfold kentry_apart_bpB. rewrite ?AX2BL.L_AX2BL_ranges_apart_pBF, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kimg_b : @kimg_b = @APC.kimg_b.
Proof. unfold kimg_b. reflexivity. Qed.

Lemma L_APCL_kn_unfill : @kn_unfill = @APC.kn_unfill.
Proof. unfold kn_unfill. rewrite ?L_APCL_kentry_apart_bp, ?L_APCL_kimg_b, ?AX2L.L_AX2L_mk_sprep. reflexivity. Qed.

Lemma L_APCL_kn_unfillB : @kn_unfillB = @APC.kn_unfillB.
Proof. unfold kn_unfillB. rewrite ?L_APCL_kentry_apart_bpB, ?L_APCL_kimg_b, ?AX2BL.L_AX2BL_mk_sprepB. reflexivity. Qed.

Lemma L_APCL_kn_unfillM : @kn_unfillM = @APC.kn_unfillM.
Proof. unfold kn_unfillM. rewrite ?L_APCL_kn_unfillB, ?AX2BL.L_AX2BL_mkbc. reflexivity. Qed.

Lemma L_APCL_kwr_b : @kwr_b = @APC.kwr_b.
Proof. unfold kwr_b. reflexivity. Qed.

Lemma L_APCL_havoc1 : @havoc1 = @APC.havoc1.
Proof. unfold havoc1. rewrite ?L_APCL_kentry_apart_b, ?L_APCL_kwr_b, ?AX2L.L_AX2L_kfill_cut, ?AX2L.L_AX2L_kunk_cut, ?AX2L.L_AX2L_kzero_cut. reflexivity. Qed.

Lemma L_APCL_havoc1B : @havoc1B = @APC.havoc1B.
Proof. unfold havoc1B. rewrite ?L_APCL_kentry_apart_bB, ?L_APCL_kwr_b, ?AX2BL.L_AX2BL_kfill_cutB, ?AX2BL.L_AX2BL_kunk_cutB, ?AX2BL.L_AX2BL_kzero_cutB. reflexivity. Qed.

Lemma L_APCL_havoc1p : @havoc1p = @APC.havoc1p.
Proof. unfold havoc1p. rewrite ?L_APCL_kentry_apart_bp, ?L_APCL_kwr_b, ?AX2L.L_AX2L_kfill_cut, ?AX2L.L_AX2L_kunk_cut, ?AX2L.L_AX2L_kzero_cut. reflexivity. Qed.

Lemma L_APCL_havoc1pB : @havoc1pB = @APC.havoc1pB.
Proof. unfold havoc1pB. rewrite ?L_APCL_kentry_apart_bpB, ?L_APCL_kwr_b, ?AX2BL.L_AX2BL_kfill_cutB, ?AX2BL.L_AX2BL_kunk_cutB, ?AX2BL.L_AX2BL_kzero_cutB. reflexivity. Qed.

Lemma L_APCL_kn_havoc : @kn_havoc = @APC.kn_havoc.
Proof. unfold kn_havoc. rewrite ?L_APCL_havoc1p, ?AX2L.L_AX2L_mk_sprep. reflexivity. Qed.

Lemma L_APCL_kn_havocB : @kn_havocB = @APC.kn_havocB.
Proof. unfold kn_havocB. rewrite ?L_APCL_havoc1pB, ?AX2BL.L_AX2BL_mk_sprepB. reflexivity. Qed.

Lemma L_APCL_kn_havocM : @kn_havocM = @APC.kn_havocM.
Proof. unfold kn_havocM. rewrite ?L_APCL_kn_havocB, ?AX2BL.L_AX2BL_mkbc. reflexivity. Qed.

Lemma L_APCL_kwr_cut : @kwr_cut = @APC.kwr_cut.
Proof. unfold kwr_cut. rewrite ?AX2L.L_AX2L_kcut. reflexivity. Qed.

Lemma L_APCL_kwr_cutB : @kwr_cutB = @APC.kwr_cutB.
Proof. unfold kwr_cutB. rewrite ?AX2BL.L_AX2BL_kcutB. reflexivity. Qed.

Lemma L_APCL_cutout1 : @cutout1 = @APC.cutout1.
Proof. unfold cutout1. rewrite ?L_APCL_kentry_apart_b, ?L_APCL_kwr_cut, ?AX2L.L_AX2L_kfill_cut, ?AX2L.L_AX2L_kunk_cut, ?AX2L.L_AX2L_kzero_cut. reflexivity. Qed.

Lemma L_APCL_cutout1B : @cutout1B = @APC.cutout1B.
Proof. unfold cutout1B. rewrite ?L_APCL_kentry_apart_bB, ?L_APCL_kwr_cutB, ?AX2BL.L_AX2BL_kfill_cutB, ?AX2BL.L_AX2BL_kunk_cutB, ?AX2BL.L_AX2BL_kzero_cutB. reflexivity. Qed.

Lemma L_APCL_cutout1p : @cutout1p = @APC.cutout1p.
Proof. unfold cutout1p. rewrite ?L_APCL_kentry_apart_bp, ?L_APCL_kwr_cut, ?AX2L.L_AX2L_kfill_cut, ?AX2L.L_AX2L_kunk_cut, ?AX2L.L_AX2L_kzero_cut. reflexivity. Qed.

Lemma L_APCL_cutout1pB : @cutout1pB = @APC.cutout1pB.
Proof. unfold cutout1pB. rewrite ?L_APCL_kentry_apart_bpB, ?L_APCL_kwr_cutB, ?AX2BL.L_AX2BL_kfill_cutB, ?AX2BL.L_AX2BL_kunk_cutB, ?AX2BL.L_AX2BL_kzero_cutB. reflexivity. Qed.

Lemma L_APCL_kn_cutout : @kn_cutout = @APC.kn_cutout.
Proof. unfold kn_cutout. rewrite ?L_APCL_cutout1p, ?AX2L.L_AX2L_mk_sprep. reflexivity. Qed.

Lemma L_APCL_kn_cutoutB : @kn_cutoutB = @APC.kn_cutoutB.
Proof. unfold kn_cutoutB. rewrite ?L_APCL_cutout1pB, ?AX2BL.L_AX2BL_mk_sprepB. reflexivity. Qed.

Lemma L_APCL_kn_cutoutM : @kn_cutoutM = @APC.kn_cutoutM.
Proof. unfold kn_cutoutM. rewrite ?L_APCL_kn_cutoutB, ?AX2BL.L_AX2BL_mkbc. reflexivity. Qed.

Lemma L_APCL_kn_keep : @kn_keep = @APC.kn_keep.
Proof. unfold kn_keep. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_gcdisj_keep : @gcdisj_keep = @APC.gcdisj_keep.
Proof. unfold gcdisj_keep. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_ledger_bases : @ledger_bases = @APC.ledger_bases.
Proof. unfold ledger_bases. rewrite ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_kn_gcdisj : @kn_gcdisj = @APC.kn_gcdisj.
Proof. unfold kn_gcdisj. rewrite ?L_APCL_kn, ?L_APCL_gcdisj_keep, ?L_APCL_ledger_bases, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_evars_cnt : @evars_cnt = @APC.evars_cnt.
Proof. unfold evars_cnt. rewrite ?AX2L.L_AX2L_pt_get, ?AX2L.L_AX2L_pt_set, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kvars_cnt : @kvars_cnt = @APC.kvars_cnt.
Proof. unfold kvars_cnt. rewrite ?L_APCL_evars_cnt. reflexivity. Qed.

Lemma L_APCL_pvars_cnt : @pvars_cnt = @APC.pvars_cnt.
Proof. unfold pvars_cnt. rewrite ?L_APCL_evars_cnt. reflexivity. Qed.

Lemma L_APCL_csvars_cnt : @csvars_cnt = @APC.csvars_cnt.
Proof. unfold csvars_cnt. rewrite ?L_APCL_kn, ?L_APCL_evars_cnt, ?L_APCL_kvars_cnt, ?L_APCL_pvars_cnt. reflexivity. Qed.

Lemma L_APCL_var_lonely : @var_lonely = @APC.var_lonely.
Proof. unfold var_lonely. rewrite ?AX2L.L_AX2L_pt_get, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_gcrange_keep : @gcrange_keep = @APC.gcrange_keep.
Proof. unfold gcrange_keep. rewrite ?L_APCL_var_lonely, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kn_gcrange : @kn_gcrange = @APC.kn_gcrange.
Proof. unfold kn_gcrange. rewrite ?L_APCL_kn, ?L_APCL_csvars_cnt, ?L_APCL_gcrange_keep. reflexivity. Qed.

Lemma L_APCL_kimg_cut1 : @kimg_cut1 = @APC.kimg_cut1.
Proof. unfold kimg_cut1. reflexivity. Qed.

Lemma L_APCL_kimg_cut : @kimg_cut = @APC.kimg_cut.
Proof. unfold kimg_cut. rewrite ?L_APCL_kimg_cut1. reflexivity. Qed.

Lemma L_APCL_kimg_clip : @kimg_clip = @APC.kimg_clip.
Proof. unfold kimg_clip. reflexivity. Qed.

Lemma L_APCL_kreadZ : @kreadZ = @APC.kreadZ.
Proof. unfold kreadZ. rewrite ?AX2L.L_AX2L_know_lookup, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kreadZB : @kreadZB = @APC.kreadZB.
Proof. unfold kreadZB. rewrite ?AX2BL.L_AX2BL_know_lookupB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kread8e : @kread8e = @APC.kread8e.
Proof. unfold kread8e. rewrite ?AX2L.L_AX2L_know_lookup. reflexivity. Qed.

Lemma L_APCL_kread8eB : @kread8eB = @APC.kread8eB.
Proof. unfold kread8eB. rewrite ?AX2BL.L_AX2BL_know_lookupB. reflexivity. Qed.

Lemma L_APCL_kwritable : @kwritable = @APC.kwritable.
Proof. unfold kwritable. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xinside, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_kwritableB : @kwritableB = @APC.kwritableB.
Proof. unfold kwritableB. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xinsideB, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_APCL_kwritable_x : @kwritable_x = @APC.kwritable_x.
Proof. unfold kwritable_x. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xinside, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_kwritable_xB : @kwritable_xB = @APC.kwritable_xB.
Proof. unfold kwritable_xB. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xinsideB, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_APCL_kzero_x : @kzero_x = @APC.kzero_x.
Proof. unfold kzero_x. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xinside, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_kzero_xB : @kzero_xB = @APC.kzero_xB.
Proof. unfold kzero_xB. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xinsideB, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_APCL_kfill_x : @kfill_x = @APC.kfill_x.
Proof. unfold kfill_x. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xinside, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_kfill_xB : @kfill_xB = @APC.kfill_xB.
Proof. unfold kfill_xB. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xinsideB, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_APCL_off_image_x : @off_image_x = @APC.off_image_x.
Proof. unfold off_image_x. rewrite ?AX2L.L_AX2L_ranges_apart_x. reflexivity. Qed.

Lemma L_APCL_off_image_xB : @off_image_xB = @APC.off_image_xB.
Proof. unfold off_image_xB. rewrite ?AX2BL.L_AX2BL_ranges_apart_xB. reflexivity. Qed.

Lemma L_APCL_flat_x : @flat_x = @APC.flat_x.
Proof. unfold flat_x. rewrite ?AX2L.L_AX2L_base_range, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_flat_xB : @flat_xB = @APC.flat_xB.
Proof. unfold flat_xB. rewrite ?AX2BL.L_AX2BL_base_rangeB, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_APCL_ehi : @ehi = @APC.ehi.
Proof. unfold ehi. rewrite ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_APCL_elo : @elo = @APC.elo.
Proof. unfold elo. rewrite ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_len_eqb : @len_eqb = @APC.len_eqb.
Proof. unfold len_eqb. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_lin_ge0. reflexivity. Qed.

Lemma L_APCL_len_eqbB : @len_eqbB = @APC.len_eqbB.
Proof. unfold len_eqbB. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2BL.L_AX2BL_lin_ge0B. reflexivity. Qed.

Lemma L_APCL_lit_diff : @lit_diff = @APC.lit_diff.
Proof. unfold lit_diff. rewrite ?L_APCL_esub, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_page_aligned : @page_aligned = @APC.page_aligned.
Proof. unfold page_aligned. rewrite ?AX2L.L_AX2L_ealign. reflexivity. Qed.

Lemma L_APCL_page_alignedB : @page_alignedB = @APC.page_alignedB.
Proof. unfold page_alignedB. rewrite ?AX2BL.L_AX2BL_ealignB. reflexivity. Qed.

Lemma L_APCL_kn_contra : @kn_contra = @APC.kn_contra.
Proof. unfold kn_contra. rewrite ?AX2L.L_AX2L_erange, ?AX2L.L_AX2L_lin_of, ?AX2L.L_AX2L_lin_range, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_caller_saved : @caller_saved = @APC.caller_saved.
Proof. unfold caller_saved. reflexivity. Qed.

Lemma L_APCL_sr_fresh : @sr_fresh = @APC.sr_fresh.
Proof. unfold sr_fresh. rewrite ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_NCS : @NCS = @APC.NCS.
Proof. unfold NCS. reflexivity. Qed.

Lemma L_APCL_ret_lit : @ret_lit = @APC.ret_lit.
Proof. unfold ret_lit. rewrite ?L_APCL_reg, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_after_call : @after_call = @APC.after_call.
Proof. unfold after_call. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_expr_vars_lt, ?L_APCL_kn_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_caller_saved, ?L_APCL_sr_fresh, ?L_APCL_NCS, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_after_call2 : @after_call2 = @APC.after_call2.
Proof. unfold after_call2. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_expr_vars_lt, ?L_APCL_kn_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_caller_saved, ?L_APCL_sr_fresh, ?L_APCL_NCS, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_page_up : @page_up = @APC.page_up.
Proof. unfold page_up. reflexivity. Qed.

Lemma L_APCL_is_ecall_at : @is_ecall_at = @APC.is_ecall_at.
Proof. unfold is_ecall_at. rewrite ?L_APCL_pc, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_xlo1 : @xlo1 = @APC.xlo1.
Proof. unfold xlo1. rewrite ?AX2L.L_AX2L_erange, ?AX2L.L_AX2L_lin_brange, ?AX2L.L_AX2L_lin_srange, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Lemma L_APCL_xlo1B : @xlo1B = @APC.xlo1B.
Proof. unfold xlo1B. rewrite ?AX2BL.L_AX2BL_erangeB, ?AX2BL.L_AX2BL_lin_brangeB, ?AX2BL.L_AX2BL_lin_srangeB, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Lemma L_APCL_xhi1 : @xhi1 = @APC.xhi1.
Proof. unfold xhi1. rewrite ?AX2L.L_AX2L_erange, ?AX2L.L_AX2L_lin_brange, ?AX2L.L_AX2L_lin_srange, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Lemma L_APCL_xhi1B : @xhi1B = @APC.xhi1B.
Proof. unfold xhi1B. rewrite ?AX2BL.L_AX2BL_erangeB, ?AX2BL.L_AX2BL_lin_brangeB, ?AX2BL.L_AX2BL_lin_srangeB, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Lemma L_APCL_deand : @deand = @APC.deand.
Proof. unfold deand. rewrite ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_xb2 : @xb2 = @APC.xb2.
Proof. unfold xb2. rewrite ?L_APCL_xlo1, ?L_APCL_xhi1, ?L_APCL_deand, ?AX2L.L_AX2L_deand. reflexivity. Qed.

Lemma L_APCL_xb2B : @xb2B = @APC.xb2B.
Proof. unfold xb2B. rewrite ?L_APCL_xlo1B, ?L_APCL_xhi1B, ?L_APCL_deand, ?AX2L.L_AX2L_deand. reflexivity. Qed.

Lemma L_APCL_xlo2 : @xlo2 = @APC.xlo2.
Proof. unfold xlo2. rewrite ?L_APCL_xb2. reflexivity. Qed.

Lemma L_APCL_xlo2B : @xlo2B = @APC.xlo2B.
Proof. unfold xlo2B. rewrite ?L_APCL_xb2B. reflexivity. Qed.

Lemma L_APCL_xhi2 : @xhi2 = @APC.xhi2.
Proof. unfold xhi2. rewrite ?L_APCL_xb2. reflexivity. Qed.

Lemma L_APCL_xhi2B : @xhi2B = @APC.xhi2B.
Proof. unfold xhi2B. rewrite ?L_APCL_xb2B. reflexivity. Qed.

Lemma L_APCL_fact_ok : @fact_ok = @APC.fact_ok.
Proof. unfold fact_ok. rewrite ?L_APCL_xlo2, ?L_APCL_xhi2, ?AX2L.L_AX2L_ealign, ?AX2L.L_AX2L_ranges_apart_x. reflexivity. Qed.

Lemma L_APCL_kread_bytes : @kread_bytes = @APC.kread_bytes.
Proof. unfold kread_bytes. rewrite ?L_APCL_kreadZ. reflexivity. Qed.

Lemma L_APCL_kread_bytesB : @kread_bytesB = @APC.kread_bytesB.
Proof. unfold kread_bytesB. rewrite ?L_APCL_kreadZB. reflexivity. Qed.

Lemma L_APCL_node_join : @node_join = @APC.node_join.
Proof. unfold node_join. rewrite ?L_APCL_kn, ?L_APCL_add_kn, ?L_APCL_flat_x, ?L_APCL_kread_bytes, ?AX2L.L_AX2L_zbytes_le_to_Z, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_drop_ixs : @drop_ixs = @APC.drop_ixs.
Proof. unfold drop_ixs. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_residue_fact : @residue_fact = @APC.residue_fact.
Proof. unfold residue_fact. rewrite ?L_APCL_esub, ?L_APCL_xlo1, ?L_APCL_xhi1, ?L_APCL_deand, ?AX2L.L_AX2L_deand. reflexivity. Qed.

Lemma L_APCL_mask_fact1 : @mask_fact1 = @APC.mask_fact1.
Proof. unfold mask_fact1. rewrite ?L_APCL_esub, ?L_APCL_xhi1. reflexivity. Qed.

Lemma L_APCL_mask_fact : @mask_fact = @APC.mask_fact.
Proof. unfold mask_fact. rewrite ?L_APCL_mask_fact1. reflexivity. Qed.

Lemma L_APCL_node_fresh : @node_fresh = @APC.node_fresh.
Proof. unfold node_fresh. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_set_reg, ?L_APCL_add_kn, ?L_APCL_bump, ?L_APCL_eadd, ?L_APCL_esub, ?L_APCL_escale, ?L_APCL_expr_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_xlo2, ?L_APCL_xhi2, ?L_APCL_residue_fact, ?L_APCL_mask_fact, ?AX2L.L_AX2L_ealign, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_node_joinx : @node_joinx = @APC.node_joinx.
Proof. unfold node_joinx. rewrite ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_add_kn, ?L_APCL_bump, ?L_APCL_expr_vars_lt, ?L_APCL_fresh_ok, ?AX2L.L_AX2L_kn_readable, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_node_droprange : @node_droprange = @APC.node_droprange.
Proof. unfold node_droprange. rewrite ?L_APCL_kn, ?L_APCL_set_kn, ?L_APCL_kn_havoc, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_node_bump : @node_bump = @APC.node_bump.
Proof. unfold node_bump. rewrite ?L_APCL_nxt, ?L_APCL_bump, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_node_havoc : @node_havoc = @APC.node_havoc.
Proof. unfold node_havoc. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_fresh_ok, ?L_APCL_sr_fresh, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_esize : @esize = @APC.esize.
Proof. unfold esize. reflexivity. Qed.

Lemma L_APCL_bigb : @bigb = @APC.bigb.
Proof. unfold bigb. rewrite ?L_APCL_esize, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kn_bigsubst : @kn_bigsubst = @APC.kn_bigsubst.
Proof. unfold kn_bigsubst. rewrite ?L_APCL_bigb. reflexivity. Qed.

Lemma L_APCL_node_havocbig : @node_havocbig = @APC.node_havocbig.
Proof. unfold node_havocbig. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_fresh_ok, ?L_APCL_node_havoc, ?L_APCL_bigb, ?L_APCL_kn_bigsubst. reflexivity. Qed.

Lemma L_APCL_xinside_joint : @xinside_joint = @APC.xinside_joint.
Proof. unfold xinside_joint. rewrite ?L_APCL_kn, ?AX2L.L_AX2L_base_range, ?AX2L.L_AX2L_end_hi, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_xinside_jointB : @xinside_jointB = @APC.xinside_jointB.
Proof. unfold xinside_jointB. rewrite ?AX2BL.L_AX2BL_base_rangeB, ?AX2BL.L_AX2BL_end_hiB, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_APCL_xinsideJ : @xinsideJ = @APC.xinsideJ.
Proof. unfold xinsideJ. rewrite ?L_APCL_kn, ?L_APCL_xinside_joint, ?AX2L.L_AX2L_xinside. reflexivity. Qed.

Lemma L_APCL_xinsideJB : @xinsideJB = @APC.xinsideJB.
Proof. unfold xinsideJB. rewrite ?L_APCL_xinside_jointB, ?AX2BL.L_AX2BL_xinsideB. reflexivity. Qed.

Lemma L_APCL_find_containing : @find_containing = @APC.find_containing.
Proof. unfold find_containing. rewrite ?L_APCL_mkind_eqb, ?L_APCL_is_fog, ?L_APCL_xinsideJ. reflexivity. Qed.

Lemma L_APCL_find_containingB : @find_containingB = @APC.find_containingB.
Proof. unfold find_containingB. rewrite ?L_APCL_mkind_eqb, ?L_APCL_is_fog, ?L_APCL_xinsideJB. reflexivity. Qed.

Lemma L_APCL_shadow_of : @shadow_of = @APC.shadow_of.
Proof. unfold shadow_of. rewrite ?L_APCL_eadd, ?AX2L.L_AX2L_mkSrl, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_shadow_ofB : @shadow_ofB = @APC.shadow_ofB.
Proof. unfold shadow_ofB. rewrite ?L_APCL_eadd, ?AX2BL.L_AX2BL_mkSrlB, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_TASK : @TASK = @APC.TASK.
Proof. unfold TASK. reflexivity. Qed.

Lemma L_APCL_sh_covered : @sh_covered = @APC.sh_covered.
Proof. unfold sh_covered. rewrite ?L_APCL_shadows_ready, ?L_APCL_sa_zone, ?L_APCL_en_zone, ?L_APCL_flat_x, ?L_APCL_TASK, ?AX2L.L_AX2L_base_range, ?AX2L.L_AX2L_end_hi, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_APCL_sh_coveredB : @sh_coveredB = @APC.sh_coveredB.
Proof. unfold sh_coveredB. rewrite ?L_APCL_shadows_ready, ?L_APCL_sa_zone, ?L_APCL_en_zone, ?L_APCL_flat_xB, ?L_APCL_TASK, ?AX2BL.L_AX2BL_base_rangeB, ?AX2BL.L_AX2BL_end_hiB, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2BL.L_AX2BL_xhiB. reflexivity. Qed.

Lemma L_APCL_shadow_facts : @shadow_facts = @APC.shadow_facts.
Proof. unfold shadow_facts. rewrite ?L_APCL_find_containing, ?L_APCL_shadow_of, ?L_APCL_sh_covered, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_shadow_factsB : @shadow_factsB = @APC.shadow_factsB.
Proof. unfold shadow_factsB. rewrite ?L_APCL_find_containingB, ?L_APCL_shadow_ofB, ?L_APCL_sh_coveredB, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_vis_cost : @vis_cost = @APC.vis_cost.
Proof. unfold vis_cost. reflexivity. Qed.

Lemma L_APCL_vis_add_ref : @vis_add_ref = @APC.vis_add_ref.
Proof. unfold vis_add_ref. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_expr_vars_lt, ?L_APCL_flat_x, ?L_APCL_shadow_of, ?L_APCL_shadow_facts, ?L_APCL_vis_cost, ?AX2L.L_AX2L_ealign, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_APCL_vis_add : @vis_add = @APC.vis_add.
Proof. unfold vis_add. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_expr_vars_lt, ?L_APCL_flat_xB, ?L_APCL_shadow_ofB, ?L_APCL_shadow_factsB, ?L_APCL_vis_cost, ?AX2BL.L_AX2BL_ealignB, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_split_lit, ?AX2BL.L_AX2BL_xhiB. reflexivity. Qed.

Lemma L_APCL_find_disj : @find_disj = @APC.find_disj.
Proof. unfold find_disj. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_disj_side_fact : @disj_side_fact = @APC.disj_side_fact.
Proof. unfold disj_side_fact. rewrite ?L_APCL_esub, ?L_APCL_eaddz, ?L_APCL_xlo2, ?AX2L.L_AX2L_base_range. reflexivity. Qed.

Lemma L_APCL_node_casedisj : @node_casedisj = @APC.node_casedisj.
Proof. unfold node_casedisj. rewrite ?L_APCL_kn, ?L_APCL_add_kn, ?L_APCL_flat_x, ?L_APCL_find_disj, ?L_APCL_disj_side_fact. reflexivity. Qed.

Lemma L_APCL_find_zone_disj : @find_zone_disj = @APC.find_zone_disj.
Proof. unfold find_zone_disj. rewrite ?L_APCL_en_zone, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_node_band_at : @node_band_at = @APC.node_band_at.
Proof. unfold node_band_at. rewrite ?L_APCL_kn, ?L_APCL_add_kn, ?L_APCL_escale, ?L_APCL_flat_x, ?L_APCL_xlo2, ?L_APCL_xhi2, ?L_APCL_find_zone_disj, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_band_var : @band_var = @APC.band_var.
Proof. unfold band_var. rewrite ?L_APCL_reg, ?AX2L.L_AX2L_lin_of, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_node_band : @node_band = @APC.node_band.
Proof. unfold node_band. rewrite ?L_APCL_node_band_at, ?L_APCL_band_var. reflexivity. Qed.

Lemma L_APCL_node_shdisj_ref : @node_shdisj_ref = @APC.node_shdisj_ref.
Proof. unfold node_shdisj_ref. rewrite ?L_APCL_kn, ?L_APCL_add_kn, ?L_APCL_flat_x, ?L_APCL_shadow_of, ?AX2L.L_AX2L_ealign, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_node_shdisj : @node_shdisj = @APC.node_shdisj.
Proof. unfold node_shdisj. rewrite ?L_APCL_kn, ?L_APCL_add_kn, ?L_APCL_flat_xB, ?L_APCL_shadow_ofB, ?AX2BL.L_AX2BL_ealignB, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_mmap_len_ref : @mmap_len_ref = @APC.mmap_len_ref.
Proof. unfold mmap_len_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_reg_lit, ?L_APCL_page_up, ?AX2L.L_AX2L_ealign, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_mmap_len : @mmap_len = @APC.mmap_len.
Proof. unfold mmap_len. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_reg_lit, ?L_APCL_page_up, ?AX2BL.L_AX2BL_ealignB, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xloB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_inside_maps : @inside_maps = @APC.inside_maps.
Proof. unfold inside_maps. rewrite ?L_APCL_is_fog, ?AX2L.L_AX2L_xinside. reflexivity. Qed.

Lemma L_APCL_inside_mapsB : @inside_mapsB = @APC.inside_mapsB.
Proof. unfold inside_mapsB. rewrite ?L_APCL_is_fog, ?AX2BL.L_AX2BL_xinsideB. reflexivity. Qed.

Lemma L_APCL_safe_range : @safe_range = @APC.safe_range.
Proof. unfold safe_range. rewrite ?L_APCL_sa_stk, ?L_APCL_en_stk, ?L_APCL_zone_reserved, ?L_APCL_sa_zone, ?L_APCL_en_zone, ?L_APCL_inside_maps, ?AX2L.L_AX2L_base_range, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xinside. reflexivity. Qed.

Lemma L_APCL_safe_rangeB : @safe_rangeB = @APC.safe_rangeB.
Proof. unfold safe_rangeB. rewrite ?L_APCL_sa_stk, ?L_APCL_en_stk, ?L_APCL_zone_reserved, ?L_APCL_sa_zone, ?L_APCL_en_zone, ?L_APCL_inside_mapsB, ?AX2BL.L_AX2BL_base_rangeB, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xinsideB. reflexivity. Qed.

Lemma L_APCL_grant_keep_b : @grant_keep_b = @APC.grant_keep_b.
Proof. unfold grant_keep_b. rewrite ?L_APCL_safe_range, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_grant_keep_bB : @grant_keep_bB = @APC.grant_keep_bB.
Proof. unfold grant_keep_bB. rewrite ?L_APCL_safe_rangeB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kn_grant_filter : @kn_grant_filter = @APC.kn_grant_filter.
Proof. unfold kn_grant_filter. rewrite ?L_APCL_kimg_clip, ?L_APCL_grant_keep_b. reflexivity. Qed.

Lemma L_APCL_kn_grant_filterB : @kn_grant_filterB = @APC.kn_grant_filterB.
Proof. unfold kn_grant_filterB. rewrite ?L_APCL_kimg_clip, ?L_APCL_grant_keep_bB. reflexivity. Qed.

Lemma L_APCL_safe_rangeBF : @safe_rangeBF = @APC.safe_rangeBF.
Proof. unfold safe_rangeBF. rewrite ?L_APCL_sa_stk, ?L_APCL_en_stk, ?L_APCL_zone_reserved, ?L_APCL_sa_zone, ?L_APCL_en_zone, ?L_APCL_inside_mapsB, ?AX2BL.L_AX2BL_base_rangeB, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xinsideB. reflexivity. Qed.

Lemma L_APCL_grant_keep_bBF : @grant_keep_bBF = @APC.grant_keep_bBF.
Proof. unfold grant_keep_bBF. rewrite ?L_APCL_safe_rangeBF, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kn_grant_filterF : @kn_grant_filterF = @APC.kn_grant_filterF.
Proof. unfold kn_grant_filterF. rewrite ?L_APCL_kimg_clip, ?L_APCL_grant_keep_bBF, ?AX2BL.L_AX2BL_mkbc. reflexivity. Qed.

Lemma L_APCL_gap_ok : @gap_ok = @APC.gap_ok.
Proof. unfold gap_ok. rewrite ?L_APCL_CEIL, ?L_APCL_FLOOR. reflexivity. Qed.

Lemma L_APCL_budget_ok : @budget_ok = @APC.budget_ok.
Proof. unfold budget_ok. reflexivity. Qed.

Lemma L_APCL_kdisj_maps : @kdisj_maps = @APC.kdisj_maps.
Proof. unfold kdisj_maps. rewrite ?L_APCL_is_fog. reflexivity. Qed.

Lemma L_APCL_kdisj_new : @kdisj_new = @APC.kdisj_new.
Proof. unfold kdisj_new. rewrite ?L_APCL_sa_stk, ?L_APCL_en_stk, ?L_APCL_sa_stk0, ?L_APCL_zone_reserved, ?L_APCL_sa_hull, ?L_APCL_en_hull, ?L_APCL_sa_zone, ?L_APCL_en_zone, ?L_APCL_kdisj_maps. reflexivity. Qed.

Lemma L_APCL_with_maps0 : @with_maps0 = @APC.with_maps0.
Proof. unfold with_maps0. reflexivity. Qed.

Lemma L_APCL_add_entry : @add_entry = @APC.add_entry.
Proof. unfold add_entry. rewrite ?L_APCL_pc, ?L_APCL_mk_ss. reflexivity. Qed.

Lemma L_APCL_null_kend : @null_kend = @APC.null_kend.
Proof. unfold null_kend. rewrite ?L_APCL_TOPMAX, ?L_APCL_eadd. reflexivity. Qed.

Lemma L_APCL_null_lo : @null_lo = @APC.null_lo.
Proof. unfold null_lo. rewrite ?L_APCL_zone_reserved. reflexivity. Qed.

Lemma L_APCL_mmap_null : @mmap_null = @APC.mmap_null.
Proof. unfold mmap_null. rewrite ?L_APCL_TOPMAX, ?L_APCL_no_holes, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_escale, ?L_APCL_expr_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_vis_add, ?L_APCL_mmap_len, ?L_APCL_kn_grant_filter, ?L_APCL_gap_ok, ?L_APCL_budget_ok, ?L_APCL_kdisj_new, ?L_APCL_add_entry, ?L_APCL_null_kend, ?L_APCL_null_lo, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_fixed_args : @fixed_args = @APC.fixed_args.
Proof. unfold fixed_args. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_flat_x, ?L_APCL_page_aligned, ?L_APCL_mmap_len, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_fixed_args_base : @fixed_args_base = @APC.fixed_args_base.
Proof. unfold fixed_args_base. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_flat_x, ?L_APCL_page_aligned, ?L_APCL_mmap_len, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_same_val : @same_val = @APC.same_val.
Proof. unfold same_val. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_lin_ge0. reflexivity. Qed.

Lemma L_APCL_find_hole : @find_hole = @APC.find_hole.
Proof. unfold find_hole. rewrite ?L_APCL_is_hole, ?L_APCL_same_val. reflexivity. Qed.

Lemma L_APCL_unhole : @unhole = @APC.unhole.
Proof. unfold unhole. rewrite ?L_APCL_is_hole, ?L_APCL_amap_eqb. reflexivity. Qed.

Lemma L_APCL_mmap_fixed_grant : @mmap_fixed_grant = @APC.mmap_fixed_grant.
Proof. unfold mmap_fixed_grant. rewrite ?L_APCL_mkind_eqb, ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_shadow_facts, ?L_APCL_vis_add, ?L_APCL_kn_grant_filter, ?L_APCL_with_maps0, ?L_APCL_add_entry. reflexivity. Qed.

Lemma L_APCL_mmap_fixed_free : @mmap_fixed_free = @APC.mmap_fixed_free.
Proof. unfold mmap_fixed_free. rewrite ?L_APCL_CEIL, ?L_APCL_is_hole, ?L_APCL_no_fog, ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_expr_vars_lt, ?L_APCL_budget_ok, ?L_APCL_fixed_args, ?L_APCL_find_hole, ?L_APCL_unhole, ?L_APCL_mmap_fixed_grant, ?AX2L.L_AX2L_ranges_apart_x. reflexivity. Qed.

Lemma L_APCL_kn_rezero : @kn_rezero = @APC.kn_rezero.
Proof. unfold kn_rezero. rewrite ?L_APCL_kentry_apart_bp, ?AX2L.L_AX2L_mk_sprep. reflexivity. Qed.

Lemma L_APCL_kn_rezeroB : @kn_rezeroB = @APC.kn_rezeroB.
Proof. unfold kn_rezeroB. rewrite ?L_APCL_kentry_apart_bpB, ?AX2BL.L_AX2BL_mk_sprepB. reflexivity. Qed.

Lemma L_APCL_kn_rezeroM : @kn_rezeroM = @APC.kn_rezeroM.
Proof. unfold kn_rezeroM. rewrite ?L_APCL_kn_rezeroB, ?AX2BL.L_AX2BL_mkbc. reflexivity. Qed.

Lemma L_APCL_rekind : @rekind = @APC.rekind.
Proof. unfold rekind. rewrite ?L_APCL_amap_eqb. reflexivity. Qed.

Lemma L_APCL_fixed_in_args_ref : @fixed_in_args_ref = @APC.fixed_in_args_ref.
Proof. unfold fixed_in_args_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_expr_vars_lt, ?L_APCL_find_containing, ?L_APCL_fixed_args_base. reflexivity. Qed.

Lemma L_APCL_fixed_in_args : @fixed_in_args = @APC.fixed_in_args.
Proof. unfold fixed_in_args. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_expr_vars_lt, ?L_APCL_find_containingB, ?L_APCL_fixed_args_base, ?AX2BL.L_AX2BL_mkbc. reflexivity. Qed.

Lemma L_APCL_mmap_fixed_in_ref : @mmap_fixed_in_ref = @APC.mmap_fixed_in_ref.
Proof. unfold mmap_fixed_in_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_mk_ss, ?L_APCL_kn_unfill, ?L_APCL_kn_cutout, ?L_APCL_kimg_clip, ?L_APCL_vis_add, ?L_APCL_budget_ok, ?L_APCL_kn_rezero, ?L_APCL_rekind, ?L_APCL_fixed_in_args. reflexivity. Qed.

Lemma L_APCL_mmap_fixed_in : @mmap_fixed_in = @APC.mmap_fixed_in.
Proof. unfold mmap_fixed_in. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_mk_ss, ?L_APCL_kn_unfillB, ?L_APCL_kn_cutoutB, ?L_APCL_kimg_clip, ?L_APCL_vis_add, ?L_APCL_budget_ok, ?L_APCL_kn_rezeroB, ?L_APCL_rekind, ?L_APCL_fixed_in_args, ?AX2BL.L_AX2BL_mkbc. reflexivity. Qed.

Lemma L_APCL_ENOMEM_RET : @ENOMEM_RET = @APC.ENOMEM_RET.
Proof. unfold ENOMEM_RET. rewrite ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_refuse : @refuse = @APC.refuse.
Proof. unfold refuse. rewrite ?L_APCL_pc, ?L_APCL_set_reg, ?L_APCL_set_pc, ?L_APCL_ENOMEM_RET. reflexivity. Qed.

Lemma L_APCL_replace_entry : @replace_entry = @APC.replace_entry.
Proof. unfold replace_entry. rewrite ?L_APCL_amap_eqb. reflexivity. Qed.

Lemma L_APCL_dest_lfact : @dest_lfact = @APC.dest_lfact.
Proof. unfold dest_lfact. rewrite ?L_APCL_esub, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_dest_rfact : @dest_rfact = @APC.dest_rfact.
Proof. unfold dest_rfact. rewrite ?L_APCL_eadd, ?L_APCL_esub, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_mmap_destroyed_with_ref : @mmap_destroyed_with_ref = @APC.mmap_destroyed_with_ref.
Proof. unfold mmap_destroyed_with_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_mk_ss, ?L_APCL_eadd, ?L_APCL_esub, ?L_APCL_kn_cutout, ?L_APCL_kimg_clip, ?L_APCL_ENOMEM_RET, ?L_APCL_replace_entry, ?L_APCL_dest_lfact, ?L_APCL_dest_rfact, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_mmap_destroyed_with : @mmap_destroyed_with = @APC.mmap_destroyed_with.
Proof. unfold mmap_destroyed_with. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_mk_ss, ?L_APCL_eadd, ?L_APCL_esub, ?L_APCL_kn_cutoutB, ?L_APCL_kimg_clip, ?L_APCL_ENOMEM_RET, ?L_APCL_replace_entry, ?L_APCL_dest_lfact, ?L_APCL_dest_rfact, ?AX2BL.L_AX2BL_mkbc, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_dest_cases : @dest_cases = @APC.dest_cases.
Proof. unfold dest_cases. rewrite ?L_APCL_reg, ?L_APCL_kn, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_lin_ge0. reflexivity. Qed.

Lemma L_APCL_mmap_destroyed : @mmap_destroyed = @APC.mmap_destroyed.
Proof. unfold mmap_destroyed. rewrite ?L_APCL_mmap_destroyed_with, ?L_APCL_dest_cases. reflexivity. Qed.

Lemma L_APCL_mmap_gate : @mmap_gate = @APC.mmap_gate.
Proof. unfold mmap_gate. rewrite ?L_APCL_reg_lit, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_node_mmap2 : @node_mmap2 = @APC.node_mmap2.
Proof. unfold node_mmap2. rewrite ?L_APCL_mmap_null, ?L_APCL_mmap_fixed_free, ?L_APCL_refuse, ?L_APCL_mmap_gate. reflexivity. Qed.

Lemma L_APCL_mmap_nullF : @mmap_nullF = @APC.mmap_nullF.
Proof. unfold mmap_nullF. rewrite ?L_APCL_TOPMAX, ?L_APCL_no_holes, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_escale, ?L_APCL_expr_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_vis_add, ?L_APCL_mmap_len, ?L_APCL_kn_grant_filterF, ?L_APCL_gap_ok, ?L_APCL_budget_ok, ?L_APCL_kdisj_new, ?L_APCL_add_entry, ?L_APCL_null_kend, ?L_APCL_null_lo, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_mmap_fixed_grantF : @mmap_fixed_grantF = @APC.mmap_fixed_grantF.
Proof. unfold mmap_fixed_grantF. rewrite ?L_APCL_mkind_eqb, ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_shadow_facts, ?L_APCL_vis_add, ?L_APCL_kn_grant_filterF, ?L_APCL_with_maps0, ?L_APCL_add_entry. reflexivity. Qed.

Lemma L_APCL_mmap_fixed_freeF : @mmap_fixed_freeF = @APC.mmap_fixed_freeF.
Proof. unfold mmap_fixed_freeF. rewrite ?L_APCL_CEIL, ?L_APCL_is_hole, ?L_APCL_no_fog, ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_expr_vars_lt, ?L_APCL_budget_ok, ?L_APCL_fixed_args, ?L_APCL_find_hole, ?L_APCL_unhole, ?L_APCL_mmap_fixed_grantF, ?AX2L.L_AX2L_ranges_apart_x. reflexivity. Qed.

Lemma L_APCL_node_mmap2F : @node_mmap2F = @APC.node_mmap2F.
Proof. unfold node_mmap2F. rewrite ?L_APCL_refuse, ?L_APCL_mmap_gate, ?L_APCL_mmap_nullF, ?L_APCL_mmap_fixed_freeF. reflexivity. Qed.

Lemma L_APCL_node_mmapin : @node_mmapin = @APC.node_mmapin.
Proof. unfold node_mmapin. rewrite ?L_APCL_fixed_in_args, ?L_APCL_mmap_fixed_in, ?L_APCL_refuse, ?L_APCL_mmap_destroyed, ?L_APCL_mmap_gate. reflexivity. Qed.

Lemma L_APCL_node_mprotect_ref : @node_mprotect_ref = @APC.node_mprotect_ref.
Proof. unfold node_mprotect_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_reg_lit, ?L_APCL_expr_vars_lt, ?L_APCL_kn_unfill, ?L_APCL_kimg_clip, ?L_APCL_find_containing, ?L_APCL_vis_add, ?L_APCL_budget_ok, ?L_APCL_fixed_args_base, ?L_APCL_rekind, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_node_mprotect : @node_mprotect = @APC.node_mprotect.
Proof. unfold node_mprotect. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_reg_lit, ?L_APCL_expr_vars_lt, ?L_APCL_kn_unfillB, ?L_APCL_kimg_clip, ?L_APCL_find_containingB, ?L_APCL_vis_add, ?L_APCL_budget_ok, ?L_APCL_fixed_args_base, ?L_APCL_rekind, ?AX2BL.L_AX2BL_mkbc, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_node_mprotect2 : @node_mprotect2 = @APC.node_mprotect2.
Proof. unfold node_mprotect2. rewrite ?L_APCL_refuse, ?L_APCL_node_mprotect. reflexivity. Qed.

Lemma L_APCL_amap_match : @amap_match = @APC.amap_match.
Proof. unfold amap_match. rewrite ?L_APCL_is_fog, ?L_APCL_len_eqb, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_amap_matchB : @amap_matchB = @APC.amap_matchB.
Proof. unfold amap_matchB. rewrite ?L_APCL_is_fog, ?L_APCL_len_eqbB, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_node_munmap_ref : @node_munmap_ref = @APC.node_munmap_ref.
Proof. unfold node_munmap_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_mk_ss, ?L_APCL_reg_lit, ?L_APCL_kn_unfill, ?L_APCL_kzero_x, ?L_APCL_flat_x, ?L_APCL_page_aligned, ?L_APCL_shadow_of, ?L_APCL_mmap_len, ?L_APCL_amap_match, ?AX2L.L_AX2L_ealign, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xinside. reflexivity. Qed.

Lemma L_APCL_node_munmap : @node_munmap = @APC.node_munmap.
Proof. unfold node_munmap. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_mk_ss, ?L_APCL_reg_lit, ?L_APCL_kn_unfillB, ?L_APCL_kn_unfillM, ?L_APCL_kzero_xB, ?L_APCL_flat_xB, ?L_APCL_page_alignedB, ?L_APCL_shadow_ofB, ?L_APCL_mmap_len, ?L_APCL_amap_matchB, ?AX2BL.L_AX2BL_ealignB, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xinsideB. reflexivity. Qed.

Lemma L_APCL_brk_req : @brk_req = @APC.brk_req.
Proof. unfold brk_req. rewrite ?L_APCL_reg, ?L_APCL_lit_diff, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_brk_base_ok : @brk_base_ok = @APC.brk_base_ok.
Proof. unfold brk_base_ok. rewrite ?L_APCL_KHI, ?L_APCL_kn, ?L_APCL_page_aligned, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_brk_grow_possible : @brk_grow_possible = @APC.brk_grow_possible.
Proof. unfold brk_grow_possible. rewrite ?L_APCL_no_fog, ?L_APCL_kn, ?L_APCL_budget_ok, ?L_APCL_brk_base_ok, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_brk_grow_blocked : @brk_grow_blocked = @APC.brk_grow_blocked.
Proof. unfold brk_grow_blocked. rewrite ?L_APCL_is_fog, ?L_APCL_kn, ?L_APCL_brk_base_ok, ?AX2L.L_AX2L_lin_ge0. reflexivity. Qed.

Lemma L_APCL_node_brk1 : @node_brk1 = @APC.node_brk1.
Proof. unfold node_brk1. rewrite ?L_APCL_pc, ?L_APCL_set_reg, ?L_APCL_set_pc, ?L_APCL_reg_lit, ?L_APCL_brk_req, ?L_APCL_brk_grow_blocked. reflexivity. Qed.

Lemma L_APCL_node_settid : @node_settid = @APC.node_settid.
Proof. unfold node_settid. rewrite ?L_APCL_PID_MAX, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_reg_lit, ?L_APCL_fresh_ok, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_node_exit : @node_exit = @APC.node_exit.
Proof. unfold node_exit. rewrite ?L_APCL_reg_lit. reflexivity. Qed.

Lemma L_APCL_list_set_nth : @list_set_nth = @APC.list_set_nth.
Proof. unfold list_set_nth. reflexivity. Qed.

Lemma L_APCL_list_insert_nth : @list_insert_nth = @APC.list_insert_nth.
Proof. unfold list_insert_nth. reflexivity. Qed.

Lemma L_APCL_fog_token : @fog_token = @APC.fog_token.
Proof. unfold fog_token. reflexivity. Qed.

Lemma L_APCL_with_maps : @with_maps = @APC.with_maps.
Proof. unfold with_maps. reflexivity. Qed.

Lemma L_APCL_node_fog : @node_fog = @APC.node_fog.
Proof. unfold node_fog. rewrite ?L_APCL_is_fog, ?L_APCL_kn, ?L_APCL_list_set_nth, ?L_APCL_fog_token, ?L_APCL_with_maps, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_APCL_node_fognew : @node_fognew = @APC.node_fognew.
Proof. unfold node_fognew. rewrite ?L_APCL_list_insert_nth, ?L_APCL_fog_token, ?L_APCL_with_maps, ?AX2L.L_AX2L_two64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_node_ghost : @node_ghost = @APC.node_ghost.
Proof. unfold node_ghost. rewrite ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_expr_vars_lt, ?L_APCL_vis_cost, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_APCL_vis_here : @vis_here = @APC.vis_here.
Proof. unfold vis_here. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_node_unvis_ref : @node_unvis_ref = @APC.node_unvis_ref.
Proof. unfold node_unvis_ref. rewrite ?L_APCL_TOPMAX, ?L_APCL_kn, ?L_APCL_mk_ss, ?L_APCL_kn_unfill, ?L_APCL_kzero_x, ?L_APCL_flat_x, ?L_APCL_shadow_of, ?L_APCL_vis_here, ?AX2L.L_AX2L_ealign, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_APCL_node_unvis : @node_unvis = @APC.node_unvis.
Proof. unfold node_unvis. rewrite ?L_APCL_TOPMAX, ?L_APCL_kn, ?L_APCL_mk_ss, ?L_APCL_kn_unfillB, ?L_APCL_kn_unfillM, ?L_APCL_kzero_xB, ?L_APCL_flat_xB, ?L_APCL_shadow_ofB, ?L_APCL_vis_here, ?AX2BL.L_AX2BL_ealignB, ?AX2BL.L_AX2BL_mkbc, ?AX2L.L_AX2L_split_lit, ?AX2BL.L_AX2BL_xhiB. reflexivity. Qed.

Lemma L_APCL_node_havocbrk : @node_havocbrk = @APC.node_havocbrk.
Proof. unfold node_havocbrk. rewrite ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_fresh_ok, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_node_intro : @node_intro = @APC.node_intro.
Proof. unfold node_intro. rewrite ?L_APCL_nxt, ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_fresh_ok, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_introg_witness : @introg_witness = @APC.introg_witness.
Proof. unfold introg_witness. rewrite ?L_APCL_CEIL. reflexivity. Qed.

Lemma L_APCL_node_introg : @node_introg = @APC.node_introg.
Proof. unfold node_introg. rewrite ?L_APCL_nxt, ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_escale, ?L_APCL_sa_stk, ?L_APCL_en_stk, ?L_APCL_sa_stk0, ?L_APCL_zone_reserved, ?L_APCL_sa_hull, ?L_APCL_en_hull, ?L_APCL_sa_zone, ?L_APCL_en_zone, ?L_APCL_fresh_ok, ?L_APCL_introg_witness, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_SPIN_WORD : @SPIN_WORD = @APC.SPIN_WORD.
Proof. unfold SPIN_WORD. reflexivity. Qed.

Lemma L_APCL_node_spin : @node_spin = @APC.node_spin.
Proof. unfold node_spin. rewrite ?L_APCL_pc, ?L_APCL_SPIN_WORD, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_summary_fill_ref : @summary_fill_ref = @APC.summary_fill_ref.
Proof. unfold summary_fill_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_reg_lit, ?L_APCL_kn_havoc, ?L_APCL_kimg_cut, ?L_APCL_kwritable_x, ?L_APCL_kzero_x, ?L_APCL_off_image_x, ?L_APCL_ret_lit, ?L_APCL_after_call, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_summary_fill : @summary_fill = @APC.summary_fill.
Proof. unfold summary_fill. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_reg_lit, ?L_APCL_kn_havocB, ?L_APCL_kn_havocM, ?L_APCL_kimg_cut, ?L_APCL_kwritable_xB, ?L_APCL_kzero_xB, ?L_APCL_off_image_xB, ?L_APCL_ret_lit, ?L_APCL_after_call, ?AX2BL.L_AX2BL_mkbc, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xloB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_copy_facts : @copy_facts = @APC.copy_facts.
Proof. unfold copy_facts. rewrite ?L_APCL_kread8e, ?L_APCL_kread_bytes, ?AX2L.L_AX2L_know_lookup, ?AX2L.L_AX2L_zbytes_le_to_Z. reflexivity. Qed.

Lemma L_APCL_copy_factsB : @copy_factsB = @APC.copy_factsB.
Proof. unfold copy_factsB. rewrite ?L_APCL_kread8eB, ?L_APCL_kread_bytesB, ?AX2BL.L_AX2BL_know_lookupB, ?AX2L.L_AX2L_zbytes_le_to_Z. reflexivity. Qed.

Lemma L_APCL_kblob_prefix : @kblob_prefix = @APC.kblob_prefix.
Proof. unfold kblob_prefix. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_summary_copy_ref : @summary_copy_ref = @APC.summary_copy_ref.
Proof. unfold summary_copy_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_kn_havoc, ?L_APCL_kimg_cut, ?L_APCL_kwritable_x, ?L_APCL_kzero_x, ?L_APCL_off_image_x, ?L_APCL_flat_x, ?L_APCL_NCS, ?L_APCL_ret_lit, ?L_APCL_after_call, ?L_APCL_after_call2, ?L_APCL_copy_facts, ?L_APCL_kblob_prefix, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_summary_copy : @summary_copy = @APC.summary_copy.
Proof. unfold summary_copy. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_kn_havocB, ?L_APCL_kn_havocM, ?L_APCL_kimg_cut, ?L_APCL_kwritable_xB, ?L_APCL_kzero_xB, ?L_APCL_off_image_xB, ?L_APCL_flat_xB, ?L_APCL_NCS, ?L_APCL_ret_lit, ?L_APCL_after_call, ?L_APCL_after_call2, ?L_APCL_copy_factsB, ?L_APCL_kblob_prefix, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xloB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_summary_miz_ref : @summary_miz_ref = @APC.summary_miz_ref.
Proof. unfold summary_miz_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_eaddz, ?L_APCL_kn_havoc, ?L_APCL_kwritable, ?L_APCL_kzero_x, ?L_APCL_ret_lit, ?L_APCL_after_call, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_summary_miz : @summary_miz = @APC.summary_miz.
Proof. unfold summary_miz. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_eaddz, ?L_APCL_kn_havocB, ?L_APCL_kwritableB, ?L_APCL_kzero_xB, ?L_APCL_ret_lit, ?L_APCL_after_call, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xloB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_img_cov : @img_cov = @APC.img_cov.
Proof. unfold img_cov. reflexivity. Qed.

Lemma L_APCL_img_covB : @img_covB = @APC.img_covB.
Proof. unfold img_covB. reflexivity. Qed.

Lemma L_APCL_SEALED_W : @SEALED_W = @APC.SEALED_W.
Proof. unfold SEALED_W. reflexivity. Qed.

Lemma L_APCL_summary_istrncpy_ref : @summary_istrncpy_ref = @APC.summary_istrncpy_ref.
Proof. unfold summary_istrncpy_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_reg_lit, ?L_APCL_kn_havoc, ?L_APCL_kimg_cut, ?L_APCL_kwritable_x, ?L_APCL_off_image_x, ?L_APCL_ret_lit, ?L_APCL_after_call, ?L_APCL_img_cov, ?L_APCL_SEALED_W, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_summary_istrncpy : @summary_istrncpy = @APC.summary_istrncpy.
Proof. unfold summary_istrncpy. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_reg_lit, ?L_APCL_kn_havocM, ?L_APCL_kimg_cut, ?L_APCL_kwritable_xB, ?L_APCL_off_image_xB, ?L_APCL_ret_lit, ?L_APCL_after_call, ?L_APCL_img_cov, ?L_APCL_SEALED_W, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_popfree_facts : @popfree_facts = @APC.popfree_facts.
Proof. unfold popfree_facts. reflexivity. Qed.

Lemma L_APCL_summary_popfree : @summary_popfree = @APC.summary_popfree.
Proof. unfold summary_popfree. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_reg_lit, ?L_APCL_eaddz, ?L_APCL_fresh_ok, ?L_APCL_kn_havoc, ?L_APCL_kwritable_x, ?L_APCL_off_image_x, ?L_APCL_popfree_facts, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_sr_upd, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_kn_readable_x : @kn_readable_x = @APC.kn_readable_x.
Proof. unfold kn_readable_x. rewrite ?AX2L.L_AX2L_xinside. reflexivity. Qed.

Lemma L_APCL_summary_sniff_ref : @summary_sniff_ref = @APC.summary_sniff_ref.
Proof. unfold summary_sniff_ref. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_eadd, ?L_APCL_eaddz, ?L_APCL_kn_havoc, ?L_APCL_kwritable, ?L_APCL_flat_x, ?L_APCL_ehi, ?L_APCL_ret_lit, ?L_APCL_after_call, ?L_APCL_img_cov, ?L_APCL_kn_readable_x, ?AX2L.L_AX2L_ealign, ?AX2L.L_AX2L_erange, ?AX2L.L_AX2L_extK, ?AX2L.L_AX2L_kn_readable, ?AX2L.L_AX2L_know_lookup, ?AX2L.L_AX2L_lin_ge0, ?AX2L.L_AX2L_mkSrl, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_summary_sniff : @summary_sniff = @APC.summary_sniff.
Proof. unfold summary_sniff. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_eadd, ?L_APCL_eaddz, ?L_APCL_kn_havocB, ?L_APCL_kwritableB, ?L_APCL_flat_xB, ?L_APCL_ehi, ?L_APCL_ret_lit, ?L_APCL_after_call, ?L_APCL_img_covB, ?L_APCL_kn_readable_x, ?AX2BL.L_AX2BL_ealignB, ?AX2BL.L_AX2BL_erangeB, ?AX2BL.L_AX2BL_extKB, ?AX2BL.L_AX2BL_kn_readableB, ?AX2BL.L_AX2BL_know_lookupB, ?AX2BL.L_AX2BL_lin_ge0B, ?AX2BL.L_AX2BL_mkSrlB, ?AX2BL.L_AX2BL_mkbc, ?AX2BL.L_AX2BL_ranges_apart_xB, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2BL.L_AX2BL_xhiB, ?AX2BL.L_AX2BL_xloB. reflexivity. Qed.

Lemma L_APCL_V_S1 : @V_S1 = @APC.V_S1.
Proof. unfold V_S1. reflexivity. Qed.

Lemma L_APCL_V_ARGC : @V_ARGC = @APC.V_ARGC.
Proof. unfold V_ARGC. reflexivity. Qed.

Lemma L_APCL_V_ENVC : @V_ENVC = @APC.V_ENVC.
Proof. unfold V_ENVC. reflexivity. Qed.

Lemma L_APCL_V_L0 : @V_L0 = @APC.V_L0.
Proof. unfold V_L0. reflexivity. Qed.

Lemma L_APCL_V_W : @V_W = @APC.V_W.
Proof. unfold V_W. reflexivity. Qed.

Lemma L_APCL_V_BRK : @V_BRK = @APC.V_BRK.
Proof. unfold V_BRK. reflexivity. Qed.

Lemma L_APCL_V_S2 : @V_S2 = @APC.V_S2.
Proof. unfold V_S2. reflexivity. Qed.

Lemma L_APCL_V_P : @V_P = @APC.V_P.
Proof. unfold V_P. reflexivity. Qed.

Lemma L_APCL_V_Q : @V_Q = @APC.V_Q.
Proof. unfold V_Q. reflexivity. Qed.

Lemma L_APCL_V_HW : @V_HW = @APC.V_HW.
Proof. unfold V_HW. reflexivity. Qed.

Lemma L_APCL_V_L1 : @V_L1 = @APC.V_L1.
Proof. unfold V_L1. reflexivity. Qed.

Lemma L_APCL_V_UID : @V_UID = @APC.V_UID.
Proof. unfold V_UID. reflexivity. Qed.

Lemma L_APCL_e_sp0 : @e_sp0 = @APC.e_sp0.
Proof. unfold e_sp0. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_S1, ?L_APCL_V_S2, ?L_APCL_V_P. reflexivity. Qed.

Lemma L_APCL_e_sp8 : @e_sp8 = @APC.e_sp8.
Proof. unfold e_sp8. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_S1, ?L_APCL_V_S2, ?L_APCL_V_P. reflexivity. Qed.

Lemma L_APCL_e_envp : @e_envp = @APC.e_envp.
Proof. unfold e_envp. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_ARGC, ?L_APCL_e_sp0. reflexivity. Qed.

Lemma L_APCL_e_auxv : @e_auxv = @APC.e_auxv.
Proof. unfold e_auxv. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_ENVC, ?L_APCL_e_envp. reflexivity. Qed.

Lemma L_APCL_e_str0 : @e_str0 = @APC.e_str0.
Proof. unfold e_str0. rewrite ?L_APCL_eaddz, ?L_APCL_e_auxv. reflexivity. Qed.

Lemma L_APCL_e_str1 : @e_str1 = @APC.e_str1.
Proof. unfold e_str1. rewrite ?L_APCL_eadd, ?L_APCL_eaddz, ?L_APCL_V_L0, ?L_APCL_e_str0. reflexivity. Qed.

Lemma L_APCL_e_atrandom : @e_atrandom = @APC.e_atrandom.
Proof. unfold e_atrandom. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_W, ?L_APCL_e_str0. reflexivity. Qed.

Lemma L_APCL_e_atr8 : @e_atr8 = @APC.e_atr8.
Proof. unfold e_atr8. rewrite ?L_APCL_eadd, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_W, ?L_APCL_e_sp8. reflexivity. Qed.

Lemma L_APCL_e_Xsh : @e_Xsh = @APC.e_Xsh.
Proof. unfold e_Xsh. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_W, ?L_APCL_V_S2. reflexivity. Qed.

Lemma L_APCL_e_Xm : @e_Xm = @APC.e_Xm.
Proof. unfold e_Xm. rewrite ?L_APCL_e_Xsh, ?AX2L.L_AX2L_mkAlu. reflexivity. Qed.

Lemma L_APCL_e_atr8m : @e_atr8m = @APC.e_atr8m.
Proof. unfold e_atr8m. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_S1, ?L_APCL_V_P, ?L_APCL_e_Xm. reflexivity. Qed.

Lemma L_APCL_e_vis3b : @e_vis3b = @APC.e_vis3b.
Proof. unfold e_vis3b. rewrite ?L_APCL_escale, ?L_APCL_V_S1. reflexivity. Qed.

Lemma L_APCL_e_vis3n : @e_vis3n = @APC.e_vis3n.
Proof. unfold e_vis3n. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_P, ?L_APCL_V_Q. reflexivity. Qed.

Lemma L_APCL_e_pgslack : @e_pgslack = @APC.e_pgslack.
Proof. unfold e_pgslack. rewrite ?L_APCL_eadd, ?L_APCL_esub, ?L_APCL_escale, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_W, ?L_APCL_V_S2, ?L_APCL_V_Q. reflexivity. Qed.

Lemma L_APCL_e_pgslack8 : @e_pgslack8 = @APC.e_pgslack8.
Proof. unfold e_pgslack8. rewrite ?L_APCL_eadd, ?L_APCL_esub, ?L_APCL_escale, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_W, ?L_APCL_V_S2, ?L_APCL_V_Q. reflexivity. Qed.

Lemma L_APCL_e_top8 : @e_top8 = @APC.e_top8.
Proof. unfold e_top8. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_S1, ?L_APCL_V_P, ?L_APCL_V_Q. reflexivity. Qed.

Lemma L_APCL_e_top : @e_top = @APC.e_top.
Proof. unfold e_top. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_S1, ?L_APCL_V_P, ?L_APCL_V_Q. reflexivity. Qed.

Lemma L_APCL_e_blk0 : @e_blk0 = @APC.e_blk0.
Proof. unfold e_blk0. rewrite ?L_APCL_eadd, ?L_APCL_esub, ?L_APCL_escale, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_S2, ?L_APCL_V_Q. reflexivity. Qed.

Lemma L_APCL_e_blk08 : @e_blk08 = @APC.e_blk08.
Proof. unfold e_blk08. rewrite ?L_APCL_eadd, ?L_APCL_esub, ?L_APCL_escale, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_S2, ?L_APCL_V_Q. reflexivity. Qed.

Lemma L_APCL_e_blkL0 : @e_blkL0 = @APC.e_blkL0.
Proof. unfold e_blkL0. rewrite ?L_APCL_esub, ?L_APCL_V_L0, ?L_APCL_e_blk0. reflexivity. Qed.

Lemma L_APCL_e_blkL01 : @e_blkL01 = @APC.e_blkL01.
Proof. unfold e_blkL01. rewrite ?L_APCL_esub, ?L_APCL_V_L0, ?L_APCL_V_L1, ?L_APCL_e_blk0. reflexivity. Qed.

Lemma L_APCL_e_strW0 : @e_strW0 = @APC.e_strW0.
Proof. unfold e_strW0. rewrite ?L_APCL_esub, ?L_APCL_escale, ?L_APCL_V_L0, ?L_APCL_V_W. reflexivity. Qed.

Lemma L_APCL_e_strW01 : @e_strW01 = @APC.e_strW01.
Proof. unfold e_strW01. rewrite ?L_APCL_esub, ?L_APCL_escale, ?L_APCL_V_L0, ?L_APCL_V_W, ?L_APCL_V_L1. reflexivity. Qed.

Lemma L_APCL_e_argv1w : @e_argv1w = @APC.e_argv1w.
Proof. unfold e_argv1w. rewrite ?L_APCL_V_ARGC, ?L_APCL_e_str1. reflexivity. Qed.

Lemma L_APCL_node_envscan : @node_envscan = @APC.node_envscan.
Proof. unfold node_envscan. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_set_reg, ?L_APCL_set_pc, ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_len_eqb, ?L_APCL_V_ENVC, ?L_APCL_e_envp. reflexivity. Qed.

Lemma L_APCL_node_pnscan : @node_pnscan = @APC.node_pnscan.
Proof. unfold node_pnscan. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_reg_lit, ?L_APCL_eaddz, ?L_APCL_fresh_ok, ?L_APCL_kn_havoc, ?L_APCL_kimg_cut, ?L_APCL_kwritable, ?L_APCL_len_eqb, ?L_APCL_e_str0, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Lemma L_APCL_kw_argv1 : @kw_argv1 = @APC.kw_argv1.
Proof. unfold kw_argv1. rewrite ?L_APCL_e_sp0. reflexivity. Qed.

Lemma L_APCL_node_layout : @node_layout = @APC.node_layout.
Proof. unfold node_layout. rewrite ?L_APCL_kn, ?L_APCL_set_kn, ?L_APCL_kentry_eqb, ?L_APCL_V_ARGC, ?L_APCL_e_str1, ?L_APCL_e_argv1w, ?L_APCL_kw_argv1, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_APCL_kimg_sub_covered0 : @kimg_sub_covered0 = @APC.kimg_sub_covered0.
Proof. unfold kimg_sub_covered0. reflexivity. Qed.

Lemma L_APCL_kn_incl1_eF : @kn_incl1_eF = @APC.kn_incl1_eF.
Proof. unfold kn_incl1_eF. rewrite ?L_APCL_kset, ?L_APCL_kset_mem, ?L_APCL_kimg_sub_covered0. reflexivity. Qed.

Lemma L_APCL_kn_incl_e : @kn_incl_e = @APC.kn_incl_e.
Proof. unfold kn_incl_e. rewrite ?L_APCL_kset_of, ?L_APCL_kn_incl1_eF. reflexivity. Qed.

Lemma L_APCL_entails : @entails = @APC.entails.
Proof. unfold entails. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_amap_eqb, ?L_APCL_list_eqb, ?L_APCL_pair_eqb, ?L_APCL_afd_eqb, ?L_APCL_kn_incl_e, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_esubst : @esubst = @APC.esubst.
Proof. unfold esubst. rewrite ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_mkAluw, ?AX2L.L_AX2L_mkMd, ?AX2L.L_AX2L_mkMdw, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_asubst : @asubst = @APC.asubst.
Proof. unfold asubst. rewrite ?L_APCL_esubst, ?AX2L.L_AX2L_esubst. reflexivity. Qed.

Lemma L_APCL_ksubst : @ksubst = @APC.ksubst.
Proof. unfold ksubst. rewrite ?L_APCL_esubst, ?L_APCL_asubst, ?AX2L.L_AX2L_esubst. reflexivity. Qed.

Lemma L_APCL_psubst : @psubst = @APC.psubst.
Proof. unfold psubst. rewrite ?L_APCL_esubst, ?AX2L.L_AX2L_esubst. reflexivity. Qed.

Lemma L_APCL_msubst : @msubst = @APC.msubst.
Proof. unfold msubst. rewrite ?L_APCL_esubst, ?AX2L.L_AX2L_esubst. reflexivity. Qed.

Lemma L_APCL_fsubst : @fsubst = @APC.fsubst.
Proof. unfold fsubst. rewrite ?L_APCL_esubst, ?AX2L.L_AX2L_esubst. reflexivity. Qed.

Lemma L_APCL_inst : @inst = @APC.inst.
Proof. unfold inst. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_esubst, ?L_APCL_ksubst, ?L_APCL_psubst, ?L_APCL_msubst, ?L_APCL_fsubst, ?AX2L.L_AX2L_esubst. reflexivity. Qed.

Lemma L_APCL_brk_vis : @brk_vis = @APC.brk_vis.
Proof. unfold brk_vis. rewrite ?L_APCL_kn, ?L_APCL_eaddz, ?L_APCL_vis_add. reflexivity. Qed.

Lemma L_APCL_brk_var : @brk_var = @APC.brk_var.
Proof. unfold brk_var. reflexivity. Qed.

Lemma L_APCL_node_brk2 : @node_brk2 = @APC.node_brk2.
Proof. unfold node_brk2. rewrite ?L_APCL_no_fog, ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_set_reg, ?L_APCL_set_pc, ?L_APCL_bump, ?L_APCL_reg_lit, ?L_APCL_expr_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_flat_x, ?L_APCL_kn_grant_filter, ?L_APCL_budget_ok, ?L_APCL_kdisj_new, ?L_APCL_brk_req, ?L_APCL_brk_base_ok, ?L_APCL_inst, ?L_APCL_brk_vis, ?L_APCL_brk_var, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_node_brk2F : @node_brk2F = @APC.node_brk2F.
Proof. unfold node_brk2F. rewrite ?L_APCL_no_fog, ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_mk_ss, ?L_APCL_set_reg, ?L_APCL_set_pc, ?L_APCL_bump, ?L_APCL_reg_lit, ?L_APCL_expr_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_flat_x, ?L_APCL_kn_grant_filterF, ?L_APCL_budget_ok, ?L_APCL_kdisj_new, ?L_APCL_brk_req, ?L_APCL_brk_base_ok, ?L_APCL_inst, ?L_APCL_brk_vis, ?L_APCL_brk_var, ?AX2L.L_AX2L_ranges_apart_x, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_nt_set : @nt_set = @APC.nt_set.
Proof. unfold nt_set. reflexivity. Qed.

Lemma L_APCL_nt_get : @nt_get = @APC.nt_get.
Proof. unfold nt_get. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_mk_fwd : @mk_fwd = @APC.mk_fwd.
Proof. unfold mk_fwd. rewrite ?L_APCL_nt_set, ?L_APCL_nt_get. reflexivity. Qed.

Lemma L_APCL_mk_bwd : @mk_bwd = @APC.mk_bwd.
Proof. unfold mk_bwd. rewrite ?L_APCL_nt_set, ?L_APCL_nt_get. reflexivity. Qed.

Lemma L_APCL_erename : @erename = @APC.erename.
Proof. unfold erename. rewrite ?L_APCL_nt_get. reflexivity. Qed.

Lemma L_APCL_arename : @arename = @APC.arename.
Proof. unfold arename. rewrite ?L_APCL_erename. reflexivity. Qed.

Lemma L_APCL_krename : @krename = @APC.krename.
Proof. unfold krename. rewrite ?L_APCL_erename, ?L_APCL_arename. reflexivity. Qed.

Lemma L_APCL_prename : @prename = @APC.prename.
Proof. unfold prename. rewrite ?L_APCL_erename. reflexivity. Qed.

Lemma L_APCL_mrename : @mrename = @APC.mrename.
Proof. unfold mrename. rewrite ?L_APCL_erename. reflexivity. Qed.

Lemma L_APCL_frename : @frename = @APC.frename.
Proof. unfold frename. rewrite ?L_APCL_erename. reflexivity. Qed.

Lemma L_APCL_evars_all : @evars_all = @APC.evars_all.
Proof. unfold evars_all. reflexivity. Qed.

Lemma L_APCL_kvars_all : @kvars_all = @APC.kvars_all.
Proof. unfold kvars_all. rewrite ?L_APCL_evars_all. reflexivity. Qed.

Lemma L_APCL_csvars_all : @csvars_all = @APC.csvars_all.
Proof. unfold csvars_all. rewrite ?L_APCL_kn, ?L_APCL_evars_all, ?L_APCL_kvars_all. reflexivity. Qed.

Lemma L_APCL_emaxv : @emaxv = @APC.emaxv.
Proof. unfold emaxv. reflexivity. Qed.

Lemma L_APCL_kmaxv : @kmaxv = @APC.kmaxv.
Proof. unfold kmaxv. rewrite ?L_APCL_emaxv. reflexivity. Qed.

Lemma L_APCL_csmaxv : @csmaxv = @APC.csmaxv.
Proof. unfold csmaxv. rewrite ?L_APCL_kn, ?L_APCL_emaxv, ?L_APCL_kmaxv. reflexivity. Qed.

Lemma L_APCL_rename_cs : @rename_cs = @APC.rename_cs.
Proof. unfold rename_cs. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_mk_ss, ?L_APCL_erename, ?L_APCL_krename, ?L_APCL_prename, ?L_APCL_mrename, ?L_APCL_frename. reflexivity. Qed.

Lemma L_APCL_node_rename : @node_rename = @APC.node_rename.
Proof. unfold node_rename. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_nt_get, ?L_APCL_mk_fwd, ?L_APCL_mk_bwd, ?L_APCL_csvars_all, ?L_APCL_csmaxv, ?L_APCL_rename_cs, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_bt_set : @bt_set = @APC.bt_set.
Proof. unfold bt_set. reflexivity. Qed.

Lemma L_APCL_bt_get : @bt_get = @APC.bt_get.
Proof. unfold bt_get. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_evars_fo : @evars_fo = @APC.evars_fo.
Proof. unfold evars_fo. rewrite ?L_APCL_bt_set, ?L_APCL_bt_get, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kvars_fo : @kvars_fo = @APC.kvars_fo.
Proof. unfold kvars_fo. rewrite ?L_APCL_evars_fo. reflexivity. Qed.

Lemma L_APCL_csvars_fo : @csvars_fo = @APC.csvars_fo.
Proof. unfold csvars_fo. rewrite ?L_APCL_kn, ?L_APCL_evars_fo, ?L_APCL_kvars_fo. reflexivity. Qed.

Lemma L_APCL_number_from : @number_from = @APC.number_from.
Proof. unfold number_from. reflexivity. Qed.

Lemma L_APCL_compact_map : @compact_map = @APC.compact_map.
Proof. unfold compact_map. rewrite ?L_APCL_csvars_fo, ?L_APCL_number_from. reflexivity. Qed.

Lemma L_APCL_node_compact : @node_compact = @APC.node_compact.
Proof. unfold node_compact. rewrite ?L_APCL_node_rename, ?L_APCL_compact_map. reflexivity. Qed.

Lemma L_APCL_regs_match_h : @regs_match_h = @APC.regs_match_h.
Proof. unfold regs_match_h. rewrite ?L_APCL_expr_vars_lt, ?AX2L.L_AX2L_expr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_saddr_eqb_h : @saddr_eqb_h = @APC.saddr_eqb_h.
Proof. unfold saddr_eqb_h. rewrite ?L_APCL_eaddz, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_saddr_eqb. reflexivity. Qed.

Lemma L_APCL_cover1 : @cover1 = @APC.cover1.
Proof. unfold cover1. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_cover_x : @cover_x = @APC.cover_x.
Proof. unfold cover_x. rewrite ?L_APCL_cover1. reflexivity. Qed.

Lemma L_APCL_kunk_covered : @kunk_covered = @APC.kunk_covered.
Proof. unfold kunk_covered. rewrite ?L_APCL_off_image_x, ?L_APCL_flat_x, ?L_APCL_cover_x, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kentry_eqb_h : @kentry_eqb_h = @APC.kentry_eqb_h.
Proof. unfold kentry_eqb_h. rewrite ?L_APCL_kentry_eqb, ?L_APCL_saddr_eqb_h, ?AX2L.L_AX2L_expr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_kflat_h : @kflat_h = @APC.kflat_h.
Proof. unfold kflat_h. rewrite ?L_APCL_flat_x. reflexivity. Qed.

Lemma L_APCL_kimg_sub_covered : @kimg_sub_covered = @APC.kimg_sub_covered.
Proof. unfold kimg_sub_covered. reflexivity. Qed.

Lemma L_APCL_kn_incl1_h : @kn_incl1_h = @APC.kn_incl1_h.
Proof. unfold kn_incl1_h. rewrite ?L_APCL_kentry_eqb, ?L_APCL_kunk_covered, ?L_APCL_kentry_eqb_h, ?L_APCL_kflat_h, ?L_APCL_kimg_sub_covered. reflexivity. Qed.

Lemma L_APCL_kn_incl1_hF : @kn_incl1_hF = @APC.kn_incl1_hF.
Proof. unfold kn_incl1_hF. rewrite ?L_APCL_kset, ?L_APCL_kset_mem, ?L_APCL_kunk_covered, ?L_APCL_kentry_eqb_h, ?L_APCL_kflat_h, ?L_APCL_kimg_sub_covered. reflexivity. Qed.

Lemma L_APCL_kn_incl_h : @kn_incl_h = @APC.kn_incl_h.
Proof. unfold kn_incl_h. rewrite ?L_APCL_kset_of, ?L_APCL_kn_incl1_hF. reflexivity. Qed.

Lemma L_APCL_entails_h : @entails_h = @APC.entails_h.
Proof. unfold entails_h. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_expr_vars_lt, ?L_APCL_kn_vars_lt, ?L_APCL_pairs_vars_lt, ?L_APCL_maps_vars_lt, ?L_APCL_fd_vars_lt, ?L_APCL_amap_eqb, ?L_APCL_list_eqb, ?L_APCL_pair_eqb, ?L_APCL_afd_eqb, ?L_APCL_regs_match_h, ?L_APCL_kn_incl_h, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_kzero_sub_covered : @kzero_sub_covered = @APC.kzero_sub_covered.
Proof. unfold kzero_sub_covered. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_APCL_krange_implied : @krange_implied = @APC.krange_implied.
Proof. unfold krange_implied. rewrite ?AX2L.L_AX2L_erange. reflexivity. Qed.

Lemma L_APCL_kn_incl1_x : @kn_incl1_x = @APC.kn_incl1_x.
Proof. unfold kn_incl1_x. rewrite ?L_APCL_kn, ?L_APCL_kentry_eqb, ?L_APCL_kimg_sub_covered0, ?L_APCL_kunk_covered, ?L_APCL_kzero_sub_covered, ?L_APCL_krange_implied. reflexivity. Qed.

Lemma L_APCL_kn_incl1_xF : @kn_incl1_xF = @APC.kn_incl1_xF.
Proof. unfold kn_incl1_xF. rewrite ?L_APCL_kn, ?L_APCL_kset, ?L_APCL_kset_mem, ?L_APCL_kimg_sub_covered0, ?L_APCL_kunk_covered, ?L_APCL_kzero_sub_covered, ?L_APCL_krange_implied. reflexivity. Qed.

Lemma L_APCL_kn_incl_x0 : @kn_incl_x0 = @APC.kn_incl_x0.
Proof. unfold kn_incl_x0. rewrite ?L_APCL_kn, ?L_APCL_kset_of, ?L_APCL_kn_incl1_xF. reflexivity. Qed.

Lemma L_APCL_entails0 : @entails0 = @APC.entails0.
Proof. unfold entails0. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_amap_eqb, ?L_APCL_list_eqb, ?L_APCL_pair_eqb, ?L_APCL_afd_eqb, ?L_APCL_kn_incl_x0, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_hx_cell : @hx_cell = @APC.hx_cell.
Proof. unfold hx_cell. rewrite ?AX2L.L_AX2L_saddr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_hx_cellv : @hx_cellv = @APC.hx_cellv.
Proof. unfold hx_cellv. rewrite ?L_APCL_kread_bytes, ?L_APCL_hx_cell, ?AX2L.L_AX2L_zbytes_le_to_Z. reflexivity. Qed.

Lemma L_APCL_hx_bound : @hx_bound = @APC.hx_bound.
Proof. unfold hx_bound. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_hx_add : @hx_add = @APC.hx_add.
Proof. unfold hx_add. rewrite ?L_APCL_hx_bound, ?AX2L.L_AX2L_expr_eqb, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_hx_infer_regs : @hx_infer_regs = @APC.hx_infer_regs.
Proof. unfold hx_infer_regs. rewrite ?L_APCL_hx_add. reflexivity. Qed.

Lemma L_APCL_hx_infer_kn : @hx_infer_kn = @APC.hx_infer_kn.
Proof. unfold hx_infer_kn. rewrite ?L_APCL_hx_cellv, ?L_APCL_hx_bound, ?L_APCL_hx_add, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_hx_infer_b : @hx_infer_b = @APC.hx_infer_b.
Proof. unfold hx_infer_b. rewrite ?L_APCL_kn, ?L_APCL_hx_infer_regs, ?L_APCL_hx_infer_kn. reflexivity. Qed.

Lemma L_APCL_hx_infer : @hx_infer = @APC.hx_infer.
Proof. unfold hx_infer. rewrite ?L_APCL_hx_infer_b. reflexivity. Qed.

Lemma L_APCL_inst_list : @inst_list = @APC.inst_list.
Proof. unfold inst_list. rewrite ?L_APCL_inst. reflexivity. Qed.

Lemma L_APCL_entails_xb : @entails_xb = @APC.entails_xb.
Proof. unfold entails_xb. rewrite ?L_APCL_entails0, ?L_APCL_hx_infer_b, ?L_APCL_inst_list, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_entails_x : @entails_x = @APC.entails_x.
Proof. unfold entails_x. rewrite ?L_APCL_entails_xb. reflexivity. Qed.

Lemma L_APCL_lc_bnd : @lc_bnd = @APC.lc_bnd.
Proof. unfold lc_bnd. reflexivity. Qed.

Lemma L_APCL_loop_ok : @loop_ok = @APC.loop_ok.
Proof. unfold loop_ok. rewrite ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_expr_vars_lt, ?L_APCL_kn_vars_lt, ?L_APCL_pairs_vars_lt, ?L_APCL_maps_vars_lt, ?L_APCL_fd_vars_lt, ?L_APCL_fresh_ok, ?L_APCL_regs_match_h, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_loop_body_state : @loop_body_state = @APC.loop_body_state.
Proof. unfold loop_body_state. rewrite ?L_APCL_add_kn, ?L_APCL_esub. reflexivity. Qed.

Lemma L_APCL_branch_probe : @branch_probe = @APC.branch_probe.
Proof. unfold branch_probe. rewrite ?L_APCL_pc, ?AX2L.L_AX2L_cond_probe, ?AX2L.L_AX2L_itab_lookup, ?AX2L.L_AX2L_sr_get. reflexivity. Qed.

Lemma L_APCL_diff_regs : @diff_regs = @APC.diff_regs.
Proof. unfold diff_regs. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_APCL_node_diamond_join : @node_diamond_join = @APC.node_diamond_join.
Proof. unfold node_diamond_join. rewrite ?L_APCL_kn, ?L_APCL_pc, ?L_APCL_nxt, ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_kn_isect, ?L_APCL_sr_fresh, ?L_APCL_entails_h, ?L_APCL_diff_regs, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_diamond_join_all : @diamond_join_all = @APC.diamond_join_all.
Proof. unfold diamond_join_all. rewrite ?L_APCL_pc, ?L_APCL_node_diamond_join. reflexivity. Qed.

Lemma L_APCL_via_ok : @via_ok = @APC.via_ok.
Proof. unfold via_ok. rewrite ?L_APCL_nxt, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_node_abstractcell : @node_abstractcell = @APC.node_abstractcell.
Proof. unfold node_abstractcell. rewrite ?L_APCL_kn, ?L_APCL_set_kn, ?L_APCL_kn_cutout, ?L_APCL_kunk_covered, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_respell_ok : @respell_ok = @APC.respell_ok.
Proof. unfold respell_ok. rewrite ?AX2L.L_AX2L_decide_branch, ?AX2L.L_AX2L_erange, ?AX2L.L_AX2L_mkAlu. reflexivity. Qed.

Lemma L_APCL_node_respell : @node_respell = @APC.node_respell.
Proof. unfold node_respell. rewrite ?L_APCL_reg, ?L_APCL_kn, ?L_APCL_nxt, ?L_APCL_set_reg, ?L_APCL_expr_vars_lt, ?L_APCL_respell_ok, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_APCL_sa_of : @sa_of = @APC.sa_of.
Proof. unfold sa_of. rewrite ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_APCL_hw_apply : @hw_apply = @APC.hw_apply.
Proof. unfold hw_apply. rewrite ?AX2L.L_AX2L_saddr_eqb. reflexivity. Qed.

Lemma L_APCL_hw_val : @hw_val = @APC.hw_val.
Proof. unfold hw_val. rewrite ?AX2L.L_AX2L_saddr_eqb. reflexivity. Qed.

Lemma L_APCL_hw_go : @hw_go = @APC.hw_go.
Proof. unfold hw_go. rewrite ?L_APCL_sa_of, ?L_APCL_hw_apply. reflexivity. Qed.

Lemma L_APCL_node_havocwords : @node_havocwords = @APC.node_havocwords.
Proof. unfold node_havocwords. rewrite ?L_APCL_with_ss, ?L_APCL_mk_ss, ?L_APCL_fresh_ok, ?L_APCL_hw_go. reflexivity. Qed.

Lemma L_APCL_STOPS : @STOPS = @APC.STOPS.
Proof. unfold STOPS. reflexivity. Qed.

Lemma L_APCL_mk_itab_ranges_acc : @mk_itab_ranges_acc = @APC.mk_itab_ranges_acc.
Proof. unfold mk_itab_ranges_acc. rewrite ?AX2L.L_AX2L_itab, ?AX2L.L_AX2L_mk_itab_fuel. reflexivity. Qed.

Lemma L_APCL_mk_itab_ranges : @mk_itab_ranges = @APC.mk_itab_ranges.
Proof. unfold mk_itab_ranges. rewrite ?L_APCL_mk_itab_ranges_acc, ?AX2L.L_AX2L_itab. reflexivity. Qed.

Definition BRK_ASLR : Z := 0x80000000.
Lemma L_APCL_BRK_ASLR : @BRK_ASLR = @APC.BRK_ASLR.
Proof. unfold BRK_ASLR. reflexivity. Qed.

Definition NX0 : nat := 12.
Lemma L_APCL_NX0 : @NX0 = @APC.NX0.
Proof. unfold NX0. reflexivity. Qed.

Definition K_RND : nat := 25.
Lemma L_APCL_K_RND : @K_RND = @APC.K_RND.
Proof. unfold K_RND. reflexivity. Qed.

Definition e_auxb : expr * Z := split_lit e_auxv.
Lemma L_APCL_e_auxb : @e_auxb = @APC.e_auxb.
Proof. unfold e_auxb. rewrite ?L_APCL_e_auxv, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Definition e_atrb : expr * Z := split_lit e_atrandom.
Lemma L_APCL_e_atrb : @e_atrb = @APC.e_atrb.
Proof. unfold e_atrb. rewrite ?L_APCL_e_atrandom, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].
Lemma L_APCL_auxw : @auxw = @APC.auxw.
Proof. unfold auxw. rewrite ?L_APCL_e_auxb. reflexivity. Qed.

Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 255; KRange (EVar V_P) 0 7; KRange (EVar V_Q) 1 600;
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE7;
   KRange e_atr8m 0xFFFF0000000 0xFFFFFFFFFE0;   
   KRange e_pgslack 200 4295; KRange e_pgslack8 25 536; KRange e_top8 0xFFFF0000000 0x100000000000;   
   KRange e_top 0x7FFF80000000 0x800000000000;
   
   KRange e_blkL01 201 2457600; KRange e_blkL0 201 2457600; KRange e_blk0 200 2457600; KRange e_blk08 25 307200;
   KRange e_strW01 1 2240000; KRange e_strW0 1 2240000;
   KRange e_sp0 0x7fff80000000 0x7fffffffff40;
   KRange e_sp8 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE; KRange (EVar V_HW) 0 0xFFFFFFFFFFFFFFFF;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 3 16 (EVar V_HW) ++ auxw 4 6 (ELit 4096)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].
Lemma L_APCL_init_kn_with : @init_kn_with = @APC.init_kn_with.
Proof. unfold init_kn_with. rewrite ?L_APCL_eaddz, ?L_APCL_V_S1, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_L0, ?L_APCL_V_W, ?L_APCL_V_BRK, ?L_APCL_V_S2, ?L_APCL_V_P, ?L_APCL_V_Q, ?L_APCL_V_HW, ?L_APCL_V_L1, ?L_APCL_V_UID, ?L_APCL_e_sp0, ?L_APCL_e_sp8, ?L_APCL_e_str0, ?L_APCL_e_atrandom, ?L_APCL_e_atr8, ?L_APCL_e_atr8m, ?L_APCL_e_pgslack, ?L_APCL_e_pgslack8, ?L_APCL_e_top8, ?L_APCL_e_top, ?L_APCL_e_blk0, ?L_APCL_e_blk08, ?L_APCL_e_blkL0, ?L_APCL_e_blkL01, ?L_APCL_e_strW0, ?L_APCL_e_strW01, ?L_APCL_e_argv1w, ?L_APCL_kw_argv1, ?L_APCL_BRK_ASLR, ?L_APCL_auxw. reflexivity. Qed.

Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Lemma L_APCL_atr_entry : @atr_entry = @APC.atr_entry.
Proof. unfold atr_entry. rewrite ?L_APCL_K_RND, ?L_APCL_e_atrb. reflexivity. Qed.

Definition atr_entry_zero : kentry := KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16).
Lemma L_APCL_atr_entry_zero : @atr_entry_zero = @APC.atr_entry_zero.
Proof. unfold atr_entry_zero. rewrite ?L_APCL_e_atrb. reflexivity. Qed.

Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
Lemma L_APCL_init_kn : @init_kn = @APC.init_kn.
Proof. unfold init_kn. rewrite ?L_APCL_init_kn_with, ?L_APCL_atr_entry. reflexivity. Qed.

Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.
Lemma L_APCL_init_kn_zero : @init_kn_zero = @APC.init_kn_zero.
Proof. unfold init_kn_zero. rewrite ?L_APCL_init_kn_with, ?L_APCL_atr_entry_zero. reflexivity. Qed.

Definition init_regs : list expr := sr_upd (repeat (ELit 0) 32) 2 e_sp0.
Lemma L_APCL_init_regs : @init_regs = @APC.init_regs.
Proof. unfold init_regs. rewrite ?L_APCL_e_sp0, ?AX2L.L_AX2L_sr_upd. reflexivity. Qed.

Definition en_blk : expr := eadd (escale 8 (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W)))) (ELit 200).
Lemma L_APCL_en_blk : @en_blk = @APC.en_blk.
Proof. unfold en_blk. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_V_ARGC, ?L_APCL_V_ENVC, ?L_APCL_V_W. reflexivity. Qed.

Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (eaddz e_pgsp (-8388608), eadd (ELit 8388608) (escale 16 (EVar V_S2))); (e_vis3b, e_vis3n)].
Lemma L_APCL_init_vis : @init_vis = @APC.init_vis.
Proof. unfold init_vis. rewrite ?L_APCL_eadd, ?L_APCL_escale, ?L_APCL_eaddz, ?L_APCL_e_pgsp, ?L_APCL_V_S2, ?L_APCL_e_vis3b, ?L_APCL_e_vis3n. reflexivity. Qed.

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs :=
  ACS (mk_ss (a_entry A) init_regs kn0 NX0) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis A) []
      (vis_cost (img_hi A - img_lo A) + vis_cost 8392704 + vis_cost 4194304) (escale 4096 (EVar V_BRK)) FdStd false.
Lemma L_APCL_init_acs_of_with : @init_acs_of_with = @APC.init_acs_of_with.
Proof. unfold init_acs_of_with. rewrite ?L_APCL_MBASE_MIN, ?L_APCL_mk_ss, ?L_APCL_escale, ?L_APCL_vis_cost, ?L_APCL_V_BRK, ?L_APCL_NX0, ?L_APCL_init_regs, ?L_APCL_init_vis. reflexivity. Qed.

Definition init_acs_of (A : atable) : acs := init_acs_of_with (init_kn A) A.
Lemma L_APCL_init_acs_of : @init_acs_of = @APC.init_acs_of.
Proof. unfold init_acs_of. rewrite ?L_APCL_init_kn, ?L_APCL_init_acs_of_with. reflexivity. Qed.

Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.
Lemma L_APCL_init_acs_of_zero : @init_acs_of_zero = @APC.init_acs_of_zero.
Proof. unfold init_acs_of_zero. rewrite ?L_APCL_init_kn_zero, ?L_APCL_init_acs_of_with. reflexivity. Qed.

Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba64; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1ea4; x_imemcpy := 0xe1e28; x_memset := 0x116934; x_memcpy := 0x116530; x_memiszero := 0xe2508;
     x_istrncpy := 0xe23b8; x_sealed := 0x1205f; x_popfree := 0x52a70;
     x_sniff := 0x1414dc; sniff_tab := 0x24f40; sniff_cell := 0x14bf00;
     x_envscan := 0x10d5e4; x_envscan_k := 0x10d5f0; x_pnscan := 0x10d6a8; x_pnscan_k := 0x10d6b4;
     stops_more := [0x506e4; 0x51d08; 0xddd88; 0xee070; 0xee200];  
     zone_lo := 0x7fff7000; lowsh_hi := 0x8fff7000; highsh_lo := 0x2008fff7000; zone_hi := 0x10007fff8000 |}.
Lemma L_APCL_ASAN : @ASAN = @APC.ASAN.
Proof. unfold ASAN. reflexivity. Qed.

Definition ASAN_TEXT_LO : Z := 0x4ba64.
Lemma L_APCL_ASAN_TEXT_LO : @ASAN_TEXT_LO = @APC.ASAN_TEXT_LO.
Proof. unfold ASAN_TEXT_LO. reflexivity. Qed.

Definition ASAN_TEXT_N : nat := 252263.
Lemma L_APCL_ASAN_TEXT_N : @ASAN_TEXT_N = @APC.ASAN_TEXT_N.
Proof. unfold ASAN_TEXT_N. reflexivity. Qed.

Definition asan_init : acs := init_acs_of ASAN.
Lemma L_APCL_asan_init : @asan_init = @APC.asan_init.
Proof. unfold asan_init. rewrite ?L_APCL_init_acs_of, ?L_APCL_ASAN. reflexivity. Qed.

Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba54; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1e94; x_imemcpy := 0xe1e18; x_memset := 0x116924; x_memcpy := 0x116520; x_memiszero := 0xe24f8;
     x_istrncpy := 0xe23a8; x_sealed := 0x1205f; x_popfree := 0x52a60;
     x_sniff := 0x1414cc; sniff_tab := 0x24f40; sniff_cell := 0x14bf80;   
     x_envscan := 0x10d5d4; x_envscan_k := 0x10d5e0; x_pnscan := 0x10d698; x_pnscan_k := 0x10d6a4;
     stops_more := [0x506d4; 0x51cf8; 0xddd78; 0xee060; 0xee1f0];
     zone_lo := 0x7fff7000; lowsh_hi := 0x8fff7000; highsh_lo := 0x2008fff7000; zone_hi := 0x10007fff8000 |}.
Lemma L_APCL_BOTH : @BOTH = @APC.BOTH.
Proof. unfold BOTH. reflexivity. Qed.

Definition BOTH_TEXT_LO : Z := 0x4ba54.
Lemma L_APCL_BOTH_TEXT_LO : @BOTH_TEXT_LO = @APC.BOTH_TEXT_LO.
Proof. unfold BOTH_TEXT_LO. reflexivity. Qed.

Definition BOTH_TEXT_N : nat := 252267.
Lemma L_APCL_BOTH_TEXT_N : @BOTH_TEXT_N = @APC.BOTH_TEXT_N.
Proof. unfold BOTH_TEXT_N. reflexivity. Qed.

Definition both_init : acs := init_acs_of BOTH.
Lemma L_APCL_both_init : @both_init = @APC.both_init.
Proof. unfold both_init. rewrite ?L_APCL_init_acs_of, ?L_APCL_BOTH. reflexivity. Qed.

End APCL.
