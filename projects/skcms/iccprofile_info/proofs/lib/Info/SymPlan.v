(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExec3.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import MallocDefs.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module SP.
Import SX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record atable : Type := AT {
  t_memcpy   : Z;   (* [comment removed for export] *)
  t_memset   : Z;   (* [comment removed for export] *)
  t_strnlen  : Z;   (* [comment removed for export] *)
  t_memchr   : Z;   (* [comment removed for export] *)
  t_cas_or   : Z;   (* [comment removed for export] *)
  t_cas_or_k : Z;   (* [comment removed for export] *)
  t_cas_and  : Z;   (* [comment removed for export] *)
  t_cas_and_k : Z;
  t_cas_lock : Z;   (* [comment removed for export] *)
  t_cas_lock_k : Z;
  t_calls    : Z;   (* [comment removed for export] *)
  t_main_ret : Z;   (* [comment removed for export] *)
  t_main_join : Z;  (* [comment removed for export] *)
  t_enframe  : Z;   (* [comment removed for export] *)
  t_freepro  : Z;   (* [comment removed for export] *)
  t_freepro_k : Z;  (* [comment removed for export] *)
  t_stdio_write : Z; (* [comment removed for export] *)
  d_malloc_ctx : Z; (* [comment removed for export] *)
  d_stdout   : Z;   (* [comment removed for export] *)
  d_canary_got : Z; (* [comment removed for export] *)
  d_canary   : Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  t_printf   : Z;   (* [comment removed for export] *)
  t_printf_ret : Z; (* [comment removed for export] *)
  t_exitc    : Z;   (* [comment removed for export] *)
  d_stdout_buf : Z; (* [comment removed for export] *)
  d_stderr   : Z;   (* [comment removed for export] *)
  e_cells    : list (Z * nat * Z);  (* [comment removed for export] *)
  (* [comment removed for export] *)
  text_n     : nat; (* [comment removed for export] *)
  d_img_hi   : Z;   (* [comment removed for export] *)
  d_data_lo  : Z;   (* [comment removed for export] *)
  d_sp_lo    : Z;   (* [comment removed for export] *)
  d_sizeclasses : Z; (* [comment removed for export] *)
  t_fuzz     : Z;   (* [comment removed for export] *)
  t_fuzz_ret : Z;   (* [comment removed for export] *)
  t_fuzz_depth : Z; (* [comment removed for export] *)
  d_gfool    : Z;   (* [comment removed for export] *)
  d_fuzz_ro_lo : Z; (* [comment removed for export] *)
  d_fuzz_ro_hi : Z;
  d_empty    : Z    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition TEXT_LO : Z := 0x12000.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.        (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.        (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive shape : Type :=
| SNil                                           (* [comment removed for export] *)
| SExit (code : Z)                               (* [comment removed for export] *)
| SEmit (fd : Z) (bs : list Z) (s : shape)       (* [comment removed for export] *)
| SAlt2 (a b : shape)                            (* [comment removed for export] *)
| SCase (e : expr) (mid : Z) (s1 s2 : shape).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition salt2 (a b : shape) : shape :=
  match a, b with
  | SNil, _ => b
  | _, SNil => a
  | _, _ => SAlt2 a b
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record smap : Type := SM { sm_base : expr; sm_len : expr; sm_exact : bool }.
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sslot : Type := SL { sl_start : expr; sl_stride : expr; sl_n : expr; sl_off : expr;
                            sl_W : expr; sl_idx : Z; sl_p : expr }.

Record cstate : Type := CS {
  c_ss    : sym_state;       (* [comment removed for export] *)
  c_maps  : list smap;
  c_nmaps : Z;               (* [comment removed for export] *)
  c_live  : Z;               (* [comment removed for export] *)
  c_slots : list sslot       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition slot_keep_b (k : list kentry) (ub : expr) (uk : Z) (un : expr) (s : sslot) : bool :=
  let '(hb, hk) := split_lit (sl_start s) in
  if ranges_apart_x k ub uk un hb (hk - 4) (sl_stride s) then true
  else let '(pb, pk) := split_lit (sl_p s) in xinside k ub uk un pb pk (sl_n s).

Definition slots_keep (k : list kentry) (ub : expr) (uk : Z) (un : expr) (ss : list sslot) : list sslot :=
  List.filter (slot_keep_b k ub uk un) ss.

(* [comment removed for export] *)
Fixpoint slots_carry_ref (k : list kentry) (log : list sentry) (ss : list sslot) : list sslot :=
  match log with
  | [] => ss
  | SE (SA b o) w _ :: older => slots_keep k b o (ELit (Z.of_nat w)) (slots_carry_ref k older ss)
  end.

(* [comment removed for export] *)
Definition slot_keep_bF (fs : list sfact) (fk : list kentry) (ub : expr) (uk : Z) (un : expr) (s : sslot) : bool :=
  let '(hb, hk) := split_lit (sl_start s) in
  if ranges_apart_xF fs fk ub uk un hb (hk - 4) (sl_stride s) then true
  else let '(pb, pk) := split_lit (sl_p s) in xinsideF fs fk ub uk un pb pk (sl_n s).

Fixpoint slots_carryF (fs : list sfact) (fk : list kentry) (log : list sentry) (ss : list sslot) : list sslot :=
  match log with
  | [] => ss
  | SE (SA b o) w _ :: older => List.filter (slot_keep_bF fs fk b o (ELit (Z.of_nat w))) (slots_carryF fs fk older ss)
  end.

Definition slots_carry (k : list kentry) (log : list sentry) (ss : list sslot) : list sslot :=
  match log with
  | [] => ss
  | _ => let fk := facts_of k in slots_carryF (SFS fk) fk log ss
  end.

Lemma slot_keep_bF_eq : forall k ub uk un s,
  slot_keep_bF (SFS (facts_of k)) (facts_of k) ub uk un s = slot_keep_b k ub uk un s.
Proof.
  intros. unfold slot_keep_bF, slot_keep_b. destruct (split_lit (sl_start s)) as [hb hk].
  rewrite ranges_apart_xF_eq, ranges_apart_x_fk. destruct (ranges_apart_x k ub uk un hb (hk - 4) (sl_stride s)); [reflexivity|].
  destruct (split_lit (sl_p s)) as [pb pk]. rewrite xinsideF_eq. apply xinside_fk.
Qed.

Lemma slots_carry_eq : forall k log ss, slots_carry k log ss = slots_carry_ref k log ss.
Proof.
  intros k log ss. unfold slots_carry. destruct log as [|e older] eqn:El; [reflexivity|]. rewrite <- El. clear El e older.
  induction log as [|[[b o] w v] older IH]; [reflexivity|].
  cbn [slots_carryF slots_carry_ref]. rewrite IH. unfold slots_keep.
  apply filter_ext. intros s0. apply slot_keep_bF_eq.
Qed.

(* [comment removed for export] *)
Definition slot_apart_b (k : list kentry) (ub : expr) (uk : Z) (un : expr) (s : sslot) : bool :=
  let '(hb, hk) := split_lit (sl_start s) in ranges_apart_x k ub uk un hb (hk - 4) (sl_stride s).
Definition slots_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) (ss : list sslot) : list sslot :=
  List.filter (slot_apart_b k ub uk un) ss.

Definition scr0 : scripts := SCR [] [] [].

(* [comment removed for export] *)
Definition run_block (fuel : nat) (stops : list Z) (cs : cstate) : option cstate :=
  let ss' := sym_execT' segs IT fuel true stops (c_ss cs) in   (* [comment removed for export] *)
  match carry (s_log ss') (s_know ss') [] with
  | (kn', [], _) =>
      Some (CS (SS (s_pc ss') (s_regs ss') [] kn' (s_next ss')) (c_maps cs) (c_nmaps cs) (c_live cs)
               (slots_carry kn' (s_log ss') (c_slots cs)))
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition reg (cs : cstate) (n : nat) : expr := nth n (s_regs (c_ss cs)) (ELit 0).
Definition kn (cs : cstate) : list kentry := s_know (c_ss cs).
Definition pc (cs : cstate) : Z := s_pc (c_ss cs).

Definition set_reg (cs : cstate) (n : nat) (e : expr) : cstate :=
  let ss := c_ss cs in
  CS (SS (s_pc ss) (sr_upd (s_regs ss) n e) [] (s_know ss) (s_next ss)) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs).
Definition set_pc (cs : cstate) (p : Z) : cstate :=
  let ss := c_ss cs in
  CS (SS p (s_regs ss) [] (s_know ss) (s_next ss)) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs).
Definition set_kn (cs : cstate) (k : list kentry) : cstate :=
  let ss := c_ss cs in
  CS (SS (s_pc ss) (s_regs ss) [] k (s_next ss)) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs).
Definition set_slots (cs : cstate) (ss : list sslot) : cstate :=
  CS (c_ss cs) (c_maps cs) (c_nmaps cs) (c_live cs) ss.
Definition bump_next (cs : cstate) (d : nat) : cstate :=
  let ss := c_ss cs in
  CS (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss + d)) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs).

Definition lit_of (e : expr) : option Z := match e with ELit z => Some (z mod two64) | _ => None end.
Definition reg_lit (cs : cstate) (n : nat) : option Z := lit_of (reg cs n).

(* [comment removed for export] *)
Definition kreadZ (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookup segs k b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma kwritable_fk1 : forall allkn k b off n, kwritable (facts_of allkn) k b off n = kwritable allkn k b off n.
Proof.
  intros allkn k b off n. induction k as [|K rest IH]; [reflexivity|]. cbn [kwritable]. rewrite IH.
  destruct K as [| | | | | |[wb wk] wn|]; try reflexivity. rewrite xlo_fk, xinside_fk. reflexivity.
Qed.
Lemma kwritable_fk2 : forall allkn k b off n, kwritable allkn (facts_of k) b off n = kwritable allkn k b off n.
Proof.
  intros allkn k b off n. rewrite facts_of_filter. induction k as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (is_factb K) eqn:E.
  - cbn [kwritable]. rewrite IH. reflexivity.
  - rewrite IH. destruct K as [| | | | | |[wb wk] wn|]; try reflexivity; discriminate.
Qed.
Lemma kwritable_x_fk1 : forall allkn k b off n, kwritable_x (facts_of allkn) k b off n = kwritable_x allkn k b off n.
Proof.
  intros allkn k b off n. induction k as [|K rest IH]; [reflexivity|]. cbn [kwritable_x]. rewrite IH.
  destruct K as [| | | | | |[wb wk] wn|]; try reflexivity. rewrite xhi_fk, xlo_fk, xinside_fk. reflexivity.
Qed.
Lemma kwritable_x_fk2 : forall allkn k b off n, kwritable_x allkn (facts_of k) b off n = kwritable_x allkn k b off n.
Proof.
  intros allkn k b off n. rewrite facts_of_filter. induction k as [|K rest IH]; [reflexivity|].
  cbn [List.filter]. destruct (is_factb K) eqn:E.
  - cbn [kwritable_x]. rewrite IH. reflexivity.
  - rewrite IH. destruct K as [| | | | | |[wb wk] wn|]; try reflexivity; discriminate.
Qed.

(* [comment removed for export] *)
Definition IMG_SZ : Z := d_img_hi A - 0x10000.   (* [comment removed for export] *)
Definition off_image (k : list kentry) (b : expr) (off n : Z) : bool :=
  let fk := facts_of k in ranges_apartF (SFS fk) fk b off n (ELit 0) 0x10000 IMG_SZ.
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  let fk := facts_of k in ranges_apart_xF (SFS fk) fk b off n (ELit 0) 0x10000 (ELit IMG_SZ).
Lemma off_image_eq : forall k b off n, off_image k b off n = ranges_apart k b off n (ELit 0) 0x10000 IMG_SZ.
Proof. intros. unfold off_image. rewrite ranges_apartF_eq. apply ranges_apart_fk. Qed.
Lemma off_image_x_eq : forall k b off n, off_image_x k b off n = ranges_apart_x k b off n (ELit 0) 0x10000 (ELit IMG_SZ).
Proof. intros. unfold off_image_x. rewrite ranges_apart_xF_eq. apply ranges_apart_x_fk. Qed.

(* [comment removed for export] *)
Definition lin_inside (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapR kn b1 && lin_nowrapR kn b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_test kn (fst l1 + k1 - fst l2 - k2)%Z (lsub_e (snd l1) (snd l2))
            (fun lo hi => (Z.leb 0 lo && Z.leb (hi + n1) n2)%bool))%bool.

(* [comment removed for export] *)
Definition flat_b (k : list kentry) (b : expr) (off n : Z) : bool :=
  match base_range (facts_of k) b with
  | Some (lo, hi) => (Z.leb 0 (lo + off) && Z.leb (hi + off + n) two64 && Z.ltb 0 n)%bool
  | None => false
  end.

(* [comment removed for export] *)
Definition ehi (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)
  | _ => match erange k e with Some (_, hi) => Some hi | None => None end
  end.
Definition elo (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)
  | _ => match erange k e with Some (lo, _) => Some lo | None => None end
  end.

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
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
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
  end.
Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition maps_vars_lt (b : nat) (ms : list smap) : bool :=
  forallb (fun m => expr_vars_lt b (sm_base m) && expr_vars_lt b (sm_len m)) ms.
(* [comment removed for export] *)
Definition slot_vars_lt (b : nat) (s : sslot) : bool :=
  (expr_vars_lt b (sl_start s) && expr_vars_lt b (sl_stride s) && expr_vars_lt b (sl_n s) && expr_vars_lt b (sl_off s)
   && expr_vars_lt b (sl_W s) && expr_vars_lt b (sl_p s))%bool.
Definition slots_vars_lt (b : nat) (ss : list sslot) : bool := forallb (slot_vars_lt b) ss.
Definition fresh_ok (cs : cstate) : bool :=
  let ss := c_ss cs in let v := s_next ss in
  (sr_vars_lt v (s_regs ss) && kn_vars_lt v (s_know ss) && maps_vars_lt v (c_maps cs) && slots_vars_lt v (c_slots cs) && Nat.leb nx0 v)%bool.

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
  end.

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
  end.

(* [comment removed for export] *)
Definition kimg_b (K : kentry) : bool := match K with KImg _ _ => true | _ => false end.
Definition kn_unfill_ref (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in   (* [comment removed for export] *)
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

(* [comment removed for export] *)
Definition kentry_apartF (fk : list kentry) (si : sinfo) (K : kentry) (cc : ccache) (st : scache)
  : bool * ccache * scache :=
  match K with
  | KWord (SA b k) w _ =>
      if Nat.leb w 8 then apartf fk si b k (ELit (Z.of_nat w)) cc st else (false, cc, st)
  | KZero (SA b k) l => apartf fk si b k l cc st
  | KBlob (SA b k) l _ => apartf fk si b k l cc st
  | KImg lo hi =>
      if (Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64)%bool then apartf fk si (ELit 0) lo (ELit (hi - lo)) cc st
      else (false, cc, st)
  | KAlign _ _ => (true, cc, st)
  | KRange _ _ _ => (true, cc, st)
  | KDisj _ _ _ _ => (true, cc, st)
  | KWr (SA b k) n => apartf fk si b k n cc st
  end.

(* [comment removed for export] *)
Definition apart_setup (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry * sinfo * ccache :=
  let fk := facts_of k in let fs := SFS fk in
  let '(ci1, cc) := cc_get fk (CC (kdisj_sdis fs fk fk) fs [] []) ub in
  (fk, mk_si fs fk ub uk un ci1, cc).

Fixpoint unfillF (fk : list kentry) (si : sinfo) (kn : list kentry) (cc : ccache) (st : scache) : list kentry :=
  match kn with
  | [] => []
  | K :: rest =>
      if kimg_b K then K :: unfillF fk si rest cc st
      else let '(ap, cc', st') := kentry_apartF fk si K cc st in
           if ap then K :: unfillF fk si rest cc' st' else unfillF fk si rest cc' st'
  end.

Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let '(fk, si, cc) := apart_setup k ub uk un in unfillF fk si k cc (ST [] None).

(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
(* [comment removed for export] *)
Definition havoc1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_b k ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | _ => []
       end.
(* [comment removed for export] *)
Definition havoc1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
  if (kwr_b K || kentry_apart_bp k sp ub uk un K)%bool then [K]
  else match K with
       | KZero (SA kb kk) len => kzero_cut k ub uk un kb kk len
       | _ => []
       end.

Lemma kentry_apart_bp_eq0 : forall allkn ub uk un K,
  kentry_apart_bp allkn (mk_sprep allkn ub uk un) ub uk un K = kentry_apart_b allkn ub uk un K.
Proof.
  intros allkn ub uk un K.
  destruct K as [[b k] w v|[b k] l|[b k] l bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2]; cbn [kentry_apart_bp kentry_apart_b];
    rewrite ?p5_ranges_apart_p_eq; reflexivity.
Qed.

Lemma havoc1p_eq0 : forall k ub uk un K,
  havoc1p k (mk_sprep k ub uk un) ub uk un K = havoc1 k ub uk un K.
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq0. reflexivity. Qed.

Definition kn_havoc_ref (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in   (* [comment removed for export] *)
  List.flat_map (havoc1p k sp ub uk un) k.

(* [comment removed for export] *)
Fixpoint havocF (fk : list kentry) (si : sinfo) (ub : expr) (uk : Z) (un : expr) (kn : list kentry) (cc : ccache) (st : scache)
  : list kentry :=
  match kn with
  | [] => []
  | K :: rest =>
      if kwr_b K then K :: havocF fk si ub uk un rest cc st
      else let '(ap, cc', st') := kentry_apartF fk si K cc st in
           if ap then K :: havocF fk si ub uk un rest cc' st'
           else match K with
                | KZero (SA kb kk) len => kzero_cut fk ub uk un kb kk len ++ havocF fk si ub uk un rest cc' st'
                | _ => havocF fk si ub uk un rest cc' st'
                end
  end.

Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let '(fk, si, cc) := apart_setup k ub uk un in havocF fk si ub uk un k cc (ST [] None).

(* [comment removed for export] *)
Lemma kentry_apartF_eq : forall k ub uk un K cc st,
  pcc_ok (facts_of k) cc -> pst_ok (facts_of k) (si_of (facts_of k) ub uk un) st ->
  let '(r, cc', st') := kentry_apartF (facts_of k) (si_of (facts_of k) ub uk un) K cc st in
  r = kentry_apart_b k ub uk un K /\ pcc_ok (facts_of k) cc' /\ pst_ok (facts_of k) (si_of (facts_of k) ub uk un) st'.
Proof.
  intros k ub uk un K cc st Hcc Hst.
  assert (AP : forall b2 k2 n2, let '(r, cc', st') := apartf (facts_of k) (si_of (facts_of k) ub uk un) b2 k2 n2 cc st in
            r = ranges_apart_x k ub uk un b2 k2 n2 /\ pcc_ok (facts_of k) cc' /\ pst_ok (facts_of k) (si_of (facts_of k) ub uk un) st').
  { intros b2 k2 n2. pose proof (apartf_eq (facts_of k) ub uk un b2 k2 n2 cc st Hcc Hst) as HA. cbv zeta in HA.
    rewrite ranges_apart_x_fk in HA. exact HA. }
  unfold kentry_apartF, kentry_apart_b.
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2]; try apply AP;
    try exact (conj eq_refl (conj Hcc Hst)).
  - destruct (Nat.leb w 8); [apply AP | exact (conj eq_refl (conj Hcc Hst))].
  - destruct (Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64)%bool; [|exact (conj eq_refl (conj Hcc Hst))].
    cbn [andb]. apply AP.
Qed.

Lemma apart_setup_ok : forall k ub uk un,
  let '(fk, si, cc) := apart_setup k ub uk un in
  fk = facts_of k /\ si = si_of fk ub uk un /\ pcc_ok fk cc /\ pst_ok fk si (ST [] None).
Proof.
  intros k ub uk un. unfold apart_setup.
  assert (H0 : pcc_ok (facts_of k) (CC (kdisj_sdis (SFS (facts_of k)) (facts_of k) (facts_of k)) (SFS (facts_of k)) [] [])).
  { split; [split; reflexivity|]. split; intros ? ? H; discriminate. }
  pose proof (cc_get_ok (facts_of k) _ ub H0) as [G1 G2].
  destruct (cc_get (facts_of k) (CC (kdisj_sdis (SFS (facts_of k)) (facts_of k) (facts_of k)) (SFS (facts_of k)) [] []) ub) as [ci1 cc]. cbn [fst snd] in G1, G2.
  subst ci1. split; [reflexivity|]. split; [reflexivity|]. split; [exact G2|].
  split; [intros b e H; discriminate | intros m H; discriminate].
Qed.

Lemma kn_unfill_eq : forall k ub uk un, kn_unfill k ub uk un = kn_unfill_ref k ub uk un.
Proof.
  intros k ub uk un. unfold kn_unfill, kn_unfill_ref.
  pose proof (apart_setup_ok k ub uk un) as S. destruct (apart_setup k ub uk un) as [[fk si] cc].
  destruct S as (Hfk & Hsi & Hcc & Hst). subst si fk.
  assert (GEN : forall kn0 cc0 st0, pcc_ok (facts_of k) cc0 -> pst_ok (facts_of k) (si_of (facts_of k) ub uk un) st0 ->
            unfillF (facts_of k) (si_of (facts_of k) ub uk un) kn0 cc0 st0 = List.filter (fun K => kimg_b K || kentry_apart_bp k (mk_sprep k ub uk un) ub uk un K) kn0).
  { induction kn0 as [|K rest IH]; intros cc0 st0 Hc Hs; [reflexivity|]. cbn [unfillF List.filter].
    rewrite kentry_apart_bp_eq0.
    destruct (kimg_b K); cbn [orb]; [rewrite (IH cc0 st0 Hc Hs); reflexivity|].
    pose proof (kentry_apartF_eq k ub uk un K cc0 st0 Hc Hs) as E. cbv zeta in E. destruct (kentry_apartF (facts_of k) (si_of (facts_of k) ub uk un) K cc0 st0) as [[r cc'] st']. destruct E as (-> & Hc' & Hs').
    rewrite (IH cc' st' Hc' Hs'). reflexivity. }
  apply GEN; assumption.
Qed.

Lemma kn_havoc_eq : forall k ub uk un, kn_havoc k ub uk un = kn_havoc_ref k ub uk un.
Proof.
  intros k ub uk un. unfold kn_havoc, kn_havoc_ref.
  pose proof (apart_setup_ok k ub uk un) as S. destruct (apart_setup k ub uk un) as [[fk si] cc].
  destruct S as (Hfk & Hsi & Hcc & Hst). subst si fk.
  assert (GEN : forall kn0 cc0 st0, pcc_ok (facts_of k) cc0 -> pst_ok (facts_of k) (si_of (facts_of k) ub uk un) st0 ->
            havocF (facts_of k) (si_of (facts_of k) ub uk un) ub uk un kn0 cc0 st0 = List.flat_map (havoc1p k (mk_sprep k ub uk un) ub uk un) kn0).
  { induction kn0 as [|K rest IH]; intros cc0 st0 Hc Hs; [reflexivity|]. cbn [havocF List.flat_map].
    rewrite havoc1p_eq0. unfold havoc1.
    destruct (kwr_b K); cbn [orb]; [rewrite (IH cc0 st0 Hc Hs); reflexivity|].
    pose proof (kentry_apartF_eq k ub uk un K cc0 st0 Hc Hs) as E. cbv zeta in E. destruct (kentry_apartF (facts_of k) (si_of (facts_of k) ub uk un) K cc0 st0) as [[r cc'] st']. destruct E as (-> & Hc' & Hs').
    rewrite (IH cc' st' Hc' Hs').
    destruct (kentry_apart_b k ub uk un K); [reflexivity|].
    destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2]; try reflexivity.
    rewrite kzero_cut_fk. reflexivity. }
  apply GEN; assumption.
Qed.

Fixpoint kn_havocs (k : list kentry) (rs : list (expr * Z * expr)) : list kentry :=
  match rs with
  | [] => k
  | (b, off, n) :: rest => kn_havocs (kn_havoc k b off n) rest
  end.

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fffff800000.

Definition stack_based (b : expr) (off : Z) : bool :=
  match b with
  | EVar 0 => Z.leb (-8388608) off
  | _ => false
  end.

(* [comment removed for export] *)
Definition SPBAND_LO : Z := 0x7fff7f800000.

(* [comment removed for export] *)
Definition sp_frame_ok (sp : expr) (fr : Z) : bool :=
  match split_lit sp with
  | (EVar 0, c) => Z.leb (-8388608 + fr) c && Z.leb c 0
  | _ => false
  end.

(* [comment removed for export] *)
Definition below_band (k : list kentry) (b : expr) (o : Z) (n : Z) (hi : Z) : bool :=
  kdisj_apart_x k k b o (ELit n) (EVar 0) (-8388608) (ELit 0x800000000000)
  && (hi + o + n <=? SPBAND_LO + 0x800000000000).

(* [comment removed for export] *)
Definition below_band_x (k : list kentry) (b : expr) (o : Z) (n : expr) (shi nhi : Z) : bool :=
  kdisj_apart_x k k b o n (EVar 0) (-8388608) (ELit 0x800000000000)
  && (shi + nhi <=? SPBAND_LO + 0x800000000000).

(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list smap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest =>
      (match len, sm_len m with
       | ELit l, ELit ml => lin_inside k b off (l mod two64) (sm_base m) 0 (ml mod two64)
       | _, _ => xinside k b off len (sm_base m) 0 (sm_len m)
       end)
      || inside_maps k rest b off len
  end.

Definition safe_range (k : list kentry) (ms : list smap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len with
    | Some lh =>
       match erange k b with
       | Some (lo, hi) => (stack_based b off && Z.leb (hi + off + lh) two64)      (* [comment removed for export] *)
                          || (Z.leb 0x10000 (lo + off) && Z.leb (hi + off + lh) (d_img_hi A))  (* [comment removed for export] *)
                          || (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) 0x1000)      (* [comment removed for export] *)
       | None => false
       end
    | None => false
    end) || inside_maps k ms b off len)%bool.

Definition grant_keep_b (k : list kentry) (ms : list smap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_range k ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_range k ms b o l
  | KBlob (SA b o) l _ => safe_range k ms b o l
  | KImg lo hi => (Z.leb 0 lo && Z.leb hi 0x1000) || (Z.leb 0x10000 lo && Z.leb hi (d_img_hi A))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_range k ms b o n
  end.

(* [comment removed for export] *)
Definition lin_insideF (fs : list sfact) (fk : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if lin_nowrapRF fs fk b1 then
    if lin_nowrapRF fs fk b2 then
      let l1 := lin_of b1 in let l2 := lin_of b2 in
      lin_testF fs fk (fst l1 + k1 - fst l2 - k2)%Z (lsub_e (snd l1) (snd l2))
                (fun lo hi => (Z.leb 0 lo && Z.leb (hi + n1) n2)%bool)
    else false
  else false.

Fixpoint inside_mapsF (fs : list sfact) (fk : list kentry) (ms : list smap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest =>
      if (match len, sm_len m with
          | ELit l, ELit ml => lin_insideF fs fk b off (l mod two64) (sm_base m) 0 (ml mod two64)
          | _, _ => xinsideF fs fk b off len (sm_base m) 0 (sm_len m)
          end) then true
      else inside_mapsF fs fk rest b off len
  end.

Definition safe_rangeF (fs : list sfact) (fk : list kentry) (ms : list smap) (b : expr) (off : Z) (len : expr) : bool :=
  if (match xhiF fs fk len with
      | Some lh =>
         match erange fk b with
         | Some (lo, hi) => if (stack_based b off && Z.leb (hi + off + lh) two64)%bool then true
                            else if (Z.leb 0x10000 (lo + off) && Z.leb (hi + off + lh) (d_img_hi A))%bool then true
                            else (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) 0x1000)%bool
         | None => false
         end
      | None => false
      end) then true
  else inside_mapsF fs fk ms b off len.

Definition grant_keep_bF (fs : list sfact) (fk : list kentry) (ms : list smap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => if Nat.leb w 8 then safe_rangeF fs fk ms b o (ELit (Z.of_nat w)) else false
  | KZero (SA b o) l => safe_rangeF fs fk ms b o l
  | KBlob (SA b o) l _ => safe_rangeF fs fk ms b o l
  | KImg lo hi => (Z.leb 0 lo && Z.leb hi 0x1000) || (Z.leb 0x10000 lo && Z.leb hi (d_img_hi A))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_rangeF fs fk ms b o n
  end%bool.

Definition kn_grant_filter (k : list kentry) (ms : list smap) : list kentry :=
  let fk := facts_of k in let fs := SFS fk in
  List.filter (grant_keep_bF fs fk ms) k.

(* [comment removed for export] *)
Definition slots_grant_filter (k : list kentry) (ms : list smap) (ss : list sslot) : list sslot :=
  let fk := facts_of k in let fs := SFS fk in
  List.filter (fun s => let '(hb, hk) := split_lit (sl_start s) in safe_rangeF fs fk ms hb (hk - 4) (sl_stride s)) ss.

Lemma lin_insideF_eq : forall k b1 k1 n1 b2 k2 n2,
  lin_insideF (SFS (facts_of k)) (facts_of k) b1 k1 n1 b2 k2 n2 = lin_inside k b1 k1 n1 b2 k2 n2.
Proof.
  intros. unfold lin_insideF, lin_inside. rewrite !lin_nowrapRF_eq, !lin_nowrapR_fk, lin_testF_eq, lin_test_fk.
  destruct (lin_nowrapR k b1), (lin_nowrapR k b2); reflexivity.
Qed.

Lemma inside_mapsF_eq : forall k ms b off len,
  inside_mapsF (SFS (facts_of k)) (facts_of k) ms b off len = inside_maps k ms b off len.
Proof.
  intros k ms b off len. induction ms as [|m rest IH]; [reflexivity|]. cbn [inside_mapsF inside_maps].
  rewrite IH.
  destruct len; destruct (sm_len m); rewrite ?xinsideF_eq, ?xinside_fk, ?lin_insideF_eq;
    match goal with |- (if ?c then true else ?r) = (?c || ?r)%bool => destruct c; reflexivity end.
Qed.

Lemma safe_rangeF_eq : forall k ms b off len,
  safe_rangeF (SFS (facts_of k)) (facts_of k) ms b off len = safe_range k ms b off len.
Proof.
  intros. unfold safe_rangeF, safe_range. rewrite xhiF_eq, xhi_fk, erange_fk, inside_mapsF_eq.
  destruct (xhi k len) as [lh|]; [|reflexivity]. destruct (erange k b) as [[lo hi]|]; [|reflexivity].
  destruct (stack_based b off && Z.leb (hi + off + lh) two64)%bool; [reflexivity|].
  destruct (Z.leb 0x10000 (lo + off) && Z.leb (hi + off + lh) (d_img_hi A))%bool; [reflexivity|].
  destruct (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) 0x1000)%bool; reflexivity.
Qed.

Lemma grant_keep_bF_eq : forall k ms K,
  grant_keep_bF (SFS (facts_of k)) (facts_of k) ms K = grant_keep_b k ms K.
Proof.
  intros. destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2];
    cbn [grant_keep_bF grant_keep_b]; rewrite ?safe_rangeF_eq; try reflexivity;
    destruct (Nat.leb w 8); reflexivity.
Qed.

Lemma kn_grant_filter_eq : forall k ms, kn_grant_filter k ms = List.filter (grant_keep_b k ms) k.
Proof. intros. unfold kn_grant_filter. apply filter_ext. intros K. apply grant_keep_bF_eq. Qed.

Lemma slots_grant_filter_eq : forall k ms ss,
  slots_grant_filter k ms ss
  = List.filter (fun s => let '(hb, hk) := split_lit (sl_start s) in safe_range k ms hb (hk - 4) (sl_stride s)) ss.
Proof.
  intros. unfold slots_grant_filter. apply filter_ext. intros s0. destruct (split_lit (sl_start s0)). apply safe_rangeF_eq.
Qed.

(* [comment removed for export] *)
Definition kn_mmap (v : nat) (n : expr) (nlo : Z) (ms : list smap) : list kentry :=
  [KRange (EVar v) 0x1000 (CEIL - nlo); KAlign (EVar v) 4096;
   KWr (SA (EVar v) 0) n; KZero (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) (ELit IMG_SZ) (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) (ELit 0x800000000000) (SA (EVar v) 0) n]   (* [comment removed for export] *)
  ++ map (fun m => KDisj (SA (sm_base m) 0) (sm_len m) (SA (EVar v) 0) n) ms.

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

(* [comment removed for export] *)
Definition after_call (cs : cstate) (ret : Z) (rv : option expr) (k' : list kentry) : option cstate :=
  let ss := c_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt nx k' && match rv with Some e => expr_vars_lt nx e | None => true end
      && Nat.ltb 0 nx)%bool
  then Some (CS (SS ret sr2 [] k' (nx + NCS)) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive summary : Type := SumMemcpy | SumFuzz | SumEnframe | SumFreePro | SumMainRet | SumPrintf.

Inductive cas_site : Type := CasOr | CasAnd | CasLock.

Inductive plan : Type :=
| PMmap (kfail ksucc : plan)         (* [comment removed for export] *)
| PMunmap (k : plan)
| PIoctl (k : plan)                  (* [comment removed for export] *)
| PStdioWrite (k : plan)             (* [comment removed for export] *)
| PExit                              (* [comment removed for export] *)
| PResume (k : plan)                 (* [comment removed for export] *)
| PCall (f : summary) (args : list expr) (k : plan)   (* [comment removed for export] *)
| PCas (c : cas_site) (k : plan)
| PSplit (e : expr) (mid : Z) (k1 k2 : plan)   (* [comment removed for export] *)
| PContra                            (* [comment removed for export] *)
| PExitCall.                         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_up (len : Z) : Z := ((len + 4095) / 4096) * 4096.

Definition is_ecall_at (cs : cstate) : bool :=
  (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 &&
  match fetch_word segs (Z_to_bv 64 (pc cs)) with
  | Some w => is_ecall w
  | None => false
  end)%bool.

(* [comment removed for export] *)
Definition page_up_e (e : expr) : expr :=
  mkAlu ALU_SLL (mkAlu ALU_SRL (mkAlu ALU_ADD e (ELit 4095)) (ELit 12)) (ELit 12).

(* [comment removed for export] *)
Definition mmap_len (cs : cstate) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => Some (ELit (page_up len), len, page_up len)
  | None =>
      let le := reg cs 11 in
      let ne0 := page_up_e le in
      (* [comment removed for export] *)
      let ne := match foldK (kn cs) ne0 with ELit z => ELit z | _ => ne0 end in
      match xlo (kn cs) le, xhi (kn cs) le, xhi (kn cs) ne with
      | Some lo, Some lhi, Some nhi =>
          if (Z.leb (lhi + 4095) (2 ^ 40) && expr_vars_lt (s_next (c_ss cs)) ne)%bool
          then Some (ne, lo, nhi) else None
      | _, _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition node_mmap (cs : cstate) : option (cstate * cstate) :=
  match reg_lit cs 17, reg_lit cs 10, mmap_len cs, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some 0, Some (ne, lo, nhi), Some 3, Some 34, Some m1, Some 0 =>
      if (Z.ltb 0 lo && Z.leb nhi (2 ^ 30) && Z.eqb m1 (two64 - 1)
          && Z.leb (c_nmaps cs + 1) 1000 && Z.leb (c_live cs + nhi) (2 ^ 31) && fresh_ok cs
          && Nat.ltb 0 (s_next (c_ss cs)))%bool then
        let v := s_next (c_ss cs) in
        let csf := set_pc (set_reg cs 10 (ELit (two64 - 12))) (pc cs + 4) in
        let ss := c_ss cs in
        let css := CS (SS (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) []
                          (kn_grant_filter (s_know ss) (c_maps cs) ++ kn_mmap v ne (page_up lo) (c_maps cs)) (S v))
                      (SM (EVar v) ne true :: c_maps cs) (c_nmaps cs + 1) (c_live cs + nhi)
                      (slots_grant_filter (s_know ss) (c_maps cs) (c_slots cs)) in
        Some (csf, css)
      else None
  | _, _, _, _, _, _, _ => None
  end.


(* [comment removed for export] *)
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (let fk := facts_of k in let fs := SFS fk in
                   if lin_ge0F fs fk [(n, 0%Z)] [(m, 0%Z)] then lin_ge0F fs fk [(m, 0%Z)] [(n, 0%Z)] else false).
Lemma len_eqb_eq : forall k n m,
  len_eqb k n m = (expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]))%bool.
Proof. intros. unfold len_eqb. rewrite !lin_ge0F_eq, !lin_ge0_fk. destruct (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)]); reflexivity. Qed.

Definition smap_match (k : list kentry) (b : expr) (n : expr) (m : smap) : bool :=
  (sm_exact m && expr_eqb b (sm_base m) && len_eqb k n (sm_len m))%bool.

Definition remove_exact (k : list kentry) (ms : list smap) (b : expr) (n : expr) : list smap :=
  List.filter (fun m => negb (smap_match k b n m)) ms.

(* [comment removed for export] *)
Definition others_apart (k : list kentry) (ms : list smap) (b : expr) (n : expr) : bool :=
  let fk := facts_of k in let fs := SFS fk in
  forallb (fun m => if smap_match k b n m then true else ranges_apart_xF fs fk b 0 n (sm_base m) 0 (sm_len m)) ms.
Lemma others_apart_eq : forall k ms b n,
  others_apart k ms b n = forallb (fun m => smap_match k b n m || ranges_apart_x k b 0 n (sm_base m) 0 (sm_len m)) ms.
Proof.
  intros. unfold others_apart. induction ms as [|m rest IH]; [reflexivity|]. cbn [forallb]. rewrite IH.
  rewrite ranges_apart_xF_eq, ranges_apart_x_fk. destruct (smap_match k b n m); reflexivity.
Qed.

(* [comment removed for export] *)
Definition munmap_len (cs : cstate) : option (expr * Z) :=
  match reg_lit cs 11 with
  | Some len => if (Z.ltb 0 len && Z.leb (page_up len) (2 ^ 40))%bool then Some (ELit (page_up len), page_up len) else None
  | None =>
      let le := reg cs 11 in
      match xlo (kn cs) le, xhi (kn cs) le with
      | Some lo, Some hi => if (Z.ltb 0 lo && Z.leb 12 (ealign (kn cs) le))%bool then Some (le, hi) else None
      | _, _ => None
      end
  end.

Definition node_munmap (cs : cstate) : option cstate :=
  match reg_lit cs 17, munmap_len cs with
  | Some 215, Some (n, nhi) =>
      let b := reg cs 10 in
      if (Z.leb nhi (2 ^ 30) && existsb (smap_match (kn cs) b n) (c_maps cs)
          && Z.leb 12 (ealign (kn cs) b) && others_apart (kn cs) (c_maps cs) b n
          && match ehi (kn cs) b with
             | Some hi => Z.leb (hi + nhi) 0x800000000000 || below_band_x (kn cs) b 0 n hi nhi
             | None => false end)%bool then
        (* [comment removed for export] *)
        let ss := c_ss cs in
        Some (CS (SS (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) []
                     (kn_unfill (s_know ss) b 0 n) (s_next ss))
                 (remove_exact (kn cs) (c_maps cs) b n) (c_nmaps cs) (c_live cs)
                 (slots_unfill (s_know ss) b 0 n (c_slots cs)))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_ioctl (cs : cstate) : option cstate :=
  match reg_lit cs 17, reg_lit cs 10, reg_lit cs 11 with
  | Some 29, Some 1, Some 0x5413 => Some (set_pc (set_reg cs 10 (ELit (two64 - 25))) (pc cs + 4))
  | _, _, _ => None
  end.

Definition node_exit (cs : cstate) : option Z :=
  match reg_lit cs 17, reg_lit cs 10 with
  | Some 94, Some code => Some (Z.land code 255)
  | Some 93, Some code => Some (Z.land code 255)
  | _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cas_core (cs : cstate) (ra : nat) (compute : expr -> option expr)
           (setregs : expr -> expr -> list expr -> list expr) (pc' : Z) : option cstate :=
  let '(b, k) := split_lit (reg cs ra) in
  if (Z.leb 2 (ealign (kn cs) (reg cs ra)) && flat_b (kn cs) b k 4 && kwritable (kn cs) (kn cs) b k 4)%bool then
    match know_lookup segs (kn cs) b k 4 true [] [] with
    | LHit ve [] _ =>
        let old := extK (kn cs) ve in
        match compute old with
        | Some new =>
            match carry [SE (SA b k) 4 new] (kn cs) [] with
            | (kn', [], _) =>
                Some (CS (SS pc' (setregs old new (s_regs (c_ss cs))) [] kn' (s_next (c_ss cs)))
                        (c_maps cs) (c_nmaps cs) (c_live cs) (slots_carry kn' [SE (SA b k) 4 new] (c_slots cs)))
            | _ => None
            end
        | None => None
        end
    | _ => None
    end
  else None.

(* [comment removed for export] *)
Definition cas_or (cs : cstate) : option cstate :=
  cas_core cs 14 (fun old => Some (mkAluK (kn cs) ALU_OR old (reg cs 11)))
    (fun old new sr => sr_upd (sr_upd (sr_upd (sr_upd sr 10 old) 12 new) 13 old) 15 (ELit 0)) (t_cas_or_k A).

(* [comment removed for export] *)
Definition cas_and (cs : cstate) : option cstate :=
  cas_core cs 12 (fun old => Some (mkAluK (kn cs) ALU_AND old (reg cs 13)))
    (fun old new sr => sr_upd (sr_upd (sr_upd (sr_upd sr 14 old) 15 new) 16 old) 17 (ELit 0)) (t_cas_and_k A).

(* [comment removed for export] *)
Definition cas_lock (cs : cstate) : option cstate :=
  cas_core cs 13 (fun old => if (expr_eqb old (ELit 0) && expr_eqb (reg cs 11) (ELit 0))%bool then Some (reg cs 12) else None)
    (fun old new sr => sr_upd (sr_upd sr 14 (ELit 0)) 15 (ELit 0)) (t_cas_lock_k A).

Definition node_cas (c : cas_site) (cs : cstate) : option cstate :=
  match c with
  | CasOr => if Z.eqb (pc cs) (t_cas_or A) then cas_or cs else None
  | CasAnd => if Z.eqb (pc cs) (t_cas_and A) then cas_and cs else None
  | CasLock => if Z.eqb (pc cs) (t_cas_lock A) then cas_lock cs else None
  end.

(* [comment removed for export] *)

Definition ret_lit (cs : cstate) : option Z :=
  match reg cs 1 with ELit r => if (Z.eqb (r mod 2) 0 && Z.ltb r two64 && Z.leb 0 r)%bool then Some r else None | _ => None end.

(* [comment removed for export] *)
Definition rw_ok (k : list kentry) (e : expr) (n : Z) : bool :=
  let fk := facts_of k in
  let '(b, off) := split_lit e in
  (if kwritable fk fk b off n then off_image fk b off n else false)%bool.
(* [comment removed for export] *)
Definition rw_ok_x (k : list kentry) (e : expr) (n : expr) : bool :=
  let fk := facts_of k in
  let '(b, off) := split_lit e in
  (match xlo fk n with Some l => Z.ltb 0 l | None => false end
   && (if kwritable_x fk fk b off n then off_image_x fk b off n else false))%bool.
Lemma rw_ok_eq : forall k e n,
  rw_ok k e n = (let '(b, off) := split_lit e in (kwritable k k b off n && off_image k b off n))%bool.
Proof.
  intros. unfold rw_ok. destruct (split_lit e) as [b off]. rewrite kwritable_fk1, kwritable_fk2.
  unfold off_image. rewrite facts_of_idem. destruct (kwritable k k b off n); reflexivity.
Qed.
Lemma rw_ok_x_eq : forall k e n,
  rw_ok_x k e n = (let '(b, off) := split_lit e in
                   (match xlo k n with Some l => Z.ltb 0 l | None => false end
                    && kwritable_x k k b off n && off_image_x k b off n))%bool.
Proof.
  intros. unfold rw_ok_x. destruct (split_lit e) as [b off]. rewrite xlo_fk, kwritable_x_fk1, kwritable_x_fk2.
  unfold off_image_x. rewrite facts_of_idem. destruct (xlo k n) as [l|]; [|reflexivity].
  destruct (Z.ltb 0 l), (kwritable_x k k b off n); reflexivity.
Qed.

(* [comment removed for export] *)
Definition apart_e (k : list kentry) (e1 : expr) (n1 : Z) (e2 : expr) (n2 : Z) : bool :=
  let fk := facts_of k in
  let '(b1, o1) := split_lit e1 in let '(b2, o2) := split_lit e2 in
  ranges_apartF (SFS fk) fk b1 o1 n1 b2 o2 n2.
Definition apart_x (k : list kentry) (e1 : expr) (n1 : expr) (e2 : expr) (n2 : expr) : bool :=
  let fk := facts_of k in
  let '(b1, o1) := split_lit e1 in let '(b2, o2) := split_lit e2 in
  ranges_apart_xF (SFS fk) fk b1 o1 n1 b2 o2 n2.
Lemma apart_e_eq : forall k e1 n1 e2 n2,
  apart_e k e1 n1 e2 n2 = (let '(b1, o1) := split_lit e1 in let '(b2, o2) := split_lit e2 in ranges_apart k b1 o1 n1 b2 o2 n2).
Proof. intros. unfold apart_e. destruct (split_lit e1), (split_lit e2). rewrite ranges_apartF_eq. apply ranges_apart_fk. Qed.
Lemma apart_x_eq : forall k e1 n1 e2 n2,
  apart_x k e1 n1 e2 n2 = (let '(b1, o1) := split_lit e1 in let '(b2, o2) := split_lit e2 in ranges_apart_x k b1 o1 n1 b2 o2 n2).
Proof. intros. unfold apart_x. destruct (split_lit e1), (split_lit e2). rewrite ranges_apart_xF_eq. apply ranges_apart_x_fk. Qed.

Definition havoc_e (k : list kentry) (e : expr) (n : Z) : list kentry :=
  let '(b, o) := split_lit e in kn_havoc k b o (ELit n).
Definition havoc_x (k : list kentry) (e : expr) (n : expr) : list kentry :=
  let '(b, o) := split_lit e in kn_havoc k b o n.

(* [comment removed for export] *)
Definition call_memcpy (cs : cstate) : option cstate :=
  match ret_lit cs, ehi (kn cs) (reg cs 12) with
  | Some ret, Some nhi =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      if (Z.ltb 0 nhi && Z.leb nhi (2 ^ 40) && rw_ok_x (kn cs) dst ne && rw_ok_x (kn cs) src ne && apart_x (kn cs) dst ne src ne
          && match ehi (kn cs) dst, ehi (kn cs) src with
             | Some dh, Some sh => Z.ltb (dh + nhi) two64 && Z.ltb (sh + nhi) two64 | _, _ => false end)%bool
      then match after_call cs ret (Some dst) (havoc_x (kn cs) dst ne) with
           | Some cs' => let '(db, dk) := split_lit dst in Some (set_slots cs' (slots_keep (kn cs) db dk ne (c_slots cs)))
           | None => None
           end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kread8e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Definition kimg_covers (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg a b => Z.leb a lo && Z.leb hi b | _ => false end) k.

(* [comment removed for export] *)
Definition rw_okb (k : list kentry) (b : expr) (off n : Z) : bool :=
  let fk := facts_of k in
  (if kwritable fk fk b off n then off_image fk b off n else false)%bool.
Lemma rw_okb_eq : forall k b off n, rw_okb k b off n = (kwritable k k b off n && off_image k b off n)%bool.
Proof.
  intros. unfold rw_okb. rewrite kwritable_fk1, kwritable_fk2. unfold off_image. rewrite facts_of_idem.
  destruct (kwritable k k b off n); reflexivity.
Qed.

Definition times16 (off : expr) : expr := mkMd M_MUL (ELit 16) off.

(* [comment removed for export] *)
Definition slot_lit_words (sb : expr) (sk : Z) (idx stride n : Z) : list kentry :=
  let r := stride - 4 - n in
  let q := stride * idx / 16 in
  KWord (SA sb (sk - 3)) 1 (ELit (idx + 32 * res_code r)) ::
  KWord (SA sb (sk - 2)) 2 (ELit q) ::
  (if Z.ltb 0 r then [KWord (SA sb (sk + n)) 1 (ELit 0)] else []) ++
  (if Z.leb 5 r then [KWord (SA sb (sk + stride - 4 - 5)) 1 (ELit 0); KWord (SA sb (sk + stride - 4 - 4)) 4 (ELit r)] else []).

(* [comment removed for export] *)
Definition call_enframe (cs : cstate) : option cstate :=
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some idx =>
    let g := reg cs 10 in let ne := reg cs 12 in let k := kn cs in
    let '(gb, gk) := split_lit g in
    match kread8e k gb (gk + 16), kreadZ k gb (gk + 32) 8 with
    | Some Me, Some W =>
      let ml := w_maplen W in let li := w_lastidx W in let sc := w_sizeclass W in
      let stride := slot_stride ml li sc in
      let start := mkAlu ALU_ADD Me (ELit (16 + stride * idx)) in
      let '(sb, sk) := split_lit start in
      match xlo k ne, xhi k ne, ehi k Me with
      | Some nlo, Some nhi, Some mh =>
        let shs := (stride - 4 - nlo) / 16 in          (* [comment removed for export] *)
        let symb := negb (shs =? 0) in
        let v := s_next (c_ss cs) in
        let off := if symb then EVar v else ELit 0 in
        let p := mkAlu ALU_ADD start (times16 off) in
        let '(pb, pk) := split_lit p in
        let pn := mkAlu ALU_ADD p ne in
        let '(pnb, pnk) := split_lit pn in
        let kf := if symb then [KRange (EVar v) 0 (Z.min 255 shs);
                                KRange (mkAlu ALU_ADD (times16 (EVar v)) ne) nlo (stride - 4)] else [] in
        let k0 := kf ++ k in
        let s := SL start (ELit stride) ne off (ELit W) idx p in
        let nx1 := if symb then S v else v in
        if ((implb (orb (ml =? 0) (negb (li =? 0))) (sc <? 48))
            && (16 <=? stride) && (stride <? 2 ^ 31) && (stride mod 16 =? 0) && (0 <=? idx) && (idx <? 32)
            && (stride * idx + 4096 <=? 16 * 65536)
            && (4 <=? ealign k start)
            && (0 <=? nlo) && (nhi + 4 <=? stride)
            && (mh + 16 + stride * idx + stride + 5 <=? two64)
            && flat_b k gb gk 40
            && ranges_apart k gb (gk + 16) 8 sb (sk - 3) (stride - 1)
            && match kreadZ k sb (sk - 4) 1 with Some 0 => true | _ => false end
            && rw_okb k sb (sk - 4) stride
            && kimg_covers k (d_sizeclasses A) (d_sizeclasses A + 96)
            && flat_b k0 pb pk 1 && flat_b k0 pnb pnk 1
            && expr_vars_lt v start && expr_vars_lt v ne
            && slot_vars_lt nx1 s
            && fresh_ok cs)%bool
        then
          let cs1 := if symb then bump_next cs 1 else cs in
          let len1 := mkAlu ALU_ADD (times16 off) (ELit 3) in
          let len2 := mkAlu ALU_SUB (ELit (stride - 4)) (mkAlu ALU_ADD ne (times16 off)) in
          let k1 := kn_havoc k0 sb (sk - 3) len1 in
          let k2 := kn_havoc k1 pnb pnk len2 in
          let kl := if symb then [] else match ne with ELit n0 => slot_lit_words sb sk idx stride (n0 mod two64) | _ => [] end in
          match after_call cs1 ret (Some p) (kl ++ k2) with
          | Some cs' => Some (set_slots cs' (s :: slots_keep k sb (sk - 4) (ELit stride) (c_slots cs)))
          | None => None
          end
        else None
      | _, _, _ => None
      end
    | _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition decode_W (We : expr) : option (expr * Z) :=
  match We with
  | ELit w => let w' := (w mod two64)%Z in Some (ELit (w' / 4096)%Z, (w' mod 4096)%Z)
  | EAlu ALU_ADD (EMd M_MUL (ELit 4096) Se) (ELit c) => if (Z.leb 0 c && Z.ltb c 4096)%bool then Some (Se, c) else None
  | EMd M_MUL (ELit 4096) Se => Some (Se, 0%Z)
  | _ => None
  end.

Definition rw_okb_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  let fk := facts_of k in
  (if kwritable_x fk fk b off n then off_image_x fk b off n else false)%bool.
Lemma rw_okb_x_eq : forall k b off n, rw_okb_x k b off n = (kwritable_x k k b off n && off_image_x k b off n)%bool.
Proof.
  intros. unfold rw_okb_x. rewrite kwritable_x_fk1, kwritable_x_fk2. unfold off_image_x. rewrite facts_of_idem.
  destruct (kwritable_x k k b off n); reflexivity.
Qed.

(* [comment removed for export] *)
Definition call_enframe_x (cs : cstate) : option cstate :=
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some 0 =>
    let g := reg cs 10 in let ne := reg cs 12 in let k := kn cs in
    let '(gb, gk) := split_lit g in
    match kread8e k gb (gk + 16), kread8e k gb (gk + 32) with
    | Some Me, Some We =>
      match decode_W We with
      | Some (Se, c) =>
        let stride := mkAlu ALU_ADD (mkMd M_MUL (ELit 4096) Se) (ELit (-16)) in
        let start := mkAlu ALU_ADD Me (ELit 16) in
        let '(sb, sk) := split_lit start in
        match xlo k ne, xhi k ne, ehi k Me, xlo k Se, xhi k Se with
        | Some nlo, Some nhi, Some mh, Some Slo, Some Shi =>
          let shi := 4096 * Shi - 16 in
          let shs := (shi - 4 - nlo) / 16 in
          let v := s_next (c_ss cs) in
          let off := EVar v in
          let p := mkAlu ALU_ADD start (times16 off) in
          let '(pb, pk) := split_lit p in
          let pn := mkAlu ALU_ADD p ne in
          let '(pnb, pnk) := split_lit pn in
          let rexp := mkAlu ALU_SUB stride (mkAlu ALU_ADD ne (times16 off)) in   (* [comment removed for export] *)
          let kf := [KRange (EVar v) 0 (Z.min 255 shs); KRange rexp 4 (shi - nlo)] in
          let k0 := kf ++ k in
          let s := SL start stride ne off We 0 p in
          if ((c mod 32 =? 0) && (1 <=? Slo) && (Shi <=? 2 ^ 19)
              && (4 <=? ealign k start)
              && (0 <=? nlo) && lin_ge0 k [(stride, 0%Z)] [(ne, 4%Z)]
              && (mh + 16 + shi + 5 <=? two64)
              && flat_b k gb gk 40
              && ranges_apart_x k gb (gk + 16) (ELit 8) sb (sk - 3) (mkAlu ALU_ADD stride (ELit (-1)))
              && match kreadZ k sb (sk - 4) 1 with Some 0 => true | _ => false end
              && rw_okb_x k sb (sk - 4) stride
              && kimg_covers k (d_sizeclasses A) (d_sizeclasses A + 96)
              && flat_b k0 pb pk 1 && flat_b k0 pnb pnk 1
              && expr_vars_lt v start && expr_vars_lt v ne && expr_vars_lt v stride && expr_vars_lt v We
              && slot_vars_lt (S v) s
              && fresh_ok cs)%bool
          then
            let cs1 := bump_next cs 1 in
            let len1 := mkAlu ALU_ADD (times16 off) (ELit 3) in
            let len2 := mkAlu ALU_ADD rexp (ELit (-4)) in
            let k1 := kn_havoc k0 sb (sk - 3) len1 in
            let k2 := kn_havoc k1 pnb pnk len2 in
            match after_call cs1 ret (Some p) k2 with
            | Some cs' => Some (set_slots cs' (s :: slots_keep k sb (sk - 4) stride (c_slots cs)))
            | None => None
            end
          else None
        | _, _, _, _, _ => None
        end
      | None => None
      end
    | _, _ => None
    end
  | _, _ => None
  end.

Definition call_enframe2 (cs : cstate) : option cstate :=
  match call_enframe cs with Some cs' => Some cs' | None => call_enframe_x cs end.

(* [comment removed for export] *)
Definition find_slot (k : list kentry) (pa : expr) (ss : list sslot) : option sslot :=
  List.find (fun s => if expr_eqb (sl_p s) pa then true else len_eqb k (sl_p s) pa) ss.

Definition remove_slot (s : sslot) (ss : list sslot) : list sslot :=
  List.filter (fun s' => negb (expr_eqb (sl_p s') (sl_p s))) ss.

(* [comment removed for export] *)
Definition call_freepro (cs : cstate) : option cstate :=
  let k := kn cs in let pa := reg cs 10 in let sp := reg cs 2 in
  match find_slot k pa (c_slots cs) with
  | Some s =>
    let strd := sl_stride s in let idx := sl_idx s in
    let sidx := match strd with ELit z => Some ((z mod two64) * idx)%Z | _ => if idx =? 0 then Some 0 else None end in
    match decode_W (sl_W s), xlo k strd, xhi k strd, sidx with
    | Some (Se, c), Some slo, Some shi, Some si =>
      let li := c mod 32 in let sc := (c / 64) mod 64 in
      let Me := mkAlu ALU_ADD (sl_start s) (ELit (- (16 + si))) in
      let '(mb, mk) := split_lit Me in
      match kread8e k mb mk with
      | Some ge =>
        let '(gb, gk) := split_lit ge in
        match kread8e k gb (gk + 16), kread8e k gb (gk + 32), kreadZ k gb (gk + 24) 4, kreadZ k gb (gk + 28) 4,
              lin_lowbits_kn k ge 12 with
        | Some Me', Some We, Some avail, Some freed, Some gm12 =>
          let area := mkAlu ALU_ADD ge (ELit (- gm12)) in
          let '(ab, ak) := split_lit area in
          let '(hb, hk) := split_lit (sl_start s) in
          let spm := mkAlu ALU_ADD sp (ELit (-48)) in
          let '(qb, qk) := split_lit spm in
          let e := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-4))) in
          let '(eb, ek) := split_lit e in
          match kread8e k ab ak, kread8e k (ELit 0) (d_malloc_ctx A), xlo k (sl_off s), xhi k (sl_off s),
                ehi k ge, elo k sp, ehi k hb, xlo k Se, xhi k Se with
          | Some se, Some se', Some olo, Some ohi, Some ghi, Some splo, Some hh, Some Slo, Some Shi =>
            let qlo := si / 16 + olo in let qhi := si / 16 + ohi in
            let nx := s_next (c_ss cs) in
            let reserved := mkAlu ALU_SUB (mkAlu ALU_ADD strd (ELit (-4))) (mkAlu ALU_ADD (sl_n s) (times16 (sl_off s))) in
            let e12 := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-16))) in
            if (len_eqb k Me' Me
                && expr_eqb We (sl_W s)
                && (Shi <=? 2 ^ 40)
                && (0 <=? idx) && (idx <=? li)
                && (((sc <? 48) && (size_class sc * idx <=? qlo) && (qhi <? size_class sc * (idx + 1)))
                    || ((sc =? 63) && (1 <=? Slo) && (li =? 0)))
                && ((Shi =? 0) || (qhi <=? Slo * 256 - 1))
                && (0 <=? olo)
                && negb (Z.testbit avail idx) && negb (Z.testbit freed idx)
                && expr_eqb se se'
                && flat_b k mb mk 8 && flat_b k gb gk 40 && flat_b k ab ak 8
                && match kreadZ k eb ek 1 with Some 0 => true | _ => false end
                && rw_okb k eb ek 1
                && flat_b k hb (hk - 4) (shi + 5)
                && kimg_covers k (d_sizeclasses A) (d_sizeclasses A + 96)
                && rw_okb k qb qk 48
                && (if hh + hk + shi + 48 <=? splo then true
                    else (* [comment removed for export] *)
                         (kdisj_apart_x k k eb ek (ELit 4) (EVar 0) (-8388608) (ELit 0x800000000000)
                          && (hh + hk + shi <=? SPBAND_LO + 0x800000000000) && sp_frame_ok sp 48))
                && (if ghi + 88 <=? splo then true
                    else (let '(gb', gk') := split_lit ge in below_band k gb' gk' 88 (ghi - gk') && sp_frame_ok sp 48))
                && (d_malloc_ctx A + 8 + 48 <=? splo)
                && (expr_vars_lt nx ge && expr_vars_lt nx spm && expr_vars_lt nx reserved && expr_vars_lt nx e12 && expr_vars_lt nx pa && expr_vars_lt nx We)
                && fresh_ok cs)%bool
            then
              let log := [SE (SA qb (qk + 8)) 8 (reg cs 19); SE (SA qb (qk + 16)) 8 (reg cs 18);
                          SE (SA qb (qk + 24)) 8 (reg cs 9); SE (SA qb (qk + 32)) 8 (reg cs 8);
                          SE (SA qb (qk + 40)) 8 (reg cs 1)] in
              match carry log k [] with
              | (kn', [], _) =>
                let ss := c_ss cs in
                let sr1 := sr_fresh (s_regs ss) caller_saved nx in
                let sr2 := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr1
                              2 spm) 9 pa) 8 (ELit idx)) 10 ge) 11 We) 14 reserved) 15 e12 in
                if kn_vars_lt nx kn' then
                  Some (CS (SS (t_freepro_k A) sr2 [] kn' (nx + NCS)) (c_maps cs) (c_nmaps cs) (c_live cs)
                           (slots_carry kn' log (remove_slot s (c_slots cs))))
                else None
              | _ => None
              end
            else None
          | _, _, _, _, _, _, _, _, _ => None
          end
        | _, _, _, _, _ => None
        end
      | None => None
      end
    | _, _, _, _ => None
    end
  | None => None
  end.

(* [comment removed for export] *)

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
Definition node_stdio_write (cs : cstate) : option (Z * list Z * cstate) :=
  let k := kn cs in
  match ret_lit cs, reg_lit cs 10, reg_lit cs 12 with
  | Some ret, Some f, Some l =>
    if negb (Z.eqb f (d_stdout A)) then None else
    match kreadZ k (ELit 0) (f + 120) 4, kreadZ k (ELit 0) (f + 40) 8, kreadZ k (ELit 0) (f + 56) 8,
          kread8e k (ELit 0) (f + 88), kread8e k (ELit 0) (f + 96),
          kreadZ k (ELit 0) (d_canary_got A) 8, kread8e k (ELit 0) (d_canary A) with
    | Some fd, Some wp, Some wb, Some bufp, Some bufsz, Some cg, Some _ =>
      let s := reg cs 11 in let sp := reg cs 2 in
      let '(sb, sk) := split_lit s in
      let spm := mkAlu ALU_ADD sp (ELit (-112)) in
      let '(qb, qk) := split_lit spm in
      let np := wp - wb in
      match kread_bytes (Z.to_nat np) k (ELit 0) wb, kread_bytes (Z.to_nat l) k sb sk,
            elo k sp, ehi k sp, ehi k s with
      | Some pend, Some extra, Some splo, Some sphi, Some shi =>
        if ((fd =? 1) && (cg =? d_canary A)
            && (0 <=? np) && (np + l <=? 4096)
            && (d_data_lo A <=? f) && (f + 232 <=? d_canary A) && (d_canary A + 8 <=? d_img_hi A)
            && (0x10000 <=? d_canary_got A) && (d_canary_got A + 8 <=? d_img_hi A)
            && rw_okb k qb qk 112
            && (4294967296 + 112 <=? splo) && (sphi <=? 0x800000000000)
            && ((shi + l <=? 0x800000000000) && (wp <=? 0x800000000000))   (* [comment removed for export] *)
            && flat_b k sb sk (Z.max l 1)
            && (lin_ge0 k [(spm, 0%Z)] [(ELit wp, 0%Z)] || lin_ge0 k [(ELit wb, 0%Z)] [(sp, 0%Z)])
            && (lin_ge0 k [(spm, 0%Z)] [(s, l)] || lin_ge0 k [(s, 0%Z)] [(sp, 0%Z)])
            && expr_vars_lt (s_next (c_ss cs)) bufp && expr_vars_lt (s_next (c_ss cs)) bufsz
            && fresh_ok cs)%bool
        then
          let k0 := kimg_cut (kimg_cut k (f + 32) 16) (f + 56) 8 in
          let k1 := kn_havoc k0 qb qk (ELit 112) in
          let k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 16) in
          let k3 := kn_havoc k2 (ELit 0) (f + 56) (ELit 8) in
          let k4 := KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
                    :: KWord (SA (ELit 0) (f + 40)) 8 bufp
                    :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3 in
          match after_call cs ret (Some (ELit l)) k4 with
          | Some cs' =>
              Some (fd, pend ++ extra,
                    set_slots cs' (slots_keep k (ELit 0) (f + 56) (ELit 8)
                                    (slots_keep k (ELit 0) (f + 32) (ELit 16)
                                      (slots_keep k qb qk (ELit 112) (c_slots cs)))))
          | None => None
          end
        else None
      | _, _, _, _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition call_mainret (cs : cstate) : option cstate :=
  match reg_lit cs 10 with
  | Some 0 =>
      let ss := c_ss cs in let nx := s_next ss in
      if fresh_ok cs then
        Some (CS (SS (t_main_join A)
                    (sr_upd (sr_upd (sr_upd (sr_upd (s_regs ss) 1 (EVar nx)) 8 (ELit 0)) 10 (ELit 0)) 11 (EVar (S nx)))
                    [] (s_know ss) (nx + 2))
                 (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs))
      else None
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PF_WIN : Z := 1056.

Definition call_printf (cs : cstate) : option cstate :=
  let k := kn cs in let f := d_stdout A in let buf := d_stdout_buf A in
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some 0 =>
    if negb (Z.eqb ret (t_printf_ret A)) then None else
    match kreadZ k (ELit 0) f 4, kreadZ k (ELit 0) (f + 32) 8, kreadZ k (ELit 0) (f + 40) 8,
          kreadZ k (ELit 0) (f + 96) 8, kreadZ k (ELit 0) (f + 140) 4, kreadZ k (ELit 0) (f + 144) 4,
          kread8e k (ELit 0) (d_canary A) with
    | Some flags, Some wend, Some w, Some bsz, Some lock, Some lbf, Some _ =>
      let sp := reg cs 2 in
      let spm := mkAlu ALU_ADD sp (ELit (- PF_WIN)) in
      let '(qb, qk) := split_lit spm in
      match elo k sp, ehi k sp with
      | Some splo, Some sphi =>
        if ((flags =? 5) && (wend =? buf + 1024) && (buf <=? w) && (w <=? buf + 1022) && (bsz =? 1024)
            && (lock =? 4294967295) && (lbf =? 4294967295)
            && kimg_covers k 0x10000 (d_data_lo A)
            && (4 <=? ealign k sp)
            && rw_okb k qb qk PF_WIN
            && (d_sp_lo A <=? splo) && (sphi <=? 0x7fffffffffff)
            && fresh_ok cs)%bool
        then
          let k0 := kimg_cut (kimg_cut (kimg_cut k f 4) (f + 40) 8) w 2 in
          let k1 := kn_havoc k0 qb qk (ELit PF_WIN) in
          let k2 := kn_havoc k1 (ELit 0) f (ELit 4) in
          let k3 := kn_havoc k2 (ELit 0) (f + 40) (ELit 8) in
          let k4 := kn_havoc k3 (ELit 0) w (ELit 2) in
          let k5 := KWord (SA (ELit 0) f) 4 (ELit 5)
                    :: KWord (SA (ELit 0) (f + 40)) 8 (ELit (w + 2))
                    :: KWord (SA (ELit 0) w) 2 (ELit 0x0a30) :: k4 in
          match after_call cs ret None k5 with
          | Some cs' =>
              Some (set_slots cs' (slots_keep k (ELit 0) w (ELit 2)
                                    (slots_keep k (ELit 0) (f + 40) (ELit 8)
                                      (slots_keep k (ELit 0) f (ELit 4)
                                        (slots_keep k qb qk (ELit PF_WIN) (c_slots cs))))))
          | None => None
          end
        else None
      | _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition call_fuzz (cs : cstate) : option cstate :=
  let k := kn cs in let D := t_fuzz_depth A in let g := d_gfool A in
  match ret_lit cs, ehi k (reg cs 11) with
  | Some ret, Some nhi =>
    if negb (Z.eqb ret (t_fuzz_ret A)) then None else
    let data := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let spm := mkAlu ALU_ADD sp (ELit (- D)) in
    let '(qb, qk) := split_lit spm in
    match elo k sp, ehi k sp, elo k data, ehi k data with
    | Some splo, Some sphi, Some dlo, Some dhi =>
      if ((nhi <? 2 ^ 26)
          && (((nhi =? 0) && expr_eqb data (ELit (d_empty A)))
              || (rw_ok_x k data ne && apart_x k spm (ELit D) data ne
                  && ((dhi + nhi <? 2 ^ 47) || (let '(db, dk) := split_lit data in below_band_x k db dk ne dhi nhi))))
          && (1 <=? dlo)
          && (4 <=? ealign k data) && (4 <=? ealign k sp)
          && (0 <? D) && rw_okb k qb qk D
          && (d_img_hi A <=? splo - D) && (sphi <=? 0x7fffffffffff)
          && (0x10000 <=? g) && (g + 4 <=? d_img_hi A)
          && (0x10000 <=? d_empty A) && (d_empty A + 16 <=? d_img_hi A)
          && ((d_empty A + 16 <=? g) || (g + 4 <=? d_empty A))
          && (0x10000 <=? d_fuzz_ro_lo A) && (d_fuzz_ro_lo A <=? d_fuzz_ro_hi A) && (d_fuzz_ro_hi A <=? d_img_hi A)
          && kimg_covers k (d_fuzz_ro_lo A) (d_fuzz_ro_hi A)
          && fresh_ok cs)%bool
      then
        let k0 := kimg_cut k g 4 in
        let k1 := kn_havoc k0 qb qk (ELit D) in
        let k2 := kn_havoc k1 (ELit 0) g (ELit 4) in
        match after_call cs ret (Some (ELit 0)) k2 with
        | Some cs' =>
            Some (set_slots cs' (slots_keep k (ELit 0) g (ELit 4)
                                  (slots_keep k qb qk (ELit D) (c_slots cs))))
        | None => None
        end
      else None
    | _, _, _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kread4e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 4 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

(* [comment removed for export] *)
Definition cells_ok (k : list kentry) (cells : list (Z * nat * Z)) : bool :=
  forallb (fun c => match c with (a, n, v) =>
             match kreadZ k (ELit 0) a n with Some z => Z.eqb z v | None => false end end) cells.

(* [comment removed for export] *)
Definition node_exitcall (cs : cstate) : option (list Z * Z) :=
  let k := kn cs in let f := d_stdout A in let f2 := d_stderr A in
  match reg_lit cs 10, reg_lit cs 4 with
  | Some code, Some tp =>
    let sp := reg cs 2 in
    let spm := mkAlu ALU_ADD sp (ELit (-144)) in
    let '(qb, qk) := split_lit spm in
    match elo k sp, ehi k sp, kread4e k (ELit 0) (tp - 168),
          kreadZ k (ELit 0) (f + 140) 4, kreadZ k (ELit 0) (f + 40) 8, kreadZ k (ELit 0) (f + 56) 8,
          kread8e k (ELit 0) (f + 8), kread8e k (ELit 0) (f + 16) with
    | Some splo, Some sphi, Some tide, Some lock, Some wp, Some wb, Some rp, Some re =>
      match kread8e k (ELit 0) (f2 + 40), kread8e k (ELit 0) (f2 + 56), kread8e k (ELit 0) (f2 + 8), kread8e k (ELit 0) (f2 + 16),
            elo k tide, ehi k tide with
      | Some w2, Some b2, Some r2, Some e2, Some tlo, Some thi =>
        if (cells_ok k (e_cells A)
            && (lock =? 4294967295) && expr_eqb rp re && expr_eqb w2 b2 && expr_eqb r2 e2
            && rw_okb k qb qk 144 && (4294967296 + 144 <=? splo) && (sphi <=? 0x800000000000)
            && (168 <=? tp) && (tp <=? 4294967296)
            && (1 <=? tlo) && (thi <? 2147483648))%bool
        then
          if (wb =? wp) then Some ([], Z.land code 255)
          else
            match kreadZ k (ELit 0) (f + 72) 8, kread8e k (ELit 0) (f + 88), kread8e k (ELit 0) (f + 96),
                  kreadZ k (ELit 0) (f + 120) 4, kreadZ k (ELit 0) (d_canary_got A) 8, kread8e k (ELit 0) (d_canary A),
                  kread_bytes (Z.to_nat (wp - wb)) k (ELit 0) wb with
            | Some wr, Some _, Some _, Some fd, Some cg, Some _, Some pend =>
                if ((wr =? t_stdio_write A) && (fd =? 1) && (cg =? d_canary A)
                    && (d_canary A + 8 <=? wb) && (wb <? wp) && (wp <=? d_img_hi A) && (wp - wb <=? 4096))%bool
                then Some (pend, Z.land code 255) else None
            | _, _, _, _, _, _, _ => None
            end
        else None
      | _, _, _, _, _, _ => None
      end
    | _, _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

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
Fixpoint expr_has_var (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => Nat.eqb n v
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_has_var v x || expr_has_var v y
  | EExt _ _ _ x => expr_has_var v x
  | EBlob _ _ _ _ => false
  end%bool.

Fixpoint expr_vars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (Nat.eqb n) acc then acc else n :: acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars x (expr_vars y acc)
  | EExt _ _ _ x => expr_vars x acc
  | EBlob _ _ _ _ => acc
  end.

(* [comment removed for export] *)
Definition live_vars (cs : cstate) : list nat :=
  let acc := fold_right expr_vars [] (s_regs (c_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars (a_base a) (expr_vars v acc)
                                      | KZero a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KBlob a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KWr a n => expr_vars (a_base a) (expr_vars n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars (sm_base m) (expr_vars (sm_len m) acc)) acc (c_maps cs) in
  fold_right (fun s acc => expr_vars (sl_start s) (expr_vars (sl_stride s) (expr_vars (sl_n s)
                (expr_vars (sl_off s) (expr_vars (sl_W s) (expr_vars (sl_p s) acc)))))) acc (c_slots cs).

Definition all_live (live : list nat) (e : expr) : bool :=
  forallb (fun v => existsb (Nat.eqb v) live) (expr_vars e []).

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list nat) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => all_live live e
  | KAlign e _ => all_live live e
  | KDisj a1 n1 a2 n2 => all_live live (a_base a1) && all_live live n1 && all_live live (a_base a2) && all_live live n2
  | _ => true
  end%bool.

Definition cs_gc_ref (cs : cstate) : cstate :=
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

Definition live_vars_t (cs : cstate) : ptree unit :=
  let acc := fold_right expr_vars_t PTLeaf (s_regs (c_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                                      | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_t (sm_base m) (expr_vars_t (sm_len m) acc)) acc (c_maps cs) in
  fold_right (fun s acc => expr_vars_t (sl_start s) (expr_vars_t (sl_stride s) (expr_vars_t (sl_n s)
                (expr_vars_t (sl_off s) (expr_vars_t (sl_W s) (expr_vars_t (sl_p s) acc)))))) acc (c_slots cs).

Definition in_live_t (t : ptree unit) (v : nat) : bool :=
  match pt_get t (vkey v) with Some _ => true | None => false end.

Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.

Definition kn_gc_entry_t (spb : expr) (spk : Z) (t : ptree unit) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => negb (expr_eqb b spb && Z.leb (k + Z.of_nat w) spk)
  | KZero (SA b k) (ELit n) => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KBlob (SA b k) (ELit n) _ => negb (expr_eqb b spb && Z.leb (k + n) spk)
  | KRange e _ _ => expr_all_live_t t e
  | KAlign e _ => expr_all_live_t t e
  | KDisj a1 n1 a2 n2 => expr_all_live_t t (a_base a1) && expr_all_live_t t n1 && expr_all_live_t t (a_base a2) && expr_all_live_t t n2
  | _ => true
  end%bool.

Definition cs_gc (cs : cstate) : cstate :=
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
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros a acc t H; destruct a as [[] ? ?|[] ?|[] ? ?| | | |[] ?|]; repeat apply live_agree_expr; assumption|].
  apply live_agree_fold; [intros; repeat apply live_agree_expr; assumption|].
  intros v. unfold in_live_t. rewrite pt_get_leaf. reflexivity.
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
  - rewrite <- (H n). cbn. rewrite Bool.andb_true_r. reflexivity.
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
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2]; cbn [kn_gc_entry kn_gc_entry_t];
    rewrite ?(expr_all_live_t_eq _ _ _ H); reflexivity.
Qed.

(* [comment removed for export] *)
Definition run_block_gc (fuel : nat) (stops : list Z) (cs : cstate) : option cstate :=
  match run_block fuel stops cs with Some cs' => Some (cs_gc cs') | None => None end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : list Z :=
  [t_memcpy A; t_memset A; t_strnlen A; t_memchr A; t_fuzz A; t_cas_or A; t_cas_and A; t_cas_lock A;
   t_calls A; t_main_ret A; t_enframe A; t_freepro A; t_stdio_write A; t_printf A; t_exitc A]%Z.

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : cstate).

Section Check.
Variable bfuel : nat.   (* [comment removed for export] *)

Fixpoint check (fuel : nat) (cs0 : cstate) (p : plan) {struct fuel} : cres :=
  match fuel with
  | O => CErr 0 p cs0
  | S f =>
  (* [comment removed for export] *)
  match p with
  | PContra => if kn_contra (kn cs0) then COk SNil else CErr 3 p cs0
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs0) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            match check f (set_kn cs0 (KRange e lo mid :: kn cs0)) k1 with
            | COk s1 =>
                match check f (set_kn cs0 (KRange e (mid + 1) hi :: kn cs0)) k2 with
                | COk s2 => COk (SCase e mid s1 s2)
                | err => err
                end
            | err => err
            end
          else CErr 3 p cs0
      | None => CErr 3 p cs0
      end
      else CErr 3 p cs0
  | _ =>
  match run_block_gc bfuel STOPS cs0 with
  | None => CErr 1 p cs0
  | Some cs =>
    match p with
    | PSplit _ _ _ _ => CErr 2 p cs
    | PContra => CErr 2 p cs
    | PMmap kf ks =>
        (* [comment removed for export] *)
        if is_ecall_at cs then
        match node_mmap cs with
        | Some (csf, css) => check f css ks
        | None => CErr 3 p cs
        end else CErr 2 p cs
    | PMunmap k =>
        if is_ecall_at cs then
        match node_munmap cs with Some cs' => check f cs' k | None => CErr 3 p cs end else CErr 2 p cs
    | PIoctl k =>
        if is_ecall_at cs then
        match node_ioctl cs with Some cs' => check f cs' k | None => CErr 3 p cs end else CErr 2 p cs
    | PStdioWrite k =>
        if Z.eqb (pc cs) (t_stdio_write A) then
        match node_stdio_write cs with
        | Some (fd, bs, cs') => match check f cs' k with COk s => COk (SEmit fd bs s) | err => err end
        | None => CErr 3 p cs
        end else CErr 2 p cs
    | PExit =>
        if is_ecall_at cs then
        match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end else CErr 2 p cs
    | PExitCall =>
        if Z.eqb (pc cs) (t_exitc A) then
        match node_exitcall cs with
        | Some ([], code) => COk (SExit code)                (* [comment removed for export] *)
        | Some (bs, code) => COk (SEmit 1 bs (SExit code))
        | None => CErr 3 p cs
        end
        else CErr 2 p cs
    | PResume k =>
        if (negb (is_ecall_at cs) && existsb (Z.eqb (pc cs)) STOPS)%bool then check f cs k else CErr 2 p cs
    | PCall sm args k =>
        let r := match sm with
                 | SumMemcpy => if Z.eqb (pc cs) (t_memcpy A) then call_memcpy cs else None
                 | SumFuzz => if Z.eqb (pc cs) (t_fuzz A) then call_fuzz cs else None
                 | SumEnframe => if Z.eqb (pc cs) (t_enframe A) then call_enframe2 cs else None
                 | SumFreePro => if Z.eqb (pc cs) (t_freepro A) then call_freepro cs else None
                 | SumMainRet => if Z.eqb (pc cs) (t_main_ret A) then call_mainret cs else None
                 | SumPrintf => if Z.eqb (pc cs) (t_printf A) then call_printf cs else None
                 end in
        match r with Some cs' => check f cs' k | None => CErr 3 p cs end
    | PCas c k =>
        match node_cas c cs with Some cs' => check f cs' k | None => CErr 3 p cs end
    end
  end
  end
  end.
End Check.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SRC1 : atable :=
  {| t_memcpy := 0x1dbe0; t_memset := 0x1dfe4; t_strnlen := 0x1e0dc; t_memchr := 0x1e120;
     t_cas_or := 0x17404; t_cas_or_k := 0x17424; t_cas_and := 0x17be4; t_cas_and_k := 0x17c04;
     t_cas_lock := 0x16a80; t_cas_lock_k := 0x16a90;
     t_calls := 0x12e44; t_main_ret := 0x12bfc (* [comment removed for export] *); t_main_join := 0x12c7c (* [comment removed for export] *); t_enframe := 0x18348;
     t_freepro := 0x16da8; t_freepro_k := 0x16e84; t_stdio_write := 0x18fe8;
     d_malloc_ctx := 0x50cf0; d_stdout := 0x20790; d_canary_got := 0x1f660; d_canary := 0x50c58;
     t_printf := 0x12ee0; t_printf_ret := 0x12e34; t_exitc := 0x16a60; d_stdout_buf := 0x510c0; d_stderr := 0x206a0;
     e_cells := [(0x50c50, 4%nat, 0);                                  (* [comment removed for export] *)
                 (0x1f668, 8%nat, 0x1f5d0); (0x1f670, 8%nat, 0x1f5c8);  (* [comment removed for export] *)
                 (0x1f5c8, 8%nat, 0x129f8);                            (* [comment removed for export] *)
                 (0x208d8, 1%nat, 0);                                  (* [comment removed for export] *)
                 (0x1f610, 8%nat, 0x16944); (0x1f618, 8%nat, 0);              (* [comment removed for export] *)
                 (0x50c7b, 1%nat, 0); (0x510a8, 8%nat, 0); (0x51098, 8%nat, 0);   (* [comment removed for export] *)
                 (0x20878, 8%nat, 0x20790); (0x20788, 8%nat, 0x206a0);            (* [comment removed for export] *)
                 (0x206a0 + 140, 4%nat, 4294967295);
                 (0x20678, 8%nat, 0x20678); (0x50a34, 4%nat, 0); (0x50a40, 8%nat, 0x50a48); (0x50a38, 4%nat, 1); (0x50a48, 8%nat, 0); (0x50a50, 8%nat, 0x16a0c); (0x50b50, 8%nat, 0x12eb0); (0x308e4, 1%nat, 0)]%Z;                           (* [comment removed for export] *)
     text_n := 13312%nat; d_img_hi := 0x52000; d_data_lo := 0x20000; d_sp_lo := 0x52420; d_sizeclasses := 0x10508;
     t_fuzz := 0x12f28; t_fuzz_ret := 0x12e24; t_fuzz_depth := 1824; d_gfool := 0x30910;
     d_fuzz_ro_lo := 0x103ec; d_fuzz_ro_hi := 0x1048c; d_empty := 0x308f0 |}.

(* [comment removed for export] *)
Definition INFOUB : atable :=
  {| t_memcpy := 0x1e6dc; t_memset := 0x1eae0; t_strnlen := 0x1ebd8; t_memchr := 0x1ec1c;
     t_cas_or := 0x17f00; t_cas_or_k := 0x17f20; t_cas_and := 0x186e0; t_cas_and_k := 0x18700;
     t_cas_lock := 0x1757c; t_cas_lock_k := 0x1758c;
     t_calls := 0x12ea4; t_main_ret := 0x12c5c; t_main_join := 0x12cdc; t_enframe := 0x18e44;
     t_freepro := 0x178a4; t_freepro_k := 0x17980; t_stdio_write := 0x19ae4;
     d_malloc_ctx := 0x517e0; d_stdout := 0x21288; d_canary_got := 0x20158; d_canary := 0x51748;
     t_printf := 0x12f40; t_printf_ret := 0x12e94; t_exitc := 0x1755c; d_stdout_buf := 0x51bb0; d_stderr := 0x21198;
     e_cells := [(0x51740, 4%nat, 0);
                 (0x20160, 8%nat, 0x200c8); (0x20168, 8%nat, 0x200c0);
                 (0x200c0, 8%nat, 0x12a58);
                 (0x213c8, 1%nat, 0);
                 (0x20108, 8%nat, 0x17440); (0x20110, 8%nat, 0);
                 (0x5176b, 1%nat, 0); (0x51b98, 8%nat, 0); (0x51b88, 8%nat, 0);
                 (0x21370, 8%nat, 0x21288); (0x21280, 8%nat, 0x21198);
                 (0x21198 + 140, 4%nat, 4294967295);
                 (0x21170, 8%nat, 0x21170); (0x51524, 4%nat, 0); (0x51530, 8%nat, 0x51538); (0x51528, 4%nat, 1); (0x51538, 8%nat, 0); (0x51540, 8%nat, 0x17508); (0x51640, 8%nat, 0x12f10); (0x313d4, 1%nat, 0)]%Z;
     text_n := 14336%nat; d_img_hi := 0x52000; d_data_lo := 0x21000; d_sp_lo := 0x52420; d_sizeclasses := 0x1050c;
     t_fuzz := 0x12f88; t_fuzz_ret := 0x12e84; t_fuzz_depth := 1824; d_gfool := 0x31400;
     d_fuzz_ro_lo := 0x103ec; d_fuzz_ro_hi := 0x10490; d_empty := 0x313e0 |}.

End SP.
