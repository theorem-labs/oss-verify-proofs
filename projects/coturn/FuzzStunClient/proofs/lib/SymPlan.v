(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import MallocDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
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
  t_F        : Z;   (* [comment removed for export] *)
  t_F_ret    : Z;   (* [comment removed for export] *)
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
  t_tp       : Z;   (* [comment removed for export] *)
  t_F_frame  : Z;   (* [comment removed for export] *)
  t_F_nmax   : Z;   (* [comment removed for export] *)
  d_prng     : Z;   (* [comment removed for export] *)
  d_errno    : Z;   (* [comment removed for export] *)
  d_mcount   : Z;   (* [comment removed for export] *)
  d_ro_hi    : Z;   (* [comment removed for export] *)
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
  d_sctbl    : Z;   (* [comment removed for export] *)
  d_rw_lo    : Z;   (* [comment removed for export] *)
  e_cells    : list (Z * nat * Z)  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition TEXT_LO : Z := 0x13000.
(* [comment removed for export] *)
Definition TEXT_N : nat := 36864.

(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x58000.

(* [comment removed for export] *)
Definition STK : Z := 8388608.
Definition e_sp0 : expr := EVar 0.
Definition e_top : expr := EAlu ALU_ADD e_sp0 (ELit (- STK)).
Definition TOPMAX : Z := 2 ^ 47 - STK.
Definition STKWIN : Z := 2 ^ 31 + STK.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.        (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : N.          (* [comment removed for export] *)

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
Definition slot_keep_bF (fs : fdig) (fk : list kentry) (ub : expr) (uk : Z) (un : expr) (s : sslot) : bool :=
  let '(hb, hk) := split_lit (sl_start s) in
  if ranges_apart_xF fs fk ub uk un hb (hk - 4) (sl_stride s) then true
  else let '(pb, pk) := split_lit (sl_p s) in xinsideF fs fk ub uk un pb pk (sl_n s).

Fixpoint slots_carryF (fs : fdig) (fk : list kentry) (log : list sentry) (ss : list sslot) : list sslot :=
  match log with
  | [] => ss
  | SE (SA b o) w _ :: older => List.filter (slot_keep_bF fs fk b o (ELit (Z.of_nat w))) (slots_carryF fs fk older ss)
  end.

(* [comment removed for export] *)
Definition slot_keep_bV (fs : fdig) (fk : list kentry) (br1 : option (Z * Z)) (ub : expr) (uk : Z) (w : nat)
           (s : sslot) (sp : slotpre) : bool :=
  let '(hb, hk) := split_lit (sl_start s) in
  if ranges_apart_slotF fs fk br1 ub uk (Z.of_nat w) sp hb (hk - 4) (sl_stride s) then true
  else let '(pb, pk) := split_lit (sl_p s) in xinsideF fs fk ub uk (ELit (Z.of_nat w)) pb pk (sl_n s).
Definition mk_slotpre_s (fs : fdig) (fk : list kentry) (s : sslot) : slotpre :=
  let '(hb, hk) := split_lit (sl_start s) in mk_slotpre fs fk hb (hk - 4) (sl_stride s).
Lemma slot_keep_bV_eq : forall fs fk ub uk w s,
  slot_keep_bV fs fk (base_rangeT fs ub) ub uk w s (mk_slotpre_s fs fk s) = slot_keep_bF fs fk ub uk (ELit (Z.of_nat w)) s.
Proof.
  intros. unfold slot_keep_bV, mk_slotpre_s, slot_keep_bF. destruct (split_lit (sl_start s)) as [hb hk].
  rewrite ranges_apart_slotF_eq. reflexivity.
Qed.
(* [comment removed for export] *)
Fixpoint slot_keep_allV (fs : fdig) (fk : list kentry) (log : list (sentry * option (Z * Z))) (s : sslot) (sp : slotpre) : bool :=
  match log with
  | [] => true
  | (SE (SA b o) w _, br1) :: rest => if slot_keep_bV fs fk br1 b o w s sp then slot_keep_allV fs fk rest s sp else false
  end.
Definition log_brs (fs : fdig) (log : list sentry) : list (sentry * option (Z * Z)) :=
  map (fun e => (e, base_rangeT fs (a_base (e_addr e)))) log.
Definition slots_carryV (fs : fdig) (fk : list kentry) (log : list sentry) (ss : list sslot) : list sslot :=
  let lb := log_brs fs log in
  List.filter (fun s => slot_keep_allV fs fk lb s (mk_slotpre_s fs fk s)) ss.
Lemma slots_carryF_filter : forall fs fk log ss,
  slots_carryF fs fk log ss =
  List.filter (fun s => forallb (fun e => match e with SE (SA b o) w _ => slot_keep_bF fs fk b o (ELit (Z.of_nat w)) s end) log) ss.
Proof.
  intros fs fk log. induction log as [|[[b o] w v] older IH]; intros ss; cbn [slots_carryF forallb].
  - induction ss as [|s r IHs]; [reflexivity|]. cbn. rewrite <- IHs. reflexivity.
  - rewrite IH. induction ss as [|s r IHs]; [reflexivity|]. cbn [List.filter].
    destruct (forallb _ older) eqn:E; cbn [List.filter andb].
    + destruct (slot_keep_bF fs fk b o (ELit (Z.of_nat w)) s); cbn; rewrite IHs; reflexivity.
    + rewrite Bool.andb_false_r. exact IHs.
Qed.
Lemma slot_keep_allV_eq : forall fs fk log s,
  slot_keep_allV fs fk (log_brs fs log) s (mk_slotpre_s fs fk s) =
  forallb (fun e => match e with SE (SA b o) w _ => slot_keep_bF fs fk b o (ELit (Z.of_nat w)) s end) log.
Proof.
  intros fs fk log s. induction log as [|[[b o] w v] rest IH]; [reflexivity|].
  cbn [log_brs map slot_keep_allV forallb e_addr a_base]. fold (log_brs fs rest). rewrite slot_keep_bV_eq, IH.
  destruct (slot_keep_bF _ _ _ _ _ _); reflexivity.
Qed.
Lemma slots_carryV_eq : forall fs fk log ss, slots_carryV fs fk log ss = slots_carryF fs fk log ss.
Proof.
  intros. unfold slots_carryV. rewrite slots_carryF_filter. apply filter_ext. intros s. apply slot_keep_allV_eq.
Qed.

(* [comment removed for export] *)
Definition ranges_apart_slotS (fs : fdig) (fk : list kentry) (br1 : option (Z * Z)) (sx : stctx) (sp : slotpre)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  let b1 := a_base (sx_wa sx) in let k1 := a_off (sx_wa sx) in let z1 := Z.of_nat (sx_w sx) in
  match sp_lit sp with
  | Some m2 =>
      let n1 := zlit64 z1 in
      if (match br1, sp_br2 sp with
          | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + m2) (lo1 + k1)
          | _, _ => false
          end)%Z then true
      else if dm_apart (si_dmask (sx_si sx)) (sp_pre sp) then true
      else lin_apartF fs fk b1 k1 n1 b2 k2 m2
  | None => ranges_apart_slotF fs fk br1 b1 k1 z1 sp b2 k2 n2
  end.
Lemma ranges_apart_slotS_eq : forall fk sx sp b2 k2 n2 br1,
  sx_wf fk sx -> sp = mk_slotpre (SFS fk) fk b2 k2 n2 ->
  ranges_apart_slotS (SFS fk) fk br1 sx sp b2 k2 n2
  = ranges_apart_slotF (SFS fk) fk br1 (a_base (sx_wa sx)) (a_off (sx_wa sx)) (Z.of_nat (sx_w sx)) sp b2 k2 n2.
Proof.
  intros fk sx sp b2 k2 n2 br1 Hwf ->. unfold ranges_apart_slotS, ranges_apart_slotF.
  destruct n2 as [z2| | | | | | |]; cbn [mk_slotpre sp_lit sp_pre sp_br2 sp_h2]; try reflexivity.
  rewrite (sx_si_dmask fk sx Hwf), dm_apart_eq, kdisj_apart_withF_eq. reflexivity.
Qed.

Definition slot_keep_bS (fs : fdig) (fk : list kentry) (br1 : option (Z * Z)) (sx : stctx) (s : sslot) (sp : slotpre) : bool :=
  let '(hb, hk) := split_lit (sl_start s) in
  if ranges_apart_slotS fs fk br1 sx sp hb (hk - 4) (sl_stride s) then true
  else let '(pb, pk) := split_lit (sl_p s) in
       xinsideF fs fk (a_base (sx_wa sx)) (a_off (sx_wa sx)) (ELit (Z.of_nat (sx_w sx))) pb pk (sl_n s).
Lemma slot_keep_bS_eq : forall fk sx s,
  sx_wf fk sx ->
  slot_keep_bS (SFS fk) fk (base_rangeT (SFS fk) (a_base (sx_wa sx))) sx s (mk_slotpre_s (SFS fk) fk s)
  = slot_keep_bF (SFS fk) fk (a_base (sx_wa sx)) (a_off (sx_wa sx)) (ELit (Z.of_nat (sx_w sx))) s.
Proof.
  intros fk sx s Hwf. rewrite <- slot_keep_bV_eq. unfold slot_keep_bS, slot_keep_bV, mk_slotpre_s.
  destruct (split_lit (sl_start s)) as [hb hk].
  rewrite (ranges_apart_slotS_eq fk sx _ hb (hk - 4) (sl_stride s) _ Hwf eq_refl). reflexivity.
Qed.

Fixpoint slot_keep_allS (fs : fdig) (fk : list kentry) (sxb : list (stctx * option (Z * Z))) (s : sslot) (sp : slotpre) : bool :=
  match sxb with
  | [] => true
  | (sx, br1) :: r => if slot_keep_bS fs fk br1 sx s sp then slot_keep_allS fs fk r s sp else false
  end.
Definition slots_carryS (fs : fdig) (fk : list kentry) (sxs : list stctx) (ss : list sslot) : list sslot :=
  let sxb := map (fun sx => (sx, base_rangeT fs (a_base (sx_wa sx)))) sxs in
  List.filter (fun s => slot_keep_allS fs fk sxb s (mk_slotpre_s fs fk s)) ss.

Lemma forallb_app : forall (X : Type) (f : X -> bool) l1 l2, forallb f (l1 ++ l2) = (forallb f l1 && forallb f l2)%bool.
Proof. intros X f l1 l2. induction l1 as [|x r IH]; [reflexivity|]. cbn. rewrite IH. apply Bool.andb_assoc. Qed.
Lemma forallb_rev : forall (X : Type) (f : X -> bool) l, forallb f (rev l) = forallb f l.
Proof.
  intros X f l. induction l as [|x r IH]; [reflexivity|]. cbn [rev]. rewrite forallb_app, IH. cbn.
  rewrite Bool.andb_true_r. apply Bool.andb_comm.
Qed.

Lemma slots_carryS_eq : forall fk log ss,
  slots_carryS (SFS fk) fk (map (sx_of fk) (rev log)) ss = slots_carryV (SFS fk) fk log ss.
Proof.
  intros fk log ss. unfold slots_carryS, slots_carryV. apply filter_ext. intros s.
  rewrite slot_keep_allV_eq, <- forallb_rev.
  induction (rev log) as [|[[b o] w v] r IH]; [reflexivity|].
  pose proof (slot_keep_bS_eq fk (sx_of fk (SE (SA b o) w v)) s (sx_of_wf fk _)) as E.
  cbn [sx_of sx_wa sx_w a_base a_off] in E.
  cbn [map slot_keep_allS forallb sx_of sx_wa a_base]. rewrite IH.
  match goal with |- (if ?x then _ else _) = _ => replace x with (slot_keep_bF (SFS fk) fk b o (ELit (Z.of_nat w)) s) by (symmetry; exact E) end.
  destruct (slot_keep_bF _ _ _ _ _ _); reflexivity.
Qed.


Definition slots_carry (k : list kentry) (log : list sentry) (ss : list sslot) : list sslot :=
  match log with
  | [] => ss
  | _ => let fk := facts_of k in slots_carryV (SFS fk) fk log ss
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
  intros k log ss. unfold slots_carry. destruct log as [|e older] eqn:El; [reflexivity|]. rewrite slots_carryV_eq. rewrite <- El. clear El e older.
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
Definition run_blockM (fuel : nat) (stops : list Z) (cs : cstate) (m : smemo) : option cstate * smemo :=
  let '(ss', m) := sym_execT'M segs IT fuel true stops (c_ss cs) m in
  (match s_log ss' with
   | [] => Some (CS (SS (s_pc ss') (s_regs ss') [] (s_know ss') (s_next ss')) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs))
   | _ => let '(r, sxs) := carryVS (s_log ss') (s_know ss') in let '(kn', fs) := r in
          Some (CS (SS (s_pc ss') (s_regs ss') [] kn' (s_next ss')) (c_maps cs) (c_nmaps cs) (c_live cs)
                   (slots_carryS fs (facts_of (s_know ss')) sxs (c_slots cs)))
   end, m).
Lemma run_blockM_eq : forall fuel stops cs m, smemo_ok m ->
  fst (run_blockM fuel stops cs m) = run_block fuel stops cs /\ smemo_ok (snd (run_blockM fuel stops cs m)).
Proof.
  intros fuel stops cs m Hm. unfold run_blockM, run_block.
  pose proof (sym_execT'M_eq segs IT fuel true stops (c_ss cs) m Hm) as [H1 H2].
  destruct (sym_execT'M segs IT fuel true stops (c_ss cs) m) as [ss' m1]. cbn [fst snd] in H1, H2 |- *. subst ss'.
  split; [|exact H2].
  set (ss' := sym_execT' segs IT fuel true stops (c_ss cs)).
  destruct (s_log ss') as [|e older] eqn:EL; [reflexivity|].
  pose proof (carryVS_eq (e :: older) (s_know ss')) as (C1 & C2 & C3).
  destruct (carryVS (e :: older) (s_know ss')) as [[kn' fs] sxs]. cbn [fst snd] in C1, C2, C3. subst kn' fs sxs.
  unfold carry. cbn [slots_carry].
  f_equal. f_equal.
  rewrite slots_carryS_eq. unfold slots_carry.
  (* [comment removed for export] *)
  assert (HF : facts_of (carryV (e :: older) (s_know ss')) = facts_of (s_know ss')).
  { pose proof (carry_ref_facts (e :: older) (s_know ss') []) as F. rewrite <- carry_eq in F. unfold carry in F. exact F. }
  rewrite HF. reflexivity.
Qed.

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
Definition bump_next (cs : cstate) (d : N) : cstate :=
  let ss := c_ss cs in
  CS (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss + d)%N) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs).
Arguments bump_next _ _%_N_scope.

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
Definition kreadZD (fs : fdig) (fk k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookupAF fs fk segs k b off n (Z.of_nat n) (off + Z.of_nat n) false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.
Lemma kreadZD_eq : forall k b off n, kreadZD (SFS (facts_of k)) (facts_of k) k b off n = kreadZ k b off n.
Proof. intros. unfold kreadZD, kreadZ, know_lookup. rewrite know_lookupAF_eq, know_lookupA_fk1. reflexivity. Qed.
Fixpoint kread_bytesD (fs : fdig) (fk : list kentry) (fuel : nat) (k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZD fs fk k b off 1, kread_bytesD fs fk f k b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.
Lemma kread_bytesD_eq : forall k fuel b off, kread_bytesD (SFS (facts_of k)) (facts_of k) fuel k b off = kread_bytes fuel k b off.
Proof.
  intros k fuel. induction fuel as [|f IH]; intros; [reflexivity|]. cbn [kread_bytesD kread_bytes].
  rewrite kreadZD_eq, IH. reflexivity.
Qed.
Fixpoint kwritableD (fs : fdig) (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xloF fs allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (if Z.leb 0 n then Z.ltb n two64 else false) then
             (if xinsideF fs allkn b off (ELit n) wb wk wn then true else kwritableD fs allkn rest b off n)
      else kwritableD fs allkn rest b off n
  | _ :: rest => kwritableD fs allkn rest b off n
  end.
Lemma kwritableD_eq : forall a k b off n, kwritableD (SFS (facts_of a)) (facts_of a) k b off n = kwritable a k b off n.
Proof.
  intros a k b off n. induction k as [|K rest IH]; [reflexivity|]. cbn [kwritableD kwritable]. rewrite IH.
  destruct K as [| | | | | |[wb wk] wn|]; try reflexivity. rewrite xloF_eq, xlo_fk, xinsideF_eq, xinside_fk.
  destruct (Z.leb 0 n), (Z.ltb n two64), (xinside a b off (ELit n) wb wk wn), (kwritable a rest b off n),
           (expr_eqb b wb && Z.leb wk off)%bool; try reflexivity;
  destruct (xlo a wn); try reflexivity; destruct (Z.leb _ _); reflexivity.
Qed.
Fixpoint kwritable_xD (fs : fdig) (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhiF fs allkn n, xloF fs allkn wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideF fs allkn b off n wb wk wn then true
      else kwritable_xD fs allkn rest b off n
  | _ :: rest => kwritable_xD fs allkn rest b off n
  end.
Lemma kwritable_xD_eq : forall a k b off n, kwritable_xD (SFS (facts_of a)) (facts_of a) k b off n = kwritable_x a k b off n.
Proof.
  intros a k b off n. induction k as [|K rest IH]; [reflexivity|]. cbn [kwritable_xD kwritable_x]. rewrite IH.
  destruct K as [| | | | | |[wb wk] wn|]; try reflexivity. rewrite xhiF_eq, xhi_fk, xloF_eq, xlo_fk, xinsideF_eq, xinside_fk. reflexivity.
Qed.
Lemma kreadZD_bucket : forall fs fk k b off n, kreadZD fs fk (List.filter (lk_relevant b) k) b off n = kreadZD fs fk k b off n.
Proof. intros. unfold kreadZD. rewrite know_lookupAF_bucket. reflexivity. Qed.
Lemma kread_bytesD_bucket : forall fs fk fuel k b off, kread_bytesD fs fk fuel (List.filter (lk_relevant b) k) b off = kread_bytesD fs fk fuel k b off.
Proof. intros fs fk fuel. induction fuel as [|f IH]; intros; [reflexivity|]. cbn [kread_bytesD]. rewrite kreadZD_bucket, IH. reflexivity. Qed.
Hint Rewrite kreadZD_bucket kread_bytesD_bucket kreadZD_eq kread_bytesD_eq kwritableD_eq kwritable_xD_eq : nd.

(* [comment removed for export] *)
Definition off_image (k : list kentry) (b : expr) (off n : Z) : bool :=
  let fk := facts_of k in ranges_apartF (SFS fk) fk b off n (ELit 0) IMG_LO (IMG_HI - IMG_LO).
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  let fk := facts_of k in ranges_apart_xF (SFS fk) fk b off n (ELit 0) IMG_LO (ELit (IMG_HI - IMG_LO)).
Lemma off_image_eq : forall k b off n, off_image k b off n = ranges_apart k b off n (ELit 0) IMG_LO (IMG_HI - IMG_LO).
Proof. intros. unfold off_image. rewrite ranges_apartF_eq. apply ranges_apart_fk. Qed.
Lemma off_image_x_eq : forall k b off n, off_image_x k b off n = ranges_apart_x k b off n (ELit 0) IMG_LO (ELit (IMG_HI - IMG_LO)).
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
Definition off_imageD (fs : fdig) (fk : list kentry) (b : expr) (off n : Z) : bool :=
  ranges_apartF fs fk b off n (ELit 0) IMG_LO (IMG_HI - IMG_LO).
Definition off_image_xD (fs : fdig) (fk : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_xF fs fk b off n (ELit 0) IMG_LO (ELit (IMG_HI - IMG_LO)).
Definition flat_bD (fs : fdig) (b : expr) (off n : Z) : bool :=
  match base_rangeT fs b with
  | Some (lo, hi) => (Z.leb 0 (lo + off) && Z.leb (hi + off + n) two64 && Z.ltb 0 n)%bool
  | None => false
  end.
Lemma flat_bD_eq : forall k b off n, flat_bD (SFS (facts_of k)) b off n = flat_b k b off n.
Proof. intros. unfold flat_bD, flat_b. rewrite base_rangeT_eq. reflexivity. Qed.
Definition ehiD (fs : fdig) (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)
  | _ => match erangeT fs e with Some (_, hi) => Some hi | None => None end
  end.
Definition eloD (fs : fdig) (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)
  | _ => match erangeT fs e with Some (lo, _) => Some lo | None => None end
  end.
Lemma ehiD_eq : forall k e, ehiD (SFS (facts_of k)) e = ehi k e.
Proof. intros. unfold ehiD, ehi. rewrite erangeT_eq, erange_fk. reflexivity. Qed.
Lemma eloD_eq : forall k e, eloD (SFS (facts_of k)) e = elo k e.
Proof. intros. unfold eloD, elo. rewrite erangeT_eq, erange_fk. reflexivity. Qed.
Lemma xloD_eq : forall k e, xloF (SFS (facts_of k)) (facts_of k) e = xlo k e.
Proof. intros. rewrite xloF_eq. apply xlo_fk. Qed.
Lemma xhiD_eq : forall k e, xhiF (SFS (facts_of k)) (facts_of k) e = xhi k e.
Proof. intros. rewrite xhiF_eq. apply xhi_fk. Qed.
Lemma ealignD_eq : forall k e, ealignT (SFS (facts_of k)) (facts_of k) e = ealign k e.
Proof. intros. rewrite ealignT_eq. apply ealign_fk. Qed.
Lemma lin_ge0D_eq : forall k pos neg, lin_ge0F (SFS (facts_of k)) (facts_of k) pos neg = lin_ge0 k pos neg.
Proof. intros. rewrite lin_ge0F_eq. apply lin_ge0_fk. Qed.
Lemma foldKD_eq : forall k e, foldKT (SFS (facts_of k)) (facts_of k) e = foldK k e.
Proof. intros. rewrite foldKT_eq. apply foldK_fk. Qed.
Lemma ranges_apartD_eq : forall k b1 k1 n1 b2 k2 n2,
  ranges_apartF (SFS (facts_of k)) (facts_of k) b1 k1 n1 b2 k2 n2 = ranges_apart k b1 k1 n1 b2 k2 n2.
Proof. intros. rewrite ranges_apartF_eq. apply ranges_apart_fk. Qed.
Lemma ranges_apart_xD_eq : forall k b1 k1 n1 b2 k2 n2,
  ranges_apart_xF (SFS (facts_of k)) (facts_of k) b1 k1 n1 b2 k2 n2 = ranges_apart_x k b1 k1 n1 b2 k2 n2.
Proof. intros. rewrite ranges_apart_xF_eq. apply ranges_apart_x_fk. Qed.
Lemma kdisj_apart_xD_eq : forall k kn b1 k1 n1 b2 k2 n2,
  kdisj_apart_xF (SFS (facts_of k)) (facts_of k) kn b1 k1 n1 b2 k2 n2 = kdisj_apart_x k kn b1 k1 n1 b2 k2 n2.
Proof. intros. rewrite kdisj_apart_xF_eq. apply kdisj_apart_x_fk1. Qed.
Hint Rewrite flat_bD_eq ehiD_eq eloD_eq xloD_eq xhiD_eq ealignD_eq lin_ge0D_eq foldKD_eq ranges_apartD_eq ranges_apart_xD_eq kdisj_apart_xD_eq : nd.

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
  end.
Fixpoint kn_vars_lt (b : N) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition maps_vars_lt (b : N) (ms : list smap) : bool :=
  forallb (fun m => expr_vars_lt b (sm_base m) && expr_vars_lt b (sm_len m)) ms.
(* [comment removed for export] *)
Definition slot_vars_lt (b : N) (s : sslot) : bool :=
  (expr_vars_lt b (sl_start s) && expr_vars_lt b (sl_stride s) && expr_vars_lt b (sl_n s) && expr_vars_lt b (sl_off s)
   && expr_vars_lt b (sl_W s) && expr_vars_lt b (sl_p s))%bool.
Definition slots_vars_lt (b : N) (ss : list sslot) : bool := forallb (slot_vars_lt b) ss.
Definition fresh_ok (cs : cstate) : bool :=
  let ss := c_ss cs in let v := s_next ss in
  (sr_vars_lt v (s_regs ss) && kn_vars_lt v (s_know ss) && maps_vars_lt v (c_maps cs) && slots_vars_lt v (c_slots cs) && N.leb nx0 v)%bool.

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
(* [comment removed for export] *)

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
       | Some (lo, hi) => (Z.leb IMG_LO (lo + off) && Z.leb (hi + off + lh) IMG_HI)  (* [comment removed for export] *)
                          || (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) 0x1000)      (* [comment removed for export] *)
                          || (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64
                              && lin_ge0 k [(b, off)] [(e_top, 0%Z)])                  (* [comment removed for export] *)
       | None => false
       end
    | None => false
    end) || inside_maps k ms b off len)%bool.

Definition grant_keep_b (k : list kentry) (ms : list smap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => Nat.leb w 8 && safe_range k ms b o (ELit (Z.of_nat w))
  | KZero (SA b o) l => safe_range k ms b o l
  | KBlob (SA b o) l _ => safe_range k ms b o l
  | KImg lo hi => (Z.leb 0 lo && Z.leb hi 0x1000) || (Z.leb IMG_LO lo && Z.leb hi IMG_HI)
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b o) n => safe_range k ms b o n
  end.

(* [comment removed for export] *)
Definition lin_insideF (fs : fdig) (fk : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if lin_nowrapRF fs fk b1 then
    if lin_nowrapRF fs fk b2 then
      let l1 := lin_of b1 in let l2 := lin_of b2 in
      lin_testF fs fk (fst l1 + k1 - fst l2 - k2)%Z (lsub_e (snd l1) (snd l2))
                (fun lo hi => (Z.leb 0 lo && Z.leb (hi + n1) n2)%bool)
    else false
  else false.

Fixpoint inside_mapsF (fs : fdig) (fk : list kentry) (ms : list smap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest =>
      if (match len, sm_len m with
          | ELit l, ELit ml => lin_insideF fs fk b off (zmod64 l) (sm_base m) 0 (zmod64 ml)
          | _, _ => xinsideF fs fk b off len (sm_base m) 0 (sm_len m)
          end) then true
      else inside_mapsF fs fk rest b off len
  end.

Definition safe_rangeF (fs : fdig) (fk : list kentry) (ms : list smap) (b : expr) (off : Z) (len : expr) : bool :=
  if (match xhiF fs fk len with
      | Some lh =>
         match erange fk b with
         | Some (lo, hi) => if (Z.leb IMG_LO (lo + off) && Z.leb (hi + off + lh) IMG_HI)%bool then true
                            else if (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) 0x1000)%bool then true
                            else if (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)%bool
                                 then lin_ge0F fs fk [(b, off)] [(e_top, 0%Z)] else false
         | None => false
         end
      | None => false
      end) then true
  else inside_mapsF fs fk ms b off len.

Definition grant_keep_bF (fs : fdig) (fk : list kentry) (ms : list smap) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => if Nat.leb w 8 then safe_rangeF fs fk ms b o (ELit (Z.of_nat w)) else false
  | KZero (SA b o) l => safe_rangeF fs fk ms b o l
  | KBlob (SA b o) l _ => safe_rangeF fs fk ms b o l
  | KImg lo hi => (Z.leb 0 lo && Z.leb hi 0x1000) || (Z.leb IMG_LO lo && Z.leb hi IMG_HI)
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
  destruct len; destruct (sm_len m); rewrite ?zmod64_eq2, ?xinsideF_eq, ?xinside_fk, ?lin_insideF_eq;
    match goal with |- (if ?c then true else ?r) = (?c || ?r)%bool => destruct c; reflexivity end.
Qed.

Lemma safe_rangeF_eq : forall k ms b off len,
  safe_rangeF (SFS (facts_of k)) (facts_of k) ms b off len = safe_range k ms b off len.
Proof.
  intros. unfold safe_rangeF, safe_range. rewrite xhiF_eq, xhi_fk, erange_fk, inside_mapsF_eq.
  destruct (xhi k len) as [lh|]; [|reflexivity]. destruct (erange k b) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb IMG_LO (lo + off) && Z.leb (hi + off + lh) IMG_HI)%bool; [reflexivity|].
  destruct (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) 0x1000)%bool; [reflexivity|].
  rewrite lin_ge0F_eq, lin_ge0_fk.
  destruct (Z.leb 0 (lo + off) && Z.leb (hi + off + lh) two64)%bool; reflexivity.
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

(* [comment removed for export] *)
Definition kn_havocD (fs : fdig) (fk : list kentry) (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let '(ci1, cc) := cc_get fk (CC (kdisj_sdis fs fk fk) fs [] []) ub in
  havocF fk (mk_si fs fk ub uk un ci1) ub uk un k cc (ST [] None).
Lemma kn_havocD_eq : forall k ub uk un, kn_havocD (SFS (facts_of k)) (facts_of k) k ub uk un = kn_havoc k ub uk un.
Proof. intros. reflexivity. Qed.
Definition kn_unfillD (fs : fdig) (fk : list kentry) (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let '(ci1, cc) := cc_get fk (CC (kdisj_sdis fs fk fk) fs [] []) ub in
  unfillF fk (mk_si fs fk ub uk un ci1) k cc (ST [] None).
Lemma kn_unfillD_eq : forall k ub uk un, kn_unfillD (SFS (facts_of k)) (facts_of k) k ub uk un = kn_unfill k ub uk un.
Proof. intros. reflexivity. Qed.
Definition slots_keepD (fs : fdig) (fk : list kentry) (ub : expr) (uk : Z) (un : expr) (ss : list sslot) : list sslot :=
  List.filter (slot_keep_bF fs fk ub uk un) ss.
Lemma slots_keepD_eq : forall k ub uk un ss, slots_keepD (SFS (facts_of k)) (facts_of k) ub uk un ss = slots_keep k ub uk un ss.
Proof. intros. unfold slots_keepD, slots_keep. apply filter_ext. intros s. apply slot_keep_bF_eq. Qed.
Definition slot_apart_bD (fs : fdig) (fk : list kentry) (ub : expr) (uk : Z) (un : expr) (s : sslot) : bool :=
  let '(hb, hk) := split_lit (sl_start s) in ranges_apart_xF fs fk ub uk un hb (hk - 4) (sl_stride s).
Definition slots_unfillD (fs : fdig) (fk : list kentry) (ub : expr) (uk : Z) (un : expr) (ss : list sslot) : list sslot :=
  List.filter (slot_apart_bD fs fk ub uk un) ss.
Lemma slots_unfillD_eq : forall k ub uk un ss, slots_unfillD (SFS (facts_of k)) (facts_of k) ub uk un ss = slots_unfill k ub uk un ss.
Proof.
  intros. unfold slots_unfillD, slots_unfill. apply filter_ext. intros s. unfold slot_apart_bD, slot_apart_b.
  destruct (split_lit (sl_start s)). apply ranges_apart_xD_eq.
Qed.
Definition kn_grant_filterD (fs : fdig) (fk : list kentry) (k : list kentry) (ms : list smap) : list kentry :=
  List.filter (grant_keep_bF fs fk ms) k.
Definition slots_grant_filterD (fs : fdig) (fk : list kentry) (ms : list smap) (ss : list sslot) : list sslot :=
  List.filter (fun s => let '(hb, hk) := split_lit (sl_start s) in safe_rangeF fs fk ms hb (hk - 4) (sl_stride s)) ss.
Lemma kn_grant_filterD_eq : forall k ms, kn_grant_filterD (SFS (facts_of k)) (facts_of k) k ms = kn_grant_filter k ms.
Proof. intros. reflexivity. Qed.
Lemma slots_grant_filterD_eq : forall k ms ss, slots_grant_filterD (SFS (facts_of k)) (facts_of k) ms ss = slots_grant_filter k ms ss.
Proof. intros. reflexivity. Qed.
Hint Rewrite kn_havocD_eq kn_unfillD_eq slots_keepD_eq slots_unfillD_eq kn_grant_filterD_eq slots_grant_filterD_eq : nd.

Definition kn_mmap (v : N) (n : expr) (nlo : Z) (ms : list smap) : list kentry :=
  [KRange (EVar v) 0x1000 (TOPMAX - nlo); KAlign (EVar v) 4096;
   KWr (SA (EVar v) 0) n; KZero (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) IMG_LO) (ELit (IMG_HI - IMG_LO)) (SA (EVar v) 0) n;
   KDisj (SA e_sp0 (- STK)) (ELit STKWIN) (SA (EVar v) 0) n]   (* [comment removed for export] *)
  ++ map (fun m => KDisj (SA (sm_base m) 0) (sm_len m) (SA (EVar v) 0) n) ms.

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

(* [comment removed for export] *)
Definition after_call (cs : cstate) (ret : Z) (rv : option expr) (k' : list kentry) : option cstate :=
  let ss := c_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt nx k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (CS (SS ret sr2 [] k' (nx + NCS)%N) (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive summary : Type := SumMemcpy | SumF | SumEnframe | SumFreePro | SumMainRet | SumPrintf.

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
Ltac nd_scrut x y :=
  first [ constr_eq x y
        | replace x with y by (autorewrite with nd; reflexivity)
        | replace x with y by (symmetry; autorewrite with nd; reflexivity) ].
Ltac nd_step :=
  first [ reflexivity
        | lazymatch goal with
          | |- (match ?x with _ => _ end) = (match ?y with _ => _ end) => nd_scrut x y; destruct y
          | |- (if ?x then _ else _) = (if ?y then _ else _) => nd_scrut x y; destruct y
          | |- Some _ = Some _ => f_equal
          | |- (_, _) = (_, _) => f_equal
          | |- _ => progress (autorewrite with nd)
          end ].

Definition mmap_len_ref (cs : cstate) : option (expr * Z * Z) :=
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
Definition mmap_len (cs : cstate) : option (expr * Z * Z) :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  match reg_lit cs 11 with
  | Some len => Some (ELit (page_up len), len, page_up len)
  | None =>
      let le := reg cs 11 in
      let ne0 := page_up_e le in
      (* [comment removed for export] *)
      let ne := match foldKT fs fk ne0 with ELit z => ELit z | _ => ne0 end in
      match xloF fs fk le, xhiF fs fk le, xhiF fs fk ne with
      | Some lo, Some lhi, Some nhi =>
          if (Z.leb (lhi + 4095) (2 ^ 40) && expr_vars_lt (s_next (c_ss cs)) ne)%bool
          then Some (ne, lo, nhi) else None
      | _, _, _ => None
      end
  end.
Lemma mmap_len_eq : forall cs, mmap_len cs = mmap_len_ref cs.
Proof. intros. unfold mmap_len, mmap_len_ref. repeat nd_step. Qed.


(* [comment removed for export] *)
Definition node_mmap_ref (cs : cstate) : option (cstate * cstate) :=
  match reg_lit cs 17, reg_lit cs 10, mmap_len cs, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some 0, Some (ne, lo, nhi), Some 3, Some 34, Some m1, Some 0 =>
      if (Z.ltb 0 lo && Z.leb nhi (2 ^ 30) && Z.eqb m1 (two64 - 1)
          && Z.leb (c_nmaps cs + 1) 1000 && Z.leb (c_live cs + nhi) (2 ^ 31) && fresh_ok cs)%bool then
        let v := s_next (c_ss cs) in
        let csf := set_pc (set_reg cs 10 (ELit (two64 - 12))) (pc cs + 4) in
        let ss := c_ss cs in
        let css := CS (SS (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) []
                          (kn_grant_filter (s_know ss) (c_maps cs) ++ kn_mmap v ne (page_up lo) (c_maps cs)) (N.succ v))
                      (SM (EVar v) ne true :: c_maps cs) (c_nmaps cs + 1) (c_live cs + nhi)
                      (slots_grant_filter (s_know ss) (c_maps cs) (c_slots cs)) in
        Some (csf, css)
      else None
  | _, _, _, _, _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mmap (cs : cstate) : option (cstate * cstate) :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  match reg_lit cs 17, reg_lit cs 10, mmap_len cs, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some 0, Some (ne, lo, nhi), Some 3, Some 34, Some m1, Some 0 =>
      if (Z.ltb 0 lo && Z.leb nhi (2 ^ 30) && Z.eqb m1 (two64 - 1)
          && Z.leb (c_nmaps cs + 1) 1000 && Z.leb (c_live cs + nhi) (2 ^ 31) && fresh_ok cs)%bool then
        let v := s_next (c_ss cs) in
        let csf := set_pc (set_reg cs 10 (ELit (two64 - 12))) (pc cs + 4) in
        let ss := c_ss cs in
        let css := CS (SS (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) []
                          (kn_grant_filterD fs fk (kn cs) (c_maps cs) ++ kn_mmap v ne (page_up lo) (c_maps cs)) (N.succ v))
                      (SM (EVar v) ne true :: c_maps cs) (c_nmaps cs + 1) (c_live cs + nhi)
                      (slots_grant_filterD fs fk (c_maps cs) (c_slots cs)) in
        Some (csf, css)
      else None
  | _, _, _, _, _, _, _ => None
  end.
Lemma node_mmap_eq : forall cs, node_mmap cs = node_mmap_ref cs.
Proof. intros. unfold node_mmap, node_mmap_ref. repeat nd_step. Qed.



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
Definition len_eqbD (fs : fdig) (fk : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (if lin_ge0F fs fk [(n, 0%Z)] [(m, 0%Z)] then lin_ge0F fs fk [(m, 0%Z)] [(n, 0%Z)] else false).
Lemma len_eqbD_eq : forall k n m, len_eqbD (SFS (facts_of k)) (facts_of k) n m = len_eqb k n m.
Proof. intros. reflexivity. Qed.
Definition smap_matchD (fs : fdig) (fk : list kentry) (b : expr) (n : expr) (m : smap) : bool :=
  (sm_exact m && expr_eqb b (sm_base m) && len_eqbD fs fk n (sm_len m))%bool.
Lemma smap_matchD_eq : forall k b n m, smap_matchD (SFS (facts_of k)) (facts_of k) b n m = smap_match k b n m.
Proof. intros. reflexivity. Qed.
Lemma existsb_smap_matchD_eq : forall k b n ms, existsb (smap_matchD (SFS (facts_of k)) (facts_of k) b n) ms = existsb (smap_match k b n) ms.
Proof. intros. reflexivity. Qed.
Definition remove_exactD (fs : fdig) (fk : list kentry) (ms : list smap) (b : expr) (n : expr) : list smap :=
  List.filter (fun m => negb (smap_matchD fs fk b n m)) ms.
Lemma remove_exactD_eq : forall k ms b n, remove_exactD (SFS (facts_of k)) (facts_of k) ms b n = remove_exact k ms b n.
Proof. intros. reflexivity. Qed.
Definition others_apartD (fs : fdig) (fk : list kentry) (ms : list smap) (b : expr) (n : expr) : bool :=
  forallb (fun m => if smap_matchD fs fk b n m then true else ranges_apart_xF fs fk b 0 n (sm_base m) 0 (sm_len m)) ms.
Lemma others_apartD_eq : forall k ms b n, others_apartD (SFS (facts_of k)) (facts_of k) ms b n = others_apart k ms b n.
Proof. intros. reflexivity. Qed.
Hint Rewrite len_eqbD_eq smap_matchD_eq existsb_smap_matchD_eq remove_exactD_eq others_apartD_eq : nd.

(* [comment removed for export] *)
Definition munmap_len_ref (cs : cstate) : option (expr * Z) :=
  match reg_lit cs 11 with
  | Some len => if (Z.ltb 0 len && Z.leb (page_up len) (2 ^ 40))%bool then Some (ELit (page_up len), page_up len) else None
  | None =>
      let le := reg cs 11 in
      match xlo (kn cs) le, xhi (kn cs) le with
      | Some lo, Some hi => if (Z.ltb 0 lo && Z.leb 12 (ealign (kn cs) le))%bool then Some (le, hi) else None
      | _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition munmap_len (cs : cstate) : option (expr * Z) :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  match reg_lit cs 11 with
  | Some len => if (Z.ltb 0 len && Z.leb (page_up len) (2 ^ 40))%bool then Some (ELit (page_up len), page_up len) else None
  | None =>
      let le := reg cs 11 in
      match xloF fs fk le, xhiF fs fk le with
      | Some lo, Some hi => if (Z.ltb 0 lo && Z.leb 12 (ealignT fs fk le))%bool then Some (le, hi) else None
      | _, _ => None
      end
  end.
Lemma munmap_len_eq : forall cs, munmap_len cs = munmap_len_ref cs.
Proof. intros. unfold munmap_len, munmap_len_ref. repeat nd_step. Qed.


Definition node_munmap_ref (cs : cstate) : option cstate :=
  match reg_lit cs 17, munmap_len cs with
  | Some 215, Some (n, nhi) =>
      let b := reg cs 10 in
      if (Z.leb nhi (2 ^ 30) && existsb (smap_match (kn cs) b n) (c_maps cs)
          && Z.leb 12 (ealign (kn cs) b) && others_apart (kn cs) (c_maps cs) b n
          && match ehi (kn cs) b with Some hi => Z.leb (hi + nhi) TASK_SIZE | None => false end)%bool then  (* [comment removed for export] *)
        let ss := c_ss cs in
        Some (CS (SS (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) []
                     (kn_unfill (s_know ss) b 0 n) (s_next ss))
                 (remove_exact (kn cs) (c_maps cs) b n) (c_nmaps cs) (c_live cs)
                 (slots_unfill (s_know ss) b 0 n (c_slots cs)))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_munmap (cs : cstate) : option cstate :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  match reg_lit cs 17, munmap_len cs with
  | Some 215, Some (n, nhi) =>
      let b := reg cs 10 in
      if (Z.leb nhi (2 ^ 30) && existsb (smap_matchD fs fk b n) (c_maps cs)
          && Z.leb 12 (ealignT fs fk b) && others_apartD fs fk (c_maps cs) b n
          && match ehiD fs b with Some hi => Z.leb (hi + nhi) TASK_SIZE | None => false end)%bool then  (* [comment removed for export] *)
        let ss := c_ss cs in
        Some (CS (SS (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) []
                     (kn_unfillD fs fk (kn cs) b 0 n) (s_next ss))
                 (remove_exactD fs fk (c_maps cs) b n) (c_nmaps cs) (c_live cs)
                 (slots_unfillD fs fk b 0 n (c_slots cs)))
      else None
  | _, _ => None
  end.
Lemma node_munmap_eq : forall cs, node_munmap cs = node_munmap_ref cs.
Proof. intros. unfold node_munmap, node_munmap_ref. repeat nd_step. Qed.


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
Definition rw_okD (fs : fdig) (fk : list kentry) (e : expr) (n : Z) : bool :=
  let '(b, off) := split_lit e in
  (if kwritableD fs fk fk b off n then off_imageD fs fk b off n else false)%bool.
Definition rw_ok_xD (fs : fdig) (fk : list kentry) (e : expr) (n : expr) : bool :=
  let '(b, off) := split_lit e in
  (match xloF fs fk n with Some l => Z.ltb 0 l | None => false end
   && (if kwritable_xD fs fk fk b off n then off_image_xD fs fk b off n else false))%bool.
Definition apart_eD (fs : fdig) (fk : list kentry) (e1 : expr) (n1 : Z) (e2 : expr) (n2 : Z) : bool :=
  let '(b1, o1) := split_lit e1 in let '(b2, o2) := split_lit e2 in ranges_apartF fs fk b1 o1 n1 b2 o2 n2.
Definition apart_xD (fs : fdig) (fk : list kentry) (e1 : expr) (n1 : expr) (e2 : expr) (n2 : expr) : bool :=
  let '(b1, o1) := split_lit e1 in let '(b2, o2) := split_lit e2 in ranges_apart_xF fs fk b1 o1 n1 b2 o2 n2.
Lemma facts_of_idem' : forall k, facts_of (facts_of k) = facts_of k.
Proof. intros. apply facts_of_idem. Qed.
Lemma kwritableD_eq2 : forall k b off n, kwritableD (SFS (facts_of k)) (facts_of k) (facts_of k) b off n = kwritable (facts_of k) (facts_of k) b off n.
Proof. intros. rewrite <- (facts_of_idem' k) at 1 2. rewrite kwritableD_eq. rewrite kwritable_fk1. reflexivity. Qed.
Lemma kwritable_xD_eq2 : forall k b off n, kwritable_xD (SFS (facts_of k)) (facts_of k) (facts_of k) b off n = kwritable_x (facts_of k) (facts_of k) b off n.
Proof. intros. rewrite <- (facts_of_idem' k) at 1 2. rewrite kwritable_xD_eq. rewrite kwritable_x_fk1. reflexivity. Qed.
Lemma off_imageD_eq : forall k b off n, off_imageD (SFS (facts_of k)) (facts_of k) b off n = off_image (facts_of k) b off n.
Proof. intros. unfold off_imageD, off_image. rewrite facts_of_idem'. reflexivity. Qed.
Lemma off_image_xD_eq : forall k b off n, off_image_xD (SFS (facts_of k)) (facts_of k) b off n = off_image_x (facts_of k) b off n.
Proof. intros. unfold off_image_xD, off_image_x. rewrite facts_of_idem'. reflexivity. Qed.
Lemma rw_okD_eq : forall k e n, rw_okD (SFS (facts_of k)) (facts_of k) e n = rw_ok k e n.
Proof. intros. unfold rw_okD, rw_ok. destruct (split_lit e) as [b off]. rewrite kwritableD_eq2, off_imageD_eq. reflexivity. Qed.
Lemma rw_ok_xD_eq : forall k e n, rw_ok_xD (SFS (facts_of k)) (facts_of k) e n = rw_ok_x k e n.
Proof. intros. unfold rw_ok_xD, rw_ok_x. destruct (split_lit e) as [b off]. rewrite xloF_eq, kwritable_xD_eq2, off_image_xD_eq. reflexivity. Qed.
Lemma apart_eD_eq : forall k e1 n1 e2 n2, apart_eD (SFS (facts_of k)) (facts_of k) e1 n1 e2 n2 = apart_e k e1 n1 e2 n2.
Proof. intros. reflexivity. Qed.
Lemma apart_xD_eq : forall k e1 n1 e2 n2, apart_xD (SFS (facts_of k)) (facts_of k) e1 n1 e2 n2 = apart_x k e1 n1 e2 n2.
Proof. intros. reflexivity. Qed.
Definition havoc_eD (fs : fdig) (fk : list kentry) (k : list kentry) (e : expr) (n : Z) : list kentry :=
  let '(b, o) := split_lit e in kn_havocD fs fk k b o (ELit n).
Definition havoc_xD (fs : fdig) (fk : list kentry) (k : list kentry) (e : expr) (n : expr) : list kentry :=
  let '(b, o) := split_lit e in kn_havocD fs fk k b o n.
Lemma havoc_eD_eq : forall k e n, havoc_eD (SFS (facts_of k)) (facts_of k) k e n = havoc_e k e n.
Proof. intros. reflexivity. Qed.
Lemma havoc_xD_eq : forall k e n, havoc_xD (SFS (facts_of k)) (facts_of k) k e n = havoc_x k e n.
Proof. intros. reflexivity. Qed.
Hint Rewrite rw_okD_eq rw_ok_xD_eq apart_eD_eq apart_xD_eq havoc_eD_eq havoc_xD_eq : nd.

(* [comment removed for export] *)
Definition call_memcpy_ref (cs : cstate) : option cstate :=
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
Definition call_memcpy (cs : cstate) : option cstate :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  match ret_lit cs, ehiD fs (reg cs 12) with
  | Some ret, Some nhi =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      if (Z.ltb 0 nhi && Z.leb nhi (2 ^ 40) && rw_ok_xD fs fk dst ne && rw_ok_xD fs fk src ne && apart_xD fs fk dst ne src ne
          && match ehiD fs dst, ehiD fs src with
             | Some dh, Some sh => Z.ltb (dh + nhi) two64 && Z.ltb (sh + nhi) two64 | _, _ => false end)%bool
      then match after_call cs ret (Some dst) (havoc_xD fs fk (kn cs) dst ne) with
           | Some cs' => let '(db, dk) := split_lit dst in Some (set_slots cs' (slots_keepD fs fk db dk ne (c_slots cs)))
           | None => None
           end
      else None
  | _, _ => None
  end.
Lemma call_memcpy_eq : forall cs, call_memcpy cs = call_memcpy_ref cs.
Proof. intros. unfold call_memcpy, call_memcpy_ref. repeat nd_step. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kread8e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.
Definition kread8eD (fs : fdig) (fk k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookupAF fs fk segs k b off 8 8%Z (off + 8)%Z false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.
Lemma kread8eD_eq : forall k b off, kread8eD (SFS (facts_of k)) (facts_of k) k b off = kread8e k b off.
Proof.
  intros. unfold kread8eD, kread8e, know_lookup. change 8%Z with (Z.of_nat 8) at 1. change (off + 8)%Z with (off + Z.of_nat 8)%Z.
  rewrite know_lookupAF_eq, know_lookupA_fk1. reflexivity.
Qed.
Lemma kread8eD_bucket : forall fs fk k b off, kread8eD fs fk (List.filter (lk_relevant b) k) b off = kread8eD fs fk k b off.
Proof. intros. unfold kread8eD. rewrite know_lookupAF_bucket. reflexivity. Qed.
Hint Rewrite kread8eD_bucket kread8eD_eq : nd.

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
Definition rw_okbD (fs : fdig) (fk : list kentry) (b : expr) (off n : Z) : bool :=
  (if kwritableD fs fk fk b off n then off_imageD fs fk b off n else false)%bool.
Lemma rw_okbD_eq : forall k b off n, rw_okbD (SFS (facts_of k)) (facts_of k) b off n = rw_okb k b off n.
Proof. intros. unfold rw_okbD, rw_okb. rewrite kwritableD_eq2, off_imageD_eq. reflexivity. Qed.
Hint Rewrite rw_okbD_eq : nd.

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
Definition call_enframe_ref (cs : cstate) : option cstate :=
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
        let nx1 := if symb then N.succ v else v in
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
            && kimg_covers k (d_sctbl A) (d_sctbl A + 96)
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
Definition call_enframe (cs : cstate) : option cstate :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some idx =>
    let g := reg cs 10 in let ne := reg cs 12 in let k := kn cs in
    let '(gb, gk) := split_lit g in
    match kread8eD fs fk k gb (gk + 16), kreadZD fs fk k gb (gk + 32) 8 with
    | Some Me, Some W =>
      let ml := w_maplen W in let li := w_lastidx W in let sc := w_sizeclass W in
      let stride := slot_stride ml li sc in
      let start := mkAlu ALU_ADD Me (ELit (16 + stride * idx)) in
      let '(sb, sk) := split_lit start in
      match xloF fs fk ne, xhiF fs fk ne, ehiD fs Me with
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
        let k0 := kf ++ k in let fk0 := facts_of k0 in let fs0 := SFS fk0 in
        let s := SL start (ELit stride) ne off (ELit W) idx p in
        let nx1 := if symb then N.succ v else v in
        if ((implb (orb (ml =? 0) (negb (li =? 0))) (sc <? 48))
            && (16 <=? stride) && (stride <? 2 ^ 31) && (stride mod 16 =? 0) && (0 <=? idx) && (idx <? 32)
            && (stride * idx + 4096 <=? 16 * 65536)
            && (4 <=? ealignT fs fk start)
            && (0 <=? nlo) && (nhi + 4 <=? stride)
            && (mh + 16 + stride * idx + stride + 5 <=? two64)
            && flat_bD fs gb gk 40
            && ranges_apartF fs fk gb (gk + 16) 8 sb (sk - 3) (stride - 1)
            && match kreadZD fs fk k sb (sk - 4) 1 with Some 0 => true | _ => false end
            && rw_okbD fs fk sb (sk - 4) stride
            && kimg_covers k (d_sctbl A) (d_sctbl A + 96)
            && flat_bD fs0 pb pk 1 && flat_bD fs0 pnb pnk 1
            && expr_vars_lt v start && expr_vars_lt v ne
            && slot_vars_lt nx1 s
            && fresh_ok cs)%bool
        then
          let cs1 := if symb then bump_next cs 1 else cs in
          let len1 := mkAlu ALU_ADD (times16 off) (ELit 3) in
          let len2 := mkAlu ALU_SUB (ELit (stride - 4)) (mkAlu ALU_ADD ne (times16 off)) in
          let k1 := kn_havocD fs0 fk0 k0 sb (sk - 3) len1 in
          let k2 := kn_havoc k1 pnb pnk len2 in
          let kl := if symb then [] else match ne with ELit n0 => slot_lit_words sb sk idx stride (n0 mod two64) | _ => [] end in
          match after_call cs1 ret (Some p) (kl ++ k2) with
          | Some cs' => Some (set_slots cs' (s :: slots_keepD fs fk sb (sk - 4) (ELit stride) (c_slots cs)))
          | None => None
          end
        else None
      | _, _, _ => None
      end
    | _, _ => None
    end
  | _, _ => None
  end.
Lemma call_enframe_eq : forall cs, call_enframe cs = call_enframe_ref cs.
Proof. intros. unfold call_enframe, call_enframe_ref. repeat nd_step. Qed.


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
Definition rw_okb_xD (fs : fdig) (fk : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  (if kwritable_xD fs fk fk b off n then off_image_xD fs fk b off n else false)%bool.
Lemma rw_okb_xD_eq : forall k b off n, rw_okb_xD (SFS (facts_of k)) (facts_of k) b off n = rw_okb_x k b off n.
Proof. intros. unfold rw_okb_xD, rw_okb_x. rewrite kwritable_xD_eq2, off_image_xD_eq. reflexivity. Qed.
Hint Rewrite rw_okb_xD_eq : nd.

(* [comment removed for export] *)
Definition call_enframe_x_ref (cs : cstate) : option cstate :=
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
              && kimg_covers k (d_sctbl A) (d_sctbl A + 96)
              && flat_b k0 pb pk 1 && flat_b k0 pnb pnk 1
              && expr_vars_lt v start && expr_vars_lt v ne && expr_vars_lt v stride && expr_vars_lt v We
              && slot_vars_lt (N.succ v) s
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
(* [comment removed for export] *)
Definition call_enframe_x (cs : cstate) : option cstate :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some 0 =>
    let g := reg cs 10 in let ne := reg cs 12 in let k := kn cs in
    let '(gb, gk) := split_lit g in
    match kread8eD fs fk k gb (gk + 16), kread8eD fs fk k gb (gk + 32) with
    | Some Me, Some We =>
      match decode_W We with
      | Some (Se, c) =>
        let stride := mkAlu ALU_ADD (mkMd M_MUL (ELit 4096) Se) (ELit (-16)) in
        let start := mkAlu ALU_ADD Me (ELit 16) in
        let '(sb, sk) := split_lit start in
        match xloF fs fk ne, xhiF fs fk ne, ehiD fs Me, xloF fs fk Se, xhiF fs fk Se with
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
          let k0 := kf ++ k in let fk0 := facts_of k0 in let fs0 := SFS fk0 in
          let s := SL start stride ne off We 0 p in
          if ((c mod 32 =? 0) && (1 <=? Slo) && (Shi <=? 2 ^ 19)
              && (4 <=? ealignT fs fk start)
              && (0 <=? nlo) && lin_ge0F fs fk [(stride, 0%Z)] [(ne, 4%Z)]
              && (mh + 16 + shi + 5 <=? two64)
              && flat_bD fs gb gk 40
              && ranges_apart_xF fs fk gb (gk + 16) (ELit 8) sb (sk - 3) (mkAlu ALU_ADD stride (ELit (-1)))
              && match kreadZD fs fk k sb (sk - 4) 1 with Some 0 => true | _ => false end
              && rw_okb_xD fs fk sb (sk - 4) stride
              && kimg_covers k (d_sctbl A) (d_sctbl A + 96)
              && flat_bD fs0 pb pk 1 && flat_bD fs0 pnb pnk 1
              && expr_vars_lt v start && expr_vars_lt v ne && expr_vars_lt v stride && expr_vars_lt v We
              && slot_vars_lt (N.succ v) s
              && fresh_ok cs)%bool
          then
            let cs1 := bump_next cs 1 in
            let len1 := mkAlu ALU_ADD (times16 off) (ELit 3) in
            let len2 := mkAlu ALU_ADD rexp (ELit (-4)) in
            let k1 := kn_havocD fs0 fk0 k0 sb (sk - 3) len1 in
            let k2 := kn_havoc k1 pnb pnk len2 in
            match after_call cs1 ret (Some p) k2 with
            | Some cs' => Some (set_slots cs' (s :: slots_keepD fs fk sb (sk - 4) stride (c_slots cs)))
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
Lemma call_enframe_x_eq : forall cs, call_enframe_x cs = call_enframe_x_ref cs.
Proof. intros. unfold call_enframe_x, call_enframe_x_ref. repeat nd_step. Qed.


Definition call_enframe2 (cs : cstate) : option cstate :=
  match call_enframe cs with Some cs' => Some cs' | None => call_enframe_x cs end.

(* [comment removed for export] *)
Definition find_slot (k : list kentry) (pa : expr) (ss : list sslot) : option sslot :=
  List.find (fun s => if expr_eqb (sl_p s) pa then true else len_eqb k (sl_p s) pa) ss.
Definition find_slotD (fs : fdig) (fk : list kentry) (pa : expr) (ss : list sslot) : option sslot :=
  List.find (fun s => if expr_eqb (sl_p s) pa then true else len_eqbD fs fk (sl_p s) pa) ss.
Lemma find_slotD_eq : forall k pa ss, find_slotD (SFS (facts_of k)) (facts_of k) pa ss = find_slot k pa ss.
Proof. intros. reflexivity. Qed.
Hint Rewrite find_slotD_eq : nd.

Definition remove_slot (s : sslot) (ss : list sslot) : list sslot :=
  List.filter (fun s' => negb (expr_eqb (sl_p s') (sl_p s))) ss.

(* [comment removed for export] *)
Definition call_freepro_ref (cs : cstate) : option cstate :=
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
                && kimg_covers k (d_sctbl A) (d_sctbl A + 96)
                && rw_okb k qb qk 48
                && (if hh + hk + shi + 48 <=? splo then true
                    else (* [comment removed for export] *)
                         (kdisj_apart_x k k eb ek (ELit 4) e_sp0 (- STK) (ELit STKWIN)
                          && (hh + hk + shi <? 2 ^ 47) && lin_ge0 k [(spm, 0%Z)] [(e_top, 0%Z)]))
                && ((ghi + 88 <=? splo)
                    || (* [comment removed for export] *)
                       (kdisj_apart_x k k gb gk (ELit 40) e_sp0 (- STK) (ELit STKWIN)
                        && (ghi + 40 <? 2 ^ 47) && lin_ge0 k [(spm, 0%Z)] [(e_top, 0%Z)]))
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
                  Some (CS (SS (t_freepro_k A) sr2 [] kn' (nx + NCS)%N) (c_maps cs) (c_nmaps cs) (c_live cs)
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
Definition call_freepro (cs : cstate) : option cstate :=
  let fk := facts_of (kn cs) in let fs := SFS fk in
  let k := kn cs in let pa := reg cs 10 in let sp := reg cs 2 in
  match find_slotD fs fk pa (c_slots cs) with
  | Some s =>
    let strd := sl_stride s in let idx := sl_idx s in
    let sidx := match strd with ELit z => Some ((z mod two64) * idx)%Z | _ => if idx =? 0 then Some 0 else None end in
    match decode_W (sl_W s), xloF fs fk strd, xhiF fs fk strd, sidx with
    | Some (Se, c), Some slo, Some shi, Some si =>
      let li := c mod 32 in let sc := (c / 64) mod 64 in
      let Me := mkAlu ALU_ADD (sl_start s) (ELit (- (16 + si))) in
      let '(mb, mk) := split_lit Me in
      match kread8eD fs fk k mb mk with
      | Some ge =>
        let '(gb, gk) := split_lit ge in
        match kread8eD fs fk k gb (gk + 16), kread8eD fs fk k gb (gk + 32), kreadZD fs fk k gb (gk + 24) 4, kreadZD fs fk k gb (gk + 28) 4,
              lin_lowbits_kn k ge 12 with
        | Some Me', Some We, Some avail, Some freed, Some gm12 =>
          let area := mkAlu ALU_ADD ge (ELit (- gm12)) in
          let '(ab, ak) := split_lit area in
          let '(hb, hk) := split_lit (sl_start s) in
          let spm := mkAlu ALU_ADD sp (ELit (-48)) in
          let '(qb, qk) := split_lit spm in
          let e := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-4))) in
          let '(eb, ek) := split_lit e in
          match kread8eD fs fk k ab ak, kread8eD fs fk k (ELit 0) (d_malloc_ctx A), xloF fs fk (sl_off s), xhiF fs fk (sl_off s),
                ehiD fs ge, eloD fs sp, ehiD fs hb, xloF fs fk Se, xhiF fs fk Se with
          | Some se, Some se', Some olo, Some ohi, Some ghi, Some splo, Some hh, Some Slo, Some Shi =>
            let qlo := si / 16 + olo in let qhi := si / 16 + ohi in
            let nx := s_next (c_ss cs) in
            let reserved := mkAlu ALU_SUB (mkAlu ALU_ADD strd (ELit (-4))) (mkAlu ALU_ADD (sl_n s) (times16 (sl_off s))) in
            let e12 := mkAlu ALU_ADD (sl_start s) (mkAlu ALU_ADD strd (ELit (-16))) in
            if (len_eqbD fs fk Me' Me
                && expr_eqb We (sl_W s)
                && (Shi <=? 2 ^ 40)
                && (0 <=? idx) && (idx <=? li)
                && (((sc <? 48) && (size_class sc * idx <=? qlo) && (qhi <? size_class sc * (idx + 1)))
                    || ((sc =? 63) && (1 <=? Slo) && (li =? 0)))
                && ((Shi =? 0) || (qhi <=? Slo * 256 - 1))
                && (0 <=? olo)
                && negb (Z.testbit avail idx) && negb (Z.testbit freed idx)
                && expr_eqb se se'
                && flat_bD fs mb mk 8 && flat_bD fs gb gk 40 && flat_bD fs ab ak 8
                && match kreadZD fs fk k eb ek 1 with Some 0 => true | _ => false end
                && rw_okbD fs fk eb ek 1
                && flat_bD fs hb (hk - 4) (shi + 5)
                && kimg_covers k (d_sctbl A) (d_sctbl A + 96)
                && rw_okbD fs fk qb qk 48
                && (if hh + hk + shi + 48 <=? splo then true
                    else (* [comment removed for export] *)
                         (kdisj_apart_xF fs fk k eb ek (ELit 4) e_sp0 (- STK) (ELit STKWIN)
                          && (hh + hk + shi <? 2 ^ 47) && lin_ge0F fs fk [(spm, 0%Z)] [(e_top, 0%Z)]))
                && ((ghi + 88 <=? splo)
                    || (kdisj_apart_xF fs fk k gb gk (ELit 40) e_sp0 (- STK) (ELit STKWIN)
                        && (ghi + 40 <? 2 ^ 47) && lin_ge0F fs fk [(spm, 0%Z)] [(e_top, 0%Z)]))
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
                  Some (CS (SS (t_freepro_k A) sr2 [] kn' (nx + NCS)%N) (c_maps cs) (c_nmaps cs) (c_live cs)
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
Lemma call_freepro_eq : forall cs, call_freepro cs = call_freepro_ref cs.
Proof. intros. unfold call_freepro, call_freepro_ref. repeat nd_step. Qed.



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
Definition node_stdio_write_ref (cs : cstate) : option (Z * list Z * cstate) :=
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
            && (d_rw_lo A <=? f) && (f + 232 <=? d_canary A) && (d_canary A + 8 <=? IMG_HI)
            && (IMG_LO <=? d_canary_got A) && (d_canary_got A + 8 <=? IMG_HI)
            && rw_okb k qb qk 112
            && (4294967296 + 112 <=? splo) && (sphi <=? 0x800000000000)
            && (shi + l <=? 2 ^ 47) && (wp <=? 2 ^ 47)   (* [comment removed for export] *)
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
Definition node_stdio_write (cs : cstate) : option (Z * list Z * cstate) :=
  let fk := facts_of (kn cs) in let fs := SFS fk in let kz := List.filter (lk_relevant (ELit 0)) (kn cs) in
  let k := kn cs in
  match ret_lit cs, reg_lit cs 10, reg_lit cs 12 with
  | Some ret, Some f, Some l =>
    if negb (Z.eqb f (d_stdout A)) then None else
    match kreadZD fs fk kz (ELit 0) (f + 120) 4, kreadZD fs fk kz (ELit 0) (f + 40) 8, kreadZD fs fk kz (ELit 0) (f + 56) 8,
          kread8eD fs fk kz (ELit 0) (f + 88), kread8eD fs fk kz (ELit 0) (f + 96),
          kreadZD fs fk kz (ELit 0) (d_canary_got A) 8, kread8eD fs fk kz (ELit 0) (d_canary A) with
    | Some fd, Some wp, Some wb, Some bufp, Some bufsz, Some cg, Some _ =>
      let s := reg cs 11 in let sp := reg cs 2 in
      let '(sb, sk) := split_lit s in
      let spm := mkAlu ALU_ADD sp (ELit (-112)) in
      let '(qb, qk) := split_lit spm in
      let np := wp - wb in
      match kread_bytesD fs fk (Z.to_nat np) kz (ELit 0) wb, kread_bytesD fs fk (Z.to_nat l) k sb sk,
            eloD fs sp, ehiD fs sp, ehiD fs s with
      | Some pend, Some extra, Some splo, Some sphi, Some shi =>
        if ((fd =? 1) && (cg =? d_canary A)
            && (0 <=? np) && (np + l <=? 4096)
            && (d_rw_lo A <=? f) && (f + 232 <=? d_canary A) && (d_canary A + 8 <=? IMG_HI)
            && (IMG_LO <=? d_canary_got A) && (d_canary_got A + 8 <=? IMG_HI)
            && rw_okbD fs fk qb qk 112
            && (4294967296 + 112 <=? splo) && (sphi <=? 0x800000000000)
            && (shi + l <=? 2 ^ 47) && (wp <=? 2 ^ 47)   (* [comment removed for export] *)
            && flat_bD fs sb sk (Z.max l 1)
            && (lin_ge0F fs fk [(spm, 0%Z)] [(ELit wp, 0%Z)] || lin_ge0F fs fk [(ELit wb, 0%Z)] [(sp, 0%Z)])
            && (lin_ge0F fs fk [(spm, 0%Z)] [(s, l)] || lin_ge0F fs fk [(s, 0%Z)] [(sp, 0%Z)])
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
                    set_slots cs' (slots_keepD fs fk (ELit 0) (f + 56) (ELit 8)
                                    (slots_keepD fs fk (ELit 0) (f + 32) (ELit 16)
                                      (slots_keepD fs fk qb qk (ELit 112) (c_slots cs)))))
          | None => None
          end
        else None
      | _, _, _, _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _, _ => None
  end.
Lemma node_stdio_write_eq : forall cs, node_stdio_write cs = node_stdio_write_ref cs.
Proof. intros. unfold node_stdio_write, node_stdio_write_ref. repeat nd_step. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition call_mainret (cs : cstate) : option cstate :=
  match reg_lit cs 10 with
  | Some 0 =>
      let ss := c_ss cs in let nx := s_next ss in
      if fresh_ok cs then
        Some (CS (SS (t_main_join A)
                    (sr_upd (sr_upd (sr_upd (sr_upd (s_regs ss) 1 (EVar nx)) 8 (ELit 0)) 10 (ELit 0)) 11 (EVar (N.succ nx)))
                    [] (s_know ss) (nx + 2)%N)
                 (c_maps cs) (c_nmaps cs) (c_live cs) (c_slots cs))
      else None
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PF_WIN : Z := 1056.

Definition call_printf_ref (cs : cstate) : option cstate :=
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
            && kimg_covers k IMG_LO (d_rw_lo A)
            && (4 <=? ealign k sp)
            && rw_okb k qb qk PF_WIN
            && (IMG_HI + PF_WIN <=? splo) && (sphi <=? 0x7fffffffffff)
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
Definition call_printf (cs : cstate) : option cstate :=
  let fk := facts_of (kn cs) in let fs := SFS fk in let kz := List.filter (lk_relevant (ELit 0)) (kn cs) in
  let k := kn cs in let f := d_stdout A in let buf := d_stdout_buf A in
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some 0 =>
    if negb (Z.eqb ret (t_printf_ret A)) then None else
    match kreadZD fs fk kz (ELit 0) f 4, kreadZD fs fk kz (ELit 0) (f + 32) 8, kreadZD fs fk kz (ELit 0) (f + 40) 8,
          kreadZD fs fk kz (ELit 0) (f + 96) 8, kreadZD fs fk kz (ELit 0) (f + 140) 4, kreadZD fs fk kz (ELit 0) (f + 144) 4,
          kread8eD fs fk kz (ELit 0) (d_canary A) with
    | Some flags, Some wend, Some w, Some bsz, Some lock, Some lbf, Some _ =>
      let sp := reg cs 2 in
      let spm := mkAlu ALU_ADD sp (ELit (- PF_WIN)) in
      let '(qb, qk) := split_lit spm in
      match eloD fs sp, ehiD fs sp with
      | Some splo, Some sphi =>
        if ((flags =? 5) && (wend =? buf + 1024) && (buf <=? w) && (w <=? buf + 1022) && (bsz =? 1024)
            && (lock =? 4294967295) && (lbf =? 4294967295)
            && kimg_covers k IMG_LO (d_rw_lo A)
            && (4 <=? ealignT fs fk sp)
            && rw_okbD fs fk qb qk PF_WIN
            && (IMG_HI + PF_WIN <=? splo) && (sphi <=? 0x7fffffffffff)
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
              Some (set_slots cs' (slots_keepD fs fk (ELit 0) w (ELit 2)
                                    (slots_keepD fs fk (ELit 0) (f + 40) (ELit 8)
                                      (slots_keepD fs fk (ELit 0) f (ELit 4)
                                        (slots_keepD fs fk qb qk (ELit PF_WIN) (c_slots cs))))))
          | None => None
          end
        else None
      | _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.
Lemma call_printf_eq : forall cs, call_printf cs = call_printf_ref cs.
Proof. intros. unfold call_printf, call_printf_ref. repeat nd_step. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition F_SPLO : Z := 0x7fff80000000 - 4096.
Definition F_SPHI : Z := 0x800000000000.
Definition call_F (cs : cstate) : option cstate :=
  let k := kn cs in let FR := t_F_frame A in
  match ret_lit cs, reg_lit cs 4, ehi k (reg cs 11) with
  | Some ret, Some tp, Some nhi =>
    let data := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let spm := mkAlu ALU_ADD sp (ELit (- FR)) in
    let '(qb, qk) := split_lit spm in
    match elo k sp, ehi k sp, elo k data, ehi k data with
    | Some splo, Some sphi, Some dlo, Some dhi =>
      if ((ret =? t_F_ret A) && (tp =? t_tp A) && (0 <=? nhi) && (nhi <? t_F_nmax A)
          && (1 <=? dlo) && (dhi + nhi <? 2 ^ 63)
          && ((nhi =? 0) || rw_ok k data nhi || rw_ok_x k data ne)
          && (4 <=? ealign k sp) && (0 <? FR) && rw_okb k qb qk FR
          && (F_SPLO <=? splo) && (sphi <=? F_SPHI)
          && ((dhi + nhi <=? splo - FR) || (sphi <=? dlo)      (* [comment removed for export] *)
              || ((0 <? nhi) && rw_ok k data nhi && apart_e k data nhi spm FR)          (* [comment removed for export] *)
              || (rw_ok_x k data ne && rw_ok_x k spm (ELit FR) && apart_x k spm (ELit FR) data ne))
          && kimg_covers k IMG_LO (d_ro_hi A)
          && kimg_covers k (d_canary_got A) (d_canary_got A + 8)
          && kimg_covers k (d_mcount A) (d_mcount A + 8)
          && fresh_ok cs)%bool
      then
        (* [comment removed for export] *)
        let v := s_next (c_ss cs) in
        let cs1 := bump_next cs 1 in
        let k0 := kimg_cut (kimg_cut k (d_prng A) 8) (d_errno A) 4 in
        let k1 := kn_havoc k0 qb qk (ELit FR) in
        let k2 := kn_havoc k1 (ELit 0) (d_prng A) (ELit 8) in
        let k3 := kn_havoc k2 (ELit 0) (d_errno A) (ELit 4) in
        let k4 := KWord (SA (ELit 0) (d_errno A)) 4 (EVar v) :: k3 in
        match after_call cs1 ret (Some (ELit 0)) k4 with
        | Some cs' =>
            Some (set_slots cs' (slots_keep k (ELit 0) (d_errno A) (ELit 4)
                                  (slots_keep k (ELit 0) (d_prng A) (ELit 8)
                                    (slots_keep k qb qk (ELit FR) (c_slots cs)))))
        | None => None
        end
      else None
    | _, _, _, _ => None
    end
  | _, _, _ => None
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
Definition kread4eD (fs : fdig) (fk k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookupAF fs fk segs k b off 4 4%Z (off + 4)%Z false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.
Lemma kread4eD_eq : forall k b off, kread4eD (SFS (facts_of k)) (facts_of k) k b off = kread4e k b off.
Proof.
  intros. unfold kread4eD, kread4e, know_lookup. change 4%Z with (Z.of_nat 4) at 1. change (off + 4)%Z with (off + Z.of_nat 4)%Z.
  rewrite know_lookupAF_eq, know_lookupA_fk1. reflexivity.
Qed.
Definition cells_okD (fs : fdig) (fk k : list kentry) (cells : list (Z * nat * Z)) : bool :=
  forallb (fun c => match c with (a, n, v) =>
             match kreadZD fs fk k (ELit 0) a n with Some z => Z.eqb z v | None => false end end) cells.
Lemma cells_okD_eq : forall k cells, cells_okD (SFS (facts_of k)) (facts_of k) k cells = cells_ok k cells.
Proof.
  intros. unfold cells_okD, cells_ok. induction cells as [|[[a n] v] r IH]; [reflexivity|]. cbn [forallb].
  rewrite kreadZD_eq, IH. reflexivity.
Qed.
Lemma kread4eD_bucket : forall fs fk k b off, kread4eD fs fk (List.filter (lk_relevant b) k) b off = kread4eD fs fk k b off.
Proof. intros. unfold kread4eD. rewrite know_lookupAF_bucket. reflexivity. Qed.
Lemma cells_okD_bucket : forall fs fk k cells, cells_okD fs fk (List.filter (lk_relevant (ELit 0)) k) cells = cells_okD fs fk k cells.
Proof.
  intros. unfold cells_okD. induction cells as [|[[a n] v] r IH]; [reflexivity|]. cbn [forallb].
  rewrite kreadZD_bucket, IH. reflexivity.
Qed.
Hint Rewrite kread4eD_bucket cells_okD_bucket kread4eD_eq cells_okD_eq : nd.

(* [comment removed for export] *)
Definition node_exitcall_ref (cs : cstate) : option (list Z * Z) :=
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
                    && (d_stdout_buf A <=? wb) && (wb <? wp) && (wp <=? IMG_HI) && (wp - wb <=? 4096))%bool
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
Definition node_exitcall (cs : cstate) : option (list Z * Z) :=
  let fk := facts_of (kn cs) in let fs := SFS fk in let kz := List.filter (lk_relevant (ELit 0)) (kn cs) in
  let k := kn cs in let f := d_stdout A in let f2 := d_stderr A in
  match reg_lit cs 10, reg_lit cs 4 with
  | Some code, Some tp =>
    let sp := reg cs 2 in
    let spm := mkAlu ALU_ADD sp (ELit (-144)) in
    let '(qb, qk) := split_lit spm in
    match eloD fs sp, ehiD fs sp, kread4eD fs fk kz (ELit 0) (tp - 168),
          kreadZD fs fk kz (ELit 0) (f + 140) 4, kreadZD fs fk kz (ELit 0) (f + 40) 8, kreadZD fs fk kz (ELit 0) (f + 56) 8,
          kread8eD fs fk kz (ELit 0) (f + 8), kread8eD fs fk kz (ELit 0) (f + 16) with
    | Some splo, Some sphi, Some tide, Some lock, Some wp, Some wb, Some rp, Some re =>
      match kread8eD fs fk kz (ELit 0) (f2 + 40), kread8eD fs fk kz (ELit 0) (f2 + 56), kread8eD fs fk kz (ELit 0) (f2 + 8), kread8eD fs fk kz (ELit 0) (f2 + 16),
            eloD fs tide, ehiD fs tide with
      | Some w2, Some b2, Some r2, Some e2, Some tlo, Some thi =>
        if (cells_okD fs fk kz (e_cells A)
            && (lock =? 4294967295) && expr_eqb rp re && expr_eqb w2 b2 && expr_eqb r2 e2
            && rw_okbD fs fk qb qk 144 && (4294967296 + 144 <=? splo) && (sphi <=? 0x800000000000)
            && (168 <=? tp) && (tp <=? 4294967296)
            && (1 <=? tlo) && (thi <? 2147483648))%bool
        then
          if (wb =? wp) then Some ([], Z.land code 255)
          else
            match kreadZD fs fk kz (ELit 0) (f + 72) 8, kread8eD fs fk kz (ELit 0) (f + 88), kread8eD fs fk kz (ELit 0) (f + 96),
                  kreadZD fs fk kz (ELit 0) (f + 120) 4, kreadZD fs fk kz (ELit 0) (d_canary_got A) 8, kread8eD fs fk kz (ELit 0) (d_canary A),
                  kread_bytesD fs fk (Z.to_nat (wp - wb)) kz (ELit 0) wb with
            | Some wr, Some _, Some _, Some fd, Some cg, Some _, Some pend =>
                if ((wr =? t_stdio_write A) && (fd =? 1) && (cg =? d_canary A)
                    && (d_stdout_buf A <=? wb) && (wb <? wp) && (wp <=? IMG_HI) && (wp - wb <=? 4096))%bool
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
Lemma node_exitcall_eq : forall cs, node_exitcall cs = node_exitcall_ref cs.
Proof. intros. unfold node_exitcall, node_exitcall_ref. repeat nd_step. Qed.


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
Fixpoint expr_has_var (v : N) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => N.eqb n v
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_has_var v x || expr_has_var v y
  | EExt _ _ _ x => expr_has_var v x
  | EBlob _ _ _ _ => false
  end%bool.

Fixpoint expr_vars (e : expr) (acc : list N) : list N :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (N.eqb n) acc then acc else n :: acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars x (expr_vars y acc)
  | EExt _ _ _ x => expr_vars x acc
  | EBlob _ _ _ _ => acc
  end.

(* [comment removed for export] *)
Definition live_vars (cs : cstate) : list N :=
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

Definition all_live (live : list N) (e : expr) : bool :=
  forallb (fun v => existsb (N.eqb v) live) (expr_vars e []).

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list N) (K : kentry) : bool :=
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lvset : Type := ptree unit.
Definition lv_get (t : lvset) (n : N) : bool := match nm_get t n with Some _ => true | None => false end.
Definition lv_set (t : lvset) (n : N) : lvset := nm_set t n tt.
Lemma lv_get_nil : forall n, lv_get PTLeaf n = false.
Proof. intros. unfold lv_get. rewrite nm_get_leaf. reflexivity. Qed.
Lemma lv_get_set_same : forall l n, lv_get (lv_set l n) n = true.
Proof. intros. unfold lv_get, lv_set. rewrite nm_get_set_same. reflexivity. Qed.
Lemma lv_get_set_other : forall l n n', n <> n' -> lv_get (lv_set l n') n = lv_get l n.
Proof. intros. unfold lv_get, lv_set. rewrite nm_get_set_other by assumption. reflexivity. Qed.

Fixpoint expr_vars_t (e : expr) (acc : lvset) : lvset :=
  match e with
  | ELit _ => acc
  | EVar n => if lv_get acc n then acc else lv_set acc n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_t x (expr_vars_t y acc)
  | EExt _ _ _ x => expr_vars_t x acc
  | EBlob _ _ _ _ => acc
  end.

Definition live_vars_t (cs : cstate) : lvset :=
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

Definition in_live_t (t : lvset) (v : N) : bool := lv_get t v.

Fixpoint expr_all_live_t (t : lvset) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.

Definition kn_gc_entry_t (spb : expr) (spk : Z) (t : lvset) (K : kentry) : bool :=
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
Definition live_agree (acc : list N) (t : lvset) : Prop :=
  forall v, existsb (N.eqb v) acc = in_live_t t v.

Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (N.eqb n) acc then acc else n :: acc) (if lv_get t n then t else lv_set t n).
Proof.
  intros acc t n H v. pose proof (H n) as Hn. unfold in_live_t in *. rewrite <- Hn.
  destruct (existsb (N.eqb n) acc) eqn:E; [exact (H v)|].
  cbn [existsb]. destruct (N.eqb_spec v n) as [->|NE].
  - rewrite lv_get_set_same. reflexivity.
  - rewrite lv_get_set_other by exact NE. exact (H v).
Qed.

Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof.
  induction e; intros acc t H; cbn [expr_vars expr_vars_t]; try exact H; try (apply live_agree_var; exact H); auto.
Qed.

Lemma live_agree_fold : forall (X : Type) (f : X -> list N -> list N) (g : X -> lvset -> lvset) (l : list X) acc t,
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
  intros v. unfold in_live_t. rewrite lv_get_nil. reflexivity.
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

Definition run_block_gcM (fuel : nat) (stops : list Z) (cs : cstate) (m : smemo) : option cstate * smemo :=
  let '(r, m) := run_blockM fuel stops cs m in (match r with Some cs' => Some (cs_gc cs') | None => None end, m).
Lemma run_block_gcM_eq : forall fuel stops cs m, smemo_ok m ->
  fst (run_block_gcM fuel stops cs m) = run_block_gc fuel stops cs /\ smemo_ok (snd (run_block_gcM fuel stops cs m)).
Proof.
  intros fuel stops cs m Hm. unfold run_block_gcM, run_block_gc.
  pose proof (run_blockM_eq fuel stops cs m Hm) as [H1 H2]. destruct (run_blockM fuel stops cs m) as [r m1].
  cbn [fst snd] in H1, H2 |- *. subst r. split; [reflexivity | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : list Z :=
  [t_memcpy A; t_memset A; t_strnlen A; t_memchr A; t_F A; t_cas_or A; t_cas_and A; t_cas_lock A;
   t_calls A; t_main_ret A; t_enframe A; t_freepro A; t_stdio_write A; t_printf A; t_exitc A]%Z.

(* [comment removed for export] *)
Inductive cres : Type := COk (s : shape) | CErr (code : Z) (where_ : plan) (cs : cstate).

Section Check.
Variable bfuel : nat.   (* [comment removed for export] *)

Fixpoint check_ref (fuel : nat) (cs0 : cstate) (p : plan) {struct fuel} : cres :=
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
            match check_ref f (set_kn cs0 (KRange e lo mid :: kn cs0)) k1 with
            | COk s1 =>
                match check_ref f (set_kn cs0 (KRange e (mid + 1) hi :: kn cs0)) k2 with
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
        if is_ecall_at cs then
        match node_mmap cs with
        | Some (csf, css) =>
            match check_ref f csf kf with
            | COk sf => match check_ref f css ks with
                        | COk ss => COk (salt2 sf ss)
                        | err => err
                        end
            | err => err
            end
        | None => CErr 3 p cs
        end else CErr 2 p cs
    | PMunmap k =>
        if is_ecall_at cs then
        match node_munmap cs with Some cs' => check_ref f cs' k | None => CErr 3 p cs end else CErr 2 p cs
    | PIoctl k =>
        if is_ecall_at cs then
        match node_ioctl cs with Some cs' => check_ref f cs' k | None => CErr 3 p cs end else CErr 2 p cs
    | PStdioWrite k =>
        if Z.eqb (pc cs) (t_stdio_write A) then
        match node_stdio_write cs with
        | Some (fd, bs, cs') => match check_ref f cs' k with COk s => COk (SEmit fd bs s) | err => err end
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
        if (negb (is_ecall_at cs) && existsb (Z.eqb (pc cs)) STOPS)%bool then check_ref f cs k else CErr 2 p cs
    | PCall sm args k =>
        let r := match sm with
                 | SumMemcpy => if Z.eqb (pc cs) (t_memcpy A) then call_memcpy cs else None
                 | SumF => if Z.eqb (pc cs) (t_F A) then call_F cs else None
                 | SumEnframe => if Z.eqb (pc cs) (t_enframe A) then call_enframe2 cs else None
                 | SumFreePro => if Z.eqb (pc cs) (t_freepro A) then call_freepro cs else None
                 | SumMainRet => if Z.eqb (pc cs) (t_main_ret A) then call_mainret cs else None
                 | SumPrintf => if Z.eqb (pc cs) (t_printf A) then call_printf cs else None
                 end in
        match r with Some cs' => check_ref f cs' k | None => CErr 3 p cs end
    | PCas c k =>
        match node_cas c cs with Some cs' => check_ref f cs' k | None => CErr 3 p cs end
    end
  end
  end
  end.

Fixpoint checkM (fuel : nat) (cs0 : cstate) (p : plan) (m : smemo) {struct fuel} : cres * smemo :=
  match fuel with
  | O => (CErr 0 p cs0, m)
  | S f =>
  (* [comment removed for export] *)
  match p with
  | PContra => (if kn_contra (kn cs0) then COk SNil else CErr 3 p cs0, m)
  | PSplit e mid k1 k2 =>
      if expr_vars_lt nx0 e then
      match erange (kn cs0) e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool then
            let '(r1, m) := checkM f (set_kn cs0 (KRange e lo mid :: kn cs0)) k1 m in
            match r1 with
            | COk s1 =>
                let '(r2, m) := checkM f (set_kn cs0 (KRange e (mid + 1) hi :: kn cs0)) k2 m in
                (match r2 with
                 | COk s2 => COk (SCase e mid s1 s2)
                 | err => err
                 end, m)
            | err => (err, m)
            end
          else (CErr 3 p cs0, m)
      | None => (CErr 3 p cs0, m)
      end
      else (CErr 3 p cs0, m)
  | _ =>
  let '(rb, m) := run_block_gcM bfuel STOPS cs0 m in
  match rb with
  | None => (CErr 1 p cs0, m)
  | Some cs =>
    match p with
    | PSplit _ _ _ _ => (CErr 2 p cs, m)
    | PContra => (CErr 2 p cs, m)
    | PMmap kf ks =>
        if is_ecall_at cs then
        match node_mmap cs with
        | Some (csf, css) =>
            let '(r1, m) := checkM f csf kf m in
            match r1 with
            | COk sf => let '(r2, m) := checkM f css ks m in
                        (match r2 with
                         | COk ss => COk (salt2 sf ss)
                         | err => err
                         end, m)
            | err => (err, m)
            end
        | None => (CErr 3 p cs, m)
        end else (CErr 2 p cs, m)
    | PMunmap k =>
        if is_ecall_at cs then
        match node_munmap cs with Some cs' => checkM f cs' k m | None => (CErr 3 p cs, m) end else (CErr 2 p cs, m)
    | PIoctl k =>
        if is_ecall_at cs then
        match node_ioctl cs with Some cs' => checkM f cs' k m | None => (CErr 3 p cs, m) end else (CErr 2 p cs, m)
    | PStdioWrite k =>
        if Z.eqb (pc cs) (t_stdio_write A) then
        match node_stdio_write cs with
        | Some (fd, bs, cs') => let '(r1, m) := checkM f cs' k m in (match r1 with COk s => COk (SEmit fd bs s) | err => err end, m)
        | None => (CErr 3 p cs, m)
        end else (CErr 2 p cs, m)
    | PExit =>
        (if is_ecall_at cs then
         match node_exit cs with Some code => COk (SExit code) | None => CErr 3 p cs end else CErr 2 p cs, m)
    | PExitCall =>
        (if Z.eqb (pc cs) (t_exitc A) then
         match node_exitcall cs with
         | Some ([], code) => COk (SExit code)
         | Some (bs, code) => COk (SEmit 1 bs (SExit code))
         | None => CErr 3 p cs
         end
         else CErr 2 p cs, m)
    | PResume k =>
        if (negb (is_ecall_at cs) && existsb (Z.eqb (pc cs)) STOPS)%bool then checkM f cs k m else (CErr 2 p cs, m)
    | PCall sm args k =>
        let r := match sm with
                 | SumMemcpy => if Z.eqb (pc cs) (t_memcpy A) then call_memcpy cs else None
                 | SumF => if Z.eqb (pc cs) (t_F A) then call_F cs else None
                 | SumEnframe => if Z.eqb (pc cs) (t_enframe A) then call_enframe2 cs else None
                 | SumFreePro => if Z.eqb (pc cs) (t_freepro A) then call_freepro cs else None
                 | SumMainRet => if Z.eqb (pc cs) (t_main_ret A) then call_mainret cs else None
                 | SumPrintf => if Z.eqb (pc cs) (t_printf A) then call_printf cs else None
                 end in
        match r with Some cs' => checkM f cs' k m | None => (CErr 3 p cs, m) end
    | PCas c k =>
        match node_cas c cs with Some cs' => checkM f cs' k m | None => (CErr 3 p cs, m) end
    end
  end
  end
  end.

(* [comment removed for export] *)
Definition check (fuel : nat) (cs0 : cstate) (p : plan) : cres := fst (checkM fuel cs0 p []).

Ltac chM L :=
  let H1 := fresh "HM" in let H2 := fresh "HM" in
  lazymatch goal with
  | Hm : smemo_ok ?m |- context [?t] =>
      lazymatch t with
      | checkM ?f ?c ?p m => pose proof (L f c p m Hm) as [H1 H2]; destruct (checkM f c p m) as [? ?]; cbn [fst snd] in H1, H2 |- *; subst; clear Hm
      end
  end.
Lemma checkM_eq : forall fuel cs0 p m, smemo_ok m ->
  fst (checkM fuel cs0 p m) = check_ref fuel cs0 p /\ smemo_ok (snd (checkM fuel cs0 p m)).
Proof.
  induction fuel as [|f IH]; intros cs0 p m Hm; [split; [reflexivity|exact Hm]|].
  cbn [checkM check_ref].
  destruct p;
  try (pose proof (run_block_gcM_eq bfuel STOPS cs0 m Hm) as [R1 R2];
       destruct (run_block_gcM bfuel STOPS cs0 m) as [rb m0]; cbn [fst snd] in R1, R2 |- *; subst rb;
       destruct (run_block_gc bfuel STOPS cs0) as [cs|]; [|split; [reflexivity|exact R2]]);
  repeat first
    [ progress (cbn [fst snd])
    | split; [reflexivity | assumption]
    | match goal with
      | H : smemo_ok ?m1 |- context [checkM f ?c ?q ?m1] =>
          let H1 := fresh "HM" in let H2 := fresh "HM" in
          pose proof (IH c q m1 H) as [H1 H2]; destruct (checkM f c q m1) as [? ?]; cbn [fst snd] in H1, H2 |- *; subst
      | |- fst (match ?x with _ => _ end) = _ /\ _ => destruct x
      | |- fst (if ?x then _ else _) = _ /\ _ => destruct x
      | |- (match ?x with _ => _ end) = _ /\ _ => destruct x
      | |- (if ?x then _ else _) = _ /\ _ => destruct x
      end ].
Qed.
Lemma check_eq : forall fuel cs0 p, check fuel cs0 p = check_ref fuel cs0 p.
Proof. intros. unfold check. apply checkM_eq. apply smemo_ok_nil. Qed.
End Check.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End SP.
