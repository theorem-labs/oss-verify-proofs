(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_W13 ASlot_W14 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P ASlot_M4 ASlot_M5P.
Import ListNotations.
Open Scope Z_scope.

Lemma slot_ok_N st g b r idx n N :
  slot_ok st g b r idx n -> get_stride (get_meta_rec st g) = N + 4 -> 0 <= N -> slot_ok st g b r idx N.
Proof.
  intros SO STR N0. destruct SO. constructor; try assumption; try lia.
  intros off O0 OF. apply so_q16; lia.
Qed.

Lemma outside_app' W1 W2 a : outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; [LiaTuning.ctauto|]. rewrite IH. LiaTuning.ctauto. Qed.

Lemma arith_prog_dec a c s n : 0 < s ->
  (exists j, 0 <= j <= n /\ a = c + s * j) \/ (forall j, 0 <= j <= n -> a <> c + s * j).
Proof.
  intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
  - pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
    destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
    + left. exists ((a - c) / s). split; [lia|]. lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
  - right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.

Lemma errno_lit5 (tp : word) : tp = Z_to_bv 64 0x1b708 -> errno_addr tp = 112228.
Proof. intros ->. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma meta_slot_mono stA stB g :
  (forall a, is_Some ((s_areas stA) !! a) -> is_Some ((s_areas stB) !! a)) -> meta_slot stA g -> meta_slot stB g.
Proof.
  intros HA (ar & arr & kk & Ha & Hk & E). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
  exists ar, arr', kk. auto.
Qed.

Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).

Lemma nest_class sc (SC : 0 <= sc < 48) cnt1 : 1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  nreq sc cnt1 = size_class sc * 16 * cnt1 + 12 /\ 0 <= ncls sc cnt1 <= 26 /\ 16 * size_class sc * cnt1 + 16 <= UNIT * size_class (ncls sc cnt1)
  /\ sc < ncls sc cnt1 /\ 0 <= nreq sc cnt1 < 2^32 /\ nreq sc cnt1 + 4 <= 16 * size_class (ncls sc cnt1).
Proof.
  intros C1 SM. pose proof (size_class_range sc SC) as SZR.
  assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
  assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
  pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
  assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
  destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
  split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
  split.
  { destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
    destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
    pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
  split; [lia|]. nia.
Qed.

Section LEVEL.
Context {HCEIL : HasCeiling}.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 0x1b708.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.

End LEVEL.