(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocRep MallocKit_AB MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_A3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc.
From Stdlib Require Lia. 
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls F_malloc_free F_malloc_fast MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module ASlot_W3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma meta_word_upd_af mr a f' : meta_word (m_set_avail a (m_set_freed f' mr)) = meta_word mr.
Proof. reflexivity. Qed.

Lemma decay_bounces_eq sc st :
  decay_bounces sc st =
  if ((7 <=? sc) && (sc <? 39)) && negb (bounces st (sc - 7) =? 0) then set_bounce (sc - 7) (bounces st (sc - 7) - 1) st else st.
Proof. reflexivity. Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.

(* [comment removed for export] *)
End AVZ.

End ACeilS1.
End ASlot_W3.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module ASlot_W5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma dequeue_self_eq sc g st :
  m_next (get_meta_rec st g) = Some g ->
  dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
  intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
  rewrite upd_meta_put. reflexivity.
Qed.

Lemma dequeue_other_eq sc g nx pv st :
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
  active st sc = Some g ->
  dequeue (LActive sc) g st =
    let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
    let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
    let st3 := set_active sc (Some nx) st2 in
    put_meta g (clr (get_meta_rec st g)) st3.
Proof.
  intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
  rewrite !upd_meta_put.
  match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
  rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
  f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
  rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End DEQ.

End ACeilS1.
End ASlot_W5.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
Module ASlot_W6.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition full_skip : bool := (f =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End M.

End ACeilS1.
End ASlot_W6.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition ctx_ta_same (c c1 : mctx) : Prop :=
  c_secret c1 = c_secret c /\ c_init_done c1 = c_init_done c /\ c_mmap_counter c1 = c_mmap_counter c
  /\ c_free_meta_head c1 = c_free_meta_head c /\ c_avail_meta c1 = c_avail_meta c /\ c_avail_meta_count c1 = c_avail_meta_count c
  /\ c_avail_meta_area_count c1 = c_avail_meta_area_count c /\ c_meta_alloc_shift c1 = c_meta_alloc_shift c
  /\ c_meta_area_head c1 = c_meta_area_head c /\ c_meta_area_tail c1 = c_meta_area_tail c /\ c_avail_meta_areas c1 = c_avail_meta_areas c
  /\ c_usage c1 = c_usage c /\ c_unmap_seq c1 = c_unmap_seq c /\ c_seq c1 = c_seq c /\ c_brk c1 = c_brk c.

(* [comment removed for export] *)
Definition geom_same (r r1 : meta) : Prop :=
  m_mem r1 = m_mem r /\ m_last_idx r1 = m_last_idx r /\ m_freeable r1 = m_freeable r /\ m_sizeclass r1 = m_sizeclass r /\ m_maplen r1 = m_maplen r.

Record ta_rel (sc : Z) (st st1 : mstate) : Prop := mkTR {
  tr_regions : s_regions st1 = s_regions st;
  tr_shadow : s_shadow st1 = s_shadow st;
  tr_next : s_next_rid st1 = s_next_rid st;
  tr_areas : s_areas st1 = s_areas st;
  tr_slots : s_slots st1 = s_slots st;
  tr_tick : s_tick st1 = s_tick st;
  tr_secret : s_secret st1 = s_secret st;
  tr_reserved : s_reserved st1 = s_reserved st;
  tr_ctx : ctx_ta_same (ctx st) (ctx st1);
  tr_active : forall c, c <> sc -> active st1 c = active st c;
  tr_bounces : forall i, 0 <= bounces st i -> 0 <= bounces st1 i <= bounces st i;
  tr_geom : forall q, geom_same (get_meta_rec st q) (get_meta_rec st1 q);
  (* [comment removed for export] *)
  tr_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st1 q)) i || Z.testbit (m_freed (get_meta_rec st1 q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true;
  tr_mrange : forall q, 0 <= m_avail (get_meta_rec st q) < 2^32 -> 0 <= m_freed (get_meta_rec st q) < 2^32 ->
      0 <= m_avail (get_meta_rec st1 q) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 q) < 2^32;
  (* [comment removed for export] *)
  tr_groups : forall b, (exists gh1, (s_groups st1) !! b = Some gh1) <-> (exists gh, (s_groups st) !! b = Some gh);
  tr_gmeta : forall b gh1, (s_groups st1) !! b = Some gh1 ->
      exists gh, (s_groups st) !! b = Some gh /\ g_meta gh1 = g_meta gh
                 /\ (g_active_idx gh1 = g_active_idx gh
                     \/ (0 <= g_active_idx gh1 <= 31 /\ forall g, g_meta gh = Some g -> m_sizeclass (get_meta_rec st g) <> 0))
}.

Lemma ctx_ta_same_refl c : ctx_ta_same c c.
Proof. repeat split; reflexivity. Qed.
Lemma geom_same_refl r : geom_same r r.
Proof. repeat split; reflexivity. Qed.
End ACeilS1.


Ltac ta_auto :=
  first [ reflexivity
        | apply ctx_ta_same_refl
        | (cbn; repeat split; reflexivity)
        | (intros; apply geom_same_refl)
        | (intros ? ? ? Hb__; exact Hb__)
        | (intros ? Ha__ Hf__; split; [exact Ha__| exact Hf__])
        | (intros ? ? Hq__; eexists; split; [exact Hq__|]; split; [reflexivity| left; reflexivity])
        | (intros; unfold bounces, ctx in *; cbn in *; lia)
        | idtac ].
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma ta_rel_refl sc st : ta_rel sc st st.
Proof. constructor; ta_auto. Qed.

Lemma ta_rel_trans sc st st1 st2 : ta_rel sc st st1 -> ta_rel sc st1 st2 -> ta_rel sc st st2.
Proof.
  intros A B. destruct A as [R1 S1 N1 A1 L1 T1 E1 V1 C1 AC1 B1 G1 BI1 MR1 GR1 GM1].
  destruct B as [R2 S2 N2 A2 L2 T2 E2 V2 C2 AC2 B2 G2 BI2 MR2 GR2 GM2].
  constructor; try congruence.
  - unfold ctx_ta_same in *. cps_destruct C1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). cps_destruct C2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
    repeat split; congruence.
  - intros c Hc. rewrite AC2 by exact Hc. apply AC1. exact Hc.
  - intros i Hi. pose proof (B1 i Hi). pose proof (B2 i ltac:(lia)). lia.
  - intros q. cps_destruct (G1 q) as (?&?&?&?&?). cps_destruct (G2 q) as (?&?&?&?&?). repeat split; congruence.
  - intros q i Hi Hb. apply (BI1 q i Hi). apply (BI2 q i Hi). exact Hb.
  - intros q Ha Hf. destruct (MR1 q Ha Hf) as [Ha1 Hf1]. exact (MR2 q Ha1 Hf1).
  - intros b. rewrite GR2. apply GR1.
  - intros b gh2 H2. cps_destruct (GM2 b gh2 H2) as (gh1 & H1 & M1 & AI1). cps_destruct (GM1 b gh1 H1) as (gh & H & M & AI).
    exists gh. split; [exact H|]. split; [congruence|].
    destruct AI1 as [Q1|[RR1 P1]]; destruct AI as [Q0|[R0 P0]]; [left; congruence| right; split; [lia| exact P0] | right | right; split; [lia| exact P0]].
    split; [lia|]. intros g Hg E0. apply (P1 g); [congruence|]. cps_destruct (G1 g) as (_ & _ & _ & SC1 & _). rewrite SC1. exact E0.
Qed.

(* [comment removed for export] *)
Lemma ta_rel_set_active sc st v : ta_rel sc st (set_active sc v st).
Proof.
  constructor; ta_auto.
  intros c Hc. rewrite active_set_active. destruct (Z.eqb_spec c sc); [lia| reflexivity].
Qed.

Lemma ta_rel_put_meta sc st g r :
  geom_same (get_meta_rec st g) r ->
  (forall i, 0 <= i -> Z.testbit (m_avail r) i || Z.testbit (m_freed r) i = true ->
             Z.testbit (m_avail (get_meta_rec st g)) i || Z.testbit (m_freed (get_meta_rec st g)) i = true) ->
  (0 <= m_avail (get_meta_rec st g) < 2^32 -> 0 <= m_freed (get_meta_rec st g) < 2^32 -> 0 <= m_avail r < 2^32 /\ 0 <= m_freed r < 2^32) ->
  ta_rel sc st (put_meta g r st).
Proof.
  intros GS BS RS. constructor; ta_auto.
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact GS| apply geom_same_refl].
  - intros q i Hi. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; apply BS; exact Hi| auto].
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact RS| auto].
Qed.

(* [comment removed for export] *)
Lemma ta_rel_put_links sc st g p n :
  ta_rel sc st (put_meta g (m_set_prev p (m_set_next n (get_meta_rec st g))) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_next sc st g n :
  ta_rel sc st (put_meta g (m_set_next n (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
Lemma ta_rel_put_prev sc st g p :
  ta_rel sc st (put_meta g (m_set_prev p (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.

Lemma ta_rel_set_bounce sc st i v : 0 <= v <= bounces st i -> ta_rel sc st (set_bounce i v st).
Proof.
  intros Hv. constructor; ta_auto.
  intros j Hj. rewrite bounces_set. destruct (Z.eqb_spec j i); [subst; lia| lia].
Qed.

Lemma ta_rel_decay sc st c : 0 <= bounces st (c - 7) -> ta_rel sc st (decay_bounces c st).
Proof.
  intros Hb. unfold decay_bounces. destruct (_ && _) eqn:E; [|apply ta_rel_refl].
  apply andb_prop in E. destruct E as [_ E]. apply negb_true_iff in E. apply Z.eqb_neq in E.
  apply ta_rel_set_bounce. lia.
Qed.

Lemma ta_rel_set_gai sc st b ai : 0 <= Z.land ai 31 <= 31 ->
  (forall h g, (s_groups st) !! b = Some h -> g_meta h = Some g -> m_sizeclass (get_meta_rec st g) <> 0) ->
  ta_rel sc st (set_group_active_idx b ai st).
Proof.
  intros Hai HSC. unfold set_group_active_idx. destruct (get_group st b) as [h|] eqn:Hb; [|apply ta_rel_refl].
  unfold get_group in Hb.
  constructor; ta_auto.
  - intros b'. cbn [s_groups set_groups]. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq. split; intros _; eauto.
    + rewrite lookup_insert_ne by congruence. split; intros X; exact X.
  - intros b' gh1 H. cbn [s_groups set_groups] in H. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in H. inversion H; subst. exists h. split; [exact Hb|]. cbn. split; [reflexivity| right; split; [exact Hai| intros g Hg; exact (HSC h g Hb Hg)]].
    + rewrite lookup_insert_ne in H by congruence. exists gh1. auto.
Qed.

Lemma tr_get_shadow sc st st1 rid : ta_rel sc st st1 -> get_shadow st1 rid = get_shadow st rid.
Proof. intros TR. unfold get_shadow. rewrite (tr_shadow _ _ _ TR). reflexivity. Qed.
Lemma tr_conc sc st st1 q : ta_rel sc st st1 -> conc st1 q = conc st q.
Proof. intros TR. unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity. Qed.
Lemma rec_set_gai b ai st q : get_meta_rec (set_group_active_idx b ai st) q = get_meta_rec st q.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
Lemma active_set_gai b ai st i : active (set_group_active_idx b ai st) i = active st i.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.

End ACeilS2.
