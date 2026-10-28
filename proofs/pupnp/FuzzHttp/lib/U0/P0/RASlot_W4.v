(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 F_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RASlot_W2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section ENTRY.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

#[using="MR SC CLO AMS"] Lemma ras_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  a0 = Z_to_bv 64 sc ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' : word) m' junk,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 guard_word a1' (pw st (active st sc)) a3 a4 a5 a6 a7
                   a1 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (match active st sc with None => 0x18fd0 | Some _ => 0x18e54 end)) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ stk rsegs m' lo (bv_unsigned sp + -144)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep st m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros HA ST LO MI. subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & _) & _). unfold wz in G4.
  ceil_facts; unfold ralloc_slot_entry, RCTX, RMLOCK, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.

  step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.

  step. step. step. step. step. step. step. step. step. step.
  rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; ceil_facts; lia]) end.
  pose proof (rmrep_active_read st _ sc (wa (375584 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
  step. clear RDA.

  step.
  replace (375576 + sc * 8 + 88) with (375584 + 80 + 8 * sc) by lia.
  replace (375576 + sc * 8) with (375576 + 8 * sc) by lia.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.

  step. if_cases K; zify_cond K.
  - destruct (active st sc) as [g|] eqn:HA.
    { exfalso. pose proof (rmeta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _). ceil_facts.
      unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
  - destruct (active st sc) as [g|] eqn:HA.
    2:{ exfalso. apply K. reflexivity. }
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
    repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End ENTRY.

Section T1.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
      (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.

#[using="HGW HCEIL MR MSL AVR"] Lemma rt1_fin_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr <> 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) (wz (sxv (m_avail mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18f90) fc None m (seg_rom rsegs))
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18e54) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros AVNZ MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). ceil_facts. fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
  pose proof (sxv_range (m_avail mr)) as RA.

  step. rewrite sx32_wz_sxv by lia.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
  { exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
  step. step.
  apply evt_done. reflexivity.
Qed.

#[using="HGW HCEIL MR MSL"] Lemma rt1_deq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr = 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz 0) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18e78) fc None m (seg_rom rsegs))
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18e54) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). ceil_facts. fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.

  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. unfold pw, wz. reflexivity.
Qed.

#[using="MR MSL SC FRR"] Lemma rt1_next_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_avail mr = 0 -> m_freed mr <> 0 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz (sxv (m_freed mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18eb8) fc None m' (seg_rom rsegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep (set_active sc (m_next mr) st) m')
    (MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18e54) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). ceil_facts. fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
  pose proof (sxv_range (m_freed mr)) as RF.

  step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. rewrite sx32_wz_sxv by lia. step.
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
  { exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.

  clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (375584 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (375584 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.

  step.
  apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End T1.

Section DEQ.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

#[using="MR MSL SC"] Lemma rdeq_self_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  m_next mr = Some g -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (wz 0) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18fd0) fc None m' (seg_rom rsegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep (put_meta g (clr mr) (set_active sc None st)) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18e78) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). ceil_facts. fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.

  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step.

  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (375584 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR1; unfold RCTX in MR1 end.
  rraw_store_finish0 (375584 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
  set (st1 := set_active sc None st) in MR1.
  assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).

  rmeta_open G MUg WMg.
  rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
  st1. st1.
  rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.

  pose proof (rmrep_active_read _ _ sc (wa (375584 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. unfold wz.

  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

#[using="MR MSL SC HA"] Lemma rdeq_other_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nx pv : aptr),
  m_next mr = Some nx -> m_prev mr = Some pv -> nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  mem_inv rsegs m ->
  let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
  let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
  let st3 := set_active sc (Some nx) st2 in
  let st4 := put_meta g (clr mr) st3 in
  evt rsegs (fun ms' => exists (a1' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st nx)) a1' (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18eb8) fc None m' (seg_rom rsegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep st4 m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18e78) fc None m (seg_rom rsegs)).
Proof.
  intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). ceil_facts. fold G in Gpos, GC, GI.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _). ceil_facts.
  pose proof (rmeta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _). ceil_facts.
  assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  unfold RCTX, RMLOCK, RSSP_GUARD in *.

  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.

  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  step. clear CH.

  rmeta_open (conc st pv) MUp WMp.
  rmchunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

  rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. step. clear CH.

  rmeta_open (conc st nx) MUn WMn.
  rmchunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

  pose proof (rmrep_active_read st2 _ sc (wa (375584 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
  change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.

  step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

  rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
  unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
  step. clear CH. step.

  pose proof MR2 as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (wa (375584 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
  rraw_store_finish0 (375584 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
  fold st3 in MR3.
  assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).

  rmeta_open G MUg WMg.
  rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
  replace (get_meta_rec st3 g) with mr in CH.
  2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1.
  rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.

  pose proof (rmrep_active_read _ _ sc (wa (375584 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
  change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
  step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.

  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
End DEQ.

Section M.
Context {HGW : HasGuard}.
Context {HCEIL : HasCeiling}.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

#[using="HGW HCEIL MR MSL FRR MW"] Lemma rm_act_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  full_skip st g = false -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' (wz (sxv f)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18ee4) fc None m (seg_rom rsegs))
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18eb8) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros NSK MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). ceil_facts. fold G in Gpos, GC, GI.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  {   apply evt_done. do 2 eexists. reflexivity. }

  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  { apply evt_done. do 2 eexists. reflexivity. }
  exfalso. unfold full_skip in NSK. fold mr f in NSK.
  assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
  rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.

#[using="f MR MSL SC FRR MW"] Lemma rm_skip_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mn : aptr),
  full_skip st g = true -> m_next mr = Some mn -> meta_slot st mn ->
  0 <= m_freed (get_meta_rec st mn) < 2^32 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' (wz (sxv (m_freed (get_meta_rec st mn)))) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x18ee4) fc None m' (seg_rom rsegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rmrep (set_active sc (Some mn) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x18eb8) fc None m (seg_rom rsegs)).
Proof.
  intros until mn. intros FSK GN MSn FNR MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). ceil_facts. fold G in Gpos, GC, GI.
  pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _). ceil_facts.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  pose proof (MallocKit_A3.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
  unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
  apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
  pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

  step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
  step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.

  step. clear CH.

  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (375584 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (375584 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.

  assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
  rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
  step. rewrite sx32_wz_sxv by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End M.
