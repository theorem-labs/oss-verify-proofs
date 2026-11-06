(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_F_malloc_enframe A_MallocTree A_MallocFacts_A A_MallocHINV A_MallocKit_A A_MallocKit_AB A_MallocKit_A2 A_MallocKit_A3 A_MallocKit_B A_MallocKit_B3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_Malloc_fp A_MallocNat A_MallocFacts_AS A_ASlot_W0 A_ASlot_W1 A_ASlot_W9 A_ASlot_W18 A_ASlot_I A_ASlot_M0.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma rgmf_of_facts st LB sc g :
  RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
  intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
  pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
  pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  constructor.
  - exact MSL.
  - exact AVr.
  - exact FRr.
  - exact MW.
  - exact SC48.
  - exact GSC.
  - exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
    + intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
      change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
      exact (X Hmem Hgh S0).
    + intros o Ho. exact (GU b _ o Hgh Ho).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
  - destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
    exists n, p. split; reflexivity.
Qed.

Lemma rtaf_of_facts st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
  intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
  pose proof (lf_lists _ LF) as (L1 & L2 & L3).
  change (fact_active (strip st)) with (fact_active st).
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  pose proof (lf_links _ LF) as LK.
  constructor.
  - intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
    change (lmem (strip st) g) with (lmem st g) in LM.
    split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
  - intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
    change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
    split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
    split; [exact SCn|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
    exact (LKn n Hn).
  - intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
    change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
    split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
    exact (LKp p Hp).
  - pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
  0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x1e000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x1e000 \/ 0x52000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x52000 \/ 0x56000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x56000 \/ 0x88000 <= r_base r).
Proof.
  intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. pose_ceil. lia.
Qed.

Lemma rmalloc_fp_cases_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
  intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
  pose_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). pose_ceil. lia.
  - right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). pose_ceil. lia.
  - right. pose_ceil. lia.
Qed.

Lemma rmalloc_fp_image_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
  0x10000 <= a < 0x88000 -> RCTX <= a < RCTX + 928 \/ 0x673ec <= a < 0x673f0.
Proof.
  intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
  pose_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
  rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
  alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
  intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
    destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). pose_ceil. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL in Ha.
    destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
  rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells rsegs m1 A cs ->
  sp <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
  intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_enframe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocTree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A3 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_B3.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_fp OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocNat OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_AS OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W0 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W1 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W9 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W18 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_I OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_M0.
Import RMallocRep.TwinB RMallocTree.TwinB RF_get_meta.TwinB RMallocKit_B.TwinB RMallocKit_B2.TwinB RMallocKit_B3.TwinB RMallocKit_A.TwinB RMallocKit_A2.TwinB RMalloc_fp.TwinB RAllocSlot_iface.TwinB RASlot_I.TwinB.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma rgmf_of_facts st LB sc g :
  RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
  intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
  pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
  pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  constructor.
  - exact MSL.
  - exact AVr.
  - exact FRr.
  - exact MW.
  - exact SC48.
  - exact GSC.
  - exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
    + intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
      change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
      exact (X Hmem Hgh S0).
    + intros o Ho. exact (GU b _ o Hgh Ho).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
  - intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
  - destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
    exists n, p. split; reflexivity.
Qed.

Lemma rtaf_of_facts st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
  intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
  pose proof (lf_lists _ LF) as (L1 & L2 & L3).
  change (fact_active (strip st)) with (fact_active st).
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  pose proof (lf_links _ LF) as LK.
  constructor.
  - intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
    change (lmem (strip st) g) with (lmem st g) in LM.
    split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
  - intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
    change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
    split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
    split; [exact SCn|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
    exact (LKn n Hn).
  - intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
    destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
    change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
    split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
    destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
    exact (LKp p Hp).
  - pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
  0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x1f000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x1f000 \/ 0x53000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x53000 \/ 0x57000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x57000 \/ 0x8a000 <= r_base r).
Proof.
  intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
  pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
  destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. pose_ceil. lia.
Qed.

Lemma rmalloc_fp_cases_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
  intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
  pose_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). pose_ceil. lia.
  - right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). pose_ceil. lia.
  - right. pose_ceil. lia.
Qed.

Lemma rmalloc_fp_image_ER stE mE lo sp a :
  rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
  0x10000 <= a < 0x8a000 -> RCTX <= a < RCTX + 928 \/ 0x68bec <= a < 0x68bf0.
Proof.
  intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
  pose_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
  - exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
  - exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
  rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
  alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
  intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
    destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). pose_ceil. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL in Ha.
    destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.

Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
  rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells rsegs m1 A cs ->
  sp <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
  intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

End CEIL.
End TwinB.
