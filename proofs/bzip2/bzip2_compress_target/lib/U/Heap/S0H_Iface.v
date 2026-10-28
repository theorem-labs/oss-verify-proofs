(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec CatSim ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc EvtBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad MSafe Prog KInv KStep KStepC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_free MallocHINV MallocFacts_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocRep MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_free F_free_spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RF_ntf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RF_free_spec.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocBlocks OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface. (* [comment removed for export] *)      
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_Bpres OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_ntf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free.F_free_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free_spec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_free.RF_free_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_free.


 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma rauxv_ok_pres_B : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof.
  (intros C m m' B; cps_intros (av & x3 & x4 & x5 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H); intros HP HB HC).
  exists av, x3, x4, x5, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply auxv_keys_map; [|exact A1]. intros A w HA HB' Hb. pose proof (length_le8 w) as LL.
    eapply rpres_except_bytes_at; [exact HP| exact Hb|]. intros a Ha. apply HB. rewrite LL in Ha. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 278844 <= a < 278848) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 278844 <= a < 278848.

(* [comment removed for export] *)
Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof.
  intros Ha. pose proof MR as (WF & _). cps_pose WF as (Hres & WR & DJ & WA & WG). bz_ceil.
  intros [FP|[DR|ER]].
  - pose proof (rfree_fp_lt st m lo sp a MR ltac:(bz_ceil; lia) LS FP). lia.
  - cps_destruct DR as (rid & r & Hr & _ & _ & Hin). cps_destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). bz_ceil. lia.
  - lia.
Qed.

Lemma rfp_not_img a : 0x32000 <= a < 0x66000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (278844 <= a < 278848) -> ~ FPT a.
Proof.
  intros Ha N1 N2. pose proof MR as (WF & _). cps_pose WF as (Hres & WR & DJ & WA & WG). bz_ceil.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + cps_destruct X as (rid & r & Hr & _ & Hin). cps_destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + cps_destruct X as (b & gh & Hb & Hin). cps_destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      cps_destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + cps_destruct X as (rid & r & v & Hr & _ & Hin & _). cps_destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - cps_destruct DR as (rid & r & Hr & _ & _ & Hin). cps_destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - exact (N2 ER).
Qed.

Lemma rfp_not_image a : 0x32000 <= a < 0x66000 -> ~ ralloc_static a -> ~ FPT a.
Proof.
  intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
  intros Hb' Hab. pose proof MR as (WF & _). cps_pose WF as (Hres & WR & DJ & WA & WG). bz_ceil.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  cps_destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). cps_pose (rreserved_disjoint _ _ RGF) as (?&?&?&?). bz_ceil.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + cps_destruct X as (rid & r & Hr & NK & Hin).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + cps_destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * cps_destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + cps_destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - cps_destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed.

Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof.
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof.
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rfree_spec_proof : rfree_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  cps_destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
  (* [comment removed for export] *)
  eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - exact HOK.
  - apply rimplT_reach.
    apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    cps_destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
    unfold rfree_post. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
    split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
             intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [reflexivity|]. split; [reflexivity|].
    exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
    split; [reflexivity|]. split; [exact MR'|]. split.
    + (* [comment removed for export] *) unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + cps_destruct LEAF as (ans & o' & FO).
      eapply (MallocFacts_inv.areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
      cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
      cbn [fst]. rewrite <- FB. cps_destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.

End ACeilS1.
End RF_free_spec.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_ifaceP OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Iface.RF_free_spec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import TreeBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require TightBridge.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Notation rsegs := s0segs (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition TrueG : PState -> Model -> Prop := fun _ _ => True.
(* [comment removed for export] *)

Definition S0_inv (s : PState) (LB : list ablock) (m : word -> option byte) (MD : Model) : Prop :=
  RHEAP s LB m /\ OWNX (map blk_id LB) TrueG s MD.

(* [comment removed for export] *)
Definition S0_sys_ok (s : PState) (LB : list ablock) (n : Z) (MD : Model) : Prop :=
  forall tr s' MD', ~ tpath nstep (raw_malloc n s) MD tr (Ok (None, s')) MD'.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma perm_remove_id : forall (p : bid) (LB : list ablock) A n,
  List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
  Permutation (map blk_id LB) (p :: map blk_id (lb_remove p LB)).
Proof.
  intros p LB A n ND Hin. induction LB as [|b LB IH]; [destruct Hin|].
  cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
  destruct Hin as [->|Hin].
  - rewrite (lb_remove_head p A n LB Hni). cbn [map]. apply Permutation_refl.
  - unfold lb_remove. cbn [List.filter map].
    destruct (bid_eqb_spec (blk_id b) p) as [E|NE].
    + exfalso. apply Hni. rewrite E. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hin].
    + cbn [negb map]. eapply Permutation_trans; [apply perm_skip; apply IH; assumption|]. apply perm_swap.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_cj : forall p LB, Malloc_iface.lb_remove p LB = lb_remove p LB.
Proof.
  intros p LB. unfold Malloc_iface.lb_remove, lb_remove. induction LB as [|b LB IH]; [reflexivity|].
  cbn [filter list_filter List.filter].
  assert (E : bptr_eqb (MallocBlocks.blk_id b) p = bid_eqb (blk_id b) p) by reflexivity.
  rewrite E. destruct (bid_eqb (blk_id b) p); cbn [negb].
  - rewrite decide_False by (intros H; exact H). exact IH.
  - rewrite decide_True by exact I. f_equal. exact IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma S0_inv_model : forall s LB m MD, S0_inv s LB m MD -> m_halted MD = None /\ m_vm_lazy MD = [].
Proof. intros s LB m MD [_ [(L & _ & HK & _) _]]. split; [exact (kl_halt _ _ _ HK)| exact (kl_lazy _ _ _ HK)]. Qed.

Lemma S0_inv_blocks : forall s LB m MD b, S0_inv s LB m MD -> In b LB -> block_ok S0_layout (blk_addr b) (blk_size b).
Proof.
  intros s LB m MD b [HR _] Hin. pose proof (RHEAP_block_range_proof s LB m b HR Hin) as H.
  unfold rblock_range in H. unfold block_ok. cbn [al_img_lo al_img_hi S0_layout].
  bz_ceil. exact H.
Qed.

Lemma S0_inv_nodup : forall s LB m MD, S0_inv s LB m MD -> NoDup (map blk_id LB).
Proof. intros s LB m MD [HR _]. apply NoDup_ListNoDup. exact (RHEAP_blocks_nodup_proof s LB m HR). Qed.

Lemma S0_inv_disjoint : forall s LB m MD b1 b2, S0_inv s LB m MD -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s LB m MD b1 b2 HI H1 H2 NE. destruct HI as [HR _].
  apply (RHEAP_blocks_disjoint_proof s LB m b1 b2 HR H1 H2).
  intros E. apply NE. pose proof (RHEAP_blocks_nodup_proof s LB m HR) as ND.
  clear -ND H1 H2 E. induction LB as [|b LB IH]; [destruct H1|]. cbn in ND. inversion ND; subst.
  destruct H1 as [->|H1], H2 as [->|H2]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply H3. rewrite E. apply in_map_iff. exists b2; auto.
  - exfalso. apply H3. rewrite <- E. apply in_map_iff. exists b1; auto.
Qed.

Lemma S0_inv_globals : forall s LB m MD, S0_inv s LB m MD -> S0_globals s0segs m.
Proof.
  intros s LB m MD [(st & LB0 & _ & _ & MR & _) _].
  cps_pose MR as (_ & _ & (GL & GN & GP & GG & GS) & _).
  unfold S0_globals. unfold RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, wz, b8 in *.
  split; [exact GN|]. split; [exact GP|]. split; [exact GL|]. split; [exact GG| exact GS].
Qed.

Lemma client_write_ok_r : forall LB iv, fst iv < snd iv -> client_write_ok S0_layout LB iv -> rclient_write_ok LB iv.
Proof.
  intros LB [lo hi] Hlt H. cbn [fst snd] in *. unfold client_write_ok in H. cbn [fst snd al_rw_lo al_img_hi al_static S0_layout] in H.
  unfold rclient_write_ok. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP.
  destruct H as [H|[(H1 & H2 & H3)|(b & Hb & B1 & B2)]].
  - left. bz_ceil. exact H.
  - right; left. split; [exact H1|]. split; [exact H2|]. unfold S0_static in H3.
    split; [|split].
    + destruct (Z_le_gt_dec hi 0x64470) as [?|?]; [left; lia|]. right.
      destruct (Z_le_gt_dec 0x64888 lo) as [?|?]; [lia|]. exfalso.
      destruct (Z_lt_le_dec lo 0x64470).
      * apply (H3 0x64470); lia.
      * apply (H3 lo); lia.
    + destruct (Z_le_gt_dec hi 0x64450) as [?|?]; [left; lia|]. right.
      destruct (Z_le_gt_dec 0x64458 lo) as [?|?]; [lia|]. exfalso.
      destruct (Z_lt_le_dec lo 0x64450); [apply (H3 0x64450); lia| apply (H3 lo); lia].
    + destruct (Z_le_gt_dec hi 0x32138) as [?|?]; [left; lia|]. right.
      destruct (Z_le_gt_dec 0x32140 lo) as [?|?]; [lia|]. exfalso.
      destruct (Z_lt_le_dec lo 0x32138); [apply (H3 0x32138); lia| apply (H3 lo); lia].
  - right; right. exists b. auto.
Qed.

(* [comment removed for export] *)
Lemma outside_filter_nonempty : forall W x,
  outside (List.filter (fun iv => Z.ltb (fst iv) (snd iv)) W) x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn [List.filter fst snd] in H.
  destruct (Z.ltb_spec lo hi); cbn in H.
  - destruct H as [H1 H2]. split; [exact H1| apply IH; exact H2].
  - split; [lia| apply IH; exact H].
Qed.

Lemma munch_nonempty : forall W m m', munch W m m' -> munch (List.filter (fun iv => Z.ltb (fst iv) (snd iv)) W) m m'.
Proof. intros W m m' MU x Hout. apply MU. apply outside_filter_nonempty. exact Hout. Qed.

Lemma S0_inv_frame : forall s LB m m' MD W,
  S0_inv s LB m MD -> munch W m m' -> wmono s0segs m m' -> Forall (client_write_ok S0_layout LB) W -> S0_inv s LB m' MD.
Proof.
  intros s LB m m' MD W [HR HO] MU WM FW. split; [|exact HO].
  apply (RHEAP_frame_proof s LB m m' _ HR (munch_nonempty W m m' MU) WM).
  apply Forall_forall. intros iv Hin. apply List.filter_In in Hin as [Hin Hlt]. apply Z.ltb_lt in Hlt.
  apply client_write_ok_r; [exact Hlt|]. exact (proj1 (Forall_forall _ _) FW iv Hin).
Qed.

Lemma KL_model_frame : forall L pbrk MD MD', KL L pbrk MD -> m_vm MD' = m_vm MD -> m_halted MD' = None -> KL L pbrk MD'.
Proof.
  intros L pbrk MD MD' HK Evm Hh.
  assert (E1 : m_vmmaps MD' = m_vmmaps MD) by (unfold m_vmmaps; rewrite Evm; reflexivity).
  assert (E2 : m_vm_lazy MD' = m_vm_lazy MD) by (unfold m_vm_lazy; rewrite Evm; reflexivity).
  destruct HK; constructor; rewrite ?E1, ?E2; auto.
Qed.

Lemma S0_inv_model_frame : forall s LB m MD MD', S0_inv s LB m MD -> m_vm MD' = m_vm MD -> m_halted MD' = None -> S0_inv s LB m MD'.
Proof.
  intros s LB m MD MD' [HR [(L & Hc & HK & Hi) [ND _]]] Evm Hh. split; [exact HR|].
  split; [|split; [exact ND| exact I]]. exists L. split; [exact Hc|]. split; [|exact Hi].
  eapply KL_model_frame; eauto.
Qed.

Lemma S0_aux_frame : forall m m' B W, rauxv_ok m B -> munch W m m' -> wmono s0segs m m' ->
  Forall (fun iv => snd iv <= B /\ (forall a, fst iv <= a < snd iv -> ~ al_static S0_layout a)) W -> rauxv_ok m' B.
Proof.
  intros m m' B W AV MU WM FW.
  apply (rauxv_ok_frame m m' B _ AV (munch_nonempty W m m' MU) WM).
  apply Forall_forall. intros [lo hi] Hin. apply List.filter_In in Hin as [Hin Hlt]. cbn [fst snd] in Hlt. apply Z.ltb_lt in Hlt.
  pose proof (proj1 (Forall_forall _ _) FW _ Hin) as [HB HS]. cbn [fst snd] in HB, HS. cbn [fst snd].
  split; [exact HB|]. unfold RAUXV_CELL. cbn [al_static S0_layout] in HS. unfold S0_static in HS.
  destruct (Z_le_gt_dec hi 0x64478) as [?|?]; [left; lia|]. right.
  destruct (Z_le_gt_dec 0x64480 lo) as [?|?]; [lia|]. exfalso.
  destruct (Z_lt_le_dec lo 0x64478); [apply (HS 0x64478); lia| apply (HS lo); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma heap_pres_of_r : forall LB SP m m', rheap_pres LB SP m m' -> heap_pres s0segs S0_layout LB SP m m'.
Proof.
  intros LB SP m m' HP a Ha Hc. apply HP; [exact Ha|].
  unfold client_addr in Hc. cbn [al_rw_lo al_img_hi al_private errno_cell al_tp S0_layout] in Hc.
  unfold rclient_addr, ralloc_static, RCTX, RERRNO. unfold S0_private in Hc.
  destruct Hc as [H|[([H0 H1] & H2 & H3)|H]]; [left; exact H| right; left| right; right; exact H].
  unfold errno_cell in H3. cbn [al_tp S0_layout] in H3.
  split; [lia|]. intros [X|X]; [apply H2; lia| apply H3; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errno_cell_S0 : forall tp : word, tp = Z_to_bv 64 0x441e0 -> (bv_unsigned tp + (-164))%Z = errno_cell S0_layout.
Proof. intros tp ->. unfold errno_cell. cbn [al_tp S0_layout]. rewrite unsigned_lit by lia. reflexivity. Qed.

Definition vmG (MD : Model) : PState -> Model -> Prop := fun _ mo => vm_only MD mo.
Lemma vmG_frame : forall MD, frame_ok (vmG MD).
Proof. intros MD s s' mo mo' _ _ V H. unfold vmG in *. eapply vm_only_trans; [exact H| exact V]. Qed.

Lemma OWN_vmG : forall X s MD, OWNX X TrueG s MD -> OWNX X (vmG MD) s MD.
Proof. intros X s MD H. eapply OWNX_weakG; [exact H|]. intros _. apply vm_only_refl. Qed.
Lemma OWN_TrueG : forall X G s MD, OWNX X G s MD -> OWNX X TrueG s MD.
Proof. intros X G s MD H. eapply OWNX_weakG; [exact H|]. intros _. exact I. Qed.

Lemma S0_malloc_dc : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
    (forall (s' : PState) (LB' : list ablock) (m' : word -> option byte) (MD' : Model) (r : Z)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        S0_inv s' LB' m' MD' -> vm_only MD MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        ((r = 0 /\ LB' = LB)
         \/ (r <> 0 /\ block_ok S0_layout r n /\ (exists p, LB' = (p, r, n) :: LB /\ ~ In p (map blk_id LB))
             /\ exists junk, rw_cells s0segs m' r [CB (Z.to_nat n) junk])) ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI AUX SB ST CLO LO ERR MI TP A0 N K.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
                HR AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RMALLOC_STACK; lia) ERR MI TP A0 N) as HM.
  pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) ltac:(lia)) as HS.
  eapply rz_conseq.
  - apply (implM_mspec_realizes s0segs (raw_malloc n) s _ (OWNX (map blk_id LB) (vmG MD)) _ (fun _ _ => T) _ MD HM HS
             (OWN_vmG _ _ _ HO) Hh Hl).
    intros r s' ms' MD' HQm HQk.
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & Hr).
    rewrite (errno_cell_S0 tp TP) in ERR'.
    destruct r as [p|].
    + cps_destruct Hr as (A & junk & -> & BR & HR' & CH & _). destruct HQk as [HO' _].
      pose proof (OWNX_G _ _ _ _ HO') as V. unfold vmG in V.
      apply (K s' ((p, A, n) :: LB) m' MD' A u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv'); try assumption.
      * split; [exact HR'|]. cbn [map blk_id fst]. exact (OWN_TrueG _ _ _ _ HO').
      * apply heap_pres_of_r. exact HP'.
      * right. unfold rblock_range in BR. split; [lia|]. split.
        { unfold block_ok. cbn [al_img_lo al_img_hi S0_layout]. bz_ceil. exact BR. }
        split; [| exists junk; exact CH].
        exists p. split; [reflexivity|].
        pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND. cbn [map] in ND. inversion ND; subst. assumption.
    + destruct Hr as [-> HR']. pose proof (OWNX_G _ _ _ _ HQk) as V. unfold vmG in V.
      apply (K s' LB m' MD' 0 u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv'); try assumption.
      * split; [exact HR'| exact (OWN_TrueG _ _ _ _ HQk)].
      * apply heap_pres_of_r. exact HP'.
      * left. split; reflexivity.
  - eapply t_leaves_const; [exact (HS s MD (OWN_vmG _ _ _ HO))|]. intros MD' HF. exact HF.
Qed.

Lemma S0_malloc_sys : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (n lo B : Z) (errv : word) (Tok : TSet),
    S0_inv s LB m MD -> S0_sys_ok s LB n MD ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 n -> 0 < n < 2^32 ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        S0_inv s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv'] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok S0_layout r n -> ~ In p (map blk_id LB) -> rw_cells s0segs m' r [CB (Z.to_nat n) junk] ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') Tok) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc S0_layout)) fc None m (seg_rom s0segs)) MD) Tok.
Proof.
  intros until Tok. intros HI NF AUX SB ST CLO LO ERR MI TP A0 N Kt.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
                HR AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RMALLOC_STACK; lia) ERR MI TP A0 ltac:(lia)) as HM.
  pose proof (raw_malloc_spec_c (map blk_id LB) (vmG MD) n (vmG_frame MD) ltac:(lia)) as HS.
  (* [comment removed for export] *)
  pose proof (TightBridge.mspec_strengthen (OWNX (map blk_id LB) (vmG MD)) (raw_malloc n) _
                (fun s0 mo0 r s' mo' => s0 = s -> mo0 = MD -> r <> None) HS) as HS1.
  assert (HRR : forall sx mox tr ax sx' mox', OWNX (map blk_id LB) (vmG MD) sx mox -> tpath nstep (raw_malloc n sx) mox tr (Ok (ax, sx')) mox' ->
                 sx = s -> mox = MD -> ax <> None).
  { intros sx mox tr ax sx' mox' _ Hp -> -> ->. exact (NF tr sx' mox' Hp). }
  specialize (HS1 HRR s MD (OWN_vmG _ _ _ HO)). clear HRR.
  eapply rz_conseq.
  - apply (implM_mspec_realizes s0segs (raw_malloc n) s _ (fun s1 mo1 => s1 = s /\ mo1 = MD) _
             (fun _ _ => Tok) _ MD HM HS1
             (conj eq_refl eq_refl) Hh Hl).
    intros r s' ms' MD' HQm [HQk CL]. specialize (CL eq_refl eq_refl).
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & Hr).
    rewrite (errno_cell_S0 tp TP) in ERR'. cbn [fst].
    destruct r as [p|].
    + cps_destruct Hr as (A & junk & -> & BR & HR' & CH & _). destruct HQk as [HO' _].
      pose proof (OWNX_G _ _ _ _ HO') as V. unfold vmG in V.
      pose proof (RHEAP_blocks_nodup_proof _ _ _ HR') as ND. cbn [map] in ND. inversion ND; subst.
      unfold rblock_range in BR.
      bz_ceil.
      assert (HI' : S0_inv s' ((p, A, n) :: LB) m' MD') by (split; [exact HR'| cbn [map blk_id fst]; exact (OWN_TrueG _ _ _ _ HO')]).
      assert (HPP : heap_pres s0segs S0_layout LB (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
      assert (BOK : block_ok S0_layout A n) by (unfold block_ok; cbn [al_img_lo al_img_hi S0_layout]; exact BR).
      apply (Kt s' m' MD' A p u0 u1 u2 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 errv' junk); try assumption. lia.
    + exfalso. exact (CL eq_refl).
  - eapply t_leaves_const; [exact (HS1 s MD (conj eq_refl eq_refl))|]. intros MD' HF. exact HF.
Qed.

Lemma S0_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : PState) (LB : list ablock) (p : bid) (A n lo B : Z) (errv : word) (T : TSet),
    S0_inv s LB m MD -> In (p, A, n) LB ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk s0segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack S0_layout ->
    rw_cells s0segs m (errno_cell S0_layout) [C4 errv] ->
    mem_inv s0segs m ->
    tp = Z_to_bv 64 (al_tp S0_layout) ->
    a0 = Z_to_bv 64 A ->
    (forall (s' : PState) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        S0_inv s' (lb_remove p LB) m' MD' -> vm_only MD MD' ->
        mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 errv] -> rauxv_ok m' B ->
        heap_pres s0segs S0_layout (lb_remove p LB) (bv_unsigned sp) m m' ->
        realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom s0segs)) MD') T) ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros HI Hin AUX SB ST CLO LO ERR MI TP A0 K.
  destruct HI as [HR HO]. pose proof (S0_inv_model s LB m MD (conj HR HO)) as [Hh Hl].
  cbn [al_stack S0_layout] in LO. cbn [al_tp S0_layout] in TP.
  rewrite <- (errno_cell_S0 tp TP) in ERR.
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
                HR Hin AUX SB ST ltac:(bz_ceil; exact CLO) ltac:(unfold RFREE_STACK; lia) ERR MI TP A0) as HM.
  pose proof (raw_free_spec_c (map blk_id (lb_remove p LB)) (vmG MD) p (vmG_frame MD)) as HS.
  assert (HO' : OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD) s MD).
  { eapply OWNX_perm; [| apply OWN_vmG; exact HO]. eapply perm_remove_id; [exact (RHEAP_blocks_nodup_proof _ _ _ HR)| exact Hin]. }
  eapply rz_conseq.
  - apply (implM_mspec_realizes s0segs (raw_free p) s _ (OWNX (p :: map blk_id (lb_remove p LB)) (vmG MD)) _ (fun _ _ => T) _ MD HM HS HO' Hh Hl).
    intros [] s' ms' MD' HQm HQk.
    cps_destruct HQm as (u0 & u1 & u2 & ra0 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m' & -> & MI' & ST' & ERR' & AUX' & HP' & _ & _ & HR').
    rewrite (errno_cell_S0 tp TP) in ERR'. rewrite lb_remove_cj in HP', HR'.
    pose proof (OWNX_G _ _ _ _ HQk) as V. unfold vmG in V.
    assert (HI' : S0_inv s' (lb_remove p LB) m' MD') by (split; [exact HR'| exact (OWN_TrueG _ _ _ _ HQk)]).
    assert (HPP : heap_pres s0segs S0_layout (lb_remove p LB) (bv_unsigned sp) m m') by (apply heap_pres_of_r; exact HP').
    apply (K s' m' MD' u0 u1 u2 ra0 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14); assumption.
  - eapply t_leaves_const; [exact (HS s MD HO')|]. intros MD' HF. exact HF.
Qed.

Lemma S0_free_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model) (T : TSet),
    m_halted MD = None -> m_vm_lazy MD = [] ->
    a0 = Z_to_bv 64 0 ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (ret_pc ra) fc None m (seg_rom s0segs)) MD) T ->
    realizes s0segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free S0_layout)) fc None m (seg_rom s0segs)) MD) T.
Proof.
  intros until T. intros Hh Hl A0 K.
  eapply evt_realizes; [exact Hh| exact Hl| apply (rfree_null_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A0)|].
  intros ms' ->. exact K.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition S0_alloc : AllocIface s0segs S0_layout :=
  mkAllocIface s0segs S0_layout
    PState S0_inv rauxv_ok S0_sys_ok
    S0_inv_model S0_inv_blocks S0_inv_disjoint S0_inv_nodup S0_inv_globals S0_inv_frame S0_inv_model_frame
    S0_aux_frame
    (fun m B B' H HB => rauxv_ok_weaken m B B' H ltac:(bz_ceil; exact HB))
    S0_malloc_dc S0_malloc_sys S0_free S0_free_null.

End ACeilS1.
