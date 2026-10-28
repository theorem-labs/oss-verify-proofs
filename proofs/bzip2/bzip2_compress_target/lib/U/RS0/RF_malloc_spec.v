(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocTree ASlot_I MallocFacts_AM. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocRep MallocTree MallocFacts_A MallocHINV MallocFacts_AM MallocFacts_AS F_malloc_big. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_core.

From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_free F_malloc_fast F_malloc_enframe MallocKit_A MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Monad Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Shadow.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_malloc_join F_malloc_small F_malloc_entry F_malloc_core F_malloc_top.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp RF_enframe. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_entry RF_malloc_join RF_malloc_small RF_malloc_core RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_inv MallocFacts_inv2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RF_malloc_top.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocBlocks OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocHINV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_iface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Shadow.MEnfZero.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join.F_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_join OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_small OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_core OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_top.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RF_malloc_enf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_small OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_core OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_ifaceP.

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

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
  implM rsegs (membed t1) s Q1 ms ->
  implM rsegs (membed t2) s
        (fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
    exists r1, []. cbn. auto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
              impl rsegs (at_node rsegs) (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.bind _ (Ret Unr) f) Qx msx = impl rsegs (at_node rsegs) (f Unr) Qx msx) by reflexivity.
    destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.bind] in *. exact H. }
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.bind] in *. exact H. }
    all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         eapply impl_epost_mono; [eapply IH; exact H1|];
         intros [r2' s2] ms2; cbn; cps_intros (r1' & ans & F1 & F2 & HR & HQ);
         exists r1', (z :: ans); cbn; auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rimplT_silent {R} o (t : Malloc.M R) o' (x : R) s Q ms :
  mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt rsegs (Q x s) ms.
Proof. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_fp st st' LB lo sp m m' :
  RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
  rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
  rheap_pres LB sp m m'.
Proof.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); bz_ceil; lia.
  - destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
  - cps_destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    bz_ceil.
    pose proof MR' as (WF' & _). cps_pose WF' as (_ & WR' & DISJ' & _).
    pose proof MR as (WF & _). cps_pose WF as (_ & WR & DISJ & _).
    destruct REL as [RREG _ _]. cps_destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + rewrite unsigned_lit in H by lia. lia.
    + unfold RCTX in H. lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
        cps_destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ruser_chunk st' m' (p : aptr) r n :
  rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
  16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
  exists junk, rw_cells rsegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof.
  intros MR Hr Hk P0 PN N0.
  cps_pose MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  cps_pose (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). bz_ceil.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at rsegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  cps_destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.

(* [comment removed for export] *)
Lemma all_nth_error_repeat {A} (x : A) (l : list A) :
  (forall i, (i < length l)%nat -> nth_error l i = Some x) -> l = repeat x (length l).
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|]. cbn. f_equal.
  - specialize (H O ltac:(cbn; lia)). cbn in H. congruence.
  - apply IH. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

(* [comment removed for export] *)
Lemma ruser_zero ste m' (rid : N) (po : Z) r n junk :
  rmrep ste m' -> (s_regions ste) !! rid = Some r -> r_kind r = RKGroup ->
  0 <= po -> po + n <= round_up_pg (r_len r) -> 0 <= n ->
  (forall o, po <= o < po + n -> cell_read (get_shadow ste rid) o = Known 0) ->
  rw_cells rsegs m' (r_base r + po) [CB (Z.to_nat n) junk] ->
  junk = repeat (b8 0) (Z.to_nat n).
Proof.
  intros MR Hr Hk P0 PN N0 ZS CH.
  cps_pose MR as (WF & _ & _ & _ & _ & SH). destruct (SH rid r Hr Hk) as [_ HB].
  destruct (u8arr_of_rw_cells rsegs m' _ _ _ CH) as [BA _].
  destruct CH as [[WFC _] _]. cbn in WFC. destruct WFC as [LEN _].
  replace (Z.to_nat n) with (length junk) by (clear - LEN; lia).
  apply all_nth_error_repeat. intros i Hi.
  cps_destruct BA as (_ & _ & RD). rewrite <- (RD i Hi).
  destruct (HB (po + Z.of_nat i) 0 ltac:(clear - P0 PN Hi LEN N0; lia) (ZS (po + Z.of_nat i) ltac:(clear - Hi LEN N0; lia))) as [[_ [_ RB]] _].
  specialize (RB O ltac:(cbn; lia)). cbn [nth_error] in RB. rewrite <- RB. f_equal. f_equal. cbn [Z.of_nat]. lia.
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| bz_ceil; lia]).
  cps_destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_malloc.
  eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  (intros s0' s1' ms1; cps_intros (-> & -> & ->)). cbv beta.
  eapply (implM_bind rsegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + (intros [cst2 r'] s' ms''; cps_intros ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ)). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - (intros [cst2 r'] s' ms''; cps_intros (st2 & r & ans & o1 & E & F1 & F2 & CQ)). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  cps_destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & ZSH & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    cps_pose (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    bz_ceil. unfold RMALLOC_STACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(bz_ceil; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    cps_destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF & MRP).
    cps_destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    cps_pose (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (MallocFacts_inv.areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post. do 15 eexists. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - first [ solve [clear - B0 IDX SPAN S16 RI1 SKL Ha X; lia] | lia ]. }
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk.
    split; [reflexivity|].
    split. { bz_ceil; unfold rblock_range. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). first [ solve [clear - N B0 IDX SPAN S16 RC RI1 SKL OFF0 FIT; lia] | lia ]. }
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    split.
    2:{ (* [comment removed for export] *)
      intros NB.
      assert (MRP' : rmrep (fst (enframe_at st2 g idx n off)) m') by (rewrite Eoff; exact MRP).
      cps_pose (strip_eq_proj _ _ (strip_enframe_at st2 g idx n off)) as (_ & ErP & _).
      assert (HrP : (s_regions (fst (enframe_at st2 g idx n off))) !! (fst b) = Some rg) by (rewrite ErP; exact Hr).
      apply (ruser_zero (fst (enframe_at st2 g idx n off)) m' (fst b) (snd b + 16 + stride * idx + 16 * off) rg n ujunk MRP' HrP Hk
               ltac:(lia) ltac:(subst stride; lia) ltac:(lia)).
      - intros o' Ho'. rewrite (enframe_at_user_cells st2 g idx n off (fst b) o' OFF0 ltac:(lia) FIT).
        + apply (ZSH NB). lia.
        + rewrite <- Ep2, Ep. cbn [snd]. exact Ho'.
      - replace (r_base rg + (snd b + 16 + stride * idx + 16 * off)) with A by (clear - EA; lia). exact UCH. }
    (* [comment removed for export] *)
    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    cps_destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    apply evt_done. unfold rmalloc_post. do 15 eexists. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (MallocFacts_inv.areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
End TOPLEVEL.


End ACeilS1.
End RF_malloc_top.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_core OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_spec.RF_malloc_top OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_alloc_slot OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_big OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_am_P OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_alloc_meta.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Theorem rmalloc_spec : rmalloc_stmt.
Proof.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.


End ACeilS1.
