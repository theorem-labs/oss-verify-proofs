(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_enframe F_mm_syscalls MallocTree MallocBlocks MallocHINV MallocFacts_B. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocRep MallocTree MallocBlocks MallocFacts_B. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_ntf F_free_C. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B MallocKit_B3. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_ntf_C. From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B3. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B MallocKit_B3. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_ntf_C. From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B3. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module F_free_K.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocBlocks OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_B.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_Bpres.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cell_read_wr8 st p v rid o :
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) rid) o =
  if (N.eqb rid (fst p) && Z.eqb o (snd p))%bool then Known v else cell_read (get_shadow st rid) o.
Proof.
  intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
  - destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
  - rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PROT (st : mstate) (LB : list block) (rid : N) (o : Z) : Prop :=
  (exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b - IB <= o < snd b + 12)
  \/ (exists b g i, hosts st b g /\ fst b = rid /\ 0 <= i <= m_last_idx (get_meta_rec st g) /\ o = sstart_of (get_meta_rec st g) i - IB)
  \/ (exists blk, In blk LB /\ fst (blk_slot blk) = rid
        /\ snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk)) - IB <= o < snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk))).

Section KSH.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis EC : s_ctx st' = s_ctx st.
Hypothesis EM : forall q, get_meta_rec st' q = get_meta_rec st q.
Hypothesis TK' : ticks_ok st'.
Hypothesis SHP : forall rid o, PROT st LB rid o -> cell_read (get_shadow st' rid) o = cell_read (get_shadow st rid) o.

Lemma hosts_sh b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. tauto. Qed.
Lemma is_gm_sh q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
Lemma conc_sh q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

Lemma hdr_known_sh p b1 i1 rid :
  fst p = rid -> (forall k, 1 <= k <= 3 -> PROT st LB rid (snd p - k)) ->
  hdr_known st p b1 i1 -> hdr_known st' p b1 i1.
Proof.
  (intros <- HP; cps_intros (v3 & lo & hi & H3 & I3 & H2 & H1 & E)). exists v3, lo, hi.
  rewrite !SHP by (apply HP; lia). auto 10.
Qed.

Lemma KINV_shadow c : KINV st LB c -> KINV st' LB c.
Proof.
  intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
  assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
  { intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
    - unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
    - intros ML. cps_destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
      exists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
      split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
      eapply hdr_known_sh; [reflexivity| | exact HK].
      intros k Hk. left. destruct HB as [ai Hai]. exists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
  constructor.
  - apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
  - intros b g HB. apply GMO. apply hosts_sh. exact HB.
  - intros b gh Hb. rewrite EG in Hb. cps_destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. rewrite EM. auto.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
  - intros s g i Hs. rewrite ESL in Hs. rewrite EM. cps_destruct (CS s g i Hs) as (GM & E & I). split; [apply is_gm_sh; exact GM| auto].
  - intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
    left. exists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
  - intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
    right; left. exists b, g, i. auto.
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
    assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
    constructor; [| rewrite EG; exact NG| exact SZ].
    exists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
    exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
    + rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
    + eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
      cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
  - exact (ki_nodup _ _ _ K).
  - pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
  - intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
  - intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - exact TK'.
Qed.
End KSH.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_st (st : mstate) (pf : aptr) : mstate := wr16 (aadd pf (-2)) 0 (wr8 (aadd pf (-3)) 255 st).

Lemma hdr_st_tables st pf :
  s_regions (hdr_st st pf) = s_regions st /\ s_areas (hdr_st st pf) = s_areas st /\ s_groups (hdr_st st pf) = s_groups st
  /\ s_slots (hdr_st st pf) = s_slots st /\ s_reserved (hdr_st st pf) = s_reserved st /\ s_ctx (hdr_st st pf) = s_ctx st
  /\ s_tick (hdr_st st pf) = s_tick st /\ (forall q, get_meta_rec (hdr_st st pf) q = get_meta_rec st q)
  /\ s_metas (hdr_st st pf) = s_metas st /\ s_next_rid (hdr_st st pf) = s_next_rid st.
Proof. repeat split; reflexivity. Qed.

Lemma ticks_ok_hdr_st st pf : ticks_ok st -> ticks_ok (hdr_st st pf).
Proof. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.

Lemma hdr_st_cell_read st pf rid o : ticks_ok st ->
  cell_read (get_shadow (hdr_st st pf) rid) o =
    if (N.eqb rid (fst pf) && ((o =? snd pf - 1) || (o =? snd pf - 2) || (o =? snd pf - 3)))%bool
    then Known (if o =? snd pf - 3 then 255 else 0)
    else cell_read (get_shadow st rid) o.
Proof.
  intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
  cbn [aadd fst snd].
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
  destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
  destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_cell_read_other st pf rid o : ticks_ok st ->
  (rid <> fst pf \/ o < snd pf - 3 \/ snd pf <= o) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = cell_read (get_shadow st rid) o.
Proof.
  intros TK H. rewrite hdr_st_cell_read by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_st_known_back st pf rid o v : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = Known v -> exists w, cell_read (get_shadow st rid) o = Known w.
Proof.
  intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
  destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
  destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
  destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
  cbn [orb] in H. exists v; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ZINV_hdr_st st pf Zs : ZINV st Zs -> ZINV (hdr_st st pf) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

(* [comment removed for export] *)
Lemma KINV_hdr_st st LB LB' c (pf : aptr) (blk : block) r :
  CINV st LB -> In blk LB -> KINV st LB' c ->
  (forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk) ->
  fst pf = fst (blk_slot blk) -> (s_regions st) !! (fst pf) = Some r -> r_base r + snd pf = blk_addr blk -> snd pf mod 16 = 0 ->
  KINV (hdr_st st pf) LB' c.
Proof.
  intros C Hin K HLB Hfst Hr Hpo PM.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
  destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
  rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  cps_destruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _).
  apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
  intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
  destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
  pose proof (ki_gmetas _ _ _ K) as CG.
  destruct HP as [HP|[HP|HP]].
  - cps_destruct HP as (b & gh & Hb & Fb & Ho).
    specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
    rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
  - cps_destruct HP as (b & g & i & HB & Fb & Hi & ->).
    pose proof (CG b g HB) as GO. cps_destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _). pose proof (go_stride _ _ _ GO) as [S16 SM].
    pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
    assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
    { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
    set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
    unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
  - cps_destruct HP as (blk' & Hin' & Fb' & Ho). destruct (HLB blk' Hin') as [HinL NEs].
    specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
    pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
    destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
    rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
    unfold IB in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
  In x (filter P l) <-> In x l /\ P x.
Proof.
  rewrite <- list_elem_of_In, list_elem_of_filter.
  pose proof (list_elem_of_In l x) as E. tauto.
Qed.

Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
  List.NoDup l -> List.NoDup (filter P l).
Proof.
  induction l as [|x l IH]; intros ND; [constructor|].
  rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
  constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.

Lemma map_filter_slot (f : aptr -> bool) (LB : list block) :
  map blk_slot (filter (fun b => f (blk_slot b)) LB) = filter f (map blk_slot LB).
Proof.
  induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma KINV_filter_slot st LB c (f : aptr -> bool) : KINV st LB c -> KINV st (filter (fun b => f (blk_slot b)) LB) c.
Proof.
  intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
  - apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
    exact (proj1 (List.Forall_forall _ _) BL blk Hin).
  - rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.

Lemma LPRE_intro st LB c g p i (blk : block) :
  ci_slots st -> hosts st p g -> (s_slots st) !! (blk_slot blk) = Some (g, i) ->
  ~ slot_free (get_meta_rec st g) i -> (s_groups st) !! (blk_slot blk) = None -> c <= m_sizeclass (get_meta_rec st g) ->
  LPRE st (filter (fun b => negb (aptr_eqb (blk_slot b) (blk_slot blk))) LB) c g p i.
Proof.
  intros CS HB SL NF NG HC. cps_destruct (CS _ _ _ SL) as (GM & E & I).
  constructor; auto.
  - rewrite <- E. exact NG.
  - apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
    rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ci_mptrs_frame st st2 : ci_mptrs st -> amc (ctx st2) = amc (ctx st) -> s_areas st2 = s_areas st -> s_regions st2 = s_regions st ->
  ci_mptrs st2.
Proof.
  (cps_intros (M1 & M2 & M3 & M4 & M5); intros EC EA ER).
  assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
  unfold amc in EC. inversion EC.
  unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. repeat split; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.

(* [comment removed for export] *)

End ACeilS1.
End F_free_K.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free.F_free_K.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DROPPED (st st' : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ (s_regions st') !! rid = None /\ r_kind r = RKGroup
                /\ r_base r <= a < r_base r + round_up_pg (r_len r).

(* [comment removed for export] *)
Definition lbrm (LB : list block) (blk : block) : list block :=
  filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot blk))) LB.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma oracle_ok_refl m st : oracle_ok m m st.
Proof. intros rid r q h _ _ _ _ _. reflexivity. Qed.

Lemma oracle_ok_hdr_st o m st pf : ticks_ok st -> oracle_ok o m st -> oracle_ok o m (hdr_st st pf).
Proof.
  intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
  rewrite hdr_st_cell_read in Hc by exact TK.
  destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

(* [comment removed for export] *)

Lemma munmap_ok_range_val a : match a with RgErr e => 1 <= e <= 4095 | _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
  - apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  - reflexivity.
Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma mmap_len_round x : mmap_len (round_up_pg x) = round_up_pg x.
Proof.
  pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
  set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cover_intervals tac :=
  let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
  intros lo0 hi0 HW y Hy; cbn [In] in HW;
  repeat (destruct HW as [HW|HW]); try contradiction;
  injection HW; intros; subst lo0 hi0; tac y Hy.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.

(* [comment removed for export] *)
End FREE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
  List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
  cbn [map] in ND. inversion ND; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
  (forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
  induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
  rewrite IH by (intros x Hx; apply HE; right; exact Hx).
  destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
    pose proof (HE a (or_introl eq_refl)); tauto.
Qed.

End ACeilS2.
