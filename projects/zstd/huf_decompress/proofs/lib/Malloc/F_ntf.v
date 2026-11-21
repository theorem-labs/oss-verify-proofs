(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (gmeta_mw, ntf_unfold, free_group_unfold and 4 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F F_ntf_G F_ntf_H.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_ntf () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B8gmeta_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B5go_liC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Malloc=MallocFacts_B;go_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Malloc=MallocFacts_B5go_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Malloc=MallocFacts_B9go_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Malloc<MallocKit_B35mw_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7decoderC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:free_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?nontrivial_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7F_ntf_H8ntf_condC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Malloc=MallocModel_B6aor_stC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4Spec6Malloc7mapinfoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocModel_B;fg_usage_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:record_seqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib6Malloc5F_ntf9oracle_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes2idC35stdpp4base6lookupC35stdpp6option;from_optionI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6MallocAMallocFacts_Bpres9ntf_frame00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B7free_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres:nf_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres9nf_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres9nf_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B<free_fp_monoC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma gmeta_mw st g p : gmeta_ok st g p -> mw_ok (get_meta_rec st g).
Proof.
  intros GO. pose proof (go_li _ _ _ GO). pose proof (go_freeable _ _ _ GO). pose proof (go_sc _ _ _ GO). pose proof (go_maplen _ _ _ GO).
  unfold mw_ok. repeat split; lia.
Qed.

Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> Malloc.M R) bail :
  nontrivial_free dec (S f) st g i k bail =
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in
  if ntf_cond st g i then
    match m_next mr with
    | Some _ =>
      guard 50 (sc <? 48) (
        let activate_new := optr_eqb (active st sc) (Some g) in
        let st1 := dequeue (LActive sc) g st in
        match activate_new, active st1 sc with
        | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
        | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
        end) bail
    | None => free_group R dec (nontrivial_free dec f) st g k bail
    end
  else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
    guard 51 (sc <? 48) (
      if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
      else k (aor_st st g i) None) bail
  else k (aor_st st g i) None.
Proof. reflexivity. Qed.

Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> Malloc.M R) bail :
  free_group R dec rec st g k bail =
  let mr := get_meta_rec st g in
  let st1 := fg_usage_st st g in
  match m_mem mr with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
    if negb (m_maplen mr =? 0) then
      free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
    else
      dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
  end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ntf_result (st' : mstate) (mi : mapinfo) (a0v a1v : word) : Prop :=
  match mi with
  | None => a1v = wz 0
  | Some (b, len) =>
      a0v = wz (conc st' b) /\ a1v = wz len /\ 0 < len < 2^64 /\ snd b = 0
      /\ (exists r, (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup /\ len = round_up_pg (r_len r))
      /\ (forall b' gh, (s_groups st') !! b' = Some gh -> fst b' <> fst b)
  end.

(* [comment removed for export] *)
Definition oracle_ok (o m : word -> option byte) (st : mstate) : Prop :=
  forall rid r q h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= q < round_up_pg (r_len r) ->
    8 <= (r_base r + q) mod 16 ->
    cell_read (get_shadow st rid) q = Unknown h ->
    o (wa (r_base r + q)) = m (wa (r_base r + q)).

Lemma oracle_ok_frame o m st st' : oracle_ok o m st -> s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> oracle_ok o m st'.
Proof.
  intros OK ER ES rid r q h Hr Hk Hq M8 Hc. rewrite ER in Hr. unfold get_shadow in Hc. rewrite ES in Hc.
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma free_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
  intros FR HS H. eapply (free_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma free_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  free_fp st' lo sp a -> free_fp st lo sp a.
Proof. intros ER ES EG H. eapply (free_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

Lemma rdv_known o st q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rdv pans_mem o st q = v.
Proof. intros H. unfold rdv. rewrite H. reflexivity. Qed.

Section NTF.
Variables (ra0 : word) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : ATOP <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
End NTF.


End CANSEC1.
