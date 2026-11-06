(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMod OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunN OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunN2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotHyp9w OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoDepotAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMnr OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1.BoDepotMnrK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3.BoDepotRunC1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3.BoDepotRunC2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Tactic Notation "tclr" ident(H) := try clear H.
Ltac wm_bl := tclr D1; tclr D2; tclr D3; tclr D6; tclr D8; tclr D9; tclr D10; tclr LENP; tclr FRB1; tclr FRB2; tclr KC; tclr DEP0; tclr L10; tclr AL; tclr Htag; tclr Lbs;
  tclr DY; tclr E1; tclr E2; tclr EIDX; tclr STDQ; tclr NROOM; tclr LEAG.
#[local] Ltac lia ::= first [ solve [wm_bl; wm_clear_disj; wm_lia0] | solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section TOPS3.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DCELLS2 : depot_cells2 bt.
  Hypothesis DOBL : depot_obls bt.
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis GRANT_NR_EX : forall st Lc FF M0 mdl mdlm (nn : option Z), WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> a_kact st <= KCAP ->
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) -> vm_maps (m_vmmaps mdlm) = nnpart nn ++ vm_maps (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdlm) = vm_init_sp (m_vmmaps mdl) ->
    exists a : word, grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true.

  (* [comment removed for export] *)
  Definition grow_n2 (st : ast) (sz : Z) : Prop :=
    (dp_nids (a_dep st) + 1) / 2 ^ 16 = dp_nids (a_dep st) / 2 ^ 16 /\ sgrow st sz.

  Theorem miss_n2 : forall KD, 576 <= KD -> miss_case_w bt FXOK KD grow_n2.
  Proof using GRANT_NR_EX BOOTG DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS2 DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws HFX HH MW W RP DIFF XIMG PXH HOLES ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG
           Hd Mr h RUNp (F2 & F8 & F9 & F18 & F19 & F20 & F22 & F24 & F25 & AGp).
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr.
    destruct NG as (CA & SG). destruct HOLES as [h0 HOLE].
    set (d := a_dep st) in *. set (b := sd_bix h) in *. set (NIDS := dp_nids d) in *. set (idx := (NIDS + 1) / 2 ^ 16) in *.
    set (blk := nth (Z.to_nat idx) (node_blocks bt d) 0).
    set (DW := Z_to_bv 64 0x1f0098 : word). set (bW := Z_to_bv 64 (0x1f0098 + 4 * b) : word). set (MUW := Z_to_bv 64 (0x1f0098 + 4194312) : word).
    set (SM := sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) in *.
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (UDW : U DW = 0x1f0098) by reflexivity.
    assert (UbW : U bW = 0x1f0098 + 4 * b) by ((lazymatch goal with |- ?G => let G' := eval unfold bW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in R1.
    destruct R9 as (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw).
    destruct R14 as (Bw1 & Bw2 & _).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (ENID : DEPOT_NIDS bt = 0x1f0098 + 4194304) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_NIDS in G in change_no_check G' end); rewrite ETAB; reflexivity).
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, Dtab, Dnids, Dmu, Dmap, Dnw. fold NIDS in D1, D2, D3, D4, D5, D6, Dnids.
    assert (NN0 : 0 <= NIDS) by (pose proof (D4 0 ltac:(lia)) as X0; lia).
    pose proof (depot_nids_room bt st Lc FF W ROOM KC DEP0) as NROOM. fold d NIDS in NROOM.
    assert (I16 : 0 <= idx < 2 ^ 15) by ((lazymatch goal with |- ?G => let G' := eval unfold idx in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M16 : 0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    assert (INB : In blk (node_blocks bt d)).
    { (lazymatch goal with |- ?G => let G' := eval unfold blk in G in change_no_check G' end). apply nth_In. (lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end). change (length (bt_nodes0 bt :: dp_nodeblocks d)) with (S (length (dp_nodeblocks d))).
      pose proof CA as CA'. rewrite <- D6 in CA'. clear - CA' I16. lia. }
    destruct (node_blocks_dyn bt st Lc FF W blk INB) as ((GB0 & GB1 & GB2 & GB3 & _) & _). rewrite BT_ia in GB3. cbn [ia_img_lo ia_img_hi both_addrs] in GB3.
    assert (GB4 : AIMGHI <= blk) by (clear - GB0 GB3; lia).
    destruct DOBL as (DO1 & DO2 & DO3).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    assert (NHn : forall z, blk <= z < blk + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (DO1 st Lc FF M0 mdl blk z W RP INB Hz). }
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF a NE))). }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i).
    { intros i Hi Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (SF : msum (ivl (U sp - 112) 112) Mr SM) by (apply (sdf_sum Mr sp ret buf sz tag R); lia).
    assert (IMG : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= AIMGHI -> cellZ BSEGS M0 z k v ->
              rdn BSEGS SM (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk C. unfold cellZ, cellN in C. refine (eq_trans _ C). apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite (proj1 SF x) by ((lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M x (NHw x ltac:(right; lia))).
      apply EQ0. apply XI. lia. }
    assert (DEFr : forall x : word, M x <> None -> Hd x = false -> SM x <> None).
    { intros x Dx Hx. apply (proj2 SF). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M x Hx). exact Dx. }
    pose proof (Dtab b Hbix) as Cb. rewrite ETAB, BT_segs in Cb.
    pose proof Dnids as Cn. rewrite ENID, BT_segs in Cn.
    pose proof (Dmap idx I16) as Cm. rewrite EMAP, BT_segs in Cm. fold blk in Cm.
    set (blkW := Z_to_bv 64 blk : word). assert (UblW : U blkW = blk) by ((lazymatch goal with |- ?G => let G' := eval unfold blkW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Rb : rdn BSEGS SM (Z_to_bv 64 (U DW + 4 * b)) 4 = Some (LE4 (Z_to_bv 64 (dp_tab d b)))) by (rewrite UDW; apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cb]).
    assert (Rcnt : rdn BSEGS SM (at_ DW 0x400000) 4 = Some (LE4 (Z_to_bv 64 NIDS))).
    { replace (at_ DW 0x400000) with (Z_to_bv 64 (0x1f0098 + 4194304) : word) by (apply bv_eq; reflexivity). apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cn]. }
    assert (Rmap : rdn BSEGS SM (Z_to_bv 64 (U DW + 0x400010 + 8 * idx)) 8 = Some (LE8 blkW)) by (rewrite UDW; apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cm]).
    set (ndW := di_node blkW NIDS).
    assert (Und : U ndW = blk + 16 * ((NIDS + 1) mod 2 ^ 16)) by ((lazymatch goal with |- ?G => let G' := eval unfold ndW, di_node in G in change_no_check G' end); rewrite UblW; fold NIDS; rewrite u_Z2bv by lia; reflexivity).
    assert (SOKn : store_ok BSEGS SM ndW 8 = true).
    { apply store_ok_bytes; [| rewrite Und; change (Z.of_nat 8) with 8; lia]. intros x Hx. rewrite Und in Hx. change (Z.of_nat 8) with 8 in Hx. apply store_ok1_some. pose proof (u64_range x) as Hxr.
      apply DEFr; [| rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHn; lia].
      pose proof (Dnw blk INB) as WN. assert (D0 : M0 x <> None) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply (WN (U x)); lia).
      destruct (decide (M x = M0 x)) as [E|NE]; [rewrite E; exact D0 | exact (proj2 (DIFF x NE))]. }
    assert (Hstk : store_ok BSEGS SM (at_ (at_ sp (-112)) (-48)) 48 = true).
    { rewrite at_at. apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply store_ok1_some.
      apply DEFr; [apply STK; lia | apply NHw; left; lia]. }
    pose proof (D4 b Hbix) as Htab.
    (* [comment removed for export] *)
    destruct (put_head SM (seg_rom BSEGS) sp DW h blkW (dp_tab d b) NIDS b r
                F2 F8 F9 ltac:(rewrite UDW; exact F18) F19 F22 ltac:(rewrite UDW; exact F24) F25
                ltac:(lia) ltac:(rewrite UDW; split; [reflexivity | lia]) Hbix ltac:(lia) ltac:(lia) ltac:(rewrite UblW, UDW; lia) Rb)
      as (r1 & M1r & RUN1 & SH & AT & Kn & AG1).
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [rewrite UDW, u_Z2bv by lia; lia | rewrite UDW, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rb]. }
    { exact Hstk. } { exact Rcnt. }
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [rewrite at_u; rewrite UDW; lia | rewrite at_u; rewrite UDW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rcnt]. }
    { exact Rmap. } { exact SOKn. }
    replace (Z_to_bv 64 (U DW + 4 * b)) with bW in SH, AT by ((lazymatch goal with |- ?G => let G' := eval unfold bW in G in change_no_check G' end); rewrite UDW; reflexivity). fold ndW in SH, AT.
    set (W0 := wun (ivl (U sp - 112) 112) (head_W sp DW bW ndW)).
    assert (S0r : msum W0 Mr M1r) by (exact (msum_trans _ _ Mr SM M1r SF SH)).
    assert (CLS0 : forall z, W0 z -> cls0 (U sp) b idx (U ndW) None z).
    { intros z Hz. unfold W0, head_W, wun, ivl in Hz. rewrite UDW, UbW in Hz. (lazymatch goal with |- ?G => let G' := eval unfold cls0 in G in change_no_check G' end). clear - Hz. lia. }
    assert (NHW0 : forall x : word, W0 (U x) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. destruct (CLS0 _ Hx) as [C|[C|[C|[C|[[_ C]|[(p & Ep & _)|C]]]]]].
      - apply NHw. left. clear - C SPC HKD. lia.
      - apply NHw. right. clear - C Hbix. lia.
      - apply NHw. right. clear - C. lia.
      - apply NHw. right. clear - C. lia.
      - apply NHw. right. clear - C I16. lia.
      - discriminate Ep.
      - rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHn. rewrite Und in C. clear - C M16. lia. }
    (* [comment removed for export] *)
    pose proof (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) as HOFF.
    apply (katD_msteps_acct BSEGS Hd HOFF asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) (@mkst fx r1 (Z_to_bv 64 0x8cef4) M1r (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact Bw1. } { exact Bw2. } { exact HH. }
    { rewrite restrict_mkst9. eapply msteps_trans; [exact RUNp|]. replace (Z_to_bv 64 0x8cef4) with (0x8cef4%bv : word) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x8f688) with (0x8f688%bv : word) by (apply bv_eq; reflexivity). exact RUN1. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS))) with M by reflexivity.
    set (MS := munrestrict Hd M M1r).
    pose proof (msum_unrestrict Hd W0 M M1r NHW0 S0r) as S0. fold MS in S0.
    pose proof (mrestrict_clean_mem Hd M r1 (Z_to_bv 64 0x8cef4) M1r (seg_rom BSEGS) HC1) as EMS. fold MS in EMS.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl1 & _ & _ & _ & Eeg1).
    (* [comment removed for export] *)
    assert (THRUh : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 -> U sp - 112 <= U x -> rdn BSEGS SM x n = Some v -> rdn BSEGS M1r x n = Some v).
    { intros x n v B0 Hx Hr. apply (msum_rdn_eq BSEGS _ SM M1r x n v SH B0); [| exact Hr]. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold head_W, wun, ivl in G in change_no_check G' end). rewrite UDW, UbW, Und. clear - Hz Hx Hspr SPC CR HKD Hbix GB2 M16. lia. }
    destruct (sdf_args Mr sp ret buf sz tag R ltac:(lia) ltac:(lia) ltac:(lia)) as (Atr & Asz & Atag). fold SM in Atr, Asz, Atag.
    pose proof (sdf_slots Mr sp ret buf sz tag R ltac:(lia)) as SLs. fold SM in SLs.
    apply (sgrow_main bt FXOK BT_segs BT_ia DCELLS DCELLS2 (conj DO1 (conj DO2 DO3)) DEPOT_FRAMES_ROOM DEP0 BOOTG GRANT_NR_EX KD HKD fx X st Lc FF M M0 MS mdl mdl1 R r1 sp buf ret ndW sz tag ws h0 None W0
             HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD SG).
    - fold d NIDS. split; [intros _; rewrite D6; exact CA | reflexivity].
    - intros NE. exfalso. exact (NE eq_refl).
    - intros p E. discriminate E.
    - intros p b0 n0 E. discriminate E.
    - intros p z E. discriminate E.
    - fold d NIDS idx. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt] in G in change_no_check G' end). rewrite app_nil_r. fold blk. exact Und.
    - exists blk. split; [left; exact INB|]. rewrite Und. clear - M16. lia.
    - exact I16.
    - (lazymatch goal with |- ?G => let G' := eval unfold W0, head_W in G in change_no_check G' end). repeat apply wun_dec; apply ivl_dec.
    - exact S0.
    - exact CLS0.
    - fold Hd; rewrite EMS. exact AT.
    - fold Hd; rewrite EMS. apply THRUh; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Atr].
    - fold Hd; rewrite EMS. apply THRUh; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_at, at_u by lia; lia | exact Asz].
    - fold Hd; rewrite EMS. apply THRUh; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_at, at_u by lia; lia | exact Atag].
    - fold Hd; rewrite EMS. intros k v Hin. assert (K : -88 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin).
      apply THRUh; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact (SLs k v Hin)].
    - fold Hd; rewrite EMS. replace (Z_to_bv 64 (0x1f0098 + 4194304)) with (at_ DW 0x400000 : word) by (apply bv_eq; reflexivity). rewrite Kn. f_equal. f_equal.
      (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). rewrite !u_Z2bv by lia. reflexivity.
    - fold Hd; rewrite EMS. change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))).
      pose proof Dmu as Cmu. rewrite ENID, BT_segs in Cmu.
      assert (UMU : U MUW = 0x1f0098 + 4194312) by reflexivity.
      apply (msum_rdn_eq BSEGS _ SM M1r _ _ _ SH); [rewrite u_Z2bv by (clear; lia); change (Z.of_nat 1) with 1; clear; lia
        | intros z Hz; rewrite u_Z2bv in Hz by (clear; lia); change (Z.of_nat 1) with 1 in Hz; (lazymatch goal with |- ?G => let G' := eval unfold head_W, wun, ivl in G in change_no_check G' end); rewrite UDW, UbW, Und; clear - Hz Hspr SPC CR HKD Hbix GB4 M16; lia|].
      apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cmu].
    - intros p E. discriminate E.
    - intros k N1 N2. rewrite (AG1 _ N1). exact (AGp _ N2).
    - (lazymatch goal with |- ?G => let G' := eval unfold ledN, nnpart in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map app length Z.of_nat] in G in change_no_check G' end). rewrite Evm1, Elz1, Eeg1, Ehl1. repeat (split; [reflexivity|]).
      split; [lia|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|]. split; [exact HH | exact (same_but_materialized_except_vm mdl mdl1 SBM1)].
    - exact MI1.
  Qed.
End TOPS3.
