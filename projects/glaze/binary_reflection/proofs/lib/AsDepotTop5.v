(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsDepotTop4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.AsDepotImg.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.


Section TOP4.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DOBL : depot_obls bt.
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.

  (* [comment removed for export] *)
  Definition miss_case_stmt (KD : Z) (C : ast -> Z -> Prop) : Prop :=
    forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r : bvmap 5 word) (sp buf ret : word) (sz tag : Z) (ws : list word),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> (exists h : option Z, holes_le h st) ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok ASEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      C st sz ->
      let Hd := HID st mdl in let Mr := mrestrict Hd M in let h := sd_hashN ws tag in
      msteps ASEGS (@mkst fx R (Z_to_bv 64 0x8ea80) Mr (seg_rom ASEGS))
                   (@mkst fx r (Z_to_bv 64 0x8ec18) (sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) (seg_rom ASEGS)) ->
      getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 0x1e9458
      /\ getr r 18 = Z_to_bv 64 (0x1e9458 + 4 * sd_bix h) /\ getr r 19 = h /\ getr r 20 = Z_to_bv 64 (0x1e9458 + 4194312)
      /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 24 = Z_to_bv 64 (0x1e9458 + 4194320) /\ getr r 25 = Z_to_bv 64 (dp_tab (a_dep st) (sd_bix h))
      /\ regs_agree (fun i : reg => In i sd_clobx) R r ->
      katD ASEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x8ea80) M (seg_rom ASEGS)) mdl)
           (depot_post bt FXOK KD X st Lc FF M mdl R sp ret).

  Lemma nogrow_dec : forall st sz, {nogrow st sz} + {~ nogrow st sz}.
  Proof using.
    intros st sz. (lazymatch goal with |- ?G => let G' := eval unfold nogrow in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eq_dec ((dp_nids (a_dep st) + 1) / 2 ^ 16) (dp_nids (a_dep st) / 2 ^ 16)) as [E1|N1]; [| right; tauto].
    destruct (Z.eq_dec (dp_frames (a_dep st) / 2 ^ 20) ((dp_frames (a_dep st) + sz) / 2 ^ 20)) as [E2|N2]; [| right; tauto].
    destruct (Z.eq_dec (dp_frames (a_dep st) mod 2 ^ 20) 0) as [E3|N3]; [| left; tauto].
    destruct (Z.eq_dec (dp_frames (a_dep st)) 0) as [E4|N4]; [left; tauto | right; tauto].
  Qed.

  Theorem hyp_depot9_of_grow : forall KD, 224 <= KD -> miss_case_stmt KD (fun st sz => ~ nogrow st sz) -> HYP_DEPOT9_stmt bt FXOK KD.
  Proof using DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS BT_ia BT_segs.
    intros KD HKD GROW. apply (depot_put_of_miss bt FXOK BT_segs BT_ia DCELLS DOBL KD ltac:(lia)).
    intros fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws HFX HH MW W RP DIFF XIMG PXH HOLES ROOM1 ROOM2 E1 E2 E10 E11 SP16 SPC SPHI RET STK SZ Htag KC Lws BUFS BUFW
           Hd Mr h Rws RUN FACTS.
    pose proof ceil_rng as CR. pose proof (u64_range buf) as Hbufr. pose proof (u64_range sp) as Hspr.
    (* [comment removed for export] *)
    assert (BUFD : forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None).
    { intros i Hi. set (k := (i - U buf) / 8).
      assert (Hk : 0 <= k < sz /\ U buf + 8 * k <= i < U buf + 8 * k + 8).
      { (lazymatch goal with |- ?G => let G' := eval unfold k in G in change_no_check G' end). pose proof (Z.div_mod (i - U buf) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (i - U buf) 8 ltac:(lia)) as MB.
        split; [split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] | lia]. }
      pose proof (Rws (Z.to_nat k) ltac:(lia)) as RW. rewrite Z2Nat.id in RW by lia.
      destruct (rdn_bytes ASEGS Mr 8 (at_ buf (8 * k)) _ RW ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]) (Z_to_bv 64 i)) as [b0 Hb0].
      { rewrite at_u by lia. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
      cbn [rdn] in Hb0. unfold Mr, mrestrict in Hb0. destruct (Hd (Z_to_bv 64 i)).
      - exfalso. unfold seg_rom, memory_read in Hb0. change (Z.of_N 1) with 1 in Hb0.
        rewrite (asanF_segs_hi (Z_to_bv 64 i)) in Hb0 by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). discriminate Hb0.
      - destruct (M (Z_to_bv 64 i)); [discriminate|]. exfalso. unfold seg_rom, memory_read in Hb0. change (Z.of_N 1) with 1 in Hb0.
        rewrite (asanF_segs_hi (Z_to_bv 64 i)) in Hb0 by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). discriminate Hb0. }
    assert (SPHI' : U sp + 2192 <= 2 ^ 47) by (unfold PTRHI in SPHI; exact SPHI).
    destruct (nogrow_dec st sz) as [NG | NG].
    - exact (miss_nogrow bt FXOK BT_segs BT_ia DCELLS DOBL DEPOT_FRAMES_ROOM DEP0 KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws
               HFX HH MW W RP DIFF XIMG PXH HOLES (conj ROOM1 ROOM2) KC E1 E2 SPC SPHI' RET STK SZ Htag BUFS BUFW BUFD NG RUN FACTS).
    - exact (GROW fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws
               HFX HH MW W RP DIFF XIMG PXH HOLES (conj ROOM1 ROOM2) KC E1 E2 SPC SPHI' RET STK SZ Htag BUFS BUFW BUFD NG RUN FACTS).
  Qed.
End TOP4.
End AsDepotTop4.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.AsDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsDepotMod OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotRunN OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotRunN2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotHyp9w OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsDepotMnr OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1.AsDepotMnrK OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3.AsDepotRunC1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3.AsDepotRunC2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS4.AsDepotTopN1c OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 AsDepotTop4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
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

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Lemma depot_post_narrow : forall bt FXOK KD X st Lc FF M mdl R sp ret c',
  depot_post_w bt FXOK KD X st Lc FF M mdl R sp ret c' -> depot_post bt FXOK KD X st Lc FF M mdl R sp ret c'.
Proof using.
  intros bt FXOK KD X st Lc FF M mdl R sp ret c' (fx' & st' & M' & mdl' & R' & id & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  exists fx', st', M', mdl', R', id. repeat (split; [assumption|]).
  split; [| exact P8]. intros a NE. destruct (P7 a NE) as [F D]. split; [| exact D].
  destruct F as [F | [F | F]]; [exact F | (lazymatch goal with |- ?G => let G' := eval unfold depot_foot in G in change_no_check G' end); do 4 right; left; exact F | (lazymatch goal with |- ?G => let G' := eval unfold depot_foot in G in change_no_check G' end); do 5 right; exact F].
Qed.

Section TOP5.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DCELLS2 : depot_cells2 bt.
  Hypothesis DOBL : depot_obls bt.
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis GRANT_EX : forall st Lc FF M0 mdl mdlm nZ, WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
    a_kact st <= KCAP -> 0 < nZ <= 2 ^ 23 -> nZ mod 4096 = 0 -> eager_used mdl + nZ + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl) ->
    exists a : word, grant_ok (Z_to_bv 64 0) mdlm a nZ = true.
  Hypothesis GRANT_NR_EX : forall st Lc FF M0 mdl mdlm (nn : option Z), WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> a_kact st <= KCAP ->
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) -> vm_maps (m_vmmaps mdlm) = nnpart nn ++ vm_maps (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdlm) = vm_init_sp (m_vmmaps mdl) ->
    exists a : word, grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true.

  Theorem hyp_depot9_pf : forall KD, 576 <= KD -> HYP_DEPOT9_stmt bt FXOK KD.
  Proof using GRANT_NR_EX GRANT_EX BOOTG DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS2 DCELLS BT_ia BT_segs.
    intros KD HKD. apply (hyp_depot9_of_grow bt FXOK BT_segs BT_ia DCELLS DOBL DEPOT_FRAMES_ROOM DEP0 KD ltac:(lia)).
    intros fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws HFX HH MW W RP DIFF XIMG PXH HOLES ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG Hd Mr h RUN FACTS.
    set (NIDS := dp_nids (a_dep st)) in *. set (tot := dp_frames (a_dep st)) in *.
    assert (SD : {tot / 2 ^ 20 = (tot + sz) / 2 ^ 20 /\ (tot mod 2 ^ 20 <> 0 \/ tot = 0)} + {sgrow st sz}).
    { (lazymatch goal with |- ?G => let G' := eval unfold sgrow in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold tot.
      destruct (Z.eq_dec (tot / 2 ^ 20) ((tot + sz) / 2 ^ 20)) as [E2'|N2]; [| right; tauto].
      destruct (Z.eq_dec (tot mod 2 ^ 20) 0) as [E3|N3]; [| left; tauto].
      destruct (Z.eq_dec tot 0) as [E4|N4]; [left; tauto | right; tauto]. }
    destruct (Z.eq_dec ((NIDS + 1) / 2 ^ 16) (NIDS / 2 ^ 16)) as [CA | NCA]; destruct SD as [CI | SG].
    - exfalso. apply NG. (lazymatch goal with |- ?G => let G' := eval unfold nogrow in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold NIDS tot. tauto.
    - eapply katD_conseq; [| intros c' Hc; exact (depot_post_narrow _ _ _ _ _ _ _ _ _ _ _ _ c' Hc)].
      exact (miss_n2 bt FXOK BT_segs BT_ia DCELLS DCELLS2 DOBL DEPOT_FRAMES_ROOM DEP0 BOOTG GRANT_NR_EX KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws
               HFX HH MW W RP DIFF XIMG PXH HOLES ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD (conj CA SG) RUN FACTS).
    - eapply katD_conseq; [| intros c' Hc; exact (depot_post_narrow _ _ _ _ _ _ _ _ _ _ _ _ c' Hc)].
      exact (miss_n1 bt FXOK BT_segs BT_ia DCELLS DOBL DEPOT_FRAMES_ROOM DEP0 DCELLS2 BOOTG GRANT_EX KD ltac:(lia) fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws
               HFX HH MW W RP DIFF XIMG PXH HOLES ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD (conj NCA CI) RUN FACTS).
    - eapply katD_conseq; [| intros c' Hc; exact (depot_post_narrow _ _ _ _ _ _ _ _ _ _ _ _ c' Hc)].
      exact (miss_n1n2 bt FXOK BT_segs BT_ia DCELLS DCELLS2 DOBL DEPOT_FRAMES_ROOM DEP0 BOOTG GRANT_EX GRANT_NR_EX KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws
               HFX HH MW W RP DIFF XIMG PXH HOLES ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD (conj NCA SG) RUN FACTS).
  Qed.

  (* [comment removed for export] *)
  Theorem hyp_depot_pf : forall KD, 576 <= KD -> AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Proof using GRANT_NR_EX GRANT_EX BOOTG DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS2 DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M mdl R sp buf szw ret sz HFX HH MW W RX XIMG PXH.
    refine (hyp_depot9_pf KD HKD fx X st Lc FF M mdl R sp buf szw ret sz HFX HH MW W RX XIMG _).
    intros a Xa. destruct (PXH a Xa) as [C | C]; [left; exact C | right; right; exact C].
  Qed.
End TOP5.
End WithCeil.
