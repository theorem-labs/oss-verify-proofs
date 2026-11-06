(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotTopN1c.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMod OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunN OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunN2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotHyp9w OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section TOPN1C.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DOBL : depot_obls bt.
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.
  Hypothesis DCELLS2 : depot_cells2 bt.
  Hypothesis BOOTG : boot_geom bt.
  (* [comment removed for export] *)
  Hypothesis GRANT_EX : forall st Lc FF M0 mdl mdlm nZ, WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
    a_kact st <= KCAP -> 0 < nZ <= 2 ^ 23 -> nZ mod 4096 = 0 -> eager_used mdl + nZ + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl) ->
    exists a : word, grant_ok (Z_to_bv 64 0) mdlm a nZ = true.

  (* [comment removed for export] *)
  Lemma miss_n1_front : forall KD, 464 <= KD ->
    forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r : bvmap 5 word) (sp buf ret : word) (sz tag : Z) (ws : list word) (h0 : option Z) (Qpost : config -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> holes_le h0 st ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      (dp_nids (a_dep st) + 1) / 2 ^ 16 <> dp_nids (a_dep st) / 2 ^ 16 ->
      let Hd := HID st mdl in let Mr := mrestrict Hd M in let h := sd_hashN ws tag in
      let d := a_dep st in let b := sd_bix h in let idx := (dp_nids d + 1) / 2 ^ 16 in
      let DW : word := Z_to_bv 64 0x1f0098 in let MUW : word := Z_to_bv 64 (0x1f0098 + 4194312) in let bW : word := Z_to_bv 64 (0x1f0098 + 4 * b) in
      let W1 := wun (ivl (U sp - 112) 112) (n1pre_W sp DW bW) in
      let spM := at_ (at_ sp (-112)) (-32) in let szW : word := Z_to_bv 64 1048576 in
      msteps BSEGS (@mkst fx R (Z_to_bv 64 0x8f4f0) Mr (seg_rom BSEGS))
                   (@mkst fx r (Z_to_bv 64 0x8f688) (sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) (seg_rom BSEGS)) ->
      getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 0x1f0098
      /\ getr r 18 = Z_to_bv 64 (0x1f0098 + 4 * sd_bix h) /\ getr r 19 = h /\ getr r 20 = Z_to_bv 64 (0x1f0098 + 4194312)
      /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 24 = Z_to_bv 64 (0x1f0098 + 4194320) /\ getr r 25 = Z_to_bv 64 (dp_tab (a_dep st) (sd_bix h))
      /\ regs_agree (fun i : reg => In i sd_clobx) R r ->
      (forall (r1 r' : bvmap 5 word) (Mtr MB : mem) (a : word) (mdlm mdl4 : Model),
          let M1f := munrestrict Hd M Mtr in let WB := wun (ivl (U sp - 464) 320) (ivl (U a) (2 ^ 20)) in
          regs_agree (fun i : reg => In i sd_clobx) R r -> regs_agree (fun i : reg => In i put_clob) r r1 ->
          msum W1 M M1f ->
          getr r1 8 = MUW -> getr r1 9 = Z_to_bv 64 (0x1f0098 + 4194312 + 8 * idx) -> getr r1 19 = h -> getr r1 21 = Z_to_bv 64 (dp_tab d b) ->
          getr r1 22 = Z_to_bv 64 65535 -> getr r1 23 = Z_to_bv 64 (dp_nids d + 1) ->
          rdn BSEGS Mtr (Z_to_bv 64 (0x1f0098 + 4194304)) 4 = Some (LE4 (Z_to_bv 64 (dp_nids d + 1))) ->
          (forall (k : Z) (v : word), In (k, v) [(-8, (Z_to_bv 64 0x8f790 : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (dp_nids d + 1)); (-32, bW)]%Z ->
               rdn BSEGS Mtr (at_ (at_ sp (-112)) k) 8 = Some (LE8 v)) ->
          rdn BSEGS Mtr (at_ sp (-104)) 8 = Some (LE8 buf) -> rdn BSEGS Mtr (at_ (at_ sp (-104)) 8) 4 = Some (LE4 (Z_to_bv 64 sz)) ->
          rdn BSEGS Mtr (at_ (at_ sp (-104)) 12) 4 = Some (LE4 (Z_to_bv 64 tag)) ->
          (forall (k : Z) (v : word),
              In (k, v) [(-8, ret); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20);
                         (-56, getr R 21); (-64, getr R 22); (-72, getr R 23); (-80, getr R 24); (-88, getr R 25)]%Z ->
              rdn BSEGS Mtr (at_ sp k) 8 = Some (LE8 v)) ->
          idx = Z.of_nat (length (node_blocks bt d)) -> 0 <= idx < 2 ^ 15 ->
          (* [comment removed for export] *)
          same_but_materialized mdl mdlm -> grant_ok (Z_to_bv 64 0) mdlm a (2 ^ 20) = true ->
          same_but_materialized (mmap_model a szW mdlm) mdl4 -> MInv (a_aa st) mdl4 ->
          mo_ret' r1 r' spM (Z_to_bv 64 0x8fdb8) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) a ->
          msum WB M1f MB -> (forall x : word, U a <= U x < U a + 2 ^ 20 -> MB x <> None) ->
          katD BSEGS (mkCfg (@mkst fx r' (Z_to_bv 64 0x8fdb8) MB (seg_rom BSEGS)) mdl4) Qpost) ->
      katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) mdl) Qpost.
  Proof using GRANT_EX BOOTG DCELLS2 DEP0 DEPOT_FRAMES_ROOM DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws h0 Qpost HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD CA
           Hd Mr h d b idx DW MUW bW W1 spM szW RUNp FACTS CONTH.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr.
    destruct (miss_n1_run1 bt BT_segs BT_ia DCELLS2 KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws
                W RP DIFF XIMG PXH ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD CA FACTS)
      as (r1 & Mtr & RUN1 & SUM1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A19 & A21 & A22 & A23 & Kn1 & SLt & AG1 & Atr & Asz & Atag & SLs & EIDX & I16 & NN0 & N31).
    fold Hd Mr h in RUN1, SUM1, A19.
    destruct FACTS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AGp).
    set (tot := dp_frames d) in *. set (q := tot / 2 ^ 20) in *. set (NIDS := dp_nids d) in *.
    set (blkd := nth (Z.to_nat q) (store_blocks bt d) 0) in *.
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (UDW : U DW = 0x1f0098) by reflexivity. assert (UMU : U MUW = 0x1f0098 + 4194312) by reflexivity.
    assert (UbW : U bW = 0x1f0098 + 4 * b) by ((lazymatch goal with |- ?G => let G' := eval unfold bW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Q20 : 0 <= q < 2 ^ 12).
    { pose proof W as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & D7 & _) & _). pose proof (DEPOT_FRAMES_ROOM st Lc FF W ROOM KC) as FROOM. fold d tot in D7, FROOM. unfold FRW in FROOM.
      (lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (CLS1 : forall z, W1 z -> (U sp - 160 <= z < U sp) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) \/ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 16)).
    { intros z Hz. unfold W1, n1pre_W, wun, ivl in Hz. rewrite UDW, UbW in Hz. lia. }
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in R1.
    destruct R14 as (Bw1 & Bw2 & _ & _ & _ & _ & Bw7 & _).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    assert (NHW1 : forall x : word, W1 (U x) -> Hd x = false).
    { intros x Hx. apply NHw. destruct (CLS1 _ Hx) as [C|[C|C]]; [left; lia | right; lia | right; lia]. }
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF a NE))). }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i).
    { intros i Hi Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    pose proof (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) as HOFF.
    (* [comment removed for export] *)
    apply (katD_msteps_acct BSEGS Hd HOFF asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) (@mkst fx r1 (Z_to_bv 64 0x82878) Mtr (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact Bw1. } { exact Bw2. } { exact HH. }
    { rewrite restrict_mkst9. eapply msteps_trans; [exact RUNp | exact RUN1]. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS))) with M by reflexivity.
    set (M1f := munrestrict Hd M Mtr).
    pose proof (msum_unrestrict Hd W1 M Mtr NHW1 SUM1) as [FR1 GR1]. fold M1f in FR1, GR1.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl1 & _ & _ & _ & Eeg1).
    (* [comment removed for export] *)
    assert (IMG1 : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= AIMGHI -> (forall i, z <= i < z + Z.of_nat k -> ~ W1 i) -> cellZ BSEGS M0 z k v ->
              rdn BSEGS M1f (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk NW C. unfold cellZ, cellN in C. rewrite <- C. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite (FR1 x (NW _ Hx)). apply EQ0. apply XI. lia. }
    assert (OUT1 : forall i, AIMGLO <= i < 0x1f0098 -> ~ W1 i).
    { intros i Hi WZ. destruct (CLS1 _ WZ) as [C|[C|C]]; lia. }
    destruct DCELLS2 as (C_gpg & C_pg & C_b260 & C_c144 & C_one & C_dc). destruct DCELLS as (_ & _ & _ & C_cf & _).
    assert (UspM : U spM = U sp - 144) by ((lazymatch goal with |- ?G => let G' := eval unfold spM in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    assert (Usz : U szW = 2 ^ 20) by reflexivity.
    replace (Z_to_bv 64 0x82878) with (0x82878%bv : word) by (apply bv_eq; reflexivity).
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12. fold tot in D7, D9, D10. fold NIDS in D1, D2, D3, D4, D5, D6.
    pose proof (depot_nids_room bt st Lc FF W ROOM KC DEP0) as NROOM. fold d NIDS in NROOM.
    pose proof (depot_n1_budget bt st Lc FF M0 mdl (2 ^ 20) (2 ^ 28) RP W ltac:(lia) KC NROOM) as BUDG.
    (* [comment removed for export] *)
    assert (GFACTS : forall mdlm (a : word), same_but_materialized mdl1 mdlm -> grant_ok (Z_to_bv 64 0) mdlm a (2 ^ 20) = true ->
              same_but_materialized mdl mdlm /\ m_vmmaps mdlm = m_vmmaps mdl /\ m_vm_lazy mdlm = m_vm_lazy mdl
              /\ dyn_ok (bt_ia bt) (U a) (U a + 2 ^ 20) /\ U a mod PG = 0
              /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> U a + 2 ^ 20 <= lo \/ hi <= U a)
              /\ AIMGHI <= U a /\ U a + 2 ^ 20 <= CEIL).
    { intros mdlm a SBMm G. pose proof (same_but_materialized_trans _ _ _ SBM1 SBMm) as SBM0m. assert (SZ19 : 2 ^ 19 < 2 ^ 20) by lia.
      destruct (sbm_vmmaps _ _ SBM0m) as [EVm ELm].
      destruct (grant_ok_facts bt st Lc FF M0 mdl mdlm (2 ^ 20) (2 ^ 28) W RP BOOTG EVm (Z_to_bv 64 0) a (2 ^ 20) h0 ltac:(lia) ltac:(reflexivity)
                  (or_intror (conj SZ19 HOLE)) G) as (DY & AL & AP).
      split; [exact SBM0m|]. split; [exact EVm|]. split; [exact ELm|]. split; [exact DY|]. split; [exact AL|]. split; [exact AP|].
      destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4. split; [lia | exact Y3]. }
    apply (mo_katD Hd HOFF asanF_segs_wx (a_aa st) r1 M1f (seg_rom BSEGS) mdl1 spM (Z_to_bv 64 0x8fdb8)
             (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) szW (Z_to_bv 64 138627) (Z_to_bv 64 0) 0x19dc60 0x19fce8 Qpost
             (fun mdlm a => grant_ok (Z_to_bv 64 0) mdlm a (2 ^ 20) = true) (fun mdlm a => mmap_model a szW mdlm)).
    - exact A1.
    - exact A2.
    - exact A10.
    - exact A11.
    - exact A12.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite UspM. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end). apply bv_eq. vm_compute. reflexivity.
    - rewrite Usz. split; [reflexivity | lia].
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - apply store_ok_bytes; [| rewrite at_u by lia; rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. intros x Hx. rewrite at_u in Hx by lia. rewrite UspM in Hx. cbn in Hx.
      eapply store_ok_mono; [exact GR1|]. exact (proj2 (STK x ltac:(lia))).
    - apply IMG1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_gpg)].
    - apply IMG1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_pg)].
    - apply IMG1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_cf)].
    - change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))).
      apply IMG1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_b260)].
    - apply IMG1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_c144)].
    - apply IMG1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_one)].
    - apply IMG1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply OUT1; cbn in Hi; lia | exact (const_cell bt M0 _ _ _ R1 C_dc)].
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. left. rewrite UspM in Hx. lia.
    - rewrite Ehl1. exact HH.
    - rewrite Elz1. apply lazy_cover_HID.
    - exact Bw1.
    - exact MI1.
    - (* [comment removed for export] *) intros mdlm a SBMm G. destruct (GFACTS mdlm a SBMm G) as (_ & _ & _ & _ & _ & _ & GA & GC). rewrite Usz, UspM. lia.
    - (* [comment removed for export] *) intros mdlm rr SBMm MIm HLm B10 B11 B12 B13 B14 B15 Q' KOK KKP.
      apply (node_dm_of_mmap_rw rr _ _ mdlm szW Q' HLm B10 B11 B12 B13 B14 B15 ltac:(rewrite Usz; lia) ltac:(rewrite Usz; reflexivity)).
      + rewrite Usz. apply (GRANT_EX st Lc FF M0 mdl mdlm (2 ^ 20) W RP (same_but_materialized_trans _ _ _ SBM1 SBMm) MIm KC ltac:(lia) ltac:(reflexivity)). lia.
      + intros a Ha. rewrite Usz in Ha. exact (KOK a Ha).
      + exact KKP.
    - (* [comment removed for export] *) intros mdlm a SBMm MIm G. destruct (GFACTS mdlm a SBMm G) as (SBM0m & EVm & ELm & _ & _ & _ & GA & GC).
      split; [rewrite mmap_model_halted; pose proof (same_but_materialized_frame mdl mdlm SBM0m) as F;
              destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _); rewrite HL; exact HH|].
      split; [rewrite mmap_model_lazy, ELm; apply lazy_cover_HID|].
      apply (plain_child_MInv mdl mdlm a szW MW EVm ELm ltac:(rewrite Usz; lia) (a_aa st) MIm). rewrite Usz. lia.
    - (* [comment removed for export] *) intros a r' mdlm mdl4 SBMm MIm G SBM4 MI4 MR.
      destruct (GFACTS mdlm a SBMm G) as (SBM0m & _ & _ & _ & _ & _ & GA & GC).
      pose proof (u64_range a) as Har.
      match goal with |- katD _ (mkCfg (mkst _ _ ?m _) _) _ => set (MB := m) end.
      apply (CONTH r1 r' Mtr MB a mdlm mdl4 AGp AG1 (conj FR1 GR1) A8 A9 A19 A21 A22 A23 Kn1 SLt Atr Asz Atag SLs EIDX I16 SBM0m G SBM4 MI4 MR).
      + split.
        * intros x Hx. unfold wun, ivl in Hx. (lazymatch goal with |- ?G => let G' := eval unfold MB in G in change_no_check G' end).
          rewrite wbytes_outside by (rewrite ?length_word_to_le_bytes, at_u by lia; rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
          rewrite zfill_out by (rewrite Usz; lia). apply mo_m1_outside; [rewrite UspM; lia | rewrite UspM; lia].
        * (lazymatch goal with |- ?G => let G' := eval unfold MB in G in change_no_check G' end). eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply zfill_grows2]. apply mo_m1_grows.
      + intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MB in G in change_no_check G' end). apply wbytes_grows. rewrite (zfill_in' a szW _ x) by (rewrite Usz; lia). discriminate.
  Qed.

  Theorem miss_n1 : forall KD, 464 <= KD -> miss_case_w bt FXOK KD grow_n1.
  Proof using GRANT_EX BOOTG DCELLS2 DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws HFX HH MW W RP DIFF XIMG PXH [h0 HOLE] ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG
           Hd Mr h RUNp FACTS.
    apply (miss_n1_front KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws h0 _
             HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD (proj1 NG) RUNp FACTS).
    intros r1 r' Mtr MB a mdlm mdl4. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    exact (miss_n1_cont bt FXOK BT_segs BT_ia DCELLS DOBL DEPOT_FRAMES_ROOM DEP0 BOOTG KD HKD fx X st Lc FF M M0 mdl R r r1 r' sp buf ret a sz tag ws Mtr MB mdlm mdl4 h0
             HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG).
  Qed.
End TOPN1C.
End BoDepotTopN1c.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMod OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunN OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotRunN2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotHyp9w OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoDepotAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoDepotMnr OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1.BoDepotMnrK OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3.BoDepotRunC1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3.BoDepotRunC2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopN1b.BoDepotTopN1a BoDepotTopN1c OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTopS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b.
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

Lemma mo_clob_put : forall i : reg, In i mo_clob -> In i put_clob.
Proof. intros i Hi. unfold mo_clob in Hi. (lazymatch goal with |- ?G => let G' := eval unfold put_clob in G in change_no_check G' end). cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [in_l|]). destruct Hi. Qed.

Section TOPS4.
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
  Hypothesis GRANT_EX : forall st Lc FF M0 mdl mdlm nZ, WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
    a_kact st <= KCAP -> 0 < nZ <= 2 ^ 23 -> nZ mod 4096 = 0 -> eager_used mdl + nZ + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl) ->
    exists a : word, grant_ok (Z_to_bv 64 0) mdlm a nZ = true.
  Hypothesis GRANT_NR_EX : forall st Lc FF M0 mdl mdlm (nn : option Z), WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> a_kact st <= KCAP ->
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) -> vm_maps (m_vmmaps mdlm) = nnpart nn ++ vm_maps (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdlm) = vm_init_sp (m_vmmaps mdl) ->
    exists a : word, grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true.

  Definition grow_n1n2 (st : ast) (sz : Z) : Prop :=
    (dp_nids (a_dep st) + 1) / 2 ^ 16 <> dp_nids (a_dep st) / 2 ^ 16 /\ sgrow st sz.

  Theorem miss_n1n2 : forall KD, 576 <= KD -> miss_case_w bt FXOK KD grow_n1n2.
  Proof using GRANT_NR_EX GRANT_EX BOOTG DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS2 DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws HFX HH MW W RP DIFF XIMG PXH [h0 HOLE] ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD [CA SG]
           Hd Mr h RUNp FACTS.
    apply (miss_n1_front bt FXOK BT_segs BT_ia DCELLS DEPOT_FRAMES_ROOM DEP0 DCELLS2 BOOTG GRANT_EX KD ltac:(lia) fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws h0 _
             HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD CA RUNp FACTS).
    intros r1 r' Mtr MB a mdlm mdl4. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold Hd h.
    set (d := a_dep st) in *. set (b := sd_bix h) in *. set (NIDS := dp_nids d) in *. set (idx := (NIDS + 1) / 2 ^ 16) in *.
    set (DW := Z_to_bv 64 0x1f0098 : word). set (MUW := Z_to_bv 64 (0x1f0098 + 4194312) : word). set (bW := Z_to_bv 64 (0x1f0098 + 4 * b) : word).
    set (W1 := wun (ivl (U sp - 112) 112) (n1pre_W sp DW bW)). set (M1f := munrestrict Hd M Mtr). set (spM := at_ (at_ sp (-112)) (-32)).
    set (szW := Z_to_bv 64 1048576 : word). set (WB := wun (ivl (U sp - 464) 320) (ivl (U a) (2 ^ 20))).
    intros AGp AG1 [FR1 GR1] A8 A9 A19 A21 A22 A23 Kn1 SLt Atr Asz Atag SLs EIDX I16 SBM0m G SBM4 MI4 MR [FRB GRB] DEFA.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range a) as Har.
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (UDW : U DW = 0x1f0098) by reflexivity. assert (UMU : U MUW = 0x1f0098 + 4194312) by reflexivity.
    assert (UbW : U bW = 0x1f0098 + 4 * b) by ((lazymatch goal with |- ?G => let G' := eval unfold bW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (UspM : U spM = U sp - 144) by ((lazymatch goal with |- ?G => let G' := eval unfold spM in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    assert (Usz : U szW = 2 ^ 20) by reflexivity.
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6. fold NIDS in D1, D2, D3, D4, D5, D6. clear D7 D8 D9 D10 D11 D12.
    assert (NN0 : 0 <= NIDS) by (pose proof (D4 0 ltac:(lia)) as X0; lia).
    pose proof (depot_nids_room bt st Lc FF W ROOM KC DEP0) as NROOM. fold d NIDS in NROOM.
    assert (M16 : 0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    assert (CLS1 : forall z, W1 z -> (U sp - 160 <= z < U sp) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) \/ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
                                    \/ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 4)).
    { intros z Hz. unfold W1, n1pre_W, wun, ivl in Hz. rewrite UDW, UbW in Hz. clear - Hz. lia. }
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct R14 as (Bw1 & Bw2 & _).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    pose proof (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) as HOFF.
    (* [comment removed for export] *)
    destruct (sbm_vmmaps _ _ SBM0m) as [EVm ELm].
    assert (SZ19 : 2 ^ 19 < 2 ^ 20) by lia.
    destruct (grant_ok_facts bt st Lc FF M0 mdl mdlm (2 ^ 20) (2 ^ 28) W RP BOOTG EVm (Z_to_bv 64 0) a (2 ^ 20) h0 ltac:(lia) ltac:(reflexivity)
                (or_intror (conj SZ19 HOLE)) G) as (DY & AL & AP).
    assert (GAC : AIMGHI <= U a /\ U a + 2 ^ 20 <= CEIL).
    { destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4. clear - Y3 Y4 Y1 Har. lia. }
    destruct GAC as [GA GC].
    destruct MR as (B10 & B2 & B1 & B8 & B9 & B18 & B19 & AGm).
    destruct (plain_child_ledger mdl mdlm mdl4 a szW MW EVm ELm ltac:(rewrite Usz; lia) SBM4) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
    assert (HL4 : m_halted mdl4 = None).
    { pose proof (same_but_materialized_frame _ _ SBM4) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLa & _). rewrite HLa, mmap_model_halted.
      pose proof (same_but_materialized_frame mdl mdlm SBM0m) as F. destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLb & _). rewrite HLb. exact HH. }
    assert (NHa : forall z, U a <= z < U a + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (grant_not_lazy bt st Lc FF M0 mdl (U a) (2 ^ 20) W RP DY AP z Hz). }
    set (MBr := mrestrict Hd MB).
    assert (TB : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 ->
                   (forall i, U x <= i < U x + Z.of_nat n -> (CEIL <= i \/ (AIMGLO <= i /\ i < AIMGHI)) /\ ~ WB i) -> rdn BSEGS Mtr x n = Some v -> rdn BSEGS MBr x n = Some v).
    { intros x n v B0 F Hr. rewrite <- Hr. apply rdn_ext; [exact B0|]. intros y Hy. destruct (F (U y) Hy) as [NH NW].
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB y (NHw y NH)). rewrite (FRB y NW). (lazymatch goal with |- ?G => let G' := eval unfold M1f in G in change_no_check G' end). apply munrestrict_off. exact (NHw y NH). }
    assert (STKB : forall i, U sp - 144 <= i -> (CEIL <= i \/ (AIMGLO <= i /\ i < AIMGHI)) /\ ~ WB i).
    { intros i Hi. split; [left; clear - Hi SPC HKD; lia | (lazymatch goal with |- ?G => let G' := eval unfold WB, wun, ivl in G in change_no_check G' end); clear - Hi GC SPC HKD; lia]. }
    assert (IMB : forall i, AIMGLO <= i < AIMGHI -> (CEIL <= i \/ (AIMGLO <= i /\ i < AIMGHI)) /\ ~ WB i).
    { intros i Hi. split; [right; clear - Hi; lia | (lazymatch goal with |- ?G => let G' := eval unfold WB, wun, ivl in G in change_no_check G' end); clear - Hi GA SPC CR HKD; lia]. }
    assert (DEFB : forall x : word, M x <> None -> Hd x = false -> MBr x <> None).
    { intros x Dx Hx. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x Hx). apply GRB. apply GR1. exact Dx. }
    (* [comment removed for export] *)
    assert (SLQ : forall (k : Z) (v : word), In (k, v) [(-8, (0x8f790%bv : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (NIDS + 1)); (-32, bW)]%Z ->
                rdn BSEGS MBr (at_ (at_ sp (-112)) k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : -32 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin).
      apply TB; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; rewrite at_at, at_u in Hi by lia; apply STKB; lia |].
      apply SLt. cbn [In] in Hin |- *. replace (Z_to_bv 64 0x8f790) with (0x8f790%bv : word) by (apply bv_eq; reflexivity). exact Hin. }
    set (ndW := di_node a NIDS).
    assert (Und : U ndW = U a + 16 * ((NIDS + 1) mod 2 ^ 16)) by ((lazymatch goal with |- ?G => let G' := eval unfold ndW, di_node in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Uslot : U (tl_slot MUW idx) = 0x1f0098 + 4194320 + 8 * idx) by ((lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end); rewrite UMU; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]).
    assert (EQ0 : forall x : word, ~ X (U x) -> M x = M0 x).
    { intros x NX. destruct (decide (M x = M0 x)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF x NE))). }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i).
    { intros i Hi Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (IMGB : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= AIMGHI -> (forall i, z <= i < z + Z.of_nat k -> ~ W1 i) -> cellZ BSEGS M0 z k v ->
                   rdn BSEGS MBr (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk NW C. unfold cellZ, cellN in C. refine (eq_trans _ C). apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x (NHw x ltac:(right; lia))).
      rewrite (FRB x) by ((lazymatch goal with |- ?G => let G' := eval unfold WB, wun, ivl in G in change_no_check G' end); clear - Hx Hz Hk GA SPC CR HKD; lia). rewrite (FR1 x (NW _ Hx)). apply EQ0. apply XI. lia. }
    destruct R9 as (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (Rslot0 : rdn BSEGS MBr (tl_slot MUW idx) 8 = Some (LE8 (Z_to_bv 64 0))).
    { (lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end). rewrite UMU. pose proof (Dmap idx I16) as Cm. rewrite EMAP, BT_segs in Cm.
      fold d in Cm. rewrite (nth_overflow (node_blocks bt d) 0) in Cm by (rewrite EIDX, Nat2Z.id; apply Nat.le_refl).
      replace (0x1f0098 + 4194312 + 8 + 8 * idx) with (0x1f0098 + 4194320 + 8 * idx) by (clear; lia).
      apply IMGB; [clear - I16; lia | change (Z.of_nat 8) with 8; clear - I16; lia | | exact Cm].
      intros i Hi WZ. change (Z.of_nat 8) with 8 in Hi. destruct (CLS1 _ WZ) as [C|[C|[C|C]]]; clear - C Hi I16 Hspr SPC CR HKD Hbix; lia. }
    assert (SOKs : store_ok BSEGS MBr (tl_slot MUW idx) 8 = true).
    { refine (readable_store_ok BSEGS 0x107000 MBr _ 8 _ both_rw_above _ _ Rslot0); [rewrite Uslot; clear - I16; lia | rewrite Uslot; change (Z.of_nat 8) with 8; clear - I16; lia]. }
    assert (SOKl : store_ok BSEGS MBr MUW 1 = true).
    { apply (rwseg_store_ok BSEGS 16 (Z_to_bv 64 0x5f0098) MBr MUW 1 mu_img_ok);
        [change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | rewrite UMU; change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; clear; lia
         | rewrite UMU; change (U (Z_to_bv 64 0x5f0098)) with 0x5f0098; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]. }
    assert (SOKn : store_ok BSEGS MBr ndW 8 = true).
    { apply store_ok_bytes; [| rewrite Und; change (Z.of_nat 8) with 8; clear - Har M16 GC CR; lia]. intros x Hx. rewrite Und in Hx. change (Z.of_nat 8) with 8 in Hx. apply store_ok1_some.
      (lazymatch goal with |- ?G => let G' := eval unfold MBr in G in change_no_check G' end). rewrite (mrestrict_off Hd MB x) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHa; clear - Hx M16; lia).
      apply DEFA. clear - Hx M16. lia. }
    assert (HstkQ : store_ok BSEGS MBr (at_ (at_ sp (-112)) (-32)) 32 = true).
    { rewrite at_at. apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply store_ok1_some.
      apply DEFB; [apply STK; lia | apply NHw; left; lia]. }
    (* [comment removed for export] *)
    assert (NIm : forall i : reg, In i [20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 3%bv; 4%bv] -> ~ In i mo_clob).
    { intros i Hi Hx. unfold mo_clob in Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    assert (T21 : getr r' 21 = Z_to_bv 64 (dp_tab d b)) by (rewrite (AGm 21%bv) by (apply NIm; in_l); exact A21).
    assert (T22 : getr r' 22 = Z_to_bv 64 65535) by (rewrite (AGm 22%bv) by (apply NIm; in_l); exact A22).
    assert (T23 : getr r' 23 = Z_to_bv 64 (NIDS + 1)) by (rewrite (AGm 23%bv) by (apply NIm; in_l); exact A23).
    (* [comment removed for export] *)
    destruct (put_n1_post MBr (seg_rom BSEGS) sp MUW h a bW (dp_tab d b) NIDS r'
                B2 ltac:(rewrite B8; exact A8) ltac:(rewrite B9, A9, UMU; reflexivity) B10 ltac:(rewrite B19; exact A19) T21 T22 T23
                ltac:(clear - Hspr SPC CR HKD SPHI; lia) ltac:(rewrite UMU; clear; lia) ltac:(clear - NN0 NROOM; lia) ltac:(rewrite UMU; clear - GA; lia) ltac:(clear - GC SPC HKD; lia)
                SOKs SOKl SOKn HstkQ SLQ)
      as (r2 & M1r & RUN2 & S2 & AT & Kslot & Kmu & AG2).
    fold ndW in S2, AT.
    set (W2 := n1post_W sp MUW ndW idx) in *.
    assert (CLS2 : forall z, W2 z -> (U sp - 144 <= z < U sp - 112) \/ (0x1f0098 + 4194320 + 8 * idx <= z < 0x1f0098 + 4194320 + 8 * idx + 8)
                                    \/ (0x1f0098 + 4194312 <= z < 0x1f0098 + 4194312 + 1) \/ (U ndW <= z < U ndW + 8)).
    { intros z Hz. unfold W2, n1post_W, wun, ivl in Hz. rewrite UMU in Hz. clear - Hz. lia. }
    assert (NHW2 : forall x : word, W2 (U x) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. destruct (CLS2 _ Hx) as [C|[C|[C|C]]].
      - apply NHw. left. clear - C SPC HKD. lia.
      - apply NHw. right. clear - C I16. lia.
      - apply NHw. right. clear - C. lia.
      - rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHa. rewrite Und in C. clear - C M16. lia. }
    (* [comment removed for export] *)
    apply (katD_msteps_acct BSEGS Hd HOFF asanF_segs_wx (a_aa st)
             (@mkst fx r' (Z_to_bv 64 0x8fdb8) MB (seg_rom BSEGS)) (@mkst fx r2 (Z_to_bv 64 0x8cef4) M1r (seg_rom BSEGS)) mdl4).
    { rewrite L3. apply lazy_cover_HID. } { exact Bw1. } { exact MI4. } { exact HL4. }
    { rewrite restrict_mkst9. fold MBr. replace (Z_to_bv 64 0x8fdb8) with (0x8fdb8%bv : word) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x8cef4) with (0x8cef4%bv : word) by (apply bv_eq; reflexivity). exact RUN2. }
    intros mdl5 MI5 SBM5 HC5. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx r' (Z_to_bv 64 0x8fdb8) MB (seg_rom BSEGS))) with MB by reflexivity.
    set (MS := munrestrict Hd MB M1r).
    pose proof (msum_unrestrict Hd W2 MB M1r NHW2 S2) as [FR2 GR2]. fold MS in FR2, GR2.
    pose proof (mrestrict_clean_mem Hd MB r2 (Z_to_bv 64 0x8cef4) M1r (seg_rom BSEGS) HC5) as EMS. fold MS in EMS.
    pose proof (same_but_materialized_frame mdl4 mdl5 SBM5) as (_ & Evm5 & Elz5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl5 & _ & _ & _ & Eeg5).
    set (W0 := wun W1 (wun WB W2)).
    assert (S0 : msum W0 M MS) by (exact (msum_trans _ _ _ _ _ (conj FR1 GR1) (msum_trans _ _ _ _ _ (conj FRB GRB) (conj FR2 GR2)))).
    assert (CLS0 : forall z, W0 z -> cls0 (U sp) b idx (U ndW) (Some (U a)) z).
    { intros z [Hz | [Hz | Hz]]; (lazymatch goal with |- ?G => let G' := eval unfold cls0 in G in change_no_check G' end).
      - destruct (CLS1 _ Hz) as [C|[C|[C|C]]]; [left; clear - C; lia | right; left; exact C | do 2 right; left; exact C | do 3 right; left; exact C].
      - unfold WB, wun, ivl in Hz. destruct Hz as [Hz | Hz]; [left; clear - Hz; lia | do 5 right; left; exists (U a); split; [reflexivity | exact Hz]].
      - destruct (CLS2 _ Hz) as [C|[C|[C|C]]]; [left; clear - C; lia | do 4 right; left; split; [discriminate | exact C] | do 3 right; left; clear - C; lia | do 6 right; clear - C; lia]. }
    (* [comment removed for export] *)
    assert (THRU2 : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 ->
              (forall i, U x <= i < U x + Z.of_nat n -> ((CEIL <= i \/ (AIMGLO <= i /\ i < AIMGHI)) /\ ~ WB i) /\ ~ W2 i) -> rdn BSEGS Mtr x n = Some v -> rdn BSEGS M1r x n = Some v).
    { intros x n v B0 F Hr. apply (msum_rdn_eq BSEGS _ MBr M1r x n v S2 B0); [intros z Hz; exact (proj2 (F z Hz))|].
      apply TB; [exact B0 | intros i Hi; exact (proj1 (F i Hi)) | exact Hr]. }
    assert (STK2 : forall i, U sp - 112 <= i -> ((CEIL <= i \/ (AIMGLO <= i /\ i < AIMGHI)) /\ ~ WB i) /\ ~ W2 i).
    { intros i Hi. split; [apply STKB; clear - Hi; lia|]. intros WZ. destruct (CLS2 _ WZ) as [C|[C|[C|C]]]; [clear - C Hi; lia | clear - C Hi I16 Hspr SPC CR HKD; lia | clear - C Hi Hspr SPC CR HKD; lia
                                                                                                         | rewrite Und in C; clear - C Hi M16 GC SPC HKD; lia]. }
    assert (NNR : 0 <= U a /\ U a + 2 ^ 20 < 2 ^ 64) by (clear - Har GC CR; lia).
    apply (sgrow_main bt FXOK BT_segs BT_ia DCELLS DCELLS2 DOBL DEPOT_FRAMES_ROOM DEP0 BOOTG GRANT_NR_EX KD HKD fx X st Lc FF M M0 MS mdl mdl5 R r2 sp buf ret ndW sz tag ws h0 (Some (U a)) W0
             HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD SG).
    - fold d NIDS. split; [intros E; discriminate E | intros E; exfalso]. fold idx in E. rewrite EIDX in E. unfold node_blocks in E. cbn [length] in E. rewrite Nat2Z.inj_succ in E. clear - E. lia.
    - intros _. fold d NIDS. fold idx. rewrite EIDX. (lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). rewrite Nat2Z.inj_succ. clear. lia.
    - intros p E. injection E as <-. exact (conj DY (conj AL AP)).
    - intros p b0 n0 E Hin. injection E as <-.
      exact (grant_apart_maps0 bt st Lc FF M0 mdl mdlm (2 ^ 20) (2 ^ 28) (Z_to_bv 64 0) a (2 ^ 20) W RP EVm ltac:(clear; lia) eq_refl G b0 n0 Hin).
    - intros p z E Hz. injection E as <-. split; [exact (NHa z Hz)|]. split; [intros Xz; exact (px_off_fresh bt st Lc FF X (U a) (2 ^ 20) z W PXH Xz AP DY Hz)|].
      apply GR2. apply DEFA. rewrite u_Z2bv by (clear - Hz NNR; lia). exact Hz.
    - fold d NIDS idx. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt] in G in change_no_check G' end). rewrite EIDX, Nat2Z.id. rewrite app_nth2 by apply Nat.le_refl. rewrite Nat.sub_diag. exact Und.
    - exists (U a). split; [right; reflexivity|]. rewrite Und. clear - M16. lia.
    - exact I16.
    - (lazymatch goal with |- ?G => let G' := eval unfold W0, W1, WB, W2, n1post_W, n1pre_W in G in change_no_check G' end). repeat apply wun_dec; apply ivl_dec.
    - exact S0.
    - exact CLS0.
    - fold Hd; rewrite EMS. exact AT.
    - fold Hd; rewrite EMS. apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros i Hi; rewrite at_u in Hi by lia; apply STK2; clear - Hi; lia | exact Atr].
    - fold Hd; rewrite EMS. apply THRU2; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; rewrite at_at, at_u in Hi by lia; apply STK2; clear - Hi; lia | exact Asz].
    - fold Hd; rewrite EMS. apply THRU2; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; rewrite at_at, at_u in Hi by lia; apply STK2; clear - Hi; lia | exact Atag].
    - fold Hd; rewrite EMS. intros k v Hin. assert (K : -88 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin).
      apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros i Hi; rewrite at_u in Hi by lia; apply STK2; clear - Hi K; lia | exact (SLs k v Hin)].
    - fold Hd; rewrite EMS. apply THRU2; [rewrite u_Z2bv by (clear; lia); change (Z.of_nat 4) with 4; clear; lia | | exact Kn1].
      intros i Hi. rewrite u_Z2bv in Hi by (clear; lia). change (Z.of_nat 4) with 4 in Hi. split; [apply IMB; clear - Hi; lia|].
      intros WZ. destruct (CLS2 _ WZ) as [C|[C|[C|C]]]; [clear - C Hi Hspr SPC CR HKD; lia | clear - C Hi I16; lia | clear - C Hi; lia | rewrite Und in C; clear - C Hi GA M16; lia].
    - fold Hd; rewrite EMS. exact Kmu.
    - fold Hd; rewrite EMS. intros p E. injection E as <-. rewrite Z_to_bv_bv_unsigned. rewrite <- Kslot. f_equal; try ((lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end); rewrite UMU; f_equal; clear; lia).
    - intros k N1 N2. rewrite (AG2 _ N1). rewrite (AGm _ (fun Hm => N1 (mo_clob_put _ Hm))). rewrite (AG1 _ N1). exact (AGp _ N2).
    - (lazymatch goal with |- ?G => let G' := eval unfold ledN, nnpart in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map app length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end). rewrite Evm5, Elz5, Eeg5, Ehl5, Z_to_bv_bv_unsigned.
      split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|]. split; [exact L9|].
      split; [rewrite Usz in L10; clear - L10; lia|]. split; [exact (model_ivs_wf_sbm mdl4 mdl5 SBM5 L11)|]. split; [exact HL4|].
      apply (same_except_vm_trans mdl mdlm mdl5); [exact (same_but_materialized_except_vm mdl mdlm SBM0m)|].
      apply (same_except_vm_trans mdlm (mmap_model a szW mdlm) mdl5); [apply sev_mmap_model|].
      apply (same_except_vm_trans _ mdl4 mdl5); [exact (same_but_materialized_except_vm _ _ SBM4) | exact (same_but_materialized_except_vm _ _ SBM5)].
    - exact MI5.
  Qed.
End TOPS4.
