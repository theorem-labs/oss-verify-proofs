(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotRunP OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.AsDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsDepotMod OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMTopSa.AsDepotModK OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotRunF OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotRunN OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotRunN2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotHyp9w OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotAlloc OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotBlk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsDepotMnr OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1.AsDepotMnrK OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3.AsDepotRunC1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3.AsDepotRunC2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunC3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotRunI.AsDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
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
  tclr DY; tclr E1; tclr E2; tclr EIDX; tclr STDQ; tclr NROOM; tclr LEAG;
  tclr DM1; tclr DM2; tclr MB1; tclr MB2; tclr EQS; tclr EQM; tclr MNZ; tclr EM1; tclr LEN; tclr NEq; tclr EQq; tclr Q12; tclr Hq1; tclr QSL; tclr TZ0.
#[local] Ltac am_inner ::= first [ solve [wm_bl; wm_clear_disj; wm_lia0] | solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Definition cls0 (sp b idx ndz : Z) (nn : option Z) (z : Z) : Prop :=
  (sp - 464 <= z < sp) \/ (0x1e9458 + 4 * b <= z < 0x1e9458 + 4 * b + 4) \/ (0x1e9458 + 4194304 <= z < 0x1e9458 + 4194304 + 4)
  \/ (0x1e9458 + 4194312 <= z < 0x1e9458 + 4194312 + 4) \/ (nn <> None /\ 0x1e9458 + 4194320 + 8 * idx <= z < 0x1e9458 + 4194320 + 8 * idx + 8)
  \/ (exists p, nn = Some p /\ p <= z < p + 2 ^ 20) \/ (ndz <= z < ndz + 16).

Lemma cls0_02 : forall sp b idx ndz qs nn z, cls0 sp b idx ndz nn z -> cls02 sp b idx ndz qs nn z.
Proof.
  intros sp b idx ndz qs nn z [C|[C|[C|[C|[C|[C|C]]]]]]; (lazymatch goal with |- ?G => let G' := eval unfold cls02 in G in change_no_check G' end);
    [left; lia | right; left; exact C | do 2 right; left; exact C | do 3 right; left; exact C | do 4 right; left; exact C | do 5 right; left; exact C | do 6 right; left; exact C].
Qed.

(* [comment removed for export] *)
Definition sgrow (st : ast) (sz : Z) : Prop :=
  let tot := dp_frames (a_dep st) in ~ (tot / 2 ^ 20 = (tot + sz) / 2 ^ 20 /\ (tot mod 2 ^ 20 <> 0 \/ tot = 0)).

Section TOPS2.
  Context {RC : run_ceil}.
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
  (* [comment removed for export] *)
  Hypothesis GRANT_NR_EX : forall st Lc FF M0 mdl mdlm (nn : option Z), WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> a_kact st <= KCAP ->
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) -> vm_maps (m_vmmaps mdlm) = nnpart nn ++ vm_maps (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdlm) = vm_init_sp (m_vmmaps mdl) ->
    exists a : word, grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true.

  Lemma sgrow_main : forall KD, 576 <= KD ->
    forall fx (X : Z -> Prop) st Lc FF (M M0 MS : mem) mdl mdlS (R rS : bvmap 5 word) (sp buf ret ndW : word)
           (sz tag : Z) (ws : list word) (h0 nn : option Z) (W0 : Z -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> holes_le h0 st ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok ASEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      sgrow st sz ->
      let Hd := HID st mdl in let h := sd_hashN ws tag in
      let d := a_dep st in let b := sd_bix h in let NIDS := dp_nids d in let idx := (NIDS + 1) / 2 ^ 16 in
      let MUW : word := Z_to_bv 64 (0x1e9458 + 4194312) in let bW : word := Z_to_bv 64 (0x1e9458 + 4 * b) in
      let MSr := mrestrict Hd MS in
      (* [comment removed for export] *)
      (nn = None <-> (NIDS + 1) / 2 ^ 16 = Z.of_nat (length (dp_nodeblocks d))) ->
      (nn <> None -> idx = Z.of_nat (length (dp_nodeblocks d)) + 1) ->
      (forall p, nn = Some p -> dyn_ok (bt_ia bt) p (p + 2 ^ 20) /\ p mod PG = 0 /\ forall lo hi, In (lo, hi) (all_ranges bt st) -> p + 2 ^ 20 <= lo \/ hi <= p) ->
      (forall p b0 n0, nn = Some p -> In (b0, n0) (bt_maps0 bt) -> p + 2 ^ 20 <= U b0 \/ U b0 + U n0 <= p) ->
      (forall p z, nn = Some p -> p <= z < p + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false /\ ~ X z /\ MS (Z_to_bv 64 z) <> None) ->
      U ndW = nth (Z.to_nat idx) (node_blocks bt d ++ blk_opt nn) 0 + 16 * ((NIDS + 1) mod 2 ^ 16) ->
      (exists nb, (In nb (node_blocks bt d) \/ nn = Some nb) /\ nb <= U ndW /\ U ndW + 16 <= nb + 2 ^ 20) ->
      0 <= idx < 2 ^ 15 ->
      (* [comment removed for export] *)
      Wdec W0 -> msum W0 M MS -> (forall z, W0 z -> cls0 (U sp) b idx (U ndW) nn z) ->
      at_store sp ndW bW h (dp_tab d b) (NIDS + 1) rS MSr ->
      rdn ASEGS MSr (at_ sp (-104)) 8 = Some (LE8 buf) -> rdn ASEGS MSr (at_ (at_ sp (-104)) 8) 4 = Some (LE4 (Z_to_bv 64 sz)) ->
      rdn ASEGS MSr (at_ (at_ sp (-104)) 12) 4 = Some (LE4 (Z_to_bv 64 tag)) ->
      (forall (k : Z) (v : word),
          In (k, v) [(-8, ret); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20);
                     (-56, getr R 21); (-64, getr R 22); (-72, getr R 23); (-80, getr R 24); (-88, getr R 25)]%Z ->
          rdn ASEGS MSr (at_ sp k) 8 = Some (LE8 v)) ->
      rdn ASEGS MSr (Z_to_bv 64 (0x1e9458 + 4194304)) 4 = Some (LE4 (Z_to_bv 64 (NIDS + 1))) ->
      rdn ASEGS MSr MUW 1 = Some [Z_to_bv 8 0] ->
      (forall p, nn = Some p -> rdn ASEGS MSr (Z_to_bv 64 (0x1e9458 + 4194320 + 8 * idx)) 8 = Some (LE8 (Z_to_bv 64 p))) ->
      (forall k, ~ In (Z_to_bv 5 k) put_clob -> ~ In (Z_to_bv 5 k) sd_clobx -> getr rS (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)) ->
      ledN mdl mdlS nn -> MInv (a_aa st) mdlS ->
      katD ASEGS (mkCfg (@mkst fx rS (Z_to_bv 64 0x8c484) MS (seg_rom ASEGS)) mdlS)
           (depot_post_w bt FXOK KD X st Lc FF M mdl R sp ret).
  Proof using GRANT_NR_EX BOOTG DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS2 DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 MS mdl mdlS R rS sp buf ret ndW sz tag ws h0 nn W0
           HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD SG
           Hd h d b NIDS idx MUW bW MSr NNW NNI NNF NNM0 NNV ND NDB I16 WD0 [FR0 GR0] CLS0 AT Atr Asz Atag SLs Kn0 Kmu0 Kslot0 AG0 LEDS MIS.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr. pose proof (u64_range ndW) as Hndr.
    unfold sgrow in SG. cbv zeta in SG. fold d in SG. set (tot := dp_frames d) in *. set (q := tot / 2 ^ 20) in *. set (cnt := sz + 1).
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (UMU : U MUW = 0x1e9458 + 4194312) by reflexivity.
    assert (UbW : U bW = 0x1e9458 + 4 * b) by ((lazymatch goal with |- ?G => let G' := eval unfold bW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (USS : U SSW = 1938504) by reflexivity.
    set (spS := at_ (at_ sp (-112)) (-32)). set (spA := at_ spS (-64)). set (spB := at_ spA (-16)). set (spMn := at_ spB (-32)).
    set (packp := at_ (at_ sp (-112)) (-24)). set (args := at_ sp (-104)). set (szW := Z_to_bv 64 8388608 : word).
    assert (UspS : U spS = U sp - 144) by ((lazymatch goal with |- ?G => let G' := eval unfold spS in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    assert (UspA : U spA = U sp - 208) by ((lazymatch goal with |- ?G => let G' := eval unfold spA in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspB : U spB = U sp - 224) by ((lazymatch goal with |- ?G => let G' := eval unfold spB in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspMn : U spMn = U sp - 256) by ((lazymatch goal with |- ?G => let G' := eval unfold spMn in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Upk : U packp = U sp - 136) by ((lazymatch goal with |- ?G => let G' := eval unfold packp in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    assert (Usz : U szW = 2 ^ 23) by reflexivity.
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12. fold tot in D7, D9, D10. fold NIDS in D1, D2, D3, D4, D5, D6.
    pose proof (DEPOT_FRAMES_ROOM st Lc FF W ROOM KC) as FROOM. fold d tot in FROOM. unfold FRW in FROOM.
    assert (Q20 : 0 <= q < 2 ^ 12) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in R1.
    destruct R14 as (Bw1 & Bw2 & _ & _ & _ & _ & Bw7 & _).
    destruct R9 as (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw).
    assert (ESS : SSOBJ bt = 1938504) by ((lazymatch goal with |- ?G => let G' := eval unfold SSOBJ in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). hs_lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros x NX. destruct (decide (M x = M0 x)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF x NE))). }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i).
    { intros i Hi Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). hs_lia. }
    pose proof (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) as HOFF.
    destruct NDB as (nb & NBc & NB1 & NB2).
    assert (NBA : AIMGHI <= nb).
    { destruct NBc as [INB | ENN].
      - destruct (node_blocks_dyn bt st Lc FF W nb INB) as ((GB0 & _ & _ & GB3 & _) & _). rewrite BT_ia in GB3. cbn [ia_img_lo ia_img_hi asan_addrs] in GB3. clear - GB0 GB3. lia.
      - destruct (NNF nb ENN) as ((Y1 & _ & _ & Y4 & _) & _). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi asan_addrs] in Y4. clear - Y1 Y4. lia. }
    (* [comment removed for export] *)
    assert (OUT0 : forall i, AIMGLO <= i < 0x1e9458 -> ~ W0 i).
    { intros i Hi WZ. destruct (CLS0 _ WZ) as [C|[C|[C|[C|[[_ C]|[(p & Ep & C)|C]]]]]].
      - clear - C Hi SPC CR HKD. lia.
      - clear - C Hi Hbix. lia.
      - clear - C Hi. lia.
      - clear - C Hi. lia.
      - clear - C Hi I16. lia.
      - destruct (NNF p Ep) as ((Y1 & _ & _ & Y4 & _) & _). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi asan_addrs] in Y4. clear - C Hi Y1 Y4. lia.
      - clear - C Hi NB1 NBA. lia. }
    assert (IMGS : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= 0x1e9458 -> cellZ ASEGS M0 z k v ->
              rdn ASEGS MSr (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk C. unfold cellZ, cellN in C. refine (eq_trans _ C). apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold MSr in G in change_no_check G' end). rewrite (mrestrict_off Hd MS x (NHw x ltac:(right; lia))).
      rewrite (FR0 x (OUT0 (U x) ltac:(lia))). apply EQ0. apply XI. lia. }
    assert (DEFS : forall x : word, M x <> None -> Hd x = false -> MSr x <> None).
    { intros x Dx Hx. (lazymatch goal with |- ?G => let G' := eval unfold MSr in G in change_no_check G' end). rewrite (mrestrict_off Hd MS x Hx). apply GR0. exact Dx. }
    assert (SSOK : forall (x : word) (n : nat), 0x1d9448 <= U x -> U x + Z.of_nat n <= 0x1d9448 + 65552 -> store_ok ASEGS MSr x n = true).
    { intros x n H1 H2. exact (ss_store_ok MSr x n H1 H2). }
    assert (Hstk : store_ok ASEGS MSr (at_ sp (-256)) 112 = true).
    { apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply store_ok1_some.
      apply DEFS; [apply STK; lia | apply NHw; left; lia]. }
    assert (SOKp : store_ok ASEGS MSr packp 8 = true).
    { apply store_ok_bytes; [| rewrite Upk; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. intros x Hx. rewrite Upk in Hx. cbn in Hx. apply store_ok1_some.
      apply DEFS; [apply STK; lia | apply NHw; left; lia]. }
    pose proof Dfr as Ct. rewrite ESS, BT_segs in Ct. fold d tot in Ct.
    assert (Rtot : rdn ASEGS MSr SSW 8 = Some (LE8 (Z_to_bv 64 tot))) by (apply IMGS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ct]).
    (* [comment removed for export] *)
    destruct (rwseg_rdn ASEGS _ (Z_to_bv 64 0x1d9448) MSr (at_ SSW 8) 8 ss_img_ok) as (abs & Rab & Lab);
      [rewrite ss_len; change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448; lia | change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448; rewrite at_u by (rewrite USS; lia); rewrite USS; lia
       | rewrite ss_len; change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448; rewrite at_u by (rewrite USS; lia); rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
    set (alv := Z_to_bv 64 (bytes_le_to_Z abs) : word).
    assert (Ralloc : rdn ASEGS MSr (at_ SSW 8) 8 = Some (LE8 alv)) by ((lazymatch goal with |- ?G => let G' := eval unfold alv in G in change_no_check G' end); rewrite (le8_word2 abs Lab); exact Rab).
    (* [comment removed for export] *)
    assert (LOCKW : forall i, 0 <= i < 2 ^ 12 -> exists b1 b2 b3, rdn ASEGS MSr (Z_to_bv 64 (1938504 + 28 + 16 * i)) 4 = Some [Z_to_bv 8 0; b1; b2; b3]).
    { intros i Hi. destruct (Dblk i Hi) as (_ & _ & Cmu). rewrite ESS, BT_segs in Cmu.
      assert (R1b : rdn ASEGS MSr (Z_to_bv 64 (1938504 + 28 + 16 * i)) 1 = Some [Z_to_bv 8 0]).
      { change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))). apply IMGS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cmu]. }
      destruct (rwseg_rdn ASEGS _ (Z_to_bv 64 0x1d9448) MSr (Z_to_bv 64 (1938504 + 28 + 16 * i)) 4 ss_img_ok) as (lbs & Rl4 & _);
        [rewrite ss_len; change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448; lia | change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]
         | rewrite ss_len; change (U (Z_to_bv 64 0x1d9448)) with 0x1d9448; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      destruct (rdn4_head ASEGS MSr _ lbs _ Rl4 R1b) as (b1 & b2 & b3 & ->). exists b1, b2, b3. exact Rl4. }
    assert (STORED : forall i, 0 <= i < 2 ^ 12 -> rdn ASEGS MSr (Z_to_bv 64 (1938504 + 24 + 16 * i)) 4 = Some (LE4 (Z_to_bv 64 (dp_stored d i)))).
    { intros i Hi. destruct (Dblk i Hi) as (_ & Cso & _). rewrite ESS, BT_segs in Cso. apply IMGS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cso]. }
    assert (PTR0 : forall i, 0 <= i < 2 ^ 12 -> Z.of_nat (length (store_blocks bt d)) <= i -> rdn ASEGS MSr (Z_to_bv 64 (1938504 + 16 + 16 * i)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { intros i Hi Hl. destruct (Dblk i Hi) as (Cbd & _ & _). rewrite ESS, BT_segs in Cbd. rewrite (nth_overflow (store_blocks bt d) 0) in Cbd by lia.
      apply IMGS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cbd]. }
    destruct AT as (AT1 & AT2 & AT8 & AT10 & AT11 & AT12 & AT9 & AT18 & AT21 & AT23 & Rhsh & Rq8 & Rq16).
    pose proof (conj AT1 (conj AT2 (conj AT8 (conj AT10 (conj AT11 (conj AT12 (conj AT9 (conj AT18 (conj AT21 (conj AT23 (conj Rhsh (conj Rq8 Rq16)))))))))))) as ATS.
    pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as DM1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as MB1. fold q in DM1.
    pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as DM2. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as MB2.
    (* [comment removed for export] *)
    assert (PRE : exists (r5 : bvmap 5 word) (MPr : mem) (start pk so : Z) (std' : Z -> Z) (Wp : Z -> Prop),
       let qs := start / 2 ^ 20 in let BI : word := Z_to_bv 64 (U SSW + 16 * qs + 16) in
       msteps ASEGS (@mkst fx rS (0x8c484%bv : word) MSr (seg_rom ASEGS)) (@mkst fx r5 (0x82340%bv : word) MPr (seg_rom ASEGS))
       /\ msum Wp MSr MPr /\ inhabited (Wdec Wp)
       /\ (forall z, Wp z -> (U sp - 256 <= z < U sp - 128) \/ (1938504 <= z < 1938504 + 16) \/ (1938504 + 16 * qs + 16 <= z < 1938504 + 16 * qs + 32)
                            \/ (1938504 + 16 * (qs - 1) + 24 <= z < 1938504 + 16 * (qs - 1) + 28))
       /\ (0 <= start /\ start + sz + 1 <= 2 ^ 32) /\ start mod 2 ^ 20 + sz < 2 ^ 20 /\ qs = Z.of_nat (length (store_blocks bt d))
       /\ tot <= start + cnt /\ start + cnt <= tot + FRW + FRW
       /\ Z.of_nat (length (dp_storeblocks d)) + 1 = Z.min (Z.max 0 ((start + cnt - 1) / 2 ^ 20)) (2 ^ 12 - 1)
       /\ 0 <= so < 2 ^ 32 /\ (0 <= pk /\ pk + 1 < 2 ^ 32) /\ (forall i, 0 <= std' i < 2 ^ 32) /\ std' qs = (so + cnt) mod 2 ^ 32
       /\ getr r5 1 = (0x8d000%bv : word) /\ getr r5 2 = spMn /\ getr r5 10 = Z_to_bv 64 8388608 /\ getr r5 11 = Z_to_bv 64 0x21f70
       /\ getr r5 8 = at_ BI 12 /\ getr r5 9 = BI /\ getr r5 19 = args /\ getr r5 20 = Z_to_bv 64 sz /\ getr r5 21 = Z_to_bv 64 tag /\ getr r5 23 = Z_to_bv 64 (NIDS + 1)
       /\ regs_agree (fun i : reg => In i put_clob) rS r5
       /\ (forall (k : Z) (v : word), In (k, v) [(-8, (0x8c6bc%bv : word)); (-16, Z_to_bv 64 start); (-24, SSW); (-32, Z_to_bv 64 cnt)]%Z -> rdn ASEGS MPr (at_ spB k) 8 = Some (LE8 v))
       /\ rdn ASEGS MPr (at_ spA (-8)) 8 = Some (LE8 (0x8c4fc%bv : word)) /\ rdn ASEGS MPr (at_ spA (-16)) 8 = Some (LE8 packp)
       /\ (forall (k : Z) (v : word), In (k, v) [(-8, (0x8e7c4%bv : word)); (-16, ndW); (-24, ndW); (-32, bW); (-40, getr rS 19); (-48, getr rS 20); (-56, Z_to_bv 64 (dp_tab d b))]%Z ->
              rdn ASEGS MPr (at_ spS k) 8 = Some (LE8 v))
       /\ rdn ASEGS MPr spA 8 = Some (LE8 (Z_to_bv 64 start))
       /\ rdn ASEGS MPr packp 8 = Some (LE8 (Z_to_bv 64 pk))
       /\ rdn ASEGS MPr (st_cell SSW start) 4 = Some (LE4 (Z_to_bv 64 so))
       /\ rdn ASEGS MPr SSW 8 = Some (LE8 (Z_to_bv 64 (start + cnt)))
       /\ (forall i, 0 <= i < 2 ^ 12 -> i <> qs -> rdn ASEGS MPr (Z_to_bv 64 (1938504 + 24 + 16 * i)) 4 = Some (LE4 (Z_to_bv 64 (std' i))))).
    { destruct (Z.eq_dec (tot / 2 ^ 20) ((tot + sz) / 2 ^ 20)) as [EQq | NEq].
      - (* [comment removed for export] *)
        fold q in EQq.
        assert (TZ : tot mod 2 ^ 20 = 0 /\ tot <> 0) by (destruct (Z.eq_dec (tot mod 2 ^ 20) 0) as [Z0|NZ]; [destruct (Z.eq_dec tot 0) as [T0|TN]; [exfalso; apply SG; split; [exact EQq | right; exact T0] | split; assumption]
                                                         | exfalso; apply SG; split; [exact EQq | left; exact NZ]]).
        destruct TZ as [TZ0 TNZ].
        assert (Q1 : 1 <= q) by (clear - DM1 TZ0 TNZ D7; lia).
        assert (EM1 : (tot - 1) / 2 ^ 20 = q - 1) by (symmetry; apply (Z.div_unique (tot - 1) (2 ^ 20) (q - 1) (2 ^ 20 - 1)); clear - DM1 TZ0; lia).
        assert (LEN : Z.of_nat (length (dp_storeblocks d)) = q - 1) by (rewrite D10, EM1; clear - Q1 Q20; lia).
        assert (QSL : q = Z.of_nat (length (store_blocks bt d))) by ((lazymatch goal with |- ?G => let G' := eval unfold store_blocks in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite Nat2Z.inj_succ; clear - LEN; lia).
        destruct (LOCKW q Q20) as (b1 & b2 & b3 & Rl4).
        set (lkw := Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]) : word).
        assert (V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw).
        { (lazymatch goal with |- ?G => let G' := eval unfold lkw in G in change_no_check G' end). pose proof (bytes_le_to_Z_nonneg [Z_to_bv 8 0; b1; b2; b3]) as X1. pose proof (bytes_le_to_Z_bound [Z_to_bv 8 0; b1; b2; b3]) as X2.
          cbn [length] in X2. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in X2. rewrite u_Z2bv by lia. reflexivity. }
        set (BIq := Z_to_bv 64 (U SSW + 16 * q + 16) : word).
        assert (UBIq : U BIq = 1938504 + 16 * q + 16) by ((lazymatch goal with |- ?G => let G' := eval unfold BIq in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
        assert (EBL : at_ BIq 12 = Z_to_bv 64 (1938504 + 28 + 16 * q)) by (apply bv_eq; rewrite at_u by (rewrite UBIq; lia); rewrite UBIq, u_Z2bv by lia; lia).
        assert (EBI : BIq = Z_to_bv 64 (1938504 + 16 + 16 * q)) by ((lazymatch goal with |- ?G => let G' := eval unfold BIq in G in change_no_check G' end); rewrite USS; f_equal; lia).
        set (so := dp_stored d q). set (std' := fupdZ (dp_stored d) q ((so + cnt) mod 2 ^ 32)).
        destruct (store_c_pre_same MSr (seg_rom ASEGS) sp ndW bW h alv lkw b1 b2 b3 (dp_tab d b) (NIDS + 1) sz tag tot rS ATS
                    ltac:(clear - Hspr SPC CR HKD SPHI; lia) ltac:(clear - SZ; lia) Htag ltac:(clear - D7 FROOM SZ; lia) EQq Asz Atag Rtot
                    ltac:(fold q BIq; rewrite EBI; apply PTR0; [exact Q20 | rewrite <- QSL; apply Z.le_refl])
                    ltac:(fold q BIq; rewrite EBL; exact Rl4) V_lock Ralloc Hstk SOKp
                    ltac:(apply SSOK; [rewrite USS; clear; lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia])
                    ltac:(fold q BIq; rewrite EBL; apply SSOK; [rewrite u_Z2bv by lia; clear - Q20; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia])
                    ltac:(apply SSOK; [rewrite at_u by (rewrite USS; clear; lia); rewrite USS; clear; lia | rewrite at_u by (rewrite USS; clear; lia); rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]))
          as (r5 & MP & RUN & SUM & G1 & G2 & G10 & G11 & G8 & G9 & G19 & G20 & G21 & G23 & SLbi & Rara & Ras0 & SLst & Ridx & Rpk & Rtot' & AG).
        exists r5, MP, tot, 0, so, std', (cpre_W sp q). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold q.
        assert (THRU : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 -> (forall z, U x <= z < U x + Z.of_nat n -> ~ cpre_W sp q z) ->
                  rdn ASEGS MSr x n = Some v -> rdn ASEGS MP x n = Some v).
        { intros x n v B0 F Hr. exact (msum_rdn_eq ASEGS _ MSr MP x n v SUM B0 F Hr). }
        split; [exact RUN|]. split; [exact SUM|]. split; [constructor; (lazymatch goal with |- ?G => let G' := eval unfold cpre_W in G in change_no_check G' end); repeat apply wun_dec; apply ivl_dec|].
        split; [intros z Hz; unfold cpre_W, wun, ivl in Hz; clear - Hz; lia|].
        split; [clear - D7 FROOM SZ; lia|]. split; [rewrite TZ0; clear - SZ; lia|]. split; [exact QSL|].
        split; [(lazymatch goal with |- ?G => let G' := eval unfold cnt in G in change_no_check G' end); clear - SZ; lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold cnt, FRW in G in change_no_check G' end); clear - SZ; lia|].
        split; [rewrite LEN; replace (tot + cnt - 1) with (tot + sz) by ((lazymatch goal with |- ?G => let G' := eval unfold cnt in G in change_no_check G' end); clear; lia); rewrite <- EQq; clear - Q1 Q20; lia|].
        split; [exact (D11 q)|]. split; [clear; lia|].
        split; [intros i; (lazymatch goal with |- ?G => let G' := eval unfold std', fupdZ in G in change_no_check G' end); destruct (i =? q); [apply Z.mod_pos_bound; clear; lia | exact (D11 i)]|].
        split; [(lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end); rewrite fupdZ_same; reflexivity|].
        split; [exact G1|]. split; [exact G2|]. split; [exact G10|]. split; [exact G11|]. split; [exact G8|]. split; [exact G9|].
        split; [exact G19|]. split; [exact G20|]. split; [exact G21|]. split; [exact G23|]. split; [exact AG|].
        split; [exact SLbi|]. split; [exact Rara|]. split; [exact Ras0|].
        split; [exact SLst|].
        split; [exact Ridx|]. split; [exact Rpk|].
        split.
        { (lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end). rewrite USS. fold q. replace (1938504 + 16 * q + 24) with (1938504 + 24 + 16 * q) by (clear; lia).
          apply THRU; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia | | exact (STORED q Q20)].
          intros z Hz. rewrite u_Z2bv in Hz by lia. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold cpre_W, wun, ivl in G in change_no_check G' end). clear - Hz Q20 Hspr SPC CR HKD. lia. }
        split; [exact Rtot'|].
        intros i Hi NE. (lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end). rewrite fupdZ_other by exact NE.
        apply THRU; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hi; lia | | exact (STORED i Hi)].
        intros z Hz. rewrite u_Z2bv in Hz by lia. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold cpre_W, wun, ivl in G in change_no_check G' end). clear - Hz Hi NE Q20 Hspr SPC CR HKD. lia.
      - (* [comment removed for export] *)
        fold q in NEq.
        assert (Hq1 : (tot + sz) / 2 ^ 20 = q + 1).
        { assert (L1 : q <= (tot + sz) / 2 ^ 20) by (apply Z.div_le_mono; clear - SZ; lia).
          assert (L2 : (tot + sz) / 2 ^ 20 < q + 2) by (apply Z.div_lt_upper_bound; [clear; lia | clear - DM1 MB1 SZ; lia]).
          clear - L1 L2 NEq. lia. }
        assert (MNZ : 2 ^ 20 <= tot mod 2 ^ 20 + sz) by (rewrite Hq1 in DM2; clear - DM1 DM2 MB2; lia).
        assert (EM1 : (tot - 1) / 2 ^ 20 = q) by (symmetry; apply (Z.div_unique (tot - 1) (2 ^ 20) q (tot mod 2 ^ 20 - 1)); clear - DM1 MB1 MNZ SZ; lia).
        assert (Q12 : q + 1 < 2 ^ 12).
        { assert ((tot + sz) / 2 ^ 20 < 2 ^ 12) by (apply Z.div_lt_upper_bound; [clear; lia | clear - FROOM SZ; lia]). rewrite Hq1 in H. exact H. }
        assert (LEN : Z.of_nat (length (dp_storeblocks d)) = q) by (rewrite D10, EM1; clear - Q20 Q12; lia).
        assert (QSL : q + 1 = Z.of_nat (length (store_blocks bt d))) by ((lazymatch goal with |- ?G => let G' := eval unfold store_blocks in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite Nat2Z.inj_succ; clear - LEN; lia).
        assert (Q120 : 0 <= q + 1 < 2 ^ 12) by (clear - Q20 Q12; lia).
        destruct (LOCKW (q + 1) Q120) as (b1 & b2 & b3 & Rl4).
        set (lkw := Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]) : word).
        assert (V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw).
        { (lazymatch goal with |- ?G => let G' := eval unfold lkw in G in change_no_check G' end). pose proof (bytes_le_to_Z_nonneg [Z_to_bv 8 0; b1; b2; b3]) as X1. pose proof (bytes_le_to_Z_bound [Z_to_bv 8 0; b1; b2; b3]) as X2.
          cbn [length] in X2. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in X2. rewrite u_Z2bv by lia. reflexivity. }
        assert (EQS : (tot + (sz + 1)) / 2 ^ 20 = q + 1).
        { symmetry. apply (Z.div_unique (tot + (sz + 1)) (2 ^ 20) (q + 1) (tot mod 2 ^ 20 + sz + 1 - 2 ^ 20)); clear - DM1 MB1 MNZ SZ; lia. }
        assert (EQM : (tot + (sz + 1)) mod 2 ^ 20 = tot mod 2 ^ 20 + sz + 1 - 2 ^ 20).
        { symmetry. apply (Z.mod_unique (tot + (sz + 1)) (2 ^ 20) (q + 1) (tot mod 2 ^ 20 + sz + 1 - 2 ^ 20)); clear - DM1 MB1 MNZ SZ; lia. }
        set (BIq := Z_to_bv 64 (U SSW + 16 * ((tot + (sz + 1)) / 2 ^ 20) + 16) : word).
        assert (UBIq : U BIq = 1938504 + 16 * (q + 1) + 16) by ((lazymatch goal with |- ?G => let G' := eval unfold BIq in G in change_no_check G' end); rewrite EQS, USS; rewrite u_Z2bv by lia; reflexivity).
        assert (EBL : at_ BIq 12 = Z_to_bv 64 (1938504 + 28 + 16 * (q + 1))) by (apply bv_eq; rewrite at_u by (rewrite UBIq; lia); rewrite UBIq, u_Z2bv by lia; lia).
        assert (EBI : BIq = Z_to_bv 64 (1938504 + 16 + 16 * (q + 1))) by ((lazymatch goal with |- ?G => let G' := eval unfold BIq in G in change_no_check G' end); rewrite EQS, USS; f_equal; lia).
        set (so0 := dp_stored d q). set (so1 := dp_stored d (q + 1)). set (inf := sa_inf tot).
        assert (EC0 : st_cell SSW tot = Z_to_bv 64 (1938504 + 24 + 16 * q)) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; fold q; f_equal; clear; lia).
        assert (EC1 : st_cell SSW (tot + (sz + 1)) = Z_to_bv 64 (1938504 + 24 + 16 * (q + 1))) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS, EQS; f_equal; clear; lia).
        destruct (store_c_pre_strad MSr (seg_rom ASEGS) sp ndW bW h alv lkw b1 b2 b3 (dp_tab d b) (NIDS + 1) sz tag tot so0 so1 rS ATS
                    ltac:(clear - Hspr SPC CR HKD SPHI; lia) ltac:(clear - SZ; lia) Htag ltac:(clear - D7 FROOM SZ; lia) Hq1 (conj (D11 q) (D11 (q + 1))) Asz Atag Rtot
                    ltac:(rewrite EC0; exact (STORED q Q20)) ltac:(rewrite EC1; exact (STORED (q + 1) Q120))
                    ltac:(fold BIq; rewrite EBI; apply PTR0; [exact Q120 | rewrite <- QSL; apply Z.le_refl])
                    ltac:(fold BIq; rewrite EBL; exact Rl4) V_lock Ralloc Hstk SOKp
                    ltac:(apply SSOK; [rewrite USS; clear; lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia])
                    ltac:(rewrite EC0; apply SSOK; [rewrite u_Z2bv by lia; clear - Q20; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q20; lia])
                    ltac:(rewrite EC1; apply SSOK; [rewrite u_Z2bv by lia; clear - Q120; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q120; lia])
                    ltac:(fold BIq; rewrite EBL; apply SSOK; [rewrite u_Z2bv by lia; clear - Q120; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Q120; lia])
                    ltac:(apply SSOK; [rewrite at_u by (rewrite USS; clear; lia); rewrite USS; clear; lia | rewrite at_u by (rewrite USS; clear; lia); rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]))
          as (r5 & MP & RUN & SUM & G1 & G2 & G10 & G11 & G8 & G9 & G19 & G20 & G21 & G23 & SLbi & Rara & Ras0 & SLst & Ridx & Rpk & Rtot' & Rc0 & Rc1 & _ & INF & AG).
        fold inf in Rpk, Rc0, Rc1, INF.
        set (so := (so1 + (cnt - inf)) mod 2 ^ 32).
        set (std' := fupdZ (fupdZ (dp_stored d) q ((so0 + inf) mod 2 ^ 32)) (q + 1) ((so + cnt) mod 2 ^ 32)).
        exists r5, MP, (tot + cnt), (0 + st_full so0 inf + st_full so1 (cnt - inf)), so, std', (cpre_Wx sp q ((tot + (sz + 1)) / 2 ^ 20)). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
        unfold cnt in *. rewrite EQS in *.
        assert (THRU : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 -> (forall z, U x <= z < U x + Z.of_nat n -> ~ cpre_Wx sp q (q + 1) z) ->
                  rdn ASEGS MSr x n = Some v -> rdn ASEGS MP x n = Some v).
        { intros x n v B0 F Hr. exact (msum_rdn_eq ASEGS _ MSr MP x n v SUM B0 F Hr). }
        split; [exact RUN|]. split; [exact SUM|]. split; [constructor; (lazymatch goal with |- ?G => let G' := eval unfold cpre_Wx, cpre_W in G in change_no_check G' end); repeat apply wun_dec; apply ivl_dec|].
        split; [intros z Hz; unfold cpre_Wx, cpre_W, wun, ivl in Hz; replace (q + 1 - 1) with q by (clear; lia); clear - Hz; lia|].
        split; [clear - D7 FROOM SZ; lia|]. split; [rewrite EQM; clear - MB1 SZ; lia|]. split; [exact QSL|].
        split; [clear - SZ; lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold FRW in G in change_no_check G' end); clear - SZ; lia|].
        split.
        { rewrite LEN. replace ((tot + (sz + 1) + (sz + 1) - 1) / 2 ^ 20) with (q + 1); [clear - Q20 Q12; lia|].
          apply (Z.div_unique (tot + (sz + 1) + (sz + 1) - 1) (2 ^ 20) (q + 1) (tot mod 2 ^ 20 + sz + 1 + sz - 2 ^ 20)); clear - DM1 MB1 MNZ SZ; lia. }
        split; [(lazymatch goal with |- ?G => let G' := eval unfold so in G in change_no_check G' end); apply Z.mod_pos_bound; clear; lia|].
        split; [(lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (inf + so0 =? 1048576), (sz + 1 - inf + so1 =? 1048576); clear; lia|].
        split; [intros i; (lazymatch goal with |- ?G => let G' := eval unfold std', fupdZ in G in change_no_check G' end); destruct (i =? q + 1); [apply Z.mod_pos_bound; clear; lia | destruct (i =? q); [apply Z.mod_pos_bound; clear; lia | exact (D11 i)]]|].
        split; [(lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end); rewrite fupdZ_same; reflexivity|].
        split; [exact G1|]. split; [exact G2|]. split; [exact G10|]. split; [exact G11|]. split; [exact G8|]. split; [exact G9|].
        split; [exact G19|]. split; [exact G20|]. split; [exact G21|]. split; [exact G23|]. split; [exact AG|].
        split; [exact SLbi|]. split; [exact Rara|]. split; [exact Ras0|].
        split; [exact SLst|].
        split; [exact Ridx|]. split; [exact Rpk|].
        split; [rewrite Rc1; f_equal; (lazymatch goal with |- ?G => let G' := eval unfold so in G in change_no_check G' end); apply stored_le4b; [exact (D11 (q + 1)) | clear - INF SZ; lia]|].
        split; [exact Rtot'|].
        intros i Hi NE. (lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end). rewrite fupdZ_other by exact NE. destruct (Z.eq_dec i q) as [->|NEq2].
        + rewrite fupdZ_same. rewrite <- EC0, Rc0. f_equal. apply stored_le4b; [exact (D11 q) | clear - INF SZ; lia].
        + rewrite fupdZ_other by exact NEq2.
          apply THRU; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hi; lia | | exact (STORED i Hi)].
          intros z Hz. rewrite u_Z2bv in Hz by lia. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold cpre_Wx, cpre_W, wun, ivl in G in change_no_check G' end). clear - Hz Hi NE NEq2 Q20 Hspr SPC CR HKD. lia. }
    destruct PRE as (r5 & MPr & start & pk & so & std' & Wp & PREF). cbv zeta in PREF.
    set (qs := start / 2 ^ 20) in *. set (BI := Z_to_bv 64 (U SSW + 16 * qs + 16) : word) in *.
    destruct PREF as (RUNP & [FRp GRp] & [WDp] & CLSp & ST1 & FIT & QSL & FRB1 & FRB2 & LENP & SO & PK & STD & STDQ & G1 & G2 & G10 & G11 & G8 & G9 & G19 & G20 & G21 & G23 & AGP
                      & SLbi & Rara & Ras0 & SLst & Ridx & Rpk & Rso & Rtot' & CST).
    assert (QS20 : 0 <= qs < 2 ^ 12) by ((lazymatch goal with |- ?G => let G' := eval unfold qs in G in change_no_check G' end); destruct ST1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (NHWp : forall x : word, Wp (U x) -> Hd x = false).
    { intros x Hx. apply NHw. destruct (CLSp _ Hx) as [C|[C|[C|C]]]; [left; clear - C SPC HKD; lia | right; clear - C; lia | right; clear - C QS20; lia | right; clear - C QS20; lia]. }
    (* [comment removed for export] *)
    destruct LEDS as (LS1 & LS2 & LS3 & LS4 & LS5 & LS6 & LS7 & LS8 & LS9 & LSEAG & LSW & LSH & LSS).
    apply (katD_msteps_acct ASEGS Hd HOFF asanF_segs_wx (a_aa st)
             (@mkst fx rS (Z_to_bv 64 0x8c484) MS (seg_rom ASEGS)) (@mkst fx r5 (Z_to_bv 64 0x82340) MPr (seg_rom ASEGS)) mdlS).
    { rewrite LS3. apply lazy_cover_HID. } { exact Bw1. } { exact MIS. } { exact LSH. }
    { rewrite restrict_mkst9. fold MSr. replace (Z_to_bv 64 0x8c484) with (0x8c484%bv : word) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x82340) with (0x82340%bv : word) by (apply bv_eq; reflexivity). exact RUNP. }
    intros mdlN MIN SBMN HCN. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx rS (Z_to_bv 64 0x8c484) MS (seg_rom ASEGS))) with MS by reflexivity.
    set (M2f := munrestrict Hd MS MPr).
    pose proof (msum_unrestrict Hd Wp MS MPr NHWp (conj FRp GRp)) as [FR2 GR2]. fold M2f in FR2, GR2.
    pose proof (same_but_materialized_frame mdlS mdlN SBMN) as (_ & EvmN & ElzN & _ & _ & _ & _ & _ & _ & _ & _ & _ & EhlN & _ & _ & _ & EegN).
    assert (LEDN : ledN mdl mdlN nn).
    { (lazymatch goal with |- ?G => let G' := eval unfold ledN in G in change_no_check G' end). rewrite EvmN, ElzN, EegN, EhlN. repeat (split; [assumption|]).
      split; [exact (model_ivs_wf_sbm mdlS mdlN SBMN LSW)|]. split; [exact LSH|].
      exact (same_except_vm_trans mdl mdlS mdlN LSS (same_but_materialized_except_vm mdlS mdlN SBMN)). }
    set (W02 := wun W0 Wp).
    assert (S02 : msum W02 M M2f) by (exact (msum_trans _ _ _ _ _ (conj FR0 GR0) (conj FR2 GR2))).
    assert (CLS02 : forall z, W02 z -> cls02 (U sp) b idx (U ndW) qs nn z).
    { intros z [Hz | Hz]; [exact (cls0_02 _ _ _ _ qs _ _ (CLS0 z Hz))|].
      destruct (CLSp _ Hz) as [C|[C|[C|C]]]; (lazymatch goal with |- ?G => let G' := eval unfold cls02 in G in change_no_check G' end); [left; clear - C; lia | do 7 right; left; exact C | do 8 right; left; exact C | do 9 right; exact C]. }
    assert (VIS2 : forall x : word, Hd x = false -> M2f x = MPr x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M2f in G in change_no_check G' end); apply munrestrict_off; exact Hx).
    (* [comment removed for export] *)
    destruct DCELLS2 as (C_gpg & C_pg & C_b260 & C_c144 & C_one & C_dc). pose proof DCELLS as (_ & _ & _ & C_cf & _).
    assert (IMG2 : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= 0x1d9448 -> cellZ ASEGS M0 z k v ->
              rdn ASEGS M2f (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk C. unfold cellZ, cellN in C. refine (eq_trans _ C). apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia.
      rewrite (FR2 x) by (intros WZ; destruct (CLSp _ WZ) as [C1|[C1|[C1|C1]]]; [clear - C1 Hx Hk SPC CR HKD; lia | clear - C1 Hx Hk; lia | clear - C1 Hx Hk QS20; lia | clear - C1 Hx Hk QS20; lia]).
      rewrite (FR0 x (OUT0 (U x) ltac:(lia))). apply EQ0. apply XI. lia. }
    assert (NBC : nb + 2 ^ 20 <= CEIL).
    { destruct NBc as [INB | ENN].
      - destruct (node_blocks_dyn bt st Lc FF W nb INB) as ((_ & _ & GB2 & _) & _). exact GB2.
      - destruct (NNF nb ENN) as ((_ & _ & Y3 & _) & _). exact Y3. }
    assert (THRUP : forall (x : word) (n : nat) v, U x + Z.of_nat n <= 2 ^ 64 -> ((U sp - 128 <= U x) \/ (0x1e9458 <= U x /\ U x + Z.of_nat n <= CEIL)) ->
              rdn ASEGS MSr x n = Some v -> rdn ASEGS MPr x n = Some v).
    { intros x n v B0 Hr Hrd. apply (msum_rdn_eq ASEGS _ MSr MPr x n v (conj FRp GRp) B0); [| exact Hrd].
      intros z Hz WZ. destruct (CLSp _ WZ) as [C|[C|[C|C]]]; clear - C Hz Hr QS20 SPC HKD CR Hspr; lia. }
    set (Hd2 := HD2 bt Hd st).
    assert (HO2 : forall lo n, (CEIL <= lo \/ (AIMGLO <= lo /\ lo + n <= AIMGHI)) -> hid_off Hd2 lo n).
    { intros lo n Hr x Hx. apply hd2_off; [apply NHw; clear - Hr Hx; lia | clear - Hr Hx; lia]. }
    replace (Z_to_bv 64 0x82340) with (0x82340%bv : word) by (apply bv_eq; reflexivity).
    set (Qpost := depot_post_w bt FXOK KD X st Lc FF M mdl R sp ret).
    assert (KN : 0 <= Z.of_nat (length (blk_opt nn)) <= 1) by (destruct nn; (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); clear; lia).
    assert (NNR : forall p, nn = Some p -> 0 <= p /\ p + 2 ^ 20 < 2 ^ 64).
    { intros p E. destruct (NNF p E) as ((Y1 & Y2 & Y3 & _) & _). clear - Y1 Y3 CR. lia. }
    (* [comment removed for export] *)
    assert (GFACTS : forall mdlm (a : word), same_but_materialized mdlN mdlm -> grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true ->
              m_vmmaps mdlm = m_vmmaps mdlN /\ m_vm_lazy mdlm = m_vm_lazy mdlN /\ U a mod PG = 0
              /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> U a + 2 ^ 23 <= lo \/ hi <= U a)
              /\ AIMGHI <= U a /\ U a + 2 ^ 23 <= CEIL).
    { intros mdlm a SBMm G. destruct (sbm_vmmaps _ _ SBMm) as [EVm ELm]. destruct LEDN as (LN1 & _ & _ & LN4 & _ & _ & _ & LN8 & _).
      destruct (grant_nr_facts_x bt st Lc FF M0 mdl mdlm (2 ^ 20) (2 ^ 28) (Z_to_bv 64 0) a nn h0 W RP BOOTG
                  ltac:(rewrite EVm; exact LN4) ltac:(rewrite EVm; exact LN1) ltac:(rewrite EVm; exact LN8) NNR HOLE G) as (DY & AL & AP & _ & _).
      split; [exact EVm|]. split; [exact ELm|]. split; [exact AL|]. split; [exact AP|].
      destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi asan_addrs] in Y4. pose proof (u64_range a) as Har'. split; [clear - Y1 Y4 Har'; lia | exact Y3]. }
    apply (mnr_katD Hd2 (hoff_hd2 bt Hd st HOFF) asanF_segs_wx (a_aa st) r5 M2f (seg_rom ASEGS) mdlN spMn (Z_to_bv 64 0x8d000)
             (getr r5 8) (getr r5 9) (getr r5 18) (getr r5 19) (getr r5 20) (getr r5 21) szW (Z_to_bv 64 0x21f70) 0x197020 0x1990a8 Qpost
             (fun mdlm a => grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true) (fun mdlm a => mmap_model_noreserve a szW mdlm)).
    - rewrite G1. apply bv_eq. reflexivity.
    - exact G2.
    - exact G10.
    - exact G11.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite UspMn. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end). apply bv_eq. vm_compute. reflexivity.
    - rewrite Usz. split; [reflexivity | lia].
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - apply store_ok_bytes; [| rewrite at_u by (rewrite UspMn; lia); rewrite UspMn; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. intros x Hx. rewrite at_u in Hx by (rewrite UspMn; lia). rewrite UspMn in Hx. cbn in Hx.
      eapply store_ok_mono; [exact GR2|]. eapply store_ok_mono; [exact GR0|]. exact (proj2 (STK x ltac:(lia))).
    - apply IMG2; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_gpg)].
    - apply IMG2; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_pg)].
    - apply IMG2; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_cf)].
    - change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))). apply IMG2; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_b260)].
    - apply IMG2; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_c144)].
    - apply IMG2; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_one)].
    - apply IMG2; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_dc)].
    - apply HO2. right. lia.
    - apply HO2. right. lia.
    - apply HO2. right. lia.
    - apply HO2. right. lia.
    - apply HO2. right. lia.
    - apply HO2. right. lia.
    - apply HO2. right. lia.
    - apply HO2. left. rewrite UspMn. lia.
    - rewrite EhlN. exact LSH.
    - apply lazy_cover_hd2. rewrite ElzN, LS3. apply lazy_cover_HID.
    - exact Bw1.
    - exact MIN.
    - (* [comment removed for export] *) intros mdlm a SBMm G. destruct (GFACTS mdlm a SBMm G) as (_ & _ & _ & _ & GA & GC). rewrite Usz, UspMn. lia.
    - (* [comment removed for export] *) intros mdlm rr SBMm MIm HLm B10 B11 B12 B13 B14 B15 Q' KOK KKP.
      apply (node_dm_of_mmap_nr rr _ _ mdlm szW Q' HLm B10 B11 B12 B13 B14 B15 ltac:(rewrite Usz; lia) ltac:(rewrite Usz; reflexivity)).
      + rewrite Usz. destruct (sbm_vmmaps _ _ SBMm) as [EVm ELm]. destruct LEDN as (LN1 & _ & _ & LN4 & _ & _ & _ & LN8 & _).
        apply (GRANT_NR_EX st Lc FF M0 mdl mdlm nn W RP KC); [rewrite EVm; exact LN4 | rewrite EVm; exact LN1 | rewrite EVm; exact LN8].
      + intros a Ha. rewrite Usz in Ha. exact (KOK a Ha).
      + exact KKP.
    - (* [comment removed for export] *) intros mdlm a SBMm MIm G. destruct (GFACTS mdlm a SBMm G) as (EVm & ELm & AL & AP & GA & GC).
      destruct LEDN as (_ & _ & LN3 & _ & _ & _ & _ & _ & _ & _ & LNW & LNH & _). pose proof (u64_range a) as Har.
      assert (AALp : U a mod page_size = 0) by ((lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end); exact AL).
      destruct (nr_child_eqs mdlN mdlm a szW EVm ELm AALp ltac:(rewrite Usz; reflexivity) ltac:(rewrite Usz; lia) ltac:(rewrite Usz; lia)) as (_ & CE2 & _).
      split; [change (m_halted (mmap_model_noreserve a szW mdlm)) with (m_halted mdlm);
              pose proof (same_but_materialized_frame mdlN mdlm SBMm) as F; destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _); rewrite HL; exact LNH|].
      split.
      + rewrite CE2, LN3. apply lazy_cover_hd2_cons; [apply lazy_cover_HID | exact AL | rewrite Usz; reflexivity|].
        intros w Hw. rewrite Usz in Hw. exact (hf_fresh bt st (U a) (2 ^ 23) w AP GC GA Hw).
      + exact (nr_child_MInv mdlN mdlm a szW LNW EVm ELm AALp ltac:(rewrite Usz; reflexivity) ltac:(rewrite Usz; lia) ltac:(rewrite Usz; lia) (a_aa st) MIm).
    - (* [comment removed for export] *) intros a r' mdlm mdl4 SBMm MIm G SBM4 MI4 MR.
      destruct (GFACTS mdlm a SBMm G) as (_ & _ & _ & _ & GA & GC). pose proof (u64_range a) as Har.
      match goal with |- katD _ (mkCfg (mkst _ _ ?m _) _) _ => set (MB := m) end.
      apply (sgrow_cont bt FXOK BT_segs BT_ia DCELLS DOBL DEP0 BOOTG KD HKD fx X st Lc FF M M0 M2f MPr MB mdl mdlN mdlm mdl4 R r5 r' sp buf ret a ndW
               (getr rS 19) (getr rS 20) sz tag start pk so std' ws h0 nn W02
               HFX HH MW W RP DIFF XIMG PXH HOLE ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD
               ST1 FIT QSL FRB1 FRB2 LENP SO PK STD STDQ NNW NNI NNF NNM0).
      + intros p z Ep Hz. destruct (NNV p z Ep Hz) as (V1 & V2 & V3). split; [exact V1|]. split; [exact V2|]. apply GR2. exact V3.
      + exact ND.
      + exists nb. split; [exact NBc|]. split; [exact NB1 | exact NB2].
      + exact I16.
      + (lazymatch goal with |- ?G => let G' := eval unfold W02 in G in change_no_check G' end). apply wun_dec; [exact WD0 | exact WDp].
      + exact S02.
      + exact CLS02.
      + exact VIS2.
      + exact SLbi.
      + exact Rara.
      + exact Ras0.
      + exact SLst.
      + exact Ridx.
      + exact Rpk.
      + exact Rso.
      + exact Rtot'.
      + exact CST.
      + apply THRUP; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | left; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Atr].
      + intros k v Hin. assert (K : -88 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; clear; lia|]); destruct Hin).
        apply THRUP; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | left; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact (SLs k v Hin)].
      + apply THRUP; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; rewrite at_at, at_u by lia; lia | exact Rq8].
      + apply THRUP; [rewrite at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; rewrite at_at, at_u by lia; lia | exact Rq16].
      + apply THRUP; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hndr NB2 NBC CR; lia | right; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - NB1 NB2 NBA NBC; lia | exact Rhsh].
      + apply THRUP; [rewrite u_Z2bv by lia; change (Z.of_nat 4) with 4; lia | right; rewrite u_Z2bv by lia; change (Z.of_nat 4) with 4; clear - CR; lia | exact Kn0].
      + apply THRUP; [(lazymatch goal with |- ?G => let G' := eval unfold MUW in G in change_no_check G' end); rewrite u_Z2bv by lia; change (Z.of_nat 1) with 1; lia | right; (lazymatch goal with |- ?G => let G' := eval unfold MUW in G in change_no_check G' end); rewrite u_Z2bv by lia; change (Z.of_nat 1) with 1; clear - CR; lia | exact Kmu0].
      + intros p Ep. fold d; fold NIDS; fold idx. apply THRUP; [rewrite u_Z2bv by (clear - I16; lia); change (Z.of_nat 8) with 8; clear - I16; lia | right; rewrite u_Z2bv by (clear - I16; lia); change (Z.of_nat 8) with 8; clear - I16 CR; lia | exact (Kslot0 p Ep)].
      + exact G8.
      + exact G9.
      + exact G19.
      + exact G20.
      + exact G21.
      + exact G23.
      + intros k N1 N2. rewrite (AGP _ N1). exact (AG0 k N1 N2).
      + exact LEDN.
      + exact SBMm.
      + exact G.
      + exact SBM4.
      + exact MI4.
      + destruct MR as (B10 & B2 & B1 & B8 & B9 & B18 & AGm). repeat (split; [assumption|]). exact AGm.
      + split.
        * intros x Hx. unfold wun, ivl in Hx. (lazymatch goal with |- ?G => let G' := eval unfold MB in G in change_no_check G' end). pose proof (u64_range x) as Hxr.
          assert (OX : U x < U sp - 576 \/ U sp - 256 <= U x) by (clear - Hx; lia).
          assert (OA : U x < U a \/ U a + 2 ^ 23 <= U x) by (clear - Hx; lia).
          etransitivity; [apply MemsetLibF.MemSplit.wbytes_outside; [rewrite at_u by (rewrite UspMn; clear - Hspr SPC CR HKD; lia); rewrite UspMn; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hspr SPHI; lia
                                                         | rewrite at_u by (rewrite UspMn; clear - Hspr SPC CR HKD; lia); rewrite UspMn; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - OX; lia]|].
          etransitivity; [apply zfill_out; rewrite Usz; exact OA|].
          apply mnr_m1_outside; [rewrite UspMn; clear - Hspr SPC CR HKD SPHI; lia | rewrite UspMn; clear - OX; lia].
        * (lazymatch goal with |- ?G => let G' := eval unfold MB in G in change_no_check G' end). eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply zfill_grows2]. apply mnr_m1_grows.
      + intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MB in G in change_no_check G' end). apply wbytes_grows. rewrite (zfill_in' a szW _ x) by (rewrite Usz; lia). discriminate.
  Qed.
End TOPS2.
