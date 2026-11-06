(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac ha_prev := first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).






Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ri_mod8 : forall x c, x mod 2 ^ 16 = 0 -> (x + 2 ^ 37 + 128 * c) mod 8 = 0.
Proof. intros x c Hx. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn_heap_bytes8 : forall (m : mem) (a : word) (k : nat) (bs : list byte),
  (U a + Z.of_nat k <= AIMGLO \/ AIMGHI <= U a) -> U a + Z.of_nat k < 2 ^ 64 ->
  rdn ASEGS m a k = Some bs -> forall i : nat, (i < k)%nat -> m (Z_to_bv 64 (U a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros m a k; revert a; induction k as [|k IH]; intros a Ha Hk bs R i Hi; [lia|].
  pose proof (u64_range a) as Hua. cbn [rdn] in R.
  destruct (m a) as [b|] eqn:E.
  - destruct (rdn ASEGS m (a + 1) k) as [rest|] eqn:E2; [|discriminate R]. injection R as <-.
    destruct i as [|i].
    + (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E.
    + (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end). replace (U a + Z.of_nat (Datatypes.S i)) with (U (a + 1)%bv + Z.of_nat i) by (rewrite u_add1 by lia; lia).
      apply (IH (a + 1)%bv); [rewrite u_add1 by lia; lia | rewrite u_add1 by lia; lia | exact E2 | lia].
  - exfalso. unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1 in R.
    rewrite (find_segment1_none_outside ASEGS 0x10000 0x65d000 (U a) asanF_segs_in_hull) in R; [discriminate R|]. lia.
Qed.
Lemma rdn_same_bytes8 : forall (m1 m2 : mem) (z : Z) (k : nat) (bs : list byte) (x : word),
  0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (z + Z.of_nat k <= AIMGLO \/ AIMGHI <= z) ->
  rdn ASEGS m1 (Z_to_bv 64 z) k = Some bs -> rdn ASEGS m2 (Z_to_bv 64 z) k = Some bs ->
  z <= U x < z + Z.of_nat k -> m1 x = m2 x.
Proof.
  intros m1 m2 z k bs x Hz Hk Hoff R1 R2 Hx.
  pose proof (rdn_heap_bytes8 m1 (Z_to_bv 64 z) k bs ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) R1 (Z.to_nat (U x - z)) ltac:(lia)) as A.
  pose proof (rdn_heap_bytes8 m2 (Z_to_bv 64 z) k bs ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia) R2 (Z.to_nat (U x - z)) ltac:(lia)) as B.
  rewrite u_Z2bv in A, B by lia. replace (z + Z.of_nat (Z.to_nat (U x - z))) with (U x) in A, B by lia. rewrite Z_to_bv_bv_unsigned in A, B. congruence.
Qed.

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).

  (* [comment removed for export] *)
  Lemma repx_unlock : forall (c : Z) st Lc FF (M M' : mem) mdl mdl',
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 8)) ->
    (forall a : word, M' a <> M a -> (reginfo bt c <= U a < reginfo bt c + 8) /\ M' a <> None) ->
    rdn ASEGS M' (Z_to_bv 64 (reginfo bt c)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    MInv (a_aa st) mdl' -> same_but_materialized mdl mdl' ->
    RepX bt X st Lc FF M' mdl'.
  Proof using BT_segs.
    intros c st Lc FF M M' mdl mdl' Hc W RX XRI FOOTM LOCK0 MI SBM.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & E9 & E10 & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & _ & _ & S1 & S2 & S3). pose proof ceil_rng as CR.
    unfold KSPACE, PG, AS_HEAPLO in *. set (RIz := reginfo bt c) in *.
    apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ (RIz <= z < RIz + 8)) X).
    { intros z [[Hx | Hl] NL]; [exact Hx | exfalso; exact (NL Hl)]. }
    apply (repx_step bt (XL c) (fun z => RIz <= z < RIz + 8) (fun z => RIz <= z < RIz + 8) (Xdec_iv RIz (RIz + 8)) st st Lc Lc FF FF M M' mdl mdl' RX FOOTM).
    { intros a Ha. destruct (decide (M' a = M a)) as [E | NE]; [| exact (proj2 (FOOTM a NE))].
      rewrite E. destruct RX as (M0 & RP & D). destruct (decide (M a = M0 a)) as [E2 | NE2]; [| exact (proj2 (D a NE2))].
      rewrite E2. pose proof RP as (_ & _ & _ & R4 & _). destruct (R4 c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GW) _]. rewrite BT_segs in GW. fold RIz in GW.
      destruct (GW (U a) ltac:(lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
    intros N0 N0' RPn Dn DIFF EQ _.
    apply (Rep_sbm bt st Lc FF N0' mdl mdl'); [| exact MI | exact SBM].
    apply (Rep_frame bt st Lc FF N0 N0' mdl W RPn). intros a Ha. exfalso. apply Ha.
    destruct (DIFF a Ha) as [[F | F] _].
    - (* [comment removed for export] *)
      pose proof RPn as (_ & _ & _ & R4 & _). destruct (R4 c Hc) as [(G0 & _) _]. rewrite BT_segs in G0. fold RIz in G0. unfold cellZ, cellN in G0.
      rewrite (EQ a (or_intror F)).
      apply (rdn_same_bytes8 M' N0 RIz 8 _ a ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(right; lia) LOCK0 G0). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - pose proof RPn as (_ & _ & _ & R4 & _). destruct (R4 c Hc) as [(G0 & _) _]. rewrite BT_segs in G0. fold RIz in G0. unfold cellZ, cellN in G0.
      rewrite (EQ a (or_intror F)).
      apply (rdn_same_bytes8 M' N0 RIz 8 _ a ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(right; lia) LOCK0 G0). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  Qed.


  Theorem refill_ok_K :
    forall (K : config -> Prop), liftable K ->
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR s0R s1R g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> a_cinit st = true -> a_cache st c = [] ->
    let r := a_reg st c in let nf2 := Z.of_nat (length (r_free r)) in let m := cache_hint c in
    m <= nf2 ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (fa_beg SBEG c <= z < fa_beg SBEG c + 4 * nf2) /\ ~ (T <= z < T + 2768)) ->
    gf_inv bt M c spR raR s0R s1R (Z_to_bv 64 0x50a0c) (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 m) g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ->
    gfp_regs (at_ spR (-32)) (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (reginfo bt c) SBEG c m regs -> getr regs 10 = Z_to_bv 64 1 ->
    (CEIL + 160 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        WF bt (op_refill st c m) Lc FF -> RepX bt X (op_refill st c m) Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a ->
            ((reginfo bt c <= U a < reginfo bt c + 128) \/ (T + T_PC + PC_SZ * c <= U a < T + T_PC + PC_SZ * c + 80)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = s0R -> getr r' 9 = s1R -> s_regs r' g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 -> getr r' 4 = getr regs 4 -> getr r' 3 = getr regs 3 ->
        K (mkCfg (mkst r' raR M' rom) mdl')) ->
    K (mkCfg (mkst regs (0x50d88%bv : word) M rom) mdl).
  Proof using BT_ia BT_segs.
    intros K LK c st Lc FF M rom mdl regs spR raR s0R s1R g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 Hc W RX HALT CINIT HC0 r nf2 m LE XOFF (LOCKED & GSL & RSL) HR H10 Hsp HretR CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold nf2 in E7.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9 & _). fold r in Y9.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & _ & _ & T4k & TIMG & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & TSP & _ & S1 & S2 & S3).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16).
    pose proof RP as (_ & _ & R3 & R4 & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _).
    destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _).
    destruct (R4 c Hc) as [(_ & _ & G16 & _ & _ & _ & _ & _ & _ & GW) (F1 & _ & _)]. fold r nf2 in G16, F1.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    unfold KSPACE, PG, AS_HEAPLO, T_PC, PC_SZ in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    assert (EFAB : fa_beg SBEG c = SBEG + c * 2 ^ 32 + 3758096384) by ((lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity).
    assert (Hm : 1 <= m <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end); lia).
    assert (EMC2 : cache_max c / 2 = m) by ((lazymatch goal with |- ?G => let G' := eval unfold cache_max in G in change_no_check G' end); fold m; rewrite Z.mul_comm; apply Z.div_mul; lia).
    destruct (pos_mod4096 T T1 T4k) as [T4 T8].
    set (faf := fun j : Z => nth (Z.to_nat j) (r_free r) 0).
    assert (FAF : forall j, 0 <= j < nf2 -> nth_error (r_free r) (Z.to_nat j) = Some (faf j) /\ 0 <= faf j < 2 ^ 32).
    { intros j Hj. assert (NE : nth_error (r_free r) (Z.to_nat j) = Some (faf j)) by ((lazymatch goal with |- ?G => let G' := eval unfold faf in G in change_no_check G' end); apply nth_error_nth'; unfold nf2 in Hj; lia).
      split; [exact NE|]. exact (proj1 (Y9 (faf j) (nth_error_In _ _ NE))). }
    (* [comment removed for export] *)
    assert (XRI : forall i, RIz <= i < RIz + 128 -> ~ X i) by (intros i Hi Hx; exact (proj1 (XOFF i Hx) Hi)).
    assert (XFA : forall i, fa_beg SBEG c <= i < fa_beg SBEG c + 4 * nf2 -> ~ X i) by (intros i Hi Hx; exact (proj1 (proj2 (XOFF i Hx)) Hi)).
    assert (XT : forall i, T <= i < T + 2768 -> ~ X i) by (intros i Hi Hx; exact (proj2 (proj2 (XOFF i Hx)) Hi)).
    assert (XLRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i) by (intros i Hi [Hx | Hl]; [exact (XRI i ltac:(lia) Hx) | fold RIz in Hl; lia]).
    assert (XLFA : forall i, fa_beg SBEG c <= i < fa_beg SBEG c + 4 * nf2 -> ~ XL c i) by (intros i Hi [Hx | Hl]; [exact (XFA i Hi Hx) | fold RIz in Hl; lia]).
    assert (XLT : forall i, T <= i < T + 2768 -> ~ XL c i) by (intros i Hi [Hx | Hl]; [exact (XT i Hi Hx) | fold RIz in Hl; clear - Hl Hi TSP ERI Hc; lia]).
    assert (WRI : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
    assert (WT : writableZ ASEGS M T (T + 4096)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact TW]).
    destruct (pk_junk8 M RIz (RIz + 128) (RIz + 72) WRI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (stv & RST).
    assert (KNF : rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf2)))
      by (apply (repx_rd (XL c) M M0 D (RIz + 16) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XLRI; cbn in Hi; lia | exact G16]).
    set (spG := at_ spR (-32)) in *. assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    set (pc := Z_to_bv 64 (T + 208 + 80 * c) : word). assert (Upc : U pc = T + 208 + 80 * c) by ((lazymatch goal with |- ?G => let G' := eval unfold pc in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). left. exact Hr. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (pk_nolazy_rt bt st Lc FF M0 mdl W RP z). left. exact Hz. }
    assert (NHfa : forall z, fa_beg SBEG c <= z < fa_beg SBEG c + r_mapped_fa r -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [rewrite EFAB in Hz; lia|]. apply (rep_nolazy_fa bt st Lc FF M0 mdl W RP c); [exact Hc | exact Hz]. }
    assert (HOFF : forall lo0 n, (forall z, lo0 <= z < lo0 + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo0 n).
    { intros lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    set (Mr := mrestrict Hd M).
    assert (RDM : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn ASEGS M (Z_to_bv 64 z) k = Some v -> rdn ASEGS Mr (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; apply HOFF; exact Hh0]. }
    assert (RSP : forall (b : word) (k : Z) v, U b = U spR \/ U b = U spG -> -128 <= k -> k + 8 <= 0 -> rdn ASEGS M (at_ b k) 8 = Some v -> rdn ASEGS Mr (at_ b k) 8 = Some v).
    { intros b k v Hb K0 K1 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia]. }
    destruct (asan_mask_rdn Mr) as (msk & RMSK).
    assert (RETG : ret_ok (at_ ARB 0x50a0c)) by (rewrite ARB_lit8 by lia; apply ret_ok_lit; [lia | reflexivity]).
    assert (ECHP : Z_to_bv 64 (T + 208 + 80 * c + 16) = at_ pc 16) by (apply bv_eq; rewrite at_u by lia; rewrite Upc, u_Z2bv by lia; reflexivity).
    rewrite ECHP in HR.
    destruct (gfp_ok Mr rom spG (at_ ARB 0x50a0c) pc (Z_to_bv 64 m) g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 (at_ pc 16) stv msk SBEG c m nf2 faf
                ltac:(rewrite UspG; lia) RETG Hc ltac:(split; [exact Hm | split; [exact LE | lia]]) ltac:(split; [lia | split; [lia | exact (mod8_of_64k _ S16)]]) ltac:(rewrite UspG; lia)
                ltac:(rewrite at_u by lia; rewrite Upc, UspG; split; [clear - TSP Hc Hm; lia | split; [lia | clear - TIMG Hc Hm; lia]])
                (RDM (RIz + 16) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(intros i Hi; apply NHri; cbn in Hi; lia) KNF)
                (RDM (RIz + 72) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(intros i Hi; apply NHri; cbn in Hi; lia) RST)
                (RDM RIz 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(intros i Hi; apply NHri; cbn in Hi; lia) LOCKED)
                RMSK) with (regs := regs)
      as (r1 & RUN1 & P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & PAG).
    - (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [apply (writableZ_sok M RIz (RIz + 128)); [exact WRI | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                             | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHri; lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [apply (writableZ_sok M T (T + 4096)); [exact WT | rewrite at_u by lia; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia | lia]
                                             | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; apply HOFF; intros z Hz; apply NHrt; lia].
    - intros j Hj. destruct (FAF j ltac:(lia)) as [NE BD]. split; [| exact BD].
      replace (SBEG + c * 2 ^ 32 + 3758096384 + 4 * j) with (fa_beg SBEG c + 4 * Z.of_nat (Z.to_nat j)) by (rewrite EFAB; lia).
      apply RDM; [rewrite EFAB; lia | rewrite EFAB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHfa; cbn in Hi; lia |].
      apply (repx_rd (XL c) M M0 D _ 4 _); [rewrite EFAB; lia | rewrite EFAB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XLFA; cbn in Hi; lia | exact (F1 _ _ NE)].
    - rewrite (ARB_lit8 0x50a0c) by lia. exact (RSP spG (-8) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-8) (Z_to_bv 64 0x50a0c) ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-16) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-16) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-24) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-24) _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-32) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-32) g2 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-40) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-40) g3 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-48) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-48) g4 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-56) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-56) g5 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-64) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-64) g6 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-72) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-72) g7 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-80) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-80) g8 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-88) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-88) g9 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-96) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-96) g10 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact (RSP spG (-104) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-104) g11 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15))).
    - exact HR.
    - exact H10.
    - set (MG := gh_m5 Mr (at_ pc 16) stv faf (SBEG + 2 ^ 37 + 128 * c) nf2 m) in *.
      set (cache := Z_to_bv 64 (T + 208) : word). assert (Ucache : U cache = T + 208) by ((lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
      set (regs0 := regupd (regupd regs 8 s0R) 9 s1R).
      assert (G08 : getr regs0 8 = s0R) by ((lazymatch goal with |- ?G => let G' := eval unfold regs0 in G in change_no_check G' end); rewrite getr_other by (intros E; discriminate E); apply getr_same; intros E; discriminate E).
      assert (G09 : getr regs0 9 = s1R) by ((lazymatch goal with |- ?G => let G' := eval unfold regs0 in G in change_no_check G' end); apply getr_same; intros E; discriminate E).
      assert (MGout : forall x : word, CEIL <= U x -> MG x = Mr x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MG, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end).
        do 2 (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite gh_cp_outside; [ | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia].
        apply MemsetLibF.MemSplit.wbytes_outside; [rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
      assert (MGgr : mem_grows Mr MG).
      { (lazymatch goal with |- ?G => let G' := eval unfold MG, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [| apply wbytes_grows]). eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows]. }
      destruct (rf_epi ASEGS ARB asan_HRF ARB_ok regs0 rom raR spR cache pc c (cache_max c) HretR
                  ltac:((lazymatch goal with |- ?G => let G' := eval unfold cache_max in G in change_no_check G' end); fold m; split; [lia | rewrite Z.mul_comm; apply Z_mod_mult]) ltac:(lia) ltac:(rewrite Ucache, Upc; lia)
                  MG r1 (Z_to_bv 64 1) P1 P2 P8 ltac:(rewrite EMC2; exact P9) P10 ltac:(rewrite u_Z2bv by lia; lia))
        as (r2 & RUN2 & Q10 & Q2 & Q8 & Q9 & Q1 & QAG).
      + eapply store_ok_mono; [exact MGgr|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
        rewrite store_ok_mrestrict; [apply (writableZ_sok M T (T + 4096)); [exact WT | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                    | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHrt; lia].
      + intros k v Hin. assert (Kk : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        rewrite (rdn_ext ASEGS 8 MG Mr (at_ spR k)); [ | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply MGout; lia].
        apply RSP; [left; reflexivity | lia | lia |]. rewrite G08, G09 in Hin. exact (RSL k v Hin).
      + left. rewrite Upc. lia.
      + rewrite EMC2 in RUN2.
        set (M' := r2_mem M pc stv faf RIz nf2 m).
        assert (EM : wbytes MG pc (LE4 m) = mrestrict Hd M').
        { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite <- (r2_mem_mrestrict M pc stv faf RIz nf2 m Hm ltac:(rewrite Upc; lia) ltac:(lia) Hd
                                  ltac:(rewrite Upc; apply HOFF; intros z Hz; apply NHrt; lia) ltac:(apply HOFF; intros z Hz; apply NHri; lia)).
          reflexivity. }
        rewrite EM in RUN2.
        rewrite (ARB_lit8 0x50a0c) in RUN1, RUN2 by lia.
        replace (Z_to_bv 64 0x50a0c : word) with (0x50a0c%bv : word) in RUN1 by (apply bv_eq; reflexivity).
        replace (Z_to_bv 64 0x50a0c : word) with (0x50a0c%bv : word) in RUN2 by (apply bv_eq; reflexivity).
        assert (OUTM : forall a : word, (U a < T + 208 + 80 * c \/ T + 208 + 80 * c + 80 <= U a) -> (U a < RIz \/ RIz + 128 <= U a) -> M' a = M a).
        { intros a A1 A2. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r2_mem_outside; rewrite ?Upc; first [exact Hm | lia]. }
        apply (LK Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs _ r2 _ M M' rom mdl (msteps_trans _ _ _ _ RUN1 RUN2)); [ | exact HALT | apply lazy_cover_HID | exact Bw1 | exact Bw2 | ].
        * intros a Ha. apply OUTM.
          -- pose proof (hid_true_off Hd a (T + 208 + 80 * c) 80 Ha ltac:(apply HOFF; intros z Hz; apply NHrt; lia)). lia.
          -- pose proof (hid_true_off Hd a RIz 128 Ha ltac:(apply HOFF; intros z Hz; apply NHri; lia)). lia.
        * intros mdlm SBM MIm.
          assert (FOOTM : forall a : word, M' a <> M a -> ((RIz <= U a < RIz + 128) \/ (T + 208 + 80 * c <= U a < T + 208 + 80 * c + 80)) /\ M' a <> None).
          { intros a Ha.
            assert (IN : ((RIz <= U a < RIz + 128) \/ (T + 208 + 80 * c <= U a < T + 208 + 80 * c + 80))
                         \/ ((U a < T + 208 + 80 * c \/ T + 208 + 80 * c + 80 <= U a) /\ (U a < RIz \/ RIz + 128 <= U a))) by (clear; lia).
            destruct IN as [IN | [O1 O2]]; [| exfalso; exact (Ha (OUTM a O1 O2))]. split; [exact IN|].
            (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r2_mem_grows.
            destruct IN as [I1 | I2]; [destruct (WRI (U a) I1) as [Dd _] | destruct (WT (U a) ltac:(clear - I2 Hc; lia)) as [Dd _]]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd. }
          destruct (r2_mem_rd ASEGS M pc stv faf RIz nf2 m Hm ltac:(rewrite Upc; lia) ltac:(lia) ltac:(rewrite Upc; clear - TSP ERI Hc; lia)) as (RDcnt & RDlock & RDnf & RDch).
          assert (W2 : WF bt (op_refill st c m) Lc FF) by (apply (OPS_WF_refill_pf bt st Lc FF c m W Hc HC0 CINIT eq_refl); exact LE).
          apply (CONT r2 M' mdlm W2); [ | exact SBM | exact MIm | | exact Q10 | exact Q2 | exact Q1 | rewrite Q8; exact G08 | rewrite Q9; exact G09
                                       | (lazymatch goal with |- ?G => let G' := eval unfold s_regs in G in change_no_check G' end); rewrite !QAG by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); repeat split; assumption | | ].
          -- apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ (RIz <= z < RIz + 8)) X).
             { intros z [[Hx | Hl] NL]; [exact Hx | exfalso; exact (NL Hl)]. }
             apply (repx_step bt (XL c) (fun z => RIz <= z < RIz + 8)
                      (fun z => (RIz <= z < RIz + 128) \/ (T + 208 + 80 * c <= z < T + 208 + 80 * c + 80)) (Xdec_iv RIz (RIz + 8))
                      st (op_refill st c m) Lc Lc FF FF M M' mdl mdlm RX FOOTM).
             { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r2_mem_grows. destruct (WRI (U a) ltac:(lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
             intros N0 N0' RPn Dn DIFF EQ SAME.
             assert (EQF : forall a : word, ~ XL c (U a) \/ (RIz <= U a < RIz + 8) -> N0' a = M' a) by exact EQ.
             assert (RDN : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ XL c i \/ (RIz <= i < RIz + 8)) ->
                        rdn ASEGS M' (Z_to_bv 64 z) k = Some v -> rdn ASEGS N0' (Z_to_bv 64 z) k = Some v).
             { intros z k v Z0 Z1 OFF Hr. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply EQF. apply OFF. exact Hx. }
             apply (OPS_REP_refill_pf bt st Lc FF N0 N0' mdl mdlm c m W RPn Hc HC0 CINIT eq_refl LE); rewrite ?BT_segs; fold r nf2 RIz.
             ++ intros a Ha. destruct (DIFF a Ha) as [F Dd]. split; [| exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_refill in G in change_no_check G' end). fold RIz. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end).
                destruct F as [[F | F] | F]; [ | | left; lia].
                ** (* [comment removed for export] *)
                   destruct (Z_lt_le_dec (U a) (RIz + 8)) as [C1|C1]; [left; lia|].
                   destruct (Z_lt_le_dec (U a) (RIz + 16)) as [C2|C2].
                   { exfalso. apply Ha. rewrite (EQF a ltac:(left; apply XLRI; lia)). rewrite <- (repx_off (XL c) M N0 Dn a ltac:(apply XLRI; lia)).
                     (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r2_mem_outside; rewrite ?Upc; first [exact Hm | lia | clear - C1 C2 TSP ERI Hc F; lia]. }
                   destruct (Z_lt_le_dec (U a) (RIz + 24)) as [C3|C3]; [right; left; lia|].
                   destruct (Z_lt_le_dec (U a) (RIz + 72)) as [C4|C4]; [| right; right; left; lia].
                   exfalso. apply Ha. rewrite (EQF a ltac:(left; apply XLRI; lia)). rewrite <- (repx_off (XL c) M N0 Dn a ltac:(apply XLRI; lia)).
                   (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r2_mem_outside; rewrite ?Upc; first [exact Hm | lia | clear - C3 C4 TSP ERI Hc F; lia].
                ** destruct (Z_lt_le_dec (U a) (T + 208 + 80 * c + 4)) as [C1|C1]; [right; right; right; left; lia|].
                   destruct (Z_lt_le_dec (U a) (T + 208 + 80 * c + 16)) as [C2|C2].
                   { exfalso. apply Ha. rewrite (EQF a ltac:(left; apply XLT; clear - F Hc; lia)). rewrite <- (repx_off (XL c) M N0 Dn a ltac:(apply XLT; clear - F Hc; lia)).
                     (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r2_mem_outside; rewrite ?Upc; first [exact Hm | lia | clear - C1 C2 TSP ERI Hc F; lia]. }
                   destruct (Z_lt_le_dec (U a) (T + 208 + 80 * c + 16 + 4 * m)) as [C3|C3]; [right; right; right; right; left; lia|].
                   exfalso. apply Ha. rewrite (EQF a ltac:(left; apply XLT; clear - F Hc; lia)). rewrite <- (repx_off (XL c) M N0 Dn a ltac:(apply XLT; clear - F Hc; lia)).
                   (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r2_mem_outside; rewrite ?Upc; first [exact Hm | lia | clear - C3 TSP ERI Hc F Hm; lia].
             ++ (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; right; cbn in Hi; lia | exact RDlock].
             ++ (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; left; apply XLRI; cbn in Hi; lia | exact RDnf].
             ++ (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, T_PC, PC_SZ in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; left; apply XLT; cbn in Hi; clear - Hi Hc; lia | exact RDcnt].
             ++ intros i k Hnth.
                pose proof (split_keep_taken (r_free r) m ltac:(fold nf2; lia)) as SPL. cbn zeta in SPL. fold nf2 in SPL. destruct SPL as (_ & _ & LT & _ & NT).
                rewrite NT in Hnth.
                assert (Hi : Z.of_nat i < m).
                { assert (Z.to_nat (nf2 - m) + i < length (r_free r))%nat by (apply nth_error_Some; rewrite Hnth; discriminate). unfold nf2 in *. lia. }
                assert (Ek : k = faf (nf2 - m + Z.of_nat i)).
                { (lazymatch goal with |- ?G => let G' := eval unfold faf in G in change_no_check G' end). replace (Z.to_nat (nf2 - m + Z.of_nat i)) with (Z.to_nat (nf2 - m) + i)%nat by lia. symmetry. apply nth_error_nth. exact Hnth. }
                (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, T_PC, PC_SZ in G in change_no_check G' end). rewrite Ek.
                pose proof (RDch i Hi) as RCh.
                replace (at_ pc (16 + 4 * Z.of_nat i)) with (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * Z.of_nat i)) in RCh
                  by (apply bv_eq; rewrite at_u by lia; rewrite Upc, u_Z2bv by lia; lia).
                apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros j Hj; left; apply XLT; cbn in Hj; clear - Hj Hc Hi Hm; lia | exact RCh].
             ++ exact SBM.
             ++ exact MIm.
          -- intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. fold RIz. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). exact F.
          -- rewrite (QAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             apply PAG. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros Xi. repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]). exact Xi.
          -- rewrite (QAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             apply PAG. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros Xi. repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]). exact Xi.
  Qed.


  Theorem refill_fail_K :
    forall (K : config -> Prop), liftable K ->
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR s0R s1R g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 8)) ->
    gf_inv bt M c spR raR s0R s1R (Z_to_bv 64 0x50a0c) g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ->
    getr regs 2 = at_ (at_ spR (-32)) (-128) -> getr regs 8 = Z_to_bv 64 (reginfo bt c) -> getr regs 19 = Z_to_bv 64 (2 ^ 61) -> getr regs 10 = Z_to_bv 64 0 ->
    (CEIL + 160 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        RepX bt X st Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> (reginfo bt c <= U a < reginfo bt c + 8) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 0 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = s0R -> getr r' 9 = s1R -> s_regs r' g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 -> getr r' 4 = getr regs 4 -> getr r' 3 = getr regs 3 ->
        K (mkCfg (mkst r' raR M' rom) mdl')) ->
    K (mkCfg (mkst regs (0x50d88%bv : word) M rom) mdl).
  Proof using BT_ia BT_segs.
    intros K LK c st Lc FF M rom mdl regs spR raR s0R s1R g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 Hc W RX HALT XRI (LOCKED & GSL & RSL) H2 H8 H19 H10 Hsp HretR CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (_ & _ & _ & _ & _ & _ & _ & _ & E9 & E10 & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & _ & _ & S1 & S2 & S3).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16).
    pose proof RP as (_ & _ & _ & R4 & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _).
    destruct (R4 c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GW) _]. rewrite BT_segs in GW. destruct R14 as (Bw1 & Bw2 & _).
    unfold KSPACE, PG, AS_HEAPLO in *. set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    assert (WRI : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
    set (spG := at_ spR (-32)) in *. assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). left. exact Hr. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (HOFF : forall lo0 n, (forall z, lo0 <= z < lo0 + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo0 n).
    { intros lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    set (Mr := mrestrict Hd M).
    assert (RSP : forall (b : word) (k : Z) v, U b = U spR \/ U b = U spG -> -128 <= k -> k + 8 <= 0 -> rdn ASEGS M (at_ b k) 8 = Some v -> rdn ASEGS Mr (at_ b k) 8 = Some v).
    { intros b k v Hb K0 K1 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia]. }
    destruct (asan_mask_rdn Mr) as (msk & RMSK).
    assert (RETG : ret_ok (Z_to_bv 64 0x50a0c)) by (apply ret_ok_lit; [lia | reflexivity]).
    destruct (gfp_fail Mr rom spG (Z_to_bv 64 0x50a0c) g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 msk RIz 0
                ltac:(rewrite UspG; lia) RETG ltac:(rewrite UspG, ERI; split; [lia | split; [lia | exact (ri_mod8 _ c S16)]]) ltac:(lia)
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite rdn_mrestrict; [exact LOCKED | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHri; lia])
                RMSK
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite store_ok_mrestrict; [apply (writableZ_sok M RIz (RIz + 128)); [exact WRI | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                                             | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHri; lia])
                (RSP spG (-8) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-8) (Z_to_bv 64 0x50a0c) ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-16) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-16) g0 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-24) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-24) g1 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-32) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-32) g2 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-40) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-40) g3 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-48) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-48) g4 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-56) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-56) g5 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-64) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-64) g6 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-72) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-72) g7 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-80) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-80) g8 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-88) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-88) g9 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-96) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-96) g10 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                (RSP spG (-104) _ ltac:(right; reflexivity) ltac:(lia) ltac:(lia) (GSL (-104) g11 ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 15)))
                regs eq_refl H2 H8 H19 H10)
      as (r1 & RUN1 & P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & PAG).
    set (M2r := wbytes Mr (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0))) in *.
    assert (RS2 : forall (k : Z) v, -24 <= k -> k + 8 <= 0 -> rdn ASEGS M (at_ spR k) 8 = Some v -> rdn ASEGS M2r (at_ spR k) 8 = Some v).
    { intros k v K0 K1 Hr. (lazymatch goal with |- ?G => let G' := eval unfold M2r in G in change_no_check G' end). rewrite rdn_wbytes_out; [apply RSP; [left; reflexivity | lia | lia | exact Hr]
        | rewrite length_N_to_le_bytes, u_Z2bv, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    replace (Z_to_bv 64 0x50a0c : word) with (0x50a0c%bv : word) in RUN1 by (apply bv_eq; reflexivity).
    destruct (rf_ret0 M2r rom spR raR s0R s1R r1 P2 P10 HretR
                (RS2 (-8) _ ltac:(lia) ltac:(lia) (RSL (-8) raR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto)))
                (RS2 (-16) _ ltac:(lia) ltac:(lia) (RSL (-16) s0R ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto)))
                (RS2 (-24) _ ltac:(lia) ltac:(lia) (RSL (-24) s1R ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto))))
      as (r2 & RUN2 & Q10 & Q2 & Q1 & Q8 & Q9 & QAG).
    set (M' := wbytes M (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0))).
    assert (EM : M2r = mrestrict Hd M').
    { (lazymatch goal with |- ?G => let G' := eval unfold M2r, M', Mr in G in change_no_check G' end). apply wbytes_mrestrict; rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [lia | apply HOFF; intros z Hz; apply NHri; lia]. }
    rewrite EM in RUN1, RUN2.
    assert (OUTM : forall a : word, (U a < RIz \/ RIz + 8 <= U a) -> M' a = M a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply MemsetLibF.MemSplit.wbytes_outside; [rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact Ha]. }
    apply (LK Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs _ r2 _ M M' rom mdl (msteps_trans _ _ _ _ RUN1 RUN2)); [ | exact HALT | apply lazy_cover_HID | exact Bw1 | exact Bw2 | ].
    - intros a Ha. apply OUTM. pose proof (hid_true_off Hd a RIz 8 Ha ltac:(apply HOFF; intros z Hz; apply NHri; lia)). lia.
    - intros mdlm SBM MIm.
      assert (FOOTM : forall a : word, M' a <> M a -> (RIz <= U a < RIz + 8) /\ M' a <> None).
      { intros a Ha. assert (IN : (RIz <= U a < RIz + 8) \/ (U a < RIz \/ RIz + 8 <= U a)) by (clear; lia).
        destruct IN as [IN | O1]; [| exfalso; exact (Ha (OUTM a O1))]. split; [exact IN|].
        (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply wbytes_grows. destruct (WRI (U a) ltac:(lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT r2 M' mdlm); [ | exact SBM | exact MIm | exact FOOTM | exact Q10 | exact Q2 | exact Q1 | exact Q8 | exact Q9
                               | (lazymatch goal with |- ?G => let G' := eval unfold s_regs in G in change_no_check G' end); rewrite !QAG by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); repeat split; assumption | | ].
      + apply (repx_unlock c st Lc FF M M' mdl mdlm Hc W RX XRI FOOTM); [ | exact MIm | exact SBM].
        (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
      + rewrite (QAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
        apply PAG. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros Xi. repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]). exact Xi.
      + rewrite (QAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
        apply PAG. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros Xi. repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]). exact Xi.
  Qed.
End L3.
End WithCeil.
