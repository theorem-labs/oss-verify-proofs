(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ABudget ACover AFreeT AFreeB6 ANodijx APgGeo AFreeX1 AFreeX2.

Module AFreeX4.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.EvtAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ABudget ACover AFreeB6 ANodijx APgGeo AFreeX1 AFreeX2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.

Section Chain.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (i : nat).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQB : kQuarantineMaxSize < n0.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).

  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).
  #[warnings="-notation-for-abbreviation"] Local Notation len := (a8_pend (p - 6144) (map_size n0) - a8_pbeg (p - 6144)).

  Let NQ' : kMaxPrimaryUser < n0. Proof. unfold kQuarantineMaxSize, kMaxPrimaryUser in *. lia. Qed.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A (aview_of (pa_hull A) m). Proof. exact (conj W (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Let S0 : In (CS h n0) chunks. Proof. exact (sk_In A m md p n0 AI HL NQ'). Qed.
  Let LG : aledger_ AL_pboth P (a_reg A) (a_sec A) md. Proof. exact (ai_ledger _ _ _ _ _ _ _ AI). Qed.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma len_facts : 0 < len /\ pbeg + len = pend /\ 0 < pbeg /\ pend <= kHighMemBeg /\ pbeg mod 4096 = 0 /\ len mod 4096 = 0 /\
                    bv_unsigned (wz pbeg) = pbeg /\ bv_unsigned (wz len) = len /\ bv_unsigned (wz h) = h /\ bv_unsigned (wz msz) = msz /\
                    0x60a000 <= h /\ h + msz <= alloc_ceiling /\ 0 < msz /\ h mod 4096 = 0 /\ msz mod 4096 = 0 /\
                    page_round_up_Z len = len /\ page_round_up_Z msz = msz.
  Proof.
    (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_1; dand15 dR_1 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
    (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_2; dand11 dR_2 as HLO HAL MSZ MSZAL HHI _ _ _ _ H5 _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & HHI & _ & _ & _ & _ & H5 & _) ]). pose proof alloc_ceiling_val as CE.
    assert (LM : len mod 4096 = 0) by (rewrite <- Zminus_mod_idemp_l, M3, <- Zminus_mod_idemp_r, M2; reflexivity).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (kung_all; lia); try (apply unsigned_lit; kung_all; lia); try assumption.
    - unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full len 4096) as Q. rewrite LM, Z.add_0_r in Q.
      set (q := len / 4096) in *. clearbody q. clear -Q. rewrite Q. replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia.
      rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
    - unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full msz 4096) as Q. rewrite MSZAL, Z.add_0_r in Q.
      set (q := msz / 4096) in *. clearbody q. clear -Q. rewrite Q. replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia.
      rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fsm_shadow_map : exists bS sS, In (bS, sS) (big_maps A) /\ bS <= pbeg /\ pend <= bS + sS /\ 0 <= bS /\ bS + sS <= 2^47.
  Proof.
    (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_3; dand15 dR_3 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_4; dand5 dR_4 as _ _ E2 E3 _ | pose proof (bm_nth_fixed A) as (_ & _ & E2 & E3 & _) ]).
    destruct SIDE as [(X1 & X2 & X3)|(X1 & X2 & X3)].
    - exists kHighShadowMapBeg, kHighShadowMapSize. split; [eapply nth_error_In; exact E2|]. kung_all. unfold kHighShadowMapSize. lia.
    - exists kLowShadowMapBeg, 0x10000000. split; [eapply nth_error_In; exact E3|]. pose proof (pg_facts (sh h)) as (A1 & _). kung_all. lia.
  Qed.

  Section Models.
    Variables (md1 md2 md3 md4 md5 : Model).
    Hypothesis SB1 : same_but_materialized md md1.
    Hypothesis MD2 : md2 = madvise_model (wz pbeg) (wz len) md1.   (* [comment removed for export] *)
    Hypothesis SB3 : same_but_materialized md2 md3.
    Hypothesis MD4 : md4 = munmap_modelL (wz h) (wz msz) md3.
    Hypothesis SB5 : same_but_materialized md4 md5.
    Hypothesis HI1 : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
    Hypothesis HI3 : exists Hx HLx Ex, MInv Hx HLx Ex md3.   (* [comment removed for export] *)

    Lemma vmmaps1 : m_vmmaps md1 = m_vmmaps md.  Proof. exact (same_but_materialized_vmmaps _ _ SB1). Qed.
    Lemma vmmaps3 : m_vmmaps md3 = m_vmmaps md.
    Proof. rewrite (same_but_materialized_vmmaps _ _ SB3), MD2, madvise_model_vmmaps, vmmaps1. reflexivity. Qed.
    Lemma vmmaps5 : m_vmmaps md5 = munmap_vmmaps (m_vmmaps md) (wz h) (wz msz).
    Proof. rewrite (same_but_materialized_vmmaps _ _ SB5), MD4, munmap_modelL_vmmaps, vmmaps3. reflexivity. Qed.
    Lemma maps3 : vm_maps (m_vmmaps md3) = vm_maps (m_vmmaps md).
    Proof. rewrite vmmaps3. reflexivity. Qed.
    Lemma maps5 : vm_maps (m_vmmaps md5) = map_remove (vm_maps (m_vmmaps md)) (wz h).
    Proof. rewrite vmmaps5. reflexivity. Qed.
    Lemma resv5 : vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps md) /\ vm_reserved (m_vmmaps md3) = vm_reserved (m_vmmaps md) /\ vm_reserved (m_vmmaps md1) = vm_reserved (m_vmmaps md).
    Proof. rewrite vmmaps5, vmmaps3, vmmaps1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma fsm_in_maps : In (wz h, wz msz) (vm_maps (m_vmmaps md)).
    Proof. destruct LG as (L1 & _). apply L1. eapply nth_error_In. exact (bm_nth_sec A _ _ NTH). Qed.
    Lemma fsm_has : map_has (vm_maps (m_vmmaps md3)) (wz h) (wz msz) = true.
    Proof. rewrite maps3. apply In_map_has. exact fsm_in_maps. Qed.

    Lemma fsm_eager : eager_map (wz h) (wz msz) md3.
    Proof.
      destruct LG as (_ & _ & _ & _ & _ & L6 & _). pose proof (proj1 (Forall_forall _ _) L6 _ S0) as EM. cbn [cs_map cs_n] in EM.
      apply (eager_map_sbm _ _ md2 md3 SB3). rewrite MD2. apply (eager_map_sbm _ _ md1 _ (madvise_same_but_materialized _ _ md1)).
      exact (eager_map_sbm _ _ md md1 SB1 EM).
    Qed.

    Lemma fsm_ceil : alloc_top (m_vmmaps md5) = alloc_ceiling /\ alloc_top (m_vmmaps md3) = alloc_ceiling /\ alloc_top (m_vmmaps md1) = alloc_ceiling.
    Proof.
      pose proof (ai_ceil _ _ _ _ _ _ _ AI) as TOP. unfold alloc_top in *. rewrite vmmaps5, vmmaps3, vmmaps1. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact TOP.
    Qed.

    Lemma fsm_frame : amd_frame md md5.
    Proof.
      pose proof (same_but_materialized_frame _ _ SB1) as F1. pose proof (same_but_materialized_frame _ _ SB3) as F3. pose proof (same_but_materialized_frame _ _ SB5) as F5.
      pose proof (same_but_materialized_frame _ _ (madvise_same_but_materialized (wz pbeg) (wz len) md1)) as C2. rewrite <- MD2 in C2.
      pose proof (munmap_modelL_nonvm (wz h) (wz msz) md3) as C4. rewrite <- MD4 in C4.
      pose proof (asI_minv A m md AI) as [_ HH].
      unfold amd_frame. rewrite vmmaps5. cbn [vm_limit vm_reserved vm_mmap_base vm_init_sp munmap_vmmaps commit_vmmaps].
      (first [ dand18 F1 as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 _ | destruct F1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & _) ]).
      (first [ dand18 F3 as B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16 B17 _ | destruct F3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & _) ]).
      (first [ dand18 F5 as D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14 D15 D16 D17 _ | destruct F5 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & _) ]).
      (first [ dand18 C2 as C21 C22 C23 C24 C25 C26 C27 C28 C29 C210 C211 C212 C213 C214 C215 C216 C217 _ | destruct C2 as (C21 & C22 & C23 & C24 & C25 & C26 & C27 & C28 & C29 & C210 & C211 & C212 & C213 & C214 & C215 & C216 & C217 & _) ]). (first [ dand6 C4 as C41 C42 C43 C44 C45 C46 | destruct C4 as (C41 & C42 & C43 & C44 & C45 & C46) ]).
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try congruence.
      rewrite D17, MD4, <- munmap_model_modelL, munmap_model_halted. rewrite B17, MD2. rewrite madvise_model_halted. rewrite A17. exact HH.
    Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma fsm_shadow_noacc : region_free (vm_noaccess (m_vmmaps md)) (wz pbeg) (wz len) = true.
    Proof.
      (first [ pose proof (len_facts) as dR_13; dand9 dR_13 as F1 F2 F3 F4 F5 F6 U1 U2 _ | pose proof len_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & _) ]).
      (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_14; dand15 dR_14 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
      destruct LG as (_ & _ & _ & _ & _ & _ & _ & (N1 & N2) & _).   (* [comment removed for export] *)
      destruct SIDE as [(X1 & X2 & X3)|(X1 & X2 & X3)].
      - apply (region_free_sub _ (wz kHighShadowMapBeg) (wz kHighShadowMapSize) _ _ N2); rewrite ?U1, ?U2, !unsigned_lit by (kung_all; unfold kHighShadowMapSize; lia);
          kung_all; unfold kHighShadowMapSize; lia.
      - pose proof (pg_facts (sh h)) as (A1 & _).
        apply (region_free_sub _ (wz kLowShadowMapBeg) (wz (kShadowGapBeg - kLowShadowMapBeg)) _ _ N1); rewrite ?U1, ?U2, !unsigned_lit by (kung_all; lia);
          kung_all; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma fsm_madvise_args : forall ms, ms_gpr ms 0 = wz pbeg -> ms_gpr ms 1 = wz len -> ms_gpr ms 2 = wz 4 -> madvise_args_ok ms md1.
    Proof.
      intros ms R0 R1 R2. (first [ pose proof (len_facts) as dR_15; dand17 dR_15 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ _ PL _ | pose proof len_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _ & _ & PL & _) ]).
      apply madvise_args_ok_intro; cbv zeta; rewrite ?R0, ?R1, ?R2, ?U1, ?U2, ?PL, ?vmmaps1; unfold page_size, two_pow_64.
      - exact F5.
      - intros E; apply (f_equal bv_unsigned) in E; rewrite U2, unsigned_lit in E by lia; clear -E F1; lia.
      - reflexivity.
      - clear -F2 F4; kung_all; lia.
      - pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & _). (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_16; dand4 dR_16 as _ _ _ SD | pose proof (sk_shr A m md p n0 AI HL NQ') as (_ & _ & _ & SD) ]).
        apply (pa_cover_reserved_free A m md pbeg len AI); [clear -G1 SD; kung_all; lia| exact F1| kung_all; lia].
      - (first [ dex2 fsm_shadow_map as bS sS; dand5 fsm_shadow_map as Hin B1 B2 B3 B4 | dand7 fsm_shadow_map as bS sS Hin B1 B2 B3 B4 | destruct fsm_shadow_map as (bS & sS & Hin & B1 & B2 & B3 & B4) ]). destruct LG as (L1 & _).
        unfold map_contains. apply existsb_exists. exists (wz bS, wz sS). split; [exact (L1 _ _ Hin)|].
        cbn [fst snd]. rewrite !unsigned_lit by (kung_all; lia). rewrite ?U1. apply andb_true_iff. rewrite !Z.leb_le. lia.
      - exact fsm_shadow_noacc.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma fsm_lazy3 : m_vm_lazy md3 = m_vm_lazy md.
    Proof. rewrite (sbm_lazy _ _ SB3), MD2, madvise_model_lazy, (sbm_lazy _ _ SB1). reflexivity. Qed.
    Lemma fsm_lazy_free5 : forall lo hi, lazy_free (m_vm_lazy md) lo hi -> lazy_free (m_vm_lazy md5) lo hi.
    Proof.
      intros lo hi Z0. destruct HI3 as (Hx & HLx & Ex & MI3). rewrite (sbm_lazy _ _ SB5), MD4.
      apply (lazy_free_munmap_MInv Hx HLx Ex _ _ md3 lo hi MI3). rewrite fsm_lazy3. exact Z0.
    Qed.
    Lemma fsm_ledger : aledger_ AL_pboth P (a_reg A) (sec_remove (a_sec A) i) md5.
    Proof.
      pose proof LG as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). (first [ pose proof (len_facts) as dR_18; dand14 dR_18 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ | pose proof len_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _) ]).
      destruct HI3 as (Hx & HLx & Ex & MI3). pose proof alloc_ceiling_val as CE.
      unfold aledger_. cbv zeta. rewrite maps5. (first [ dand3 resv5 as RV5 RV3 RV1 | destruct resv5 as (RV5 & RV3 & RV1) ]). rewrite RV5.
      split; [| split; [exact L2| split; [exact L3| split; [exact L4| split; [| split; [| split]]]]]].
      - (* [comment removed for export] *)
        intros b s Hin. unfold map_remove. apply filter_In. split.
        + apply L1. unfold big_maps_ in Hin |- *. cbn [sec_remove sr_chunks] in Hin. apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right].
          apply in_map_iff in Hin as (c & <- & Hc). apply in_map_iff. exists c. split; [reflexivity|]. apply (chunks'_in_iff A m md (CS h n0) i AI NTH) in Hc as [Hc _]. exact Hc.
        + cbn [fst]. unfold bv_eqb. rewrite U3. apply Bool.negb_true_iff. apply Z.eqb_neq.
          assert (BS : 0 <= b /\ 0 < s /\ b + s <= 2^47).
          { apply (bm_bounds A b s W). unfold big_maps, big_maps_ in Hin |- *. cbn [sec_remove sr_chunks] in Hin. apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right].
            apply in_map_iff in Hin as (c & <- & Hc). apply in_map_iff. exists c. split; [reflexivity|]. apply (chunks'_in_iff A m md (CS h n0) i AI NTH) in Hc as [Hc _]. exact Hc. }
          rewrite unsigned_lit by lia.
          unfold big_maps_ in Hin. cbn [sec_remove sr_chunks] in Hin. apply in_app_iff in Hin as [Hin|Hin].
          * (* [comment removed for export] *)
            destruct (In_nth_error' _ _ Hin) as [j Hj].
            assert (JL : (j < 15)%nat) by (apply nth_error_Some_lt in Hj; exact Hj).
            assert (Hj' : nth_error (big_maps A) j = Some (b, s)) by (unfold big_maps, big_maps_; rewrite nth_error_app1 by (cbn; lia); exact Hj).
            pose proof (bm_sep A _ _ _ _ _ _ W Hj' (bm_nth_sec A _ _ NTH) ltac:(lia)) as D. cbn [cs_map cs_n] in D. lia.
          * apply in_map_iff in Hin as (c & E & Hc). injection E as <- <-. apply (chunks'_in_iff A m md (CS h n0) i AI NTH) in Hc as [Hc NEc].
            destruct (In_nth_error' _ _ Hc) as [j Hj].
            pose proof (sk_sep_chunks A m md AI j i c (CS h n0) Hj NTH ltac:(intros ->; rewrite NTH in Hj; injection Hj as E; exact (NEc (eq_sym E)))) as D.
            cbn [cs_map cs_n] in D. (first [ pose proof ((sk_chunk A m md AI c Hc)) as dR_20; dand5 dR_20 as _ _ _ C4 _ | pose proof (sk_chunk A m md AI c Hc) as (_ & _ & _ & C4 & _) ]). unfold apart in D. lia.
      - rewrite vmmaps5. cbn. exact L5.
      - apply Forall_forall. intros c Hc. cbn [sec_remove sr_chunks] in Hc. apply (chunks'_in_iff A m md (CS h n0) i AI NTH) in Hc as [Hc _].
        pose proof (proj1 (Forall_forall _ _) L6 c Hc) as EM.
        apply (eager_map_sbm _ _ md4 md5 SB5). rewrite MD4. apply (eager_map_munmap_MInv Hx HLx Ex _ _ _ _ md3 MI3).
        apply (eager_map_sbm _ _ md2 md3 SB3). rewrite MD2. apply (eager_map_sbm _ _ md1 _ (madvise_same_but_materialized _ _ md1)).
        exact (eager_map_sbm _ _ md md1 SB1 EM).
      - apply (cuts_covered_sbm md4 md5 SB5). rewrite MD4. apply (cuts_covered_munmap_MInv Hx HLx Ex _ _ md3 MI3); [rewrite maps3; exact fsm_in_maps| rewrite U4; lia|].
        apply (cuts_covered_sbm md2 md3 SB3). rewrite MD2. apply (cuts_covered_sbm md1 _ (madvise_same_but_materialized _ _ md1)).
        exact (cuts_covered_sbm md md1 SB1 L7).
      - (* [comment removed for export] *)
        destruct L8 as [N1 N2].
        split; [split; apply (noacc_free_sbm _ _ md4 md5 SB5); rewrite MD4; apply noacc_free_munmap; try exact (minv_noacc_nw MI3);
          apply (noacc_free_sbm _ _ md2 md3 SB3); rewrite MD2; apply noacc_free_madvise; apply (noacc_free_sbm _ _ md md1 SB1); assumption|].
        (* [comment removed for export] *)
        destruct L9 as (Z1 & Z2 & Z3). pose proof fsm_lazy_free5 as T.
        split; [exact (T _ _ Z1)|]. split; [exact (T _ _ Z2)|]. intros c Hc. destruct (Z3 c Hc) as [ZU ZF]. split; apply T; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma fsm_cover : acover_ LPA P (sec_remove (a_sec A) i) (m_vmmaps md5).
    Proof.
      (first [ pose proof ((ai_cover _ _ _ _ _ _ _ AI)) as dR_21; dand3 dR_21 as (fog & FL & FS & COV & F1' & F2') C3 RSV | pose proof (ai_cover _ _ _ _ _ _ _ AI) as ((fog & FL & FS & COV & F1' & F2') & C3 & RSV) ]). (first [ pose proof (len_facts) as dR_22; dand14 dR_22 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ | pose proof len_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _) ]).
      pose proof (asI_minv A m md AI) as [HMI _]. pose proof alloc_ceiling_val as CE.
      unfold acover_. rewrite maps5. destruct resv5 as (RV5 & _). rewrite RV5. split; [| split; [| exact RSV]].
      - exists fog. split; [exact FL|]. split; [exact FS|]. split; [| split; [| exact F2']].
        + intros e He. apply map_remove_In in He as [He NE]. pose proof (COV e He) as X. cbv zeta in X |- *.
          destruct X as [X|[X|X]]; [| right; left; exact X| right; right; exact X]. left.
          unfold big_maps_ in X |- *. cbn [sec_remove sr_chunks]. apply in_app_iff in X as [X|X]; apply in_or_app; [left; exact X| right].
          apply in_map_iff in X as (c & E & Hc). apply in_map_iff. exists c. split; [exact E|]. apply (chunks'_in_iff A m md (CS h n0) i AI NTH). split; [exact Hc|].
          intros ->. apply NE. cbn [cs_map cs_n] in E. injection E as E1 E2. apply bv_eq. rewrite U3. symmetry. exact E1.
        + intros bs Hbs. unfold map_remove. apply filter_In. split; [exact (F1' bs Hbs)|]. cbn [fst]. unfold bv_eqb. rewrite U3. apply Bool.negb_true_iff. apply Z.eqb_neq.
          (first [ pose proof ((proj1 (Forall_forall _ _) FS bs Hbs)) as dR_23; dand3 dR_23 as S1 S2 S3 | pose proof (proj1 (Forall_forall _ _) FS bs Hbs) as (S1 & S2 & S3) ]). rewrite unsigned_lit by lia.
          (* [comment removed for export] *)
          intros E. pose proof (minv_nooverlap HMI) as NO.
          pose proof (F1' bs Hbs) as INf. pose proof fsm_in_maps as INm.
          assert (NEQ : (wz (fst bs), wz (snd bs)) <> (wz h, wz msz)).
          { intros EE. pose proof (f_equal (fun x => bv_unsigned (snd x)) EE) as E2. cbn [snd] in E2. rewrite unsigned_lit in E2 by lia. rewrite U4 in E2.
            (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_24; dand9 dR_24 as _ _ _ _ _ _ _ N6 _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (_ & _ & _ & _ & _ & _ & _ & N6 & _) ]). clear -E2 N6 NQB S2. unfold kQuarantineMaxSize in NQB. lia. }
          destruct (nooverlap_In_In _ _ _ NO INf INm) as [D|D]; [exact (NEQ D)|].
          unfold Ledger.hi, Ledger.lo in D. cbn [fst snd] in D. rewrite ?U3, ?U4 in D. rewrite !unsigned_lit in D by lia. rewrite ?U3, ?U4 in D.
          (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_25; dand4 dR_25 as _ _ MSZ _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (_ & _ & MSZ & _) ]). lia.
      - unfold map_remove. apply filter_In. split; [exact C3|]. cbn [fst]. unfold bv_eqb. rewrite U3, unsigned_lit by (kung_all; lia). apply Bool.negb_true_iff. apply Z.eqb_neq.
        pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & _). (first [ pose proof ((aobj_facts _ _ HLO)) as dR_26; dand5 dR_26 as _ NN _ _ SIDE | pose proof (aobj_facts _ _ HLO) as (_ & NN & _ & _ & SIDE) ]). clear -SIDE NN. kung_all. lia.
    Qed.
  End Models.
End Chain.
End AFreeX4.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeWD.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeGD0.AFreeX4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_mu : forall W (m m' : mem) A cs,
  rw_cells rsegs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[WFc B] WR] MU D. split; [split; [exact WFc|]|].
  - eapply bytes_at_transport; [exact B| exact MU|]. rewrite cells_bytes_length by exact WFc. exact D.
  - (first [ dand3 WR as H0 H1 WW | destruct WR as (H0 & H1 & WW) ]). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    assert (E : m' (wa (A + i)) = m (wa (A + i))).
    { apply MU. rewrite wa_unsigned by lia. apply (disjoint_outside _ _ _ _ D). lia. }
    unfold wview. rewrite E. exact (WW i Hi).
Qed.

(* [comment removed for export] *)

Lemma u64arr_mu : forall W (m m' : mem) A ws,
  u64arr rsegs m A ws -> munch W m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
  intros W m m' A ws [B WR] MU D. split.
  - eapply bytes_at_transport; [exact B| exact MU|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact D.
  - (first [ dand3 WR as H0 H1 WW | destruct WR as (H0 & H1 & WW) ]). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    assert (E : m' (wa (A + i)) = m (wa (A + i))).
    { apply MU. rewrite wa_unsigned by lia. apply (disjoint_outside _ _ _ _ D). lia. }
    unfold wview. rewrite E. exact (WW i Hi).
Qed.

Lemma stk_mu : forall W (m m' : mem) lo hi,
  stk rsegs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk rsegs m' lo hi.
Proof.
  (intros W m m' lo hi; (first [ intro dR_26; dand3 dR_26 as H0 H1 S | intros (H0 & H1 & S) ]); intros MU D). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  assert (E : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. apply (disjoint_outside _ _ _ _ D). lia. }
  destruct (S a Ha) as [X Y]. unfold wview, mrd in *. rewrite E. exact (conj X Y).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_agp : forall (m m' : mem) A cs,
  rw_cells rsegs m A cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (A + i)) = m (wz (A + i))) -> rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[WFc B] WR] AG. split; [split; [exact WFc|]|].
  - eapply bytes_at_agree_gen; [exact B|]. rewrite cells_bytes_length by exact WFc. exact AG.
  - (first [ dand3 WR as H0 H1 WW | destruct WR as (H0 & H1 & WW) ]). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    unfold wview. unfold wa. rewrite (AG i Hi). exact (WW i Hi).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section ImgAgree.
  Context {Clg : Ceiling}.
  Variables (m m' : mem).
  Hypothesis AGq : forall x, img_quiet x -> m' (wz x) = m (wz x).

  Lemma ro_cells_agq : forall A cs, ro_cells rsegs m A cs ->
    (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_quiet (A + i)) -> ro_cells rsegs m' A cs.
  Proof. intros A cs C R. apply (ro_cells_ag m m' A cs C). intros i Hi. apply AGq. exact (R i Hi). Qed.

  Lemma poison_consts_agq : poison_consts m -> poison_consts m'.
  Proof.
    intros PC. pose proof PC as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    unfold poison_consts, CF in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      (eapply ro_cells_agq; [eassumption|]; intros i Hi; cbn [cells_size csize Nat.add] in Hi; unfold img_quiet; clear -Hi; lia).
  Qed.

  Lemma a8_consts_agq : forall canary, a8_consts m canary -> a8_consts m' canary.
  Proof.
    intros canary AC. pose proof AC as AC'. (first [ dand10 AC' as C144 C219 C244 C260 CSG CSC CLP CSL CDG CDY | destruct AC' as (C144 & C219 & C244 & C260 & CSG & CSC & CLP & CSL & CDG & CDY) ]).
    unfold a8_consts, CF, SSP_GOT, SSP_CELL, LIBC_PAGESIZE, SEALED_GOT, DYING_GOT, DYING in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      (eapply ro_cells_agq; [eassumption|]; intros i Hi; cbn [cells_size csize Nat.add] in Hi; unfold img_quiet; clear -Hi; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma thread_cells_agq : forall tp tsd ctx thr, thread_cells m tp tsd ctx thr -> tp = Z_to_bv 64 TP ->
    0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000 ->
    (forall i, 0 <= i < 8 -> m' (wz (ctx + 152 + i)) = m (wz (ctx + 152 + i))) ->
    thread_cells m' tp tsd ctx thr.
  Proof.
    intros tp tsd ctx thr TC TPE TSDL AGc. pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    unfold thread_cells. rewrite TPL in *.
    split; [eapply ro_cells_agq; [exact Cini|]; intros i Hi; cbn in Hi; unfold img_quiet; clear -Hi; lia|].
    split; [eapply ro_cells_agq; [exact Ckey|]; intros i Hi; cbn in Hi; unfold img_quiet; clear -Hi; lia|].
    split; [eapply ro_cells_agq; [exact Ctsd|]; intros i Hi; cbn in Hi; unfold img_quiet; clear -Hi; lia|].
    split; [eapply ro_cells_agq; [exact Cctx|]; intros i Hi; cbn in Hi; unfold img_quiet; clear -Hi TSDL; lia|].
    split; [apply (ro_cells_ag m m' _ _ Cthr2); intros i Hi; cbn in Hi; apply AGc; exact Hi| exact Bnds].
  Qed.
End ImgAgree.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Chain.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (i : nat).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQB : kQuarantineMaxSize < n0.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).

  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).
  #[warnings="-notation-for-abbreviation"] Local Notation len := (a8_pend (p - 6144) (map_size n0) - a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation H0p := (AFreeX2.H0p A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation H1 := (AFreeX2.H1 A p n0 i).
  #[warnings="-notation-for-abbreviation"] Local Notation H2 := (AFreeX2.H2 A p n0 i).

  Let NQ' : kMaxPrimaryUser < n0. Proof. unfold kQuarantineMaxSize, kMaxPrimaryUser in *. lia. Qed.

  (* [comment removed for export] *)
  Variables (mv0' mv1' mv2' : mem).
  Hypothesis CL0 : forall x, hidc H0p x = true -> mv0' x = None.
  Hypothesis CL1 : forall x, hidc H1 x = true -> mv1' x = None.
  Hypothesis CL2 : forall x, hidc H2 x = true -> mv2' x = None.

  (* [comment removed for export] *)
  Definition rm1 : mem := munrestrict (hidc H0p) m mv0'.
  Definition rm2 : mem := apply_zeros rm1 [(wz pbeg, wz len)].
  Definition mv1 : mem := mrestrict (hidc H1) rm2.
  Definition rm3 : mem := munrestrict (hidc H1) rm2 mv1'.
  Definition rm4 : mem := apply_unmaps rm3 [(wz h, wz msz)].
  Definition mv2 : mem := mrestrict (hidc H2) rm4.
  Definition rm5 : mem := munrestrict (hidc H2) rm4 mv2'.

  Lemma lenU : bv_unsigned (wz pbeg) = pbeg /\ bv_unsigned (wz len) = len /\ bv_unsigned (wz h) = h /\ bv_unsigned (wz msz) = msz /\
               0 < len /\ pbeg + len = pend /\ 0 < pbeg /\ pend <= kHighMemBeg /\ 0x60a000 <= h /\ h + msz <= alloc_ceiling /\ 0 < msz.
  Proof.
    (first [ pose proof ((len_facts A m md p n0 AI HL NQB)) as dR_13; dand14 dR_13 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ | pose proof (len_facts A m md p n0 AI HL NQB) as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _) ]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.

  Lemma rm2_spec : forall x, rm2 x = if in_range pbeg len x then Some (Z_to_bv 8 0) else rm1 x.
  Proof.
    intros x. (first [ pose proof (lenU) as dR_14; dand9 dR_14 as U1 U2 _ _ F1 F2 F3 F4 _ | pose proof lenU as (U1 & U2 & _ & _ & F1 & F2 & F3 & F4 & _) ]). pose proof alloc_ceiling_val as CE. unfold rm2.
    apply (apply_zeros_spec rm1 pbeg len x); clear -F1 F2 F3 F4 CE; kung_all; lia.
  Qed.
  Lemma rm4_spec : forall x, rm4 x = if in_range h msz x then None else rm3 x.
  Proof.
    intros x. (first [ pose proof (lenU) as dR_15; dand11 dR_15 as _ _ U3 U4 _ _ _ _ H5 HHI MP | pose proof lenU as (_ & _ & U3 & U4 & _ & _ & _ & _ & H5 & HHI & MP) ]). pose proof alloc_ceiling_val as CE. unfold rm4.
    apply (apply_unmaps_spec rm3 h msz x); clear -H5 HHI MP CE; lia.
  Qed.

  Lemma in_range_iff : forall a n x, in_range a n x = true <-> a <= bv_unsigned x < a + n.
  Proof. intros a n x. unfold in_range. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
  Lemma in_range_false : forall a n x, in_range a n x = false <-> ~ (a <= bv_unsigned x < a + n).
  Proof. intros a n x. rewrite <- in_range_iff. destruct (in_range a n x); split; congruence. Qed.

  (* [comment removed for export] *)
  Lemma T01 : munch [(pbeg, pend)] mv0' mv1.
  Proof.
    intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. (first [ pose proof (lenU) as dR_16; dand7 dR_16 as _ _ _ _ F1 F2 _ | pose proof lenU as (_ & _ & _ & _ & F1 & F2 & _) ]).
    unfold mv1, mrestrict. destruct (hidc H1 x) eqn:E1.
    - (* [comment removed for export] *)
      symmetry. destruct (hidc H0p x) eqn:E0; [exact (CL0 x E0)|]. exfalso.
      unfold hidc in E0, E1. apply Bool.negb_false_iff in E0. apply Bool.negb_true_iff in E1.
      pose proof (vis_H1 A m md p n0 i AI HL NQB (bv_unsigned x) E0 ltac:(lia)). congruence.
    - rewrite rm2_spec. destruct (in_range pbeg len x) eqn:R; [apply in_range_iff in R; exfalso; lia|].
      unfold rm1, munrestrict. unfold hidc in E1 |- *. apply Bool.negb_false_iff in E1.
      rewrite (vis_H1_H0p A m md p n0 i AI HL NQB (bv_unsigned x) E1). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma T12 : munch [(h, h + msz)] mv1' mv2.
  Proof.
    intros x Hx. cbn [outside] in Hx. destruct Hx as [Hx _].
    unfold mv2, mrestrict. destruct (hidc H2 x) eqn:E2.
    - symmetry. destruct (hidc H1 x) eqn:E1; [exact (CL1 x E1)|]. exfalso.
      unfold hidc in E1, E2. apply Bool.negb_false_iff in E1. apply Bool.negb_true_iff in E2.
      pose proof (vis_H2 A p n0 i (bv_unsigned x) E1 ltac:(lia)). congruence.
    - rewrite rm4_spec. destruct (in_range h msz x) eqn:R; [apply in_range_iff in R; exfalso; lia|].
      unfold rm3, munrestrict. unfold hidc in E2 |- *. apply Bool.negb_false_iff in E2.
      rewrite (vis_H2_H1 A p n0 i (bv_unsigned x) E2). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma hop01 : forall a, 0 <= a < 2^64 -> ~ (pbeg <= a < pend) -> mv1 (wz a) = mv0' (wz a).
  Proof. intros a Ha N. apply T01. rewrite unsigned_lit by exact Ha. cbn [outside]. split; [exact N| exact I]. Qed.
  Lemma hop12 : forall a, 0 <= a < 2^64 -> ~ (h <= a < h + msz) -> mv2 (wz a) = mv1' (wz a).
  Proof. intros a Ha N. apply T12. rewrite unsigned_lit by exact Ha. cbn [outside]. split; [exact N| exact I]. Qed.

  (* [comment removed for export] *)
  Lemma mv1_mid : forall a, pbeg <= a < pend -> hidc H1 (wz a) = false -> mv1 (wz a) = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha V1. (first [ pose proof (lenU) as dR_17; dand9 dR_17 as _ _ _ _ F1 F2 F3 F4 _ | pose proof lenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & _) ]). pose proof alloc_ceiling_val as CE.
    unfold mv1, mrestrict. rewrite V1. rewrite rm2_spec.
    destruct (in_range pbeg len (wz a)) eqn:R; [reflexivity|]. apply in_range_false in R. rewrite unsigned_lit in R by (clear -Ha F2 F3 F4 CE; kung_all; lia).
    exfalso. clear -R Ha F2. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma vis_edges : forall a, (sh h <= a < pbeg \/ pend <= a < sh h + msz / 8) -> in_hullb H2 a = true.
  Proof.
    intros a Ha. unfold AFreeX2.H2. cbn [in_hullb existsb]. unfold AFreeX2.e1, AFreeX2.e2, in_ivb. cbn [fst snd].
    destruct Ha as [Ha|Ha]; [apply Bool.orb_true_iff; left| apply Bool.orb_true_iff; right; apply Bool.orb_true_iff; left]; apply andb_true_iff; rewrite Z.leb_le, Z.ltb_lt; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mv1_clean : forall x, hidc H1 x = true -> mv1 x = None.
  Proof. intros x E. unfold mv1, mrestrict. rewrite E. reflexivity. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rm5_view : mrestrict (hidc H2) rm5 = mv2'.
  Proof. unfold rm5. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL2. Qed.

  (* [comment removed for export] *)
  Lemma mv2_none_map : forall a, h <= a < h + msz -> mv2 (wz a) = None.
  Proof.
    intros a Ha. (first [ pose proof (lenU) as dR_18; dand11 dR_18 as _ _ _ _ _ _ _ _ H5 HHI _ | pose proof lenU as (_ & _ & _ & _ & _ & _ & _ & _ & H5 & HHI & _) ]). pose proof alloc_ceiling_val as CE.
    unfold mv2, mrestrict. destruct (hidc H2 (wz a)); [reflexivity|]. rewrite rm4_spec.
    destruct (in_range h msz (wz a)) eqn:R; [reflexivity|]. apply in_range_false in R. rewrite unsigned_lit in R by lia. exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma T01_NN : forall x, ~ (pbeg <= bv_unsigned x < pend) -> mv0' x <> None -> mv1 x <> None.
  Proof. intros x Hx NN. rewrite (T01 x ltac:(cbn [outside]; split; [exact Hx| exact I])). exact NN. Qed.
  Lemma T12_NN : forall x, ~ (h <= bv_unsigned x < h + msz) -> mv1' x <> None -> mv2 x <> None.
  Proof. intros x Hx NN. rewrite (T12 x ltac:(cbn [outside]; split; [exact Hx| exact I])). exact NN. Qed.

  (* [comment removed for export] *)
  Lemma MI1 : mem_inv rsegs mv0' -> mem_inv rsegs mv1.
  Proof.
    intros MI x b E. unfold mv1, mrestrict in E. destruct (hidc H1 x) eqn:E1; [discriminate|].
    rewrite rm2_spec in E. destruct (in_range pbeg len x) eqn:R.
    - apply in_range_iff in R. (first [ pose proof (lenU) as dR_19; dand9 dR_19 as _ _ _ _ F1 F2 F3 F4 _ | pose proof lenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & _) ]). pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & _).
      (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_20; dand4 dR_20 as _ _ _ SD | pose proof (sk_shr A m md p n0 AI HL NQ') as (_ & _ & _ & SD) ]).
      apply pa_ro_addr_false. clear -R F2 G1 SD. kung_all. lia.
    - unfold rm1, munrestrict, hidc in E. unfold hidc in E1. apply Bool.negb_false_iff in E1.
      rewrite (vis_H1_H0p A m md p n0 i AI HL NQB (bv_unsigned x) E1) in E. exact (MI x b E).
  Qed.
  Lemma MI2 : mem_inv rsegs mv1' -> mem_inv rsegs mv2.
  Proof.
    intros MI x b E. unfold mv2, mrestrict in E. destruct (hidc H2 x) eqn:E2; [discriminate|].
    rewrite rm4_spec in E. destruct (in_range h msz x) eqn:R; [discriminate|].
    unfold rm3, munrestrict, hidc in E. unfold hidc in E2. apply Bool.negb_false_iff in E2.
    rewrite (vis_H2_H1 A p n0 i (bv_unsigned x) E2) in E. exact (MI x b E).
  Qed.

  (* [comment removed for export] *)
  Lemma rm5_mid : forall a, pbeg <= a < pend -> in_hullb H2 a = false -> rm5 (wz a) = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha V2. (first [ pose proof (lenU) as dR_21; dand11 dR_21 as _ _ _ _ F1 F2 F3 F4 H5 HHI MP | pose proof lenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & H5 & HHI & MP) ]). pose proof alloc_ceiling_val as CE.
    pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & _). (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_22; dand4 dR_22 as _ _ _ SD | pose proof (sk_shr A m md p n0 AI HL NQ') as (_ & _ & _ & SD) ]).
    assert (U : bv_unsigned (wz a) = a) by (apply unsigned_lit; clear -Ha F2 F3 F4; kung_all; lia).
    assert (V1 : in_hullb H1 a = false).
    { destruct (in_hullb H1 a) eqn:E; [| reflexivity]. rewrite (vis_H2 A p n0 i a E) in V2; [discriminate|]. clear -Ha F2 F4 G1 SD H5 HHI CE. kung_all. lia. }
    unfold rm5, munrestrict, hidc. rewrite U, V2. cbn [negb]. rewrite rm4_spec.
    destruct (in_range h msz (wz a)) eqn:R; [apply in_range_iff in R; rewrite U in R; exfalso; clear -R Ha F2 F4 G1 SD H5 HHI CE; kung_all; lia|].
    unfold rm3, munrestrict, hidc. rewrite U, V1. cbn [negb]. rewrite rm2_spec.
    destruct (in_range pbeg len (wz a)) eqn:R2; [reflexivity|]. apply in_range_false in R2. rewrite U in R2. exfalso. clear -R2 Ha F2. lia.
  Qed.
  Lemma rm5_hid : forall a, 0 <= a < 2^64 -> in_hullb H0p a = false -> ~ (h <= a < h + msz) -> rm5 (wz a) = m (wz a).
  Proof.
    intros a Ha V0 NM. (first [ pose proof (lenU) as dR_23; dand9 dR_23 as _ _ _ _ F1 F2 F3 F4 _ | pose proof lenU as (_ & _ & _ & _ & F1 & F2 & F3 & F4 & _) ]).
    assert (U : bv_unsigned (wz a) = a) by (apply unsigned_lit; exact Ha).
    assert (V1 : in_hullb H1 a = false).
    { destruct (in_hullb H1 a) eqn:E; [| reflexivity]. rewrite (vis_H1_H0p A m md p n0 i AI HL NQB a E) in V0. discriminate. }
    assert (V2 : in_hullb H2 a = false).
    { destruct (in_hullb H2 a) eqn:E; [| reflexivity]. rewrite (vis_H2_H1 A p n0 i a E) in V1. discriminate. }
    unfold rm5, munrestrict, hidc. rewrite U, V2. cbn [negb]. rewrite rm4_spec.
    destruct (in_range h msz (wz a)) eqn:R; [apply in_range_iff in R; rewrite U in R; exfalso; exact (NM R)|].
    unfold rm3, munrestrict, hidc. rewrite U, V1. cbn [negb]. rewrite rm2_spec.
    destruct (in_range pbeg len (wz a)) eqn:R2.
    - (* [comment removed for export] *) exfalso. apply in_range_iff in R2. rewrite U in R2.
      (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_24; dand7 dR_24 as G1 G2 G3 G4 G5 G6 _ | pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]).
      unfold AFreeX2.H0p in V0. cbn [in_hullb existsb] in V0. apply Bool.orb_false_iff in V0 as [_ V0]. apply Bool.orb_false_iff in V0 as [V0 _].
      unfold in_ivb in V0. cbn [fst snd] in V0. apply Bool.andb_false_iff in V0. rewrite Z.leb_gt, Z.ltb_ge in V0. clear -V0 R2 F2 G1 G6. lia.
    - unfold rm1, munrestrict, hidc. rewrite U, V0. reflexivity.
  Qed.
  Lemma rm5_vis : forall x, hidc H2 x = false -> rm5 x = mv2' x.
  Proof. intros x E. unfold rm5, munrestrict. rewrite E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma vis_same : forall x, ~ (sh h <= x < sh h + msz / 8) -> ~ (h <= x < h + msz) -> in_hullb H2 x = in_hullb H0p x.
  Proof.
    intros x N1 N2. (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_25; dand7 dR_25 as G1 G2 G3 G4 G5 G6 _ | pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & G2 & G3 & G4 & G5 & G6 & _) ]).
    unfold AFreeX2.H0p, AFreeX2.H2. cbn [in_hullb existsb].
    set (RR := existsb (in_ivb x) (AFreeX2.REST A i)). clearbody RR. unfold AFreeX2.e1, AFreeX2.e2, in_ivb. cbn [fst snd].
    destruct RR; [rewrite !Bool.orb_true_r; reflexivity|]. rewrite !Bool.orb_false_r.
    clear -N1 N2 G1 G5 G6.
    destruct (Z.leb_spec (sh h) x); destruct (Z.ltb_spec x pbeg); destruct (Z.leb_spec pend x); destruct (Z.ltb_spec x (sh h + msz / 8));
      destruct (Z.leb_spec h x); destruct (Z.ltb_spec x (h + msz)); cbn [andb orb]; try reflexivity; exfalso; lia.
  Qed.
End Chain.
