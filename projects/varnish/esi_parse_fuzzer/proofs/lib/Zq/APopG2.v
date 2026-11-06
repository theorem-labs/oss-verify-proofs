(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMalmys ATransp ABudget ACover ASecB2.
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
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize in *.

(* [comment removed for export] *)
Definition vm5_same (h h' : VmMaps) : Prop :=
  vm_maps h' = vm_maps h /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h /\ vm_init_sp h' = vm_init_sp h /\ vm_mmap_base h' = vm_mmap_base h.
Lemma vm5_same_refl : forall h, vm5_same h h. Proof. intros h. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma vm5_same_trans : forall h1 h2 h3, vm5_same h1 h2 -> vm5_same h2 h3 -> vm5_same h1 h3.
Proof. (intros h1 h2 h3; (first [ intro dR_11; dand5 dR_11 as A1 A2 A3 A4 A5 | intros (A1 & A2 & A3 & A4 & A5) ]); (first [ intro dR_12; dand5 dR_12 as B1 B2 B3 B4 B5 | intros (B1 & B2 & B3 & B4 & B5) ])). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence. Qed.
(* [comment removed for export] *)
Lemma vm5_same_commit : forall flags addr n md, vm5_same (m_vmmaps md) (m_vmmaps (commit_model flags addr n false md)).
Proof. intros. rewrite commit_model_vmmaps. unfold commit_vmmaps. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

Section Commit.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : pa_ainv A m md.
  (* [comment removed for export] *)
  Variables (md3 : Model) (H3 HL3 : hull) (E3 : Z) (beg len : Z).   (* [comment removed for export] *)
  Context {reg3 : Z -> region}.                                          (* [comment removed for export] *)
  Hypothesis V3 : vm5_same (m_vmmaps md) (m_vmmaps md3).
  Hypothesis LED3 : aledger_ AL_pboth (a_pl A) reg3 (a_sec A) md3.
  Hypothesis HH3 : m_halted md3 = None.
  Hypothesis HI3 : MInv H3 HL3 E3 md3.
  (* [comment removed for export] *)
  Hypothesis RANGE : a_sb A <= beg /\ beg + len <= a_sb A + kSpaceSize + 4096 /\ beg mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len.
  Local Notation h := (m_vmmaps md).
  Local Notation begw := (wz beg).
  Local Notation lenw := (wz len).
  Local Notation md4 := (commit_model (wz 50) begw lenw false md3).
  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let LIMv : vm_limit h = p_tlim (a_pl A).   (* [comment removed for export] *) Proof. (first [ pose proof ((ai_ledger _ _ _ _ _ _ _ AI)) as dR_1; dand6 dR_1 as _ _ _ _ L5 _ | destruct (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & L5 & _) ]). exact L5. Qed.
  Let TOP : alloc_top h = alloc_ceiling. Proof. exact (ai_ceil _ _ _ _ _ _ _ AI). Qed.
  Let SBF : a_sb A = space_beg_of (a_b6 A) /\ a_sb A mod 0x10000 = 0 /\ kHighMemBeg <= a_b6 A /\ a_b6 A < a_sb A <= a_b6 A + 0x10000 /\ a_sb A + kSpaceSize + 4096 <= alloc_ceiling.
  Proof. exact (sb_facts A W0). Qed.
  Let BEGW : bv_unsigned begw = beg. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.
  Let LENW : bv_unsigned lenw = len. Proof. apply unsigned_lit. pose proof SBF. pose proof RANGE. kung_all. lia. Qed.
  Let TOP3 : alloc_top (m_vmmaps md3) = alloc_ceiling.
  Proof. destruct V3 as (_ & _ & _ & E4 & _). unfold alloc_top in *. rewrite E4. exact TOP. Qed.
  Let LIM3 : vm_limit (m_vmmaps md3) = p_tlim (a_pl A). Proof. destruct V3 as (_ & _ & E3' & _). rewrite E3'. exact LIMv. Qed.

  Lemma c_gate : fixed_gate md3 begw len.
  Proof. unfold fixed_gate. rewrite TOP3, BEGW. pose proof SBF. pose proof RANGE. unfold page_size. kung_all. lia. Qed.

  Lemma c_contained : region_free (vm_reserved (m_vmmaps md3)) begw lenw = true /\ map_contains (vm_maps (m_vmmaps md3)) begw lenw = true.
  Proof.
    destruct V3 as (E1 & E2 & _). rewrite E1, E2. pose proof SBF as (S1 & S2 & S3 & S4 & S5). pose proof RANGE as (R1 & R2 & R3 & R4 & R5).
    destruct (ai_ledger _ _ _ _ _ _ _ AI) as (L1 & _).
    split.
    - apply (pa_cover_reserved_free A m md beg len AI); kung_all; lia.
    - unfold map_contains. apply existsb_exists. exists (wz (a_b6 A), wz kSpaceReserve). split.
      + apply L1. unfold big_maps_. cbn. left. reflexivity.
      + cbn [fst snd]. rewrite BEGW, LENW, !unsigned_lit by (kung_all; lia). apply andb_true_iff. split; apply Z.leb_le; kung_all; lia.
  Qed.

  Lemma c_budget : E3 + len + hull_bytes HL3 <= p_tlim (a_pl A) -> mmap_fixed_rw_budget_ok (wz 50) md3 begw lenw = true.
  Proof.
    intros BR. apply (gate_fixed_rw_budget_ok H3 HL3 E3 (wz 50) begw lenw md3 HI3).
    - pose proof c_gate as (G1 & _). rewrite LENW. exact G1.
    - exact (proj2 c_contained).
    - right. rewrite LENW, LIM3. clear - BR. lia.
  Qed.
  Lemma c_minv : E3 + len + hull_bytes HL3 <= p_tlim (a_pl A) -> MInv H3 HL3 (E3 + len) md4.
  Proof.
    intros BR. rewrite <- LENW at 1. apply (MInv_commit_rw H3 HL3 E3 (wz 50) begw lenw md3 HI3 mmap_noreserve_b_50).
    - pose proof c_gate as (G1 & _). rewrite LENW. exact G1.
    - exact (proj2 c_contained).
    - rewrite LENW, LIM3. clear - BR. lia.
  Qed.
  Lemma c_vm5 : vm5_same h (m_vmmaps md4).
  Proof. exact (vm5_same_trans _ _ _ V3 (vm5_same_commit _ _ _ md3)). Qed.
  Lemma c_halted : m_halted md4 = None.
  Proof. rewrite commit_model_halted. exact HH3. Qed.
  Lemma c_ceil : alloc_top (m_vmmaps md4) = alloc_ceiling.
  Proof. (first [ pose proof (c_vm5) as dR_2; dand5 dR_2 as _ _ _ E _ | pose proof c_vm5 as (_ & _ & _ & E & _) ]). unfold alloc_top in *. rewrite E. exact TOP. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma c_lzfree_new : lazy_free (m_vm_lazy md4) beg (beg + len).
  Proof. pose proof (MInv_commit_lazy_free H3 HL3 E3 (wz 50) begw lenw false md3 HI3 mmap_noreserve_b_50) as X. rewrite BEGW, LENW in X. exact X. Qed.
  Lemma c_lzfree_old : forall lo hi, lazy_free (m_vm_lazy md3) lo hi -> lazy_free (m_vm_lazy md4) lo hi.
  Proof. intros lo hi Z0. exact (lazy_free_commit (wz 50) begw lenw false md3 lo hi mmap_noreserve_b_50 (minv_lazy_nw HI3) Z0). Qed.
  (* [comment removed for export] *)
  Lemma c_ledger : aledger_ AL_pboth (a_pl A) reg3 (a_sec A) md4.
  Proof.
    destruct LED3 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & [L8 L9]). (first [ pose proof (c_vm5) as dR_4; dand5 dR_4 as C1 C2 C3 C4 C5 | pose proof c_vm5 as (C1 & C2 & C3 & C4 & C5) ]). destruct V3 as (V1 & V2 & V4 & V5 & V6).
    pose proof SBF as (S1 & S2 & S3 & S4 & S5). pose proof RANGE as (R1 & R2 & R3 & R4 & R5).
    unfold aledger_. cbv zeta. rewrite C1, C2, C3. rewrite V1, V2, V4 in *.
    split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [| split]]]]]].
    - apply Forall_forall. intros sc Hsc. pose proof (proj1 (Forall_forall _ _) L6 sc Hsc) as EM.
      pose proof (bm_nth_fixed A) as (E0 & _).
      assert (APT : cs_map sc + map_size (cs_n sc) <= a_b6 A \/ a_b6 A + kSpaceReserve <= cs_map sc).
      { apply In_nth_error' in Hsc as [i Hi]. pose proof (bm_sep A (15 + i) 0 _ _ _ _ W0 (bm_nth_sec A i sc Hi) E0 ltac:(lia)). unfold a_b6 in *. lia. }
      assert (SCB : 0 <= cs_map sc /\ 0 < map_size (cs_n sc) /\ cs_map sc + map_size (cs_n sc) <= 2^47).
      { (first [ pose proof ((sec_chunk_bounds A sc W0 Hsc)) as dR_5; dand5 dR_5 as B1 _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W0 Hsc) as (B1 & _ & B3 & B4 & _) ]). apply app_facts in B3.
        pose proof (map_size_ge (cs_n sc)). unfold kMaxPrimaryUser in *. lia. }
      apply eager_map_commit; [exact (minv_noacc_nw HI3)| exact (minv_lazy_nw HI3)| | | exact EM].
      + unfold entry_nowrap, Ledger.lo, Ledger.hi. cbn [fst snd]. rewrite BEGW, LENW. clear - RANGE SBF CE. kung_all. lia.
      + rewrite BEGW, LENW, !unsigned_lit by lia. clear - APT SCB RANGE SBF. kung_all. lia.
    - apply cuts_covered_commit_contained; [exact (minv_noacc_nw HI3)| exact (minv_lazy_nw HI3)| | exact (proj2 c_contained)| exact L7].
      unfold entry_nowrap, Ledger.lo, Ledger.hi. cbn [fst snd]. rewrite BEGW, LENW. clear - RANGE SBF CE. kung_all. lia.
    - (* [comment removed for export] *)
      destruct L8 as [N1 N2]. split; [split; [exact (noacc_free_commit_rw _ _ _ _ _ _ (minv_noacc_nw HI3) N1)| exact (noacc_free_commit_rw _ _ _ _ _ _ (minv_noacc_nw HI3) N2)]|].
      (* [comment removed for export] *)
      destruct L9 as (Z1 & Z2 & Z3). split; [exact (c_lzfree_old _ _ Z1)|]. split; [exact (c_lzfree_old _ _ Z2)|].
      intros c Hc. destruct (Z3 c Hc) as [ZU ZF]. split; apply c_lzfree_old; assumption.
  Qed.
  Lemma c_cover : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md4).
  Proof.
    (first [ pose proof (c_vm5) as dR_6; dand3 dR_6 as C1 C2 _ | pose proof c_vm5 as (C1 & C2 & _) ]). apply (acover_vmmaps _ _ _ h); [exact C1| exact C2| exact (ai_cover _ _ _ _ _ _ _ AI)].
  Qed.
  Lemma c_amd : amd_frame md md3 -> amd_frame md md4.
  Proof.
    intros F3. (first [ pose proof (c_vm5) as dR_7; dand5 dR_7 as C1 C2 C3 C4 C5 | pose proof c_vm5 as (C1 & C2 & C3 & C4 & C5) ]). pose proof c_halted as HH4.
    (first [ pose proof ((commit_model_nonvm (wz 50) begw lenw false md3)) as dR_8; dand6 dR_8 as B1 B2 B3 B4 B5 B6 | pose proof (commit_model_nonvm (wz 50) begw lenw false md3) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
    unfold amd_frame in *. rewrite C2, C3, C4, C5, B1, B2, B3, B4, B5, B6.
    destruct V3 as (V1 & V2 & V4 & V5 & V6). rewrite V2, V4, V5, V6 in F3.
    decompose [and] F3. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Commit.

(* [comment removed for export] *)
Section Sbm.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : pa_ainv A m md.
  Variables (md3 md5 : Model).
  Context {reg3 : Z -> region}.   (* [comment removed for export] *)
  Hypothesis V3 : vm5_same (m_vmmaps md) (m_vmmaps md3).
  Hypothesis LED3 : aledger_ AL_pboth (a_pl A) reg3 (a_sec A) md3.
  Hypothesis HH3 : m_halted md3 = None.
  Hypothesis F3 : amd_frame md md3.
  Hypothesis SB5 : same_but_materialized md3 md5.
  Lemma s_model :
    vm5_same (m_vmmaps md) (m_vmmaps md5) /\ aledger_ AL_pboth (a_pl A) reg3 (a_sec A) md5 /\ acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md5) /\
    alloc_top (m_vmmaps md5) = alloc_ceiling /\ amd_frame md md5 /\ m_halted md5 = None.
  Proof.
    pose proof (same_but_materialized_vmmaps _ _ SB5) as V. pose proof V3 as (C1 & C2 & C3 & C4 & C5).
    split; [rewrite V; exact V3|].
    split; [exact (aledger_sbm _ _ _ _ _ _ SB5 LED3)|].
    split; [rewrite V; apply (acover_vmmaps _ _ _ (m_vmmaps md)); [exact C1| exact C2| exact (ai_cover _ _ _ _ _ _ _ AI)]|].
    split; [rewrite V; unfold alloc_top in *; rewrite C4; exact (ai_ceil _ _ _ _ _ _ _ AI)|].
    split.
    - (first [ pose proof ((same_but_materialized_frame _ _ SB5)) as dR_10; dand18 dR_10 as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | pose proof (same_but_materialized_frame _ _ SB5) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
      unfold amd_frame in *. rewrite X1, X2, X4, X5, X6, X7, X8, X17.
      decompose [and] F3. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
    - rewrite (same_but_materialized_halted _ _ SB5). exact HH3.
  Qed.
End Sbm.

(* [comment removed for export] *)
Lemma entry_model {Clg : Ceiling} {DR : DepotRep} : forall A m md, pa_ainv A m md ->
  vm5_same (m_vmmaps md) (m_vmmaps md) /\ aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) md /\ acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md) /\
  alloc_top (m_vmmaps md) = alloc_ceiling /\ amd_frame md md /\ m_halted md = None.
Proof.
  intros A m md AI. split; [apply vm5_same_refl|]. split; [exact (ai_ledger _ _ _ _ _ _ _ AI)|]. split; [exact (ai_cover _ _ _ _ _ _ _ AI)|].
  split; [exact (ai_ceil _ _ _ _ _ _ _ AI)|]. split; [| exact (ai_halted _ _ _ _ _ _ _ AI)].
  unfold amd_frame. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. exact (ai_halted _ _ _ _ _ _ _ AI).
Qed.
