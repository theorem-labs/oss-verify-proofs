(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BazyRestrict BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BW_DepotFrame BllocWalkKit BW_Efs BS_Rta BS_LcDealloc BG_Malloc BG_Malloc2 BG_WFHit BG_RefillModel BG_Refill2 BG_MallocCold BG_FreeModel BG_WFFree BG_RepQ BG_RepQFacts BG_RepQFacts2 BG_RecycleModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BerfLia.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Lemma carved_not_31Q : forall st XC XB c a, WFQ st XC XB -> carved st c a -> c <> 31.
Proof.
  intros st XC XB c a W (Hc & CS & LO & _ & HI) E. subst c.
  pose proof W as (W1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W14 & _).
  pose proof (ro_alloc_le _ _ (proj1 (W1 31 ltac:(unfold kNumClasses; tlia)))) as LE. rewrite W14 in LE.
  pose proof (ro_alloc_nonneg _ _ (proj1 (W1 31 ltac:(unfold kNumClasses; tlia)))) as GE.
  pose proof (class_size_table_facts 31 ltac:(tlia)) as (C0 & _). tlia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section CDPost.
  Variables (s : ast) (m0 m2 : mem) (XC XB : list Z) (c p : Z) (st' : astate) (LZ SZ : list (word * word)) (AL2 lo spv : Z).
  Variables (q0 q1 q2 q3 : word) (k mfa' : Z).
  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let CA := a_cache s.
  Let sb := a_sb s.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let pc := get_pc st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let cnt := pc_count pc. Let chunks := pc_chunks pc. Let csz := class_size c.
  Let kn := Z.to_nat k. Let moved := firstn kn chunks. Let kept := skipn kn chunks.
  Let cnt1 := cnt - k. Let nf' := nf + k.
  Let cp := addr_to_compact st c p.
  Let s2 := mkAst st' TH CTX (a_fsb s) LZ SZ (a_Zr s) AL2 (a_top s) (a_bot s).
  Let W : list ivl := lcd_W lo spv P CA cnt1 RI (FA s c) TH nf mfa mfa'.

  Let W2 : list ivl := W ++ [(p, p + csz); (sh p, sh p + csz / 8)].
  Let Po := outside W2.

  Hypothesis RQ : AREPQ s XC (p :: XB) m0.
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis INIT : as_cache_inited st = true.
  Hypothesis CLS : class_of_addr st p = c.

  Hypothesis KR : (k = 0 /\ mfa' = mfa /\ cnt < max_count c) \/ (k = max_count c / 2 /\ cnt = max_count c /\ mfa' = rta_mfa nf k mfa).
  Hypothesis FROOM : mfa' <= kFreeArraySize.

  Hypothesis WQ' : WFQ st' XC XB.
  Hypothesis Fsb : as_space_beg st' = as_space_beg st. Hypothesis Fpa : as_ptr_array st' = as_ptr_array st.
  Hypothesis Fsec : as_sec st' = as_sec st. Hypothesis Fch : as_chunks st' = as_chunks st.
  Hypothesis Ftq : as_tq st' = as_tq st. Hypothesis Fgq : as_gq st' = as_gq st. Hypothesis Fnr : as_n_reserved st' = as_n_reserved st.
  Hypothesis Fci : as_cache_inited st' = true. Hypothesis Fii : as_internal_init st' = as_internal_init st.
  Hypothesis Fqx : as_qmax st' = as_qmax st. Hypothesis Fqn : as_qmin st' = as_qmin st. Hypothesis Fqc : as_qcache st' = as_qcache st.
  Hypothesis Fpc_c : get_pc st' c = mkPC (cnt1 + 1) (cp :: kept).
  Hypothesis Fpc_o : forall c0, 0 <= c0 -> c0 <> c -> get_pc st' c0 = get_pc st c0.
  Hypothesis Frg_c : get_region st' c = mkRegion mu au nf' (moved ++ fl) mfa'.
  Hypothesis Frg_o : forall c0, 0 <= c0 -> c0 <> c -> get_region st' c0 = get_region st c0.

  Hypothesis ES : SZ = (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else []) ++ a_S s.

  Hypothesis LO : aceil <= lo.
  Hypothesis AG : agree_on Po m0 m2.
  Hypothesis WM : wmono asegs m0 m2.

  Hypothesis JK : junk m2 p csz.
  Hypothesis PS : poisoned m2 p (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic.
  Hypothesis PC1' : rw_cells asegs m2 P [C4 (wz (cnt1 + 1)); C4 (wz (max_count c))].
  Hypothesis PC3' : u32arr asegs m2 (P + 16) (wlist (rev (cp :: kept))).
  Hypothesis PC4' : stk asegs m2 (P + 16 + 4 * (cnt1 + 1)) (P + 80).
  Hypothesis QST' : rw_cells asegs m2 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis TST' : stk asegs m2 (TH + 2800) (TH + 3168).
  Hypothesis RI' : rw_cells asegs m2 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf'); C8 (wz mfa'); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis RST' : stk asegs m2 (RI + 69) (RI + 128).
  Hypothesis FARR' : u32arr asegs m2 (FA s c) (wlist (rev (moved ++ fl))).
  Hypothesis FAJ' : stk asegs m2 (FA s c + 4 * nf') (FA s c + mfa').
  Hypothesis POIf' : poisoned m2 (FA s c + mfa) (Z.to_nat ((mfa' - mfa) / 8)) kAsanHeapLeftRedzoneMagic.

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st XC (p :: XB). Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let OKQ : placed_ok s /\ WFQ (a_st s) XC (p :: XB). Proof. exact (conj PL WQ). Qed.
  Let MEM : ARmem s m0. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
  Let RO : region_ok st c. Proof. exact (WFQ_region st _ _ c WQ ltac:(clear - HC; unfold kNumClasses in *; tlia)). Qed.
  Let CO : cache_ok st c. Proof. exact (WFQ_cache st _ _ c WQ ltac:(clear - HC; unfold kNumClasses in *; tlia)). Qed.
  Let CV : carved st c p. Proof. rewrite <- CLS. exact (WFQ_xb st _ _ p WQ ltac:(left; reflexivity)). Qed.

  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.
  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 7241728 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ 7241728 <= a_pa s /\ a_pa s + 8388608 <= aceil
            /\ 1 <= c <= 30 /\ CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c
            /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
            /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' <= 536870912 /\ 0 <= k <= cnt /\ cnt - k <= 15 /\ 4 * nf' <= mfa' /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384
            /\ 32 <= csz <= 65536 /\ RB s c <= p /\ p + csz <= RB s c + au.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    placed. fold TH CTX sb in T2, T3, X2, X3, S2, S3.
    apply akobj_env in T2; [| unfold kPageSize; clear; tlia]. apply aapp_env in X2; [| clear; tlia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; tlia].
    pose proof (class_size_table_facts c ltac:(clear - HC; unfold kNumClasses in *; tlia)) as (C1 & C2 & C3 & C4 & C5 & C6). specialize (C3 ltac:(clear - HC; tlia)). specialize (C5 ltac:(clear - HC; tlia)).
    pose proof (ro_numfreed _ _ RO) as Q1. pose proof (ro_fa_le _ _ RO) as Q2. pose proof (ro_fa_bound _ _ RO) as Q3. pose proof (ro_alloc_nonneg _ _ RO) as Q4.
    pose proof (ro_alloc_le _ _ RO) as Q5. pose proof (ro_mapped_bound _ _ RO) as Q6. fold st r nf mfa au mu fl in Q1, Q2, Q3, Q4, Q5, Q6.
    pose proof (co_count _ _ CO) as Y1. pose proof (co_bound _ _ CO) as Y2. fold st pc cnt chunks in Y1, Y2. rewrite INIT in Y2.
    pose proof (carved_not_31Q st _ _ c p WQ CV) as C31.
    destruct CV as (_ & _ & V3 & V4 & V5). fold st r au in V5. change (region_beg st c) with (RB s c) in V3, V5.
    assert (NF0 : 0 <= nf) by (rewrite Q1; unfold zlen; clear; tlia).
    assert (KB : (0 <= k <= cnt /\ cnt - k <= 15) /\ mfa <= mfa' /\ 4 * nf' <= mfa').
    {
      unfold nf'. unfold zlen in Y1. destruct KR as [(K0 & M0 & LT)|(Kn & EC & Mn)].
      - rewrite K0, M0. clear - Q2 Y1 LT C4. rewrite Z.add_0_r. repeat split; tlia.
      - rewrite Mn, Kn. rewrite EC. unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize.
        destruct (Z.leb_spec (4 * (nf + max_count c / 2)) mfa); clear - Q2 C4 C5 C6 NF0 H; Z.div_mod_to_equations; repeat split; tlia. }
    unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve, kFreeArraySize, kUserMapSize, kFreeArrayOffset, kNumClasses in *.
    assert (GEO : CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384).
    { unfold P, CA, RI, TH, sb, a_cache, a_ri, OT_CACHE, kSpaceSize, RB, FA, a_sb. rewrite free_array_base_eq, region_beg_eq. unfold kFreeArrayOffset. repeat split; reflexivity. }
    clear - LO T2 T3 X2 X3 S2 S3 P2 P3 HC C31 GEO Q2 Q3 Q4 Q5 Q6 Y2 NF0 KB FROOM C1 C3 C4 V3 V5.
    repeat match goal with |- _ /\ _ => split end; try tlia.
  Qed.
  Let BANDS : hidden ((TH + 4096 <= 65536 \/ (7241728 <= TH /\ TH + 4096 <= 2147446784) \/ 17594333495296 <= TH)
                   /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)).
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    pose proof PL as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _). fold TH in T2. fold CTX in X2.
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    pose proof (aapp_lit _ _ P2) as L. unfold kPtrArrayReserve in L. exact L.
  Qed.
  Tactic Notation "bands_as" simple_intropattern(pat) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [pat]).

  Let ALN : (FA s c + mfa) mod 8 = 0 /\ 8 * ((mfa' - mfa) / 8) = mfa' - mfa /\ mfa mod 8 = 0 /\ mfa' mod 8 = 0 /\ sb mod 4096 = 0 /\ p mod 16 = 0 /\ 8 * (csz / 8) = csz.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & EFA & _).
    pose proof PL as (Y1 & _). fold sb in Y1. pose proof (ro_fa_mod _ _ RO) as M1. fold st r mfa in M1.
    pose proof (class_size_table_facts c ltac:(clear - HC; unfold kNumClasses in *; tlia)) as (_ & C2 & C3 & _). specialize (C3 ltac:(clear - HC; tlia)). fold csz in C2, C3.
    destruct CV as (_ & _ & _ & V4 & _). change (region_beg st c) with (RB s c) in V4. fold csz in V4.
    assert (M2 : mfa' mod 8 = 0).
    { destruct KR as [(_ & M0 & _)|(Kn & _ & Mn)]; [rewrite M0; clear - M1; unfold kFreeArrayMapSize in M1; Z.div_mod_to_equations; tlia|].
      rewrite Mn, Kn. unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize. destruct (4 * (nf + max_count c / 2) <=? mfa); [clear - M1; unfold kFreeArrayMapSize in M1; Z.div_mod_to_equations; tlia|].
      rewrite Z.mul_comm, <- Zmult_mod_distr_r || idtac. clear. Z.div_mod_to_equations. tlia. }
    unfold kFreeArrayMapSize in M1. clear - ERB EFA Y1 M1 M2 C2 C3 V4. Z.div_mod_to_equations. nia.
  Qed.

  Let PNC : forall y, In y (carved_addr_list st) -> y <> p.
  Proof. clear - WQ. intros y Hy E. apply (NoDup_app_disjoint _ _ y (WFQ_carved _ _ _ WQ) Hy). rewrite E. left. reflexivity. Qed.
  Let PNF : forall c0 x, 0 <= c0 < kNumClasses -> In x (rg_free_array (get_region st c0)) \/ In x (pc_chunks (get_pc st c0)) -> compact_to_addr st c0 x <> p.
  Proof. clear - WQ PNC. intros c0 x Hc0 Hin. apply PNC. rewrite (carved_addr_list_eq s). apply in_app_iff. left. exact (in_seg_freeQ s c0 x Hc0 Hin). Qed.
  Let PNI : forall x, In x (chunk_list st) -> ch_primary x = true -> ch_alloc_beg x <> p.
  Proof. clear - WQ PNC. intros x Hx PX. apply PNC. rewrite (carved_addr_list_eq s). apply in_app_iff. right. apply in_app_iff. left. exact (in_seg_inuseQ s x Hx PX). Qed.
  Let PNB : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> qb_addr b <> p.
  Proof. clear - WQ PNC. intros b Hb. apply PNC. rewrite (carved_addr_list_eq s). apply in_app_iff. right. apply in_app_iff. right. exact (in_seg_batchQ s b Hb). Qed.

  Let SHP : 0x2008fff7000 <= sh p /\ sh p + csz / 8 <= sh aceil /\ sh aceil < 0x10007fff8000
            /\ 0x2008fff7000 <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh aceil.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'. pose proof BND as B. pose proof ALN as (_ & A2 & _ & _ & _ & _ & A7).
    clear - B A2 A7. acb. unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. tlia.
  Qed.

  Lemma ZC_gen : forall a, a < lo ->
    ~ (P <= a < P + 4) -> ~ (P + 16 + 4 * cnt1 <= a < P + 20 + 4 * cnt1) -> ~ (TH + 2768 <= a < TH + 3168) ->
    ~ (RI <= a < RI + 88) -> ~ (FA s c + 4 * nf <= a < FA s c + mfa') -> ~ (sh (FA s c + mfa) <= a < sh (FA s c + mfa) + (mfa' - mfa) / 8) ->
    ~ (p <= a < p + csz) -> ~ (sh p <= a < sh p + csz / 8) ->
    outside W2 a.
  Proof.
    clear. intros a H0 N1 N2 N3 N4 N5 N6 N7 N8. unfold W2, W, lcd_W. cbn [outside app]. unfold a_cache in *. fold TH in N1, N2, N3 |- *.
    repeat split; try exact I; clear - H0 N1 N2 N3 N4 N5 N6 N7 N8; unfold CA, P, a_cache, OT_CACHE in *; tlia.
  Qed.

  Lemma ZC_obj : forall X Y a, (Y <= ALOWSH_LO \/ AHI_LO <= X) -> AIMG_TOP <= X -> Y <= aceil ->
    (TH + 4096 <= X \/ Y <= TH) -> (a_ri s + 4096 <= X \/ Y <= a_ri s) -> (FA s c + mfa' <= X \/ Y <= FA s c + 4 * nf) -> (p + csz <= X \/ Y <= p) ->
    X <= a < Y -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros X Y a HB H1 H2 H3 H4 H5 H6 Ha. pose proof BND as B. pose proof SHP as SB.
    unfold ALOWSH_LO, AHI_LO, AIMG_TOP, a_ri, kSpaceSize in HB, H1, H4. fold sb in H4.
    apply ZC_gen; clear - HB H1 H2 H3 H4 H5 H6 Ha B SB; tlia.
  Qed.

  Lemma ZC_SH : forall lo' kk a, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= kk -> lo' + 8 * kk <= aceil ->
    (lo' + 8 * kk <= FA s c + mfa \/ FA s c + mfa' <= lo') -> (lo' + 8 * kk <= p \/ p + csz <= lo') -> sh lo' <= a < sh lo' + kk -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros lo' kk a H0 H8 Hk Hhi D D2 Ha. pose proof BND as B. pose proof ALN as (A1 & A2 & _ & _ & _ & A6 & A7). bands_as (BT & _).
    assert (SS : sh lo' + kk <= sh (FA s c + mfa) \/ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh lo')
      by (apply sh_sep; [exact H8| exact A1| exact Hk| clear - B; tlia| rewrite A2; clear - D; tlia]).
    assert (SS2 : sh lo' + kk <= sh p \/ sh p + csz / 8 <= sh lo')
      by (apply sh_sep; [exact H8| clear - A6; Z.div_mod_to_equations; tlia| exact Hk| clear - B; tlia| rewrite A7; exact D2]).
    assert (SB : 0x7fff8000 <= sh lo' /\ sh lo' + kk <= 0x10007fef8000) by (clear - H0 Hk Hhi; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; tlia).
    apply ZC_gen; clear - Ha B SS SS2 SB BT; tlia.
  Qed.

  Lemma ZC_lo : forall a, 65536 <= a < AIMG_TOP -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha. pose proof BND as B. pose proof SHP as SB. bands_as (BT & _).
    unfold AIMG_TOP in Ha. apply ZC_gen; clear - Ha B BT SB; tlia.
  Qed.
  Lemma ZC_static : forall a, astatic a -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha. apply ZC_lo. clear - Ha. unfold astatic in Ha.
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP in *. tlia.
  Qed.
  Lemma ZC_flags : forall a, aflags_range a -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha. apply ZC_lo; clear - Ha; unfold aflags_range in Ha;
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, AIMG_TOP, AINST in *; tlia.
  Qed.

  Lemma ZC_thr : forall a, TH <= a < TH + 4096 -> ~ (P <= a < P + 4) -> ~ (P + 16 + 4 * cnt1 <= a < P + 20 + 4 * cnt1) -> ~ (TH + 2768 <= a < TH + 3168) -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha N1 N2 N3. pose proof BND as B. pose proof SHP as SB. bands_as (BT & _). placed. fold TH sb in D2. unfold disj, kSpaceSize, kPageSize in D2.
    pose proof (carved_vs_threadQ s _ _ OKQ _ _ CV) as CS1. fold TH csz in CS1. unfold kPageSize in CS1.
    apply ZC_gen; [clear - Ha B; tlia| exact N1| exact N2| exact N3| | | | |]; clear - Ha B D2 BT SB CS1; tlia.
  Qed.
  Lemma ZC_ctx : forall a, CTX + 8 <= a < CTX + 160 -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha. pose proof BND as B. placed. fold TH CTX sb in TCX, D3. destruct TCX as (TCX & _). bands_as (_ & BC & _).
    pose proof (carved_vs_ctxQ s _ _ OKQ _ _ CV) as CS1. fold CTX csz in CS1.
    unfold disj, kPageSize, kSpaceSize in TCX, D3.
    apply (ZC_obj (CTX + 8) (CTX + 160) a); [| | | | | | | exact Ha]; clear - Ha B TCX D3 BC CS1; unfold ALOWSH_LO, AHI_LO, AIMG_TOP, a_ri, kSpaceSize; fold sb; tlia.
  Qed.

  Lemma ZC_rinfo_o : forall c0 a, 0 <= c0 < kNumClasses -> c0 <> c -> a_ri s + 128 * c0 <= a < a_ri s + 128 * c0 + 128 -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c0 a Hc0 NE Ha. pose proof BND as B. pose proof SHP as SB. bands_as (BT & _). placed. fold TH sb in D2.
    pose proof (carved_vs_rinfoQ s _ _ OKQ _ _ CV) as CS1. fold csz in CS1. unfold a_ri, kSpaceSize in CS1. fold sb in CS1.
    unfold a_ri, kSpaceSize, kPageSize, kNumClasses, disj in Hc0, Ha, D2. fold sb in Ha.
    apply ZC_gen; clear - Hc0 NE Ha B BT D2 SB CS1; tlia.
  Qed.
  Lemma ZC_rinfo_c : forall a, RI + 8 <= a < RI + 128 -> ~ (RI + 16 <= a < RI + 32) -> ~ (RI + 80 <= a < RI + 88) -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha N1 N2. pose proof BND as B. pose proof SHP as SB. bands_as (BT & _). placed. fold TH sb in D2.
    pose proof (carved_vs_rinfoQ s _ _ OKQ _ _ CV) as CS1. fold csz in CS1. unfold a_ri, kSpaceSize in CS1. fold sb in CS1.
    unfold disj, kSpaceSize, kPageSize in D2. unfold W2, W, lcd_W. cbn [outside app].
    repeat split; try exact I; clear - Ha N1 N2 B BT D2 SB CS1; tlia.
  Qed.

  Lemma carved_vs_fac : forall c1 x, carved st c1 x -> x + class_size c1 <= FA s c \/ FA s c + 536870912 <= x.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c1 x CV1. pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & EFA & _).
    pose proof (carved_rangeQ st _ _ c1 x WQ CV1) as (R1 & R2 & _). rewrite region_beg_eq in R1, R2. change (as_space_beg st) with sb in R1, R2.
    unfold kFreeArrayOffset in *. change (2 ^ 32) with 4294967296 in R1, R2.
    destruct (Z.le_gt_cases c1 c) as [LE|GT]; [left; clear - LE R1 R2 ERB EFA; nia| right; clear - GT R1 R2 ERB EFA; nia].
  Qed.

  Lemma carved_vs_p : forall c1 x, carved st c1 x -> x <> p -> x + class_size c1 <= p \/ p + csz <= x.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c1 x CV1 NE. destruct (carved_sepQ st _ _ c1 x c p WQ CV1 CV) as [[_ E]|D]; [exact (False_ind _ (NE E))| exact D].
  Qed.
  Lemma ZC_carved : forall c1 x a, carved st c1 x -> x <> p -> x <= a < x + class_size c1 -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c1 x a CV1 NE Ha. pose proof BND as B. pose proof SHP as SB.
    pose proof (carved_vs_threadQ s _ _ OKQ _ _ CV1) as X1. pose proof (carved_vs_rinfoQ s _ _ OKQ _ _ CV1) as X2.
    pose proof (carved_in_spaceQ s _ _ OKQ _ _ CV1) as (X3 & _). pose proof (carved_vs_fac c1 x CV1) as X4. pose proof (carved_vs_p c1 x CV1 NE) as X5.
    fold TH in X1. fold sb in X3. unfold a_ri, kPageSize, kSpaceSize in X1, X2. fold sb in X2.
    apply ZC_gen; clear - Ha B X1 X2 X3 X4 X5 SB; tlia.
  Qed.
  Lemma ZC_carved_sh : forall c1 x lo' kk a, carved st c1 x -> x <> p -> x <= lo' -> lo' + 8 * kk <= x + class_size c1 -> lo' mod 8 = 0 -> 0 <= kk ->
    sh lo' <= a < sh lo' + kk -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c1 x lo' kk a CV1 NE G1 G2 G3 G4 Ha. pose proof BND as B.
    pose proof (carved_in_spaceQ s _ _ OKQ _ _ CV1) as (X3 & X5 & _). pose proof (carved_vs_fac c1 x CV1) as X4. pose proof (carved_vs_p c1 x CV1 NE) as X6.
    fold sb in X3, X5. unfold kSpaceSize in X5.
    apply (ZC_SH lo' kk a); [| exact G3| exact G4| | | | exact Ha]; clear - B X3 X4 X5 X6 G1 G2 G4; tlia.
  Qed.

  Lemma ZC_slotW : forall a, p <= a < p + csz \/ sh p <= a < sh p + csz / 8 -> outside W a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha. pose proof BND as B. pose proof SHP as SB. pose proof ALN as (A1 & A2 & _ & _ & _ & A6 & A7).
    pose proof (carved_vs_threadQ s _ _ OKQ _ _ CV) as X1. pose proof (carved_vs_rinfoQ s _ _ OKQ _ _ CV) as X2. pose proof (carved_vs_fac c p CV) as X4.
    fold TH csz in X1. fold csz in X2, X4. unfold a_ri, kPageSize, kSpaceSize in X1, X2. fold sb in X2. bands_as (BT & _).
    assert (SS : sh p + csz / 8 <= sh (FA s c + mfa) \/ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh p)
      by (apply sh_sep; [clear - A6; Z.div_mod_to_equations; tlia| exact A1| clear - B; tlia| clear - B; tlia| rewrite A2, A7; clear - X4 B; tlia]).
    unfold W, lcd_W. cbn [outside]. unfold a_cache. fold TH.
    repeat split; try exact I; clear - Ha B SB X1 X2 X4 BT SS; unfold CA, P, a_cache, OT_CACHE in *; tlia.
  Qed.

  Lemma ZC_sec : forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + sc_map_size h -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros h a Hh Ha. pose proof BND as B. placed. destruct (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). fold sb in Q5. fold TH in Q7.
    pose proof (aapp_lit _ _ Q2) as L1. pose proof (aapp_env _ _ Q2 ltac:(clear - Q4; unfold kPageSize in Q4; tlia)) as L2.
    pose proof (carved_vs_secQ s _ _ OKQ _ _ CV h Hh) as CS1. fold csz in CS1.
    unfold disj, kSpaceSize, kPageSize in Q5, Q7.
    apply (ZC_obj (sc_map_beg h) (sc_map_beg h + sc_map_size h) a); [| | | | | | | exact Ha]; clear - B L1 L2 Q3 Q5 Q7 CS1; unfold ALOWSH_LO, AHI_LO, AIMG_TOP, a_ri, kSpaceSize; fold sb; tlia.
  Qed.

  Lemma ZC_rec : forall x a, In x (chunk_list st) -> ch_lo x <= a < ch_end x -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros x a Hx Ha. pose proof (ext_factsQ s _ _ OKQ x Hx) as (_ & _ & _ & XP & XS). destruct (ch_primary x) eqn:PX.
    - destruct (XP eq_refl) as (CV1 & EE & _). unfold ch_lo in Ha. rewrite PX in Ha. apply (ZC_carved _ _ a CV1 (PNI x Hx PX)). rewrite <- EE. exact Ha.
    - destruct (XS eq_refl) as (h & Hh & E1 & E2 & _). apply (ZC_sec h); [exact Hh| clear - Ha E1 E2; tlia].
  Qed.
  Lemma ZC_rec_sh : forall x lo' kk a, In x (chunk_list st) -> ch_lo x <= lo' -> lo' + 8 * kk <= ch_end x -> lo' mod 8 = 0 -> 0 <= kk ->
    sh lo' <= a < sh lo' + kk -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros x lo' kk a Hx G1 G2 G3 G4 Ha. pose proof BND as B. pose proof (ext_factsQ s _ _ OKQ x Hx) as (X1 & X2 & _ & XP & _). destruct (ch_primary x) eqn:PX.
    - destruct (XP eq_refl) as (CV1 & EE & _). unfold ch_lo in G1. rewrite PX in G1. apply (ZC_carved_sh _ _ lo' kk a CV1 (PNI x Hx PX)); try assumption. rewrite <- EE. exact G2.
    - pose proof (record_vs_spaceQ s _ _ OKQ x Hx PX) as D. fold sb in D. pose proof (carved_in_spaceQ s _ _ OKQ _ _ CV) as (X3 & X5 & _). fold sb csz in X3, X5.
      unfold kSpaceSize, kPageSize, AIMG_TOP in *.
      apply (ZC_SH lo' kk a); try assumption; clear - G1 G2 G4 D B X1 X2 X3 X5; tlia.
  Qed.
  Lemma ZC_achunk : forall x a, In x (chunk_list st) -> achunk_range x a -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros x a Hx Ha. pose proof (record_extQ s _ _ OKQ x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). pose proof (chunk_alignQ s _ _ OKQ x Hx) as (A1 & A2' & A3 & A4 & A5).
    assert (RU : ch_used x <= round_up (ch_used x) 8 /\ round_up (ch_used x) 8 mod 8 = 0) by (clear; unfold round_up; Z.div_mod_to_equations; tlia).
    assert (NS : 0 <= nsh (ch_used x) /\ 8 * nsh (ch_used x) = round_up (ch_used x) 8) by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; tlia).
    assert (RZ8 : 8 * (ch_rz x / 8) = ch_rz x) by (clear - A2'; Z.div_mod_to_equations; tlia).
    destruct Ha as [Ha|[Ha|[[_ Ha]|[Ha|[Ha|[[_ Ha]|[NP Ha]]]]]]].
    - apply (ZC_rec x a Hx). clear - Ha X3 X6 X7 X8 X9 RU. tlia.
    - apply (ZC_rec x a Hx). clear - Ha X3 X6 X8 X9. tlia.
    - apply (ZC_rec x a Hx). clear - Ha X3 X6 X7 X8 X9 RU. tlia.
    - apply (ZC_rec_sh x (ch_alloc_beg x) (ch_rz x / 8) a Hx); clear - Ha X3 X6 X7 X8 X9 RU A1 RZ8; try tlia; Z.div_mod_to_equations; tlia.
    - apply (ZC_rec_sh x (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) a Hx);
        clear - Ha X3 X6 X7 X8 X9 RU A3 A4; try tlia; Z.div_mod_to_equations; tlia.
    - apply (ZC_rec_sh x (ch_user_beg x) (nsh (ch_used x)) a Hx); clear - Ha X3 X6 X7 X8 X9 RU NS A3; try tlia; Z.div_mod_to_equations; tlia.
    - unfold ch_lo in *. rewrite NP in *. apply (ZC_rec_sh x (ch_alloc_beg x - kPageSize) 512 a Hx); unfold ch_lo; rewrite ?NP; unfold kPageSize in *;
        clear - Ha X3 X6 X7 X8 X9 RU A1; try tlia; Z.div_mod_to_equations; tlia.
  Qed.

  Lemma ZC_batch : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
    (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros b a Hb Ha. pose proof (batch_carvedQ s _ _ OKQ b Hb) as (CV1 & _). pose proof (batch_in_spaceQ s _ _ OKQ b Hb) as (_ & _ & M8). pose proof (PNB b Hb) as NE.
    change (class_size kBatchClass) with 8192 in *. unfold kBatchSize in Ha. destruct Ha as [Ha|Ha].
    - apply (ZC_carved _ _ a CV1 NE). change (class_size kBatchClass) with 8192. exact Ha.
    - apply (ZC_carved_sh _ _ (qb_addr b) 1024 a CV1 NE); change (class_size kBatchClass) with 8192; clear - Ha M8; tlia.
  Qed.

  Lemma ZC_freech : forall c0 x a, 0 <= c0 < kNumClasses -> In x (rg_free_array (get_region st c0)) \/ In x (pc_chunks (get_pc st c0)) ->
    compact_to_addr st c0 x <= a < compact_to_addr st c0 x + class_size c0 -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c0 x a Hc0 Hin Ha. apply (ZC_carved c0 (compact_to_addr st c0 x) a); [| exact (PNF c0 x Hc0 Hin)| exact Ha].
    destruct Hin as [Hin|Hin]; [exact (carved_freeQ st _ _ c0 x WQ Hc0 Hin)| exact (carved_cacheQ st _ _ c0 x WQ Hc0 Hin)].
  Qed.
  Lemma ZC_freech_sh : forall c0 x a, 0 <= c0 < kNumClasses -> In x (rg_free_array (get_region st c0)) \/ In x (pc_chunks (get_pc st c0)) ->
    sh (compact_to_addr st c0 x) <= a < sh (compact_to_addr st c0 x) + class_size c0 / 8 -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c0 x a Hc0 Hin Ha. pose proof (freech_in_spaceQ s _ _ OKQ c0 x Hc0 Hin) as (_ & _ & M8 & C0 & C8).
    assert (CV1 : carved st c0 (compact_to_addr st c0 x))
      by (destruct Hin as [Hin|Hin]; [exact (carved_freeQ st _ _ c0 x WQ Hc0 Hin)| exact (carved_cacheQ st _ _ c0 x WQ Hc0 Hin)]).
    apply (ZC_carved_sh c0 _ (compact_to_addr st c0 x) (class_size c0 / 8) a CV1 (PNF c0 x Hc0 Hin)); [clear; tlia| | exact M8| |exact Ha]; clear - C0 C8; Z.div_mod_to_equations; tlia.
  Qed.

  Lemma reg_sep : forall c0 X Y, 0 <= c0 < 32 -> c0 <> c -> RB s c0 <= X -> Y <= RB s c0 + 4294967296 -> Y <= FA s c \/ FA s c + 536870912 <= X.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c0 X Y Hc0 NE H1 H2. pose proof BND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERB & EFA & _).
    assert (ERB0 : RB s c0 = sb + c0 * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    destruct (Z.le_gt_cases c0 c) as [LE|GT]; [left; clear - LE NE H1 H2 ERB ERB0 EFA; nia| right; clear - GT NE H1 H2 ERB ERB0 EFA; nia].
  Qed.

  Lemma ZC_space : forall a, sb <= a < sb + 137438953472 -> (a < FA s c + 4 * nf \/ FA s c + mfa' <= a) -> (a < p \/ p + csz <= a) -> outside W2 a.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros a Ha Hb Hp. pose proof BND as B. pose proof SHP as SB. placed. fold TH sb in D2. unfold disj, kSpaceSize, kPageSize in D2.
    apply ZC_gen; clear - Ha Hb Hp B D2 SB; tlia.
  Qed.

  Let E2 : a_sb s2 = sb /\ a_ri s2 = a_ri s /\ a_pa s2 = a_pa s /\ a_cache s2 = CA
           /\ (forall c0, RB s2 c0 = RB s c0) /\ (forall c0, FA s2 c0 = FA s c0) /\ (forall c0 x, compact_to_addr st' c0 x = compact_to_addr st c0 x)
           /\ chunk_list st' = chunk_list st /\ (forall c0 x, carved st' c0 x <-> carved st c0 x \/ (c0 = c /\ False)).
  Proof.
    clear - Fsb Fpa Fch Frg_c Frg_o.
    assert (CARV : forall c0 x, carved st' c0 x <-> carved st c0 x \/ (c0 = c /\ False)).
    { intros c0 x. unfold carved, region_beg. rewrite Fsb. destruct (Z.eq_dec c0 c) as [->|NE].
      - rewrite Frg_c. cbn [rg_allocated_user]. split; [intros H; left; exact H| intros [H|[_ []]]; exact H].
      - split; [intros H; left| intros [H|[_ []]]]; (rewrite (Frg_o c0) in * || idtac); try exact H; try exact NE; exact (proj1 (proj1 H)). }
    unfold a_ri, a_pa, a_cache, RB, FA, a_sb, free_array_base, compact_to_addr, region_beg, chunk_list. change (a_st s2) with st'. change (a_thr s2) with TH. rewrite Fsb, Fpa, Fch.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|]. split; [reflexivity|]. exact CARV.
  Qed.

  Ltac trc H Z := eapply (rw_cells_transport_pt Po m0 m2 AG WM); [exact H|];
                  cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length repeat map]; intros ? ?; Z.
  Ltac trj H Z := eapply (junk_transport_pt Po m0 m2 AG WM); [exact H|]; intros ? ?; Z.
  Ltac tru H Z := eapply (u32arr_transport_pt Po m0 m2 AG WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev; intros ? ?; Z.
  Ltac trp H Z := eapply (poisoned_transport_pt Po m0 m2 AG WM); [exact H|]; intros ? ?; Z.

  Lemma placed_after_cd : placed_ok s2.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    pose proof PL as X. unfold placed_ok in X |- *. unfold a_sb, a_pa in X |- *. change (a_st s2) with st'. change (a_thr s2) with TH. change (a_ctx s2) with CTX.
    change (a_fsb s2) with (a_fsb s). change (a_top s2) with (a_top s). change (a_bot s2) with (a_bot s). rewrite Fsb, Fpa, Fsec. exact X.
  Qed.

  Lemma statics_after_cd : inst_rep s2 m2 /\ flags_rep s2 m2 /\ ia_rep s2 m2 /\ sec_rep s2 m2.
  Proof.
    clear JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    pose proof MEM as (INST & FL & _ & SC & IA & _). pose proof E2 as (Y1 & Y2 & Y3 & _).
    split.
    { enough (X : inst_rep s m2).
      { unfold inst_rep in X |- *. rewrite Y1, Y2, Y3. change (a_st s2) with st'. rewrite Fnr, Fsec, Fqx, Fqn, Fqc, Fgq. exact X. }
      apply (inst_rep_frame s m0 m2 Po AG WM); [| exact INST]. intros a Ha. apply ZC_static. unfold astatic. left. exact Ha. }
    split.
    { enough (X : flags_rep s m2) by (unfold flags_rep in X |- *; change (a_st s2) with st'; rewrite Fii; exact X).
      exact (flags_rep_frame s m0 m2 Po AG WM ZC_flags FL). }
    split.
    { enough (X : ia_rep s m2) by (unfold ia_rep in X |- *; change (a_st s2) with st'; rewrite Fii; exact X).
      apply (ia_rep_frame s m0 m2 Po AG WM); [| exact IA]. intros a Ha. apply ZC_static. unfold astatic. do 11 right. left. exact Ha. }
    enough (X : sec_rep s m2) by (unfold sec_rep in X |- *; rewrite Y3; change (a_st s2) with st'; rewrite Fsec, Fnr; exact X).
    apply (sec_rep_frameQ s _ _ m0 m2 Po AG WM WQ); [| | exact SC].
    - intros a Ha. pose proof BND as B. placed. bands_as (_ & _ & BP). fold sb in D1. fold TH in D4. unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in D1, D4.
      pose proof WQ as (_ & _ & _ & _ & _ & _ & W7 & W8 & _). change (a_st s) with st in W7, W8, Ha. unfold kChunksBlockCount in W8.
      assert (Z0 : 0 <= zlen (as_sec st)) by (unfold zlen; clear; tlia).
      pose proof (carved_vs_paQ s _ _ OKQ _ _ CV) as CS1. fold csz in CS1. unfold kPtrArrayReserve in CS1.
      apply (ZC_obj (a_pa s) (a_pa s + 8388608) a); [| | | | | | | clear - Ha W7 W8 Z0; tlia]; clear - B BP D1 D4 CS1; unfold ALOWSH_LO, AHI_LO, AIMG_TOP, a_ri, kSpaceSize; fold sb; tlia.
    - intros h a Hh Ha. apply (ZC_sec h a Hh). placed. pose proof (SEC h Hh) as (_ & _ & _ & Q4 & _). unfold kPageSize in *. clear - Ha Q4. tlia.
  Qed.

  Lemma thread_after_cd : thread_rep s2 m2.
  Proof.
    clear JK PS PC1' PC3' PC4' RI' RST' FARR' FAJ' POIf'.
    pose proof BND as B. pose proof MEM as (_ & _ & THR & _). destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_st s2) with st'. change (a_thr s2) with TH. change (a_ctx s2) with CTX. change (a_top s2) with (a_top s). change (a_bot s2) with (a_bot s).
    rewrite (proj1 (proj2 (proj2 (proj2 E2)))). rewrite Ftq.
    fold TH CTX in T1, T2, T2b, T2c, T2d, T3, T4, J1, J3, T5 |- *. fold CA in J2. unfold OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS in *.
    Ltac zt Ha B := first [apply ZC_thr; clear - Ha B; tlia | apply ZC_ctx; clear - Ha; tlia].
    split; [trc T1 ltac:(zt H B)|]. split; [trc T2 ltac:(zt H B)|]. split; [trc T2b ltac:(zt H B)|]. split; [trc T2c ltac:(zt H B)|]. split; [trc T2d ltac:(zt H B)|].
    split; [trc T3 ltac:(zt H B)|]. split; [trc T4 ltac:(zt H B)|]. split; [trj J1 ltac:(zt H B)|].
    split.
    { pose proof (stk_of_rw_cells asegs _ _ _ QST') as SQ. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SQ.
      apply junk_of_stk_eq with (hi := TH + 2768 + 32); [| clear - B; tlia]. replace (CA + 2560) with (TH + 2768) by (clear - B; tlia). exact SQ. }
    split; [apply junk_of_stk_eq with (hi := TH + 3168); [exact TST'| clear; tlia]|].
    trc T5 ltac:(zt H B).
  Qed.

  Lemma chunks_after_cd : forall x, In x (chunk_list st') -> chunk_rep m2 x.
  Proof.
    clear JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros x Hx. pose proof E2 as (_ & _ & _ & _ & _ & _ & _ & Y8 & _). rewrite Y8 in Hx. pose proof MEM as (_ & _ & _ & _ & _ & _ & CH & _).
    apply (chunk_rep_frameQ s _ _ m0 m2 Po AG WM WQ x Hx); [| exact (CH x Hx)]. intros a Ha. exact (ZC_achunk x a Hx Ha).
  Qed.

  Let BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> 0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b).
  Proof. clear - WQ. intros b Hb. pose proof (WFQ_batch _ _ _ b WQ Hb) as (B1 & B2 & _). unfold kBatchSize, kBatchCount in *. clear - B1 B2. tlia. Qed.

  Lemma batches_after_cd : batches_rep m2 (qc_list (as_tq st')) /\ batches_rep m2 (qc_list (as_gq st')).
  Proof.
    clear JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    rewrite Ftq, Fgq. pose proof MEM as (_ & _ & _ & _ & _ & _ & _ & BT & BG).
    split.
    - eapply (batches_rep_transport Po m0 m2); [exact AG| exact WM| | | exact BT].
      + intros b a Hb Hr. apply (ZC_batch b a); [apply in_app_iff; left; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
    - eapply (batches_rep_transport Po m0 m2); [exact AG| exact WM| | | exact BG].
      + intros b a Hb Hr. apply (ZC_batch b a); [apply in_app_iff; right; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
  Qed.

  Lemma regions_other_after_cd : forall c0, 0 <= c0 < kNumClasses -> c0 <> c ->
    region_rep s2 m2 c0 /\ pclass_rep s2 m2 c0 /\ region_shadow_rep s2 m2 c0 /\ region_junk_rep s2 m2 c0.
  Proof.
    clear JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros c0 Hc0 NE. pose proof BND as B. pose proof E2 as (Y1 & Y2 & Y3 & Y3b & Y4 & Y5 & Y7 & Y8 & _). pose proof MEM as (_ & _ & _ & _ & _ & RC & _).
    destruct (RC c0 Hc0) as (R1 & R2 & R3 & R4).
    pose proof (WFQ_region st _ _ c0 WQ Hc0) as RO0.
    pose proof (ro_alloc_nonneg _ _ RO0) as N1. pose proof (ro_alloc_le _ _ RO0) as N2. pose proof (ro_mapped_bound _ _ RO0) as N3.
    pose proof (ro_fa_le _ _ RO0) as N4. pose proof (ro_fa_bound _ _ RO0) as N5. pose proof (ro_numfreed _ _ RO0) as N6. unfold zlen in N6.
    assert (ERB0 : RB s c0 = sb + c0 * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (EFA0 : FA s c0 = RB s c0 + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kNumClasses in *. change (a_st s) with st in R1, R2, R3, R4.
    pose proof (carved_vs_farrayQ s _ _ OKQ _ _ CV c0 Hc0) as PF. pose proof (carved_vs_tailQ s _ _ OKQ _ _ CV c0 Hc0) as PT. fold csz in PF, PT. change (a_st s) with st in PF, PT.
    assert (ZFA : forall a, FA s c0 <= a < FA s c0 + rg_mapped_free_array (get_region st c0) -> outside W2 a).
    { intros a Ha. pose proof (reg_sep c0 (FA s c0) (FA s c0 + rg_mapped_free_array (get_region st c0)) Hc0 NE ltac:(clear - EFA0; tlia) ltac:(clear - EFA0 N5; tlia)) as D.
      apply ZC_space; clear - Ha B ERB0 EFA0 N4 N5 N6 Hc0 D PF; tlia. }
    assert (ZTL : forall a, RB s c0 + rg_allocated_user (get_region st c0) <= a < RB s c0 + rg_mapped_user (get_region st c0) -> outside W2 a).
    { intros a Ha. pose proof (reg_sep c0 (RB s c0 + rg_allocated_user (get_region st c0)) (RB s c0 + rg_mapped_user (get_region st c0)) Hc0 NE ltac:(clear - N1; tlia) ltac:(clear - N3; tlia)) as D.
      apply ZC_space; clear - Ha B ERB0 N1 N2 N3 Hc0 D PT; tlia. }
    assert (ZRI : forall a, a_ri s + 128 * c0 <= a < a_ri s + 128 * c0 + 128 -> outside W2 a) by (intros a Ha; exact (ZC_rinfo_o c0 a ltac:(clear - Hc0; unfold kNumClasses; tlia) NE Ha)).
    split.
    {
      enough (X : region_rep s m2 c0) by (unfold region_rep in X |- *; change (a_st s2) with st'; rewrite Y2, (Y4 c0), (Y5 c0), (Frg_o c0 (proj1 Hc0) NE); exact X).
      destruct R1 as (Q1 & J1 & Q2 & J2 & U & J3 & J4). unfold region_rep, REGIONINFO_SIZE in *. change (a_st s) with st.
      split; [trc Q1 ltac:(apply ZRI; clear - H; tlia)|]. split; [trj J1 ltac:(apply ZRI; clear - H; tlia)|].
      split; [trc Q2 ltac:(apply ZRI; clear - H; tlia)|]. split; [trj J2 ltac:(apply ZRI; clear - H; tlia)|].
      split; [tru U ltac:(apply ZFA; clear - H N4 N6; tlia)|]. split; [trj J3 ltac:(apply ZFA; clear - H N4 N6; tlia)|].
      trj J4 ltac:(apply ZTL; clear - H; tlia). }
    split.
    {
      enough (X : pclass_rep s m2 c0) by (unfold pclass_rep in X |- *; change (a_st s2) with st'; change (a_st s) with st in X; rewrite Y3b; rewrite (Fpc_o c0 (proj1 Hc0) NE), Fci; rewrite INIT in X; exact X).
      apply (pclass_rep_frameQ s _ _ m0 m2 Po AG WM WQ c0 Hc0); [| exact R2]. intros a Ha. unfold a_cache, PCLASS_SIZE, OT_CACHE in Ha. fold TH in Ha.
      apply ZC_thr; clear - Ha B Hc0 NE; tlia. }
    pose proof (class_size_table_facts c0 Hc0) as (C0 & C8 & _).
    split.
    {
      enough (X : region_shadow_rep s m2 c0).
      { unfold region_shadow_rep in X |- *. change (a_st s2) with st'. change (a_st s) with st in X. rewrite (Y4 c0), (Y5 c0), (Frg_o c0 (proj1 Hc0) NE), (Fpc_o c0 (proj1 Hc0) NE).
        destruct X as (X1 & X2 & X3 & X4). split; [intros x Hx; rewrite (Y7 c0 x); exact (X1 x Hx)|]. split; [intros x Hx; rewrite (Y7 c0 x); exact (X2 x Hx)|]. exact (conj X3 X4). }
      apply (region_shadow_rep_frameQ s _ _ m0 m2 Po AG WM WQ c0 Hc0); [| | | exact R3].
      - intros x a Hin Ha. exact (ZC_freech_sh c0 x a Hc0 Hin Ha).
      - intros a Ha. pose proof (tail_in_spaceQ s _ _ OKQ c0 Hc0) as (F1' & F2' & F3' & F4' & F5'). fold sb in F1', F2'. unfold kSpaceSize in F2'. fold st in F1', F2', F3', F4', F5'.
        pose proof (reg_sep c0 (RB s c0 + rg_allocated_user (get_region st c0)) (RB s c0 + rg_mapped_user (get_region st c0)) Hc0 NE ltac:(clear - N1; tlia) ltac:(clear - N3; tlia)) as D.
        apply (ZC_SH (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8) a); [| exact F3'| | | | | exact Ha];
          clear - F1' F2' F4' F5' B D PT; Z.div_mod_to_equations; tlia.
      - intros a Ha. pose proof (farray_in_spaceQ s _ _ OKQ c0 Hc0) as (F1' & F2' & F3' & F4' & F5'). fold sb in F1', F2'. unfold kSpaceSize in F2'. fold st in F1', F2', F3', F4', F5'.
        pose proof (reg_sep c0 (FA s c0) (FA s c0 + rg_mapped_free_array (get_region st c0)) Hc0 NE ltac:(clear - EFA0; tlia) ltac:(clear - EFA0 N5; tlia)) as D.
        apply (ZC_SH (FA s c0) (rg_mapped_free_array (get_region st c0) / 8) a); [| exact F3'| | | | | exact Ha]; clear - F1' F2' F4' F5' B D PF; Z.div_mod_to_equations; tlia. }

    enough (X : region_junk_rep s m2 c0).
    { unfold region_junk_rep in X |- *. change (a_st s2) with st'. change (a_st s) with st in X. rewrite (Frg_o c0 (proj1 Hc0) NE), (Fpc_o c0 (proj1 Hc0) NE).
      destruct X as (X1 & X2). split; [intros x Hx; rewrite (Y7 c0 x); exact (X1 x Hx)| intros x Hx; rewrite (Y7 c0 x); exact (X2 x Hx)]. }
    apply (region_junk_rep_frame s m0 m2 Po AG WM c0 Hc0); [| exact R4]. intros x a Hin Ha. exact (ZC_freech c0 x a Hc0 Hin Ha).
  Qed.

  Lemma region_c_after_cd : region_rep s2 m2 c /\ pclass_rep s2 m2 c /\ region_shadow_rep s2 m2 c /\ region_junk_rep s2 m2 c.
  Proof.
    pose proof BND as B. pose proof ALN as (A1 & A2 & A3 & A4 & A5 & A6 & A7). pose proof E2 as (Y1 & Y2 & Y3 & Y3b & Y4 & Y5 & Y7 & Y8 & _).
    pose proof MEM as (_ & _ & _ & _ & _ & RC & _).
    assert (HCC : 0 <= c < kNumClasses) by (clear - HC; unfold kNumClasses in *; tlia).
    destruct (RC c HCC) as (R1 & R2 & R3 & R4). change (a_st s) with st in R1, R2, R3, R4.
    pose proof (push_facts st _ _ c p WQ CLS) as (_ & _ & _ & CTA). fold cp in CTA.
    pose proof (carved_vs_farrayQ s _ _ OKQ _ _ CV c HCC) as PF. pose proof (carved_vs_tailQ s _ _ OKQ _ _ CV c HCC) as PT. fold csz in PF, PT. change (a_st s) with st in PF, PT.
    fold r mfa in PF. fold r au mu in PT.
    assert (INCH : forall x, In x moved \/ In x kept -> In x chunks).
    { intros x Hx. unfold moved, kept in Hx. rewrite <- (firstn_skipn kn chunks). apply in_app_iff. exact Hx. }
    pose proof (class_size_table_facts c HCC) as (C0 & C8 & _). fold csz in C0, C8.
    split.
    {
      unfold region_rep. change (a_st s2) with st'. rewrite Y2, (Y4 c), (Y5 c), Frg_c. cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array].
      unfold REGIONINFO_SIZE. fold RI. destruct R1 as (Q1 & J1 & Q2 & J2 & U & J3 & J4). unfold REGIONINFO_SIZE in Q1, J1, Q2, J2. fold RI in Q1, J1, Q2, J2.
      split; [exact RI'|].
      split; [trj J1 ltac:(apply ZC_rinfo_c; clear - H; tlia)|].
      split; [trc Q2 ltac:(apply ZC_rinfo_c; clear - H; tlia)|].
      split; [apply junk_of_stk_eq with (hi := RI + 128); [exact RST'| clear; tlia]|].
      split; [exact FARR'|].
      split; [apply junk_of_stk_eq with (hi := FA s c + mfa'); [exact FAJ'| clear; tlia]|].
      trj J4 ltac:(apply ZC_space; clear - H B PT; tlia). }
    split.
    {
      unfold pclass_rep. change (a_st s2) with st'. rewrite Y3b, Fpc_c, Fci. cbn [pc_count pc_chunks].
      replace (negb (c =? 0)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; clear - HC; tlia). cbn [andb]. unfold PCLASS_SIZE. fold P.
      destruct R2 as (Q1 & Q2 & QU & QJ). rewrite INIT in Q2. replace (negb (c =? 0)) with true in Q2 by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; clear - HC; tlia). cbn [andb] in Q2.
      unfold a_cache, PCLASS_SIZE in Q2. fold TH in Q2. replace (TH + OT_CACHE + 80 * c) with P in Q2 by (unfold OT_CACHE; clear - B; tlia).
      split; [exact PC1'|]. split; [trc Q2 ltac:(apply ZC_thr; clear - H B; tlia)|]. split; [exact PC3'|].
      apply junk_of_stk_eq with (hi := P + 80); [exact PC4'| clear; tlia]. }
    destruct R3 as (H1 & H2 & H3 & H4). destruct R4 as (J1 & J2). fold r pc csz in H1, H2, H3, H4, J1, J2. fold fl in H1, J1. fold chunks in H2, J2. fold au mu mfa in H3, H4.
    assert (ELEM : forall x, In x fl \/ In x chunks ->
              poisoned m2 (compact_to_addr st c x) (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic /\ junk m2 (compact_to_addr st c x) csz).
    { intros x Hx. split.
      - assert (H0 : poisoned m0 (compact_to_addr st c x) (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic) by (destruct Hx as [Hx|Hx]; [exact (H1 x Hx)| exact (H2 x Hx)]).
        trp H0 ltac:(apply (ZC_freech_sh c x _ HCC Hx); fold csz; rewrite Z2Nat.id in H; [exact H| clear - C0; Z.div_mod_to_equations; tlia]).
      - assert (H0 : junk m0 (compact_to_addr st c x) csz) by (destruct Hx as [Hx|Hx]; [exact (J1 x Hx)| exact (J2 x Hx)]).
        trj H0 ltac:(apply (ZC_freech c x _ HCC Hx); exact H). }
    pose proof (conj PS JK) as SLOT.
    split.
    {
      unfold region_shadow_rep. change (a_st s2) with st'. rewrite (Y4 c), (Y5 c), Frg_c, Fpc_c. cbn [rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array pc_chunks]. fold csz.
      split; [intros x Hx; rewrite (Y7 c x); apply in_app_iff in Hx; exact (proj1 (ELEM x ltac:(destruct Hx as [Hx|Hx]; [right; apply INCH; left; exact Hx| left; exact Hx])))|].
      split. { intros x [<-|Hx]; rewrite (Y7 c _); [rewrite CTA; exact (proj1 SLOT)| exact (proj1 (ELEM x ltac:(right; apply INCH; right; exact Hx)))]. }
      split.
      - pose proof (tail_in_spaceQ s _ _ OKQ c HCC) as (F1' & F2' & F3' & F4' & F5'). fold sb in F1', F2'. unfold kSpaceSize in F2'. change (a_st s) with st in F1', F2', F3', F4', F5'. fold r au mu in F1', F2', F3', F4', F5'.
        trp H3 ltac:(rewrite Z2Nat.id in H by (clear - F4' F5'; Z.div_mod_to_equations; tlia);
                     apply (ZC_SH (RB s c + au) ((mu - au) / 8)); [| exact F3'| | | | | exact H]; clear - F1' F2' F4' F5' B PT; Z.div_mod_to_equations; tlia).
      - replace (Z.to_nat (mfa' / 8)) with (Z.to_nat (mfa / 8) + Z.to_nat ((mfa' - mfa) / 8))%nat by (clear - B A2 A3 A4; Z.div_mod_to_equations; tlia).
        apply poisoned_app; [| replace (FA s c + 8 * Z.of_nat (Z.to_nat (mfa / 8))) with (FA s c + mfa) by (clear - B A3; Z.div_mod_to_equations; tlia); exact POIf'].
        pose proof (farray_in_spaceQ s _ _ OKQ c HCC) as (F1' & F2' & F3' & F4' & F5'). fold sb in F1', F2'. unfold kSpaceSize in F2'. change (a_st s) with st in F2', F4', F5'. fold r mfa in F2', F4', F5'.
        trp H4 ltac:(rewrite Z2Nat.id in H by (clear - B; Z.div_mod_to_equations; tlia);
                     apply (ZC_SH (FA s c) (mfa / 8)); [| exact F3'| | | | | exact H]; clear - F1' F2' F4' F5' B PF; Z.div_mod_to_equations; tlia). }

    unfold region_junk_rep. change (a_st s2) with st'. rewrite Frg_c, Fpc_c. cbn [rg_free_array pc_chunks]. fold csz.
    split; [intros x Hx; rewrite (Y7 c x); apply in_app_iff in Hx; exact (proj2 (ELEM x ltac:(destruct Hx as [Hx|Hx]; [right; apply INCH; left; exact Hx| left; exact Hx])))|].
    intros x [<-|Hx]; rewrite (Y7 c _); [rewrite CTA; exact (proj2 SLOT)| exact (proj2 (ELEM x ltac:(right; apply INCH; right; exact Hx)))].
  Qed.

  Theorem arepq_after_cd : AREPQ s2 XC XB m2.
  Proof.
    destruct statics_after_cd as (I1 & I2 & I3 & I4). destruct batches_after_cd as [BT BG].
    split; [exact placed_after_cd|]. split; [exact WQ'|].
    split; [exact I1|]. split; [exact I2|]. split; [exact thread_after_cd|]. split; [exact I4|]. split; [exact I3|].
    split.
    { intros c0 Hc0. destruct (Z.eq_dec c0 c) as [->|NE]; [exact region_c_after_cd| exact (regions_other_after_cd c0 Hc0 NE)]. }
    split; [exact chunks_after_cd|]. change (a_st s2) with st'. split; [exact BT| exact BG].
  Qed.

  Lemma flagsx_after_cd : flagsx_rep m0 -> flagsx_rep m2.
  Proof.
    clear JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros (X1 & X2 & [g X3] & X4 & [b X5]).
    assert (ZI : forall a, 65536 <= a < 7241728 -> outside W2 a) by (intros a Ha; apply ZC_lo; unfold AIMG_TOP; exact Ha).
    unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
    split; [trc X1 ltac:(apply ZI; clear - H; tlia)|]. split; [trc X2 ltac:(apply ZI; clear - H; tlia)|]. split; [exists g; trc X3 ltac:(apply ZI; clear - H; tlia)|].
    split; [trc X4 ltac:(apply ZI; clear - H; tlia)|]. exists b; trc X5 ltac:(apply ZI; clear - H; tlia).
  Qed.
  Lemma awin_after_cd : awin_vis s m0 -> awin_vis s2 m2.
  Proof.
    clear JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ'.
    intros AWV x Hx. change (a_S s2) with SZ in Hx. rewrite ES, in_rangesb_app in Hx. apply Bool.orb_true_iff in Hx. destruct Hx as [Hx|Hx]; [| apply WM; exact (AWV x Hx)].
    pose proof BND as B. pose proof SHP as SB. pose proof ALN as (_ & A2 & _).
    destruct (Z.ltb_spec mfa mfa') as [LT|GE]; [| cbn in Hx; discriminate Hx].
    apply in_window1 in Hx; [| clear - SB; tlia| clear - B A2; tlia| clear - SB B A2; tlia].
    apply (poisoned_visible m2 m2 _ _ _ x POIf' (fun _ H => H)). rewrite Z2Nat.id by (clear - B A2; tlia). exact Hx.
  Qed.
  Lemma depot_avoid_cd : forall d, depot_placed s d -> depot_avoid W2 d.
  Proof.
    clear AG WM JK PS PC1' PC3' PC4' QST' TST' RI' RST' FARR' FAJ' POIf'.
    intros d DPL. pose proof BND as B. pose proof SHP as SB. bands_as (BT & _).
    pose proof DPL as (G1 & G2 & G3 & G4 & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4). fold TH in G1, G2. fold sb in G3, G4.
    pose proof (aapp_lit _ _ N1) as L1. pose proof (aapp_lit _ _ N3) as L3. apply aapp_env in N1; [| clear; tlia]. apply aapp_env in N3; [| clear; tlia].
    pose proof (carved_vs_depotQ s _ _ OKQ _ _ CV d DPL) as X1. fold csz in X1.
    unfold depot_avoid, avoids, W2, W, lcd_W, disj, kPageSize, kSpaceSize in *. cbn [app]. acb. clear - B BT G1 G2 G3 G4 N1 N2 N3 N4 L1 L3 SB X1 ACEILB.

    repeat split; repeat (first [apply Forall_nil | apply Forall_cons;
      [cbn [fst snd]; first [clear - B N2 N4; fastlia | clear - B BT G1 G2; fastlia | clear - B G3 G4; fastlia | clear - B SB L1 L3; fastlia | clear - B X1; fastlia
                            | clear - B N2 N4; tlia | clear - B BT G1 G2; tlia | clear - B G3 G4; tlia | clear - B SB L1 L3; tlia | clear - B X1; tlia] |]]).
  Qed.

End CDPost.
End HCW.
