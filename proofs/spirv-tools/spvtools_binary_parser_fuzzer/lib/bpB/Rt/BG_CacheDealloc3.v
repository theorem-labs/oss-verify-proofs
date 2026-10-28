(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BAllocSim BMmapSim BazyRestrict BazyLedger BazySR BazyNodes BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BsDepotInv BW_DepotFrame BllocWalkKit BW_Efs BecLazy BS_Refill1 BS_Refill2 BS_Rta BS_LcDealloc BG_Malloc BG_Malloc2 BG_MallocModel BG_ColdModel BG_Refill3 BG_MallocCold BG_RepQ BG_RepQFacts BG_RepQFacts2 BS_Free2 BG_RecycleModel BG_CacheDealloc0 BG_CacheDealloc1 BG_CacheDealloc2 BG_WriteSet BG_RecycleDefs BllocTacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BerfLia.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Lemma nc_bound : forall csz nf cnt au mu : Z, (32 <= csz -> csz * (nf + cnt) <= au -> au <= mu -> mu + 262144 <= 3758096384 -> 0 <= nf -> 0 <= cnt ->
  32 * (nf + cnt) <= 3758096384)%Z.
Proof. intros. nia. Qed.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma kr_of_flag : forall (drained : bool) (cnt mc n nf mfa k mfa' : Z),
  k = (if drained then n else 0) -> mfa' = (if drained then rta_mfa nf n mfa else mfa) -> n = mc / 2 ->
  (if drained then cnt = mc else cnt < mc) ->
  (k = 0 /\ mfa' = mfa /\ cnt < mc) \/ (k = mc / 2 /\ cnt = mc /\ mfa' = rta_mfa nf k mfa).
Proof. intros drained; destruct drained; intros; subst; [right| left]; repeat split; assumption || reflexivity. Qed.
Lemma froom_of_flag : forall (drained : bool) (n nf mfa mfa' : Z),
  mfa' = (if drained then rta_mfa nf n mfa else mfa) -> mfa <= kFreeArraySize -> efs_new (nf + n) <= kFreeArraySize -> mfa' <= kFreeArraySize.
Proof. intros drained; destruct drained; intros; subst; [| assumption]. unfold rta_mfa. destruct (4 * (nf + n) <=? mfa); assumption. Qed.

Section CDStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (c p : Z) (d : depot) (lo : Z).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let CA := a_cache s.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let pc := get_pc st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let cnt := pc_count pc. Let chunks := pc_chunks pc. Let csz := class_size c. Let mc := max_count c. Let n := mc / 2.
  Let drained : bool := cnt =? mc.
  Let k := if drained then n else 0.
  Let mfa' := if drained then rta_mfa nf n mfa else mfa.
  Let st' := cd_state st c p drained.

  Hypothesis RQ : AREPQ s XC (p :: XB) m.
  Hypothesis CLS : class_of_addr st p = c.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis INIT : as_cache_inited st = true.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 688 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis TP : bv_unsigned tp = ATP.

  Hypothesis SLOTJ : junk m p csz.
  Hypothesis SLOTP : poisoned m p (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic.

  Hypothesis PROOM : pusage st + 303104 <= B_PRIM.
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
                    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz AINST) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x94bb0) fc None m (seg_rom asegs).

  Definition cd_model (stX : astate) : Prop :=
    forall stA, same_but_shadow stA st -> exists stA' ev, cache_dealloc stA c p = Some (stA', ev) /\ same_but_shadow stA' stX.
  Definition cd_gpost : machine_state -> Model -> Prop :=
    rstep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s d lo m mo XC XB XB cd_model.

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st XC (p :: XB). Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let OKQ : placed_ok s /\ WFQ (a_st s) XC (p :: XB). Proof. exact (conj PL WQ). Qed.
  Let HC' : 1 <= c < kNumClasses. Proof. clear - HC. unfold kNumClasses. tlia. Qed.
  Let HCC : 0 <= c < kNumClasses. Proof. clear - HC. unfold kNumClasses. tlia. Qed.
  Let CV : carved st c p. Proof. rewrite <- CLS. exact (WFQ_xb st _ _ p WQ ltac:(left; reflexivity)). Qed.

  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 7241728 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 1 <= c <= 30 /\ CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c
            /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
            /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= cnt <= mc /\ 2 <= mc <= 16 /\ 1 <= n /\ n + n = mc /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384
            /\ 32 <= csz <= 65536 /\ RB s c <= p /\ p + csz <= RB s c + au /\ csz * (nf + cnt) <= au /\ TH mod 16 = 0 /\ sb mod 65536 = 0 /\ p mod 16 = 0 /\ mfa mod 262144 = 0.
  Proof.
    clear AX AMX DEP DPL MI ST SLOTJ SLOTP PROOM OK VISE.
    placed. fold TH CTX sb in T1, T2, T3, X2, X3, S1, S2, S3.
    apply akobj_env in T2; [| unfold kPageSize; clear; tlia]. apply aapp_env in X2; [| clear; tlia].
    pose proof (cd_pure s m _ _ c RQ HC INIT) as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11). fold st r pc in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11.
    fold nf mfa au mu fl cnt chunks csz mc in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11.
    pose proof (class_size_table_facts c HCC) as (_ & C2 & _ & _ & _ & C6). fold mc in C6. fold csz in C2.
    pose proof (class_slots_count st _ _ c WQ HCC ltac:(clear - U10; fold csz; tlia)) as CNTB. fold r pc csz au fl chunks in CNTB.
    pose proof (ro_numfreed _ _ (WFQ_region st _ _ c WQ HCC)) as NFE. fold r nf fl in NFE. rewrite <- NFE, <- U8 in CNTB.
    destruct CV as (_ & _ & V3 & V4 & V5). fold st r au csz in V5. change (region_beg st c) with (RB s c) in V3, V4, V5. fold csz in V4.
    assert (GEO : CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384).
    { unfold P, CA, RI, TH, sb, a_cache, a_ri, OT_CACHE, kSpaceSize, RB, FA, a_sb. rewrite free_array_base_eq, region_beg_eq. unfold kFreeArrayOffset. repeat split; reflexivity. }
    pose proof GEO as (_ & _ & _ & ERB & _).
    assert (NN : 1 <= n /\ n + n = mc) by (unfold n; clear - U11 C6; Z.div_mod_to_equations; tlia).
    assert (P16 : p mod 16 = 0) by (clear - ERB S1 C2 U10 V4; Z.div_mod_to_equations; nia).
    assert (T16 : TH mod 16 = 0) by (clear - T1; unfold kPageSize in T1; Z.div_mod_to_equations; tlia).
    unfold AHI_LO, kSpaceSize, kPageSize, kFreeArraySize, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *.
    clear - LO T2 X2 S1 S2 S3 HC GEO U1 U2 U3 U4 U5 U9 U10 U11 NN V3 V5 CNTB P16 T16.
    repeat match goal with |- _ /\ _ => split end; tlia.
  Qed.

  Lemma cd_zones : forall m', munch (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa') m m' ->
    agree_on (fun a => bv_unsigned sp <= a) m m' /\ agree_on (pendz st XB) m m'
    /\ agree_on (outside (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa' ++ [(p, p + csz); (sh p, sh p + csz / 8)])) m m'.
  Proof.
    clear AX AMX DEP DPL MI ST SLOTJ SLOTP PROOM OK VISE.
    intros m' MU. pose proof (munch_agree _ _ _ MU) as AG. pose proof BND as B.
    assert (KR : (k = 0 /\ mfa' = mfa /\ cnt < max_count c) \/ (k = max_count c / 2 /\ cnt = max_count c /\ mfa' = rta_mfa nf k mfa)).
    { unfold k, mfa', drained. fold mc n. destruct (Z.eqb_spec cnt mc) as [E|NE]; [right| left]; repeat split; try reflexivity; try exact E. clear - NE B; tlia. }
    assert (NC : 32 * (nf + cnt) <= 3758096384) by (apply (nc_bound csz nf cnt au mu); clear - B; tlia).
    assert (FROOM : mfa' <= kFreeArraySize).
    { unfold mfa', drained, rta_mfa, efs_new, round_up, kFreeArrayMapSize, kFreeArraySize. destruct (Z.eqb_spec cnt mc) as [E|NE]; [| clear - B; tlia].
      destruct (4 * (nf + n) <=? mfa); [clear - B; tlia|]. clear - B NC E. Z.div_mod_to_equations. tlia. }
    assert (AG2 : agree_on (outside (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa' ++ [(p, p + csz); (sh p, sh p + csz / 8)])) m m').
    { intros a Ha. apply AG. exact (proj1 (proj1 (outside_app _ _ _) Ha)). }
    assert (KB : 0 <= k <= cnt /\ mfa <= mfa' <= 536870912).
    { unfold kFreeArraySize in FROOM. revert FROOM. pose proof KR as KR'. fold mc in KR'. fold n in KR'. destruct KR' as [(-> & -> & _)|(-> & E & ->)]; [clear - B; intros; tlia|].
      unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize. destruct (Z.leb_spec (4 * (nf + n)) mfa) as [LE|GT]; [clear - B E; intros; tlia|]. clear - B E GT. intros FROOM. Z.div_mod_to_equations; tlia. }
    split; [| split; [| exact AG2]].
    - intros a Ha. apply AG. unfold lcd_W. cbn [outside]. clear - Ha B HI KB. unfold sh, ASHADOW_BASE. acb.
      repeat split; try exact I; Z.div_mod_to_equations; tlia.
    - intros a (x & Hx & Ha). apply AG2. pose proof (WFQ_xb st _ _ x WQ ltac:(right; exact Hx)) as CVx. unfold xb_ok in CVx.
      assert (NE : x <> p).
      { intros E. pose proof (NoDup_app_r _ _ (WFQ_carved st _ _ WQ)) as ND. inversion ND as [|y l NI ND' EE]. subst. apply NI. exact Hx. }
      destruct Ha as [Ha|Ha].
      + exact (ZC_carved s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO _ _ a CVx NE Ha).
      + pose proof (carved_in_spaceQ s _ _ OKQ _ _ CVx) as (Y1 & Y2 & Y3). pose proof (class_size_table_facts (class_of_addr st x) (proj1 CVx)) as (_ & C8 & _).
        assert (X8 : x mod 8 = 0).
        { destruct CVx as (_ & _ & _ & V4 & _). rewrite region_beg_eq in V4. change (as_space_beg st) with sb in V4.
          apply Z.mod_divide in V4; [| clear - Y3; tlia]. destruct V4 as [q Hq]. apply Z.mod_divide in C8; [| clear; tlia]. destruct C8 as [u Hu].
          rewrite Hu in Hq. clear - Hq B. apply Z.mod_divide; [tlia|]. exists (q * u * 4 + class_of_addr st x * 536870912 + (sb / 65536) * 8192). Z.div_mod_to_equations. nia. }
        apply (ZC_carved_sh s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO _ _ x (class_size (class_of_addr st x) / 8) a CVx NE);
          [clear; tlia| | exact X8| | exact Ha]; clear - C8 Y3; Z.div_mod_to_equations; tlia.
  Qed.

  Theorem cache_dealloc_arepq :
    (forall msF' mo', cd_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. pose proof BND as B. pose proof B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & ECA & EP & ERI & ERB & EFA & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & C1 & V3 & V5 & CNTB & T16 & S16 & P16 & M18).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0). destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    destruct AB0 as [AB0a AB0b].

    destruct (cd_cells_of_arepq s m _ _ c RQ HC INIT) as (q0 & q1 & q2 & q3 & PC1 & PC2 & PC3 & PC4 & QST & TST & RIC & RIJ & EXH & RST & FARR & FAJ & USJ & REN).
    fold st TH CA r pc in PC1, PC2, PC3, PC4, QST, TST, RIC, RIJ, EXH, RST, FARR, FAJ, USJ, REN. cbv zeta in PC1.
    change (CA + PCLASS_SIZE * c) with P in PC1, PC2, PC3, PC4. change (a_ri s + REGIONINFO_SIZE * c) with RI in RIC, RIJ, EXH, RST.
    fold cnt chunks mc nf mfa au mu fl in PC1, PC3, PC4, RIC, FARR, FAJ, USJ.
    pose proof (cd_pure s m _ _ c RQ HC INIT) as (_ & _ & U3 & _ & _ & U6 & U7 & U8 & _). fold st r pc in U3, U6, U7, U8. fold nf mfa mu fl cnt chunks in U3, U6, U7, U8.
    eapply (cache_dealloc_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo sb c TH CTX ATSD p cnt mc csz chunks q0 q1 q2 q3 nf mfa au mu fl).
    { exact LO. }
    { exact HI. }
    { exact SPT. }
    { constructor. exact SPA. }
    { exact HC'. }
    { unfold AHI_LO, kSpaceSize, kPageSize. clear - B6 B7. tlia. }
    { constructor. exact S16. }
    { rewrite TP. unfold wz, ATP, AIMG_TOP. clear; tlia. }
    { placed. unfold ATSD, AIMG_TOP. fold TH CTX in T2, T3, X2, X3. unfold kPageSize in T2. clear - B T2 T3 X2 X3. repeat match goal with |- _ /\ _ => split end; first [assumption | tlia]. }
    { constructor. exact T16. }
    { constructor. placed. fold TH CTX sb in D2, D3, TCX. destruct TCX as (TCX & _). unfold disj, kSpaceSize, kPageSize in *. clear - D2 D3 TCX. tlia. }
    { clear - ERB V3 V5 N8 N9 C1. tlia. }
    { clear - N5. tlia. }
    { exact U8. }
    { exact N4. }
    { fold n. assert (NC : 32 * (nf + cnt) <= 3758096384) by (apply (nc_bound csz nf cnt au mu); clear - B; tlia). unfold kFreeArraySize. clear - N1 N2 N3 N4 N5 N6 N7 NC. tlia. }
    { constructor. unfold kFreeArrayMapSize. exact M18. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - N8 N9. tlia. }
    { exact U7. }
    { exact OK. }
    { exact VISE. }
    { exact MI. }
    { exact ST. }
    { replace tp with (wz ATP); [exact REN| unfold wz; rewrite <- TP; apply Z_to_bv_bv_unsigned]. }
    { exact PC1. }
    { exact PC2. }
    { exact PC3. }
    { exact PC4. }
    { exact QST. }
    { exact TST. }
    all: try replace (sb + kSpaceSize + REGIONINFO_SIZE * c) with RI by (unfold kSpaceSize, REGIONINFO_SIZE; clear - ERI; tlia).
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - ERB; tlia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - EFA; tlia).
    { exact RIC. }
    { exact RST. }
    { exact FARR. }
    { exact FAJ. }
    { intros a kk Ha. exact (ak_resf_hi s mo AK a kk Ha). }
    { intros a kk Ha Hk. apply (ak_prim s mo AK a kk c HCC); [exact Ha| unfold kRegionSize; exact Hk]. }
    { exact NW. }
    { exact NWA. }
    { exact NOV. }
    { intros x Hx. apply (ak_zr_sb s mo AK). unfold kSpaceSize, kPageSize. fold sb. clear - Hx B6 B7 B8 ERB. tlia. }
    { exact (ak_zrsh s mo AK). }
    { exact (ak_lsh s mo AK). }
    { intros x Hx. exact (AWV x Hx). }
    { right; right. unfold ABUDGET, aPhi in AB0b. change (a_st s) with st in AB0b. unfold page_size in AB0b. clear - AB0a AB0b PROOM. tlia. }
    { exact (ak_atop s mo AK). }
    cbv beta. intros msF2 mo2 POST. lazy zeta in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & q2' & m' & L' & S' & POST).
    destruct POST as (OK2 & VIS2 & LED & MU & WM & MI2 & REN2 & ST2 & PC1' & PC3' & PC4' & QST' & TST' & RI' & RST' & FARR' & FAJ' & POI').
    destruct LED as (EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG).
    rewrite Z.ltb_irrefl in EL, ES, VMN. rewrite Z.sub_diag, Z.add_0_r in EAG. rewrite app_nil_l in ES || idtac. cbn [app] in ES.

    change (cnt =? mc) with drained in EL, ES, VMN, EAG, MU, PC1', PC3', PC4', RI', FARR', FAJ', POI'.
    change (mc / 2) with n in EL, ES, VMN, EAG, MU, PC1', PC3', PC4', RI', FARR', FAJ', POI'.
    change (if drained then rta_mfa nf n mfa else mfa) with mfa' in EL, ES, VMN, EAG, MU, RI', FAJ', POI'.
    change (if drained then n else 0) with k in MU, PC1', PC3', PC4', RI', FARR', FAJ'.
    replace (sb + c * 2 ^ 32 + kFreeArrayOffset) with (FA s c) in EL, ES, VMN, MU, FARR', FAJ', POI' by (unfold kFreeArrayOffset; clear - ERB EFA; tlia).
    replace (sb + c * 2 ^ 32) with (RB s c) in PC3' by (clear - ERB; tlia).
    replace (sb + kSpaceSize + REGIONINFO_SIZE * c) with RI in MU, RI', RST' by (unfold kSpaceSize, REGIONINFO_SIZE; clear - ERI; tlia).
    change (TH + 208 + PCLASS_SIZE * c) with P in MU, PC1', PC3', PC4'. change (TH + 208) with CA in MU.
    change (Z.shiftr (p - RB s c) kCompactPtrScale) with (addr_to_compact st c p) in PC3'.

    assert (DR : if drained then cnt = mc else cnt < mc).
    { unfold drained. destruct (Z.eq_dec cnt mc) as [E|NE]; [rewrite (proj2 (Z.eqb_eq _ _) E); exact E| rewrite (proj2 (Z.eqb_neq _ _) NE); clear - NE N4; tlia]. }
    assert (NC : 32 * (nf + cnt) <= 3758096384) by (apply (nc_bound csz nf cnt au mu); clear - B; tlia).
    assert (FROOM0 : efs_new (nf + n) <= kFreeArraySize).
    { unfold efs_new, round_up, kFreeArrayMapSize, kFreeArraySize. clear - B NC. Z.div_mod_to_equations. tlia. }
    pose proof (cd_state_fields st XC XB c p drained WQ HC' INIT CLS DR FROOM0) as FLD. cbv zeta in FLD.
    fold pc r cnt chunks nf mfa au mu fl mc n k in FLD. change (if drained then rta_mfa nf n mfa else mfa) with mfa' in FLD. fold st' in FLD.
    change (free_array_base st c) with (FA s c) in FLD.
    destruct FLD as (Fpc_c & Fpc_o & Frg_c & Frg_o & Fmaps & Fsb & Fpa & Fsec & Fch & Ftq & Fgq & Fnr & Fci & Fii & Fqx & Fqn & Fqc).
    pose proof (WFQ_cd_state st XC XB c p drained WQ HC' INIT CLS DR FROOM0) as WQ'. fold st' in WQ'.
    set (sA := mkAst st' TH CTX (a_fsb s) L' S' (a_Zr s) (a_AL s) (a_top s) (a_bot s)).
    destruct (cd_zones m' MU) as (AGsp & AGpend & AG2).
    pose proof (kr_of_flag drained cnt mc n nf mfa k mfa' eq_refl eq_refl eq_refl DR) as KR.
    pose proof (froom_of_flag drained n nf mfa mfa' eq_refl ltac:(unfold kFreeArraySize; exact N3) FROOM0) as FROOM.

    pose proof (munch_agree _ _ _ MU) as AGW.
    assert (JK2 : junk m' p csz).
    { eapply (junk_transport_pt (outside (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa')) m m' AGW WM); [exact SLOTJ|].
      intros a Ha. apply (ZC_slotW s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO). left. exact Ha. }
    assert (PS2 : poisoned m' p (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic).
    { eapply (poisoned_transport_pt (outside (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa')) m m' AGW WM); [exact SLOTP|].
      intros a Ha. apply (ZC_slotW s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO). right.
      rewrite Z2Nat.id in Ha by (clear - C1; Z.div_mod_to_equations; tlia). exact Ha. }

    assert (R2 : AREPQ sA XC XB m').
    { eapply (arepq_after_cd s m m' XC XB c p st' L' S' (a_AL s) lo (bv_unsigned sp) q0 q1 q2' q3 k mfa');
        first [exact RQ| exact HC'| exact INIT| exact CLS| exact KR| exact FROOM| exact WQ'| exact LO| exact AG2| exact WM| exact JK2| exact PS2| eassumption| idtac]. all: fail "R2". }
    assert (AWV2 : awin_vis sA m').
    { exact (awin_after_cd s m m' XC XB c p st' L' S' (a_AL s) lo k mfa' RQ HC' INIT CLS KR FROOM ES LO WM POI' AWV). }
    assert (FX2 : flagsx_rep m').
    { exact (flagsx_after_cd s m m' XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO AG2 WM FXR). }
    assert (AMX2 : AMODELX sA mo2).
    { eapply (amodelx_after_cd s mo mo2 XC (p :: XB) c st' L' S' (a_AL s) k mfa' (firstn (Z.to_nat k) chunks ++ fl));
        first [exact AMX| exact PL| exact WQ| exact HC| exact KR'| idtac].
      all: try first [exact FROOM| exact Fsb| exact Fpa| exact Fsec| exact Frg_c| exact Frg_o| exact Fmaps| exact EL| exact ES| exact VMM| exact VMR| exact VML| exact VMB| exact VMN| exact EAG].
      - destruct KR as [(K0 & M0 & _)|(Kn & _ & Mn)]; [left; exact (conj K0 M0)| right; exact (conj Kn Mn)].
      - exact (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK)).
      - exact (nonvm_same_atop _ _ NVS).
      - clear - AB0a. tlia. }

    assert (DEP2 : DEPOT asegs d m').
    { eapply (DEPOT_transport asegs d m m' _ DEP MU WM).
      pose proof (depot_avoid_cd s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO d DPL) as DAV.
      unfold depot_avoid, avoids in DAV |- *. rewrite !Forall_app in DAV. clear - DAV. tauto. }

    assert (MODEL : forall stA, same_but_shadow stA st -> exists stA' ev, cache_dealloc stA c p = Some (stA', ev) /\ same_but_shadow stA' st').
    { intros stA SBS. apply (cd_state_eval st XC XB c p drained WQ HC' INIT DR FROOM0 stA SBS).
      intros DT GT.
      assert (IM : forall a, sb <= a -> a + 1 <= aceil -> addr_is_in_mem a = true).
      { intros a Ha Hb. apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. acb. clear - Ha Hb B ACEILB. tlia. }
      change (free_array_base st c) with (FA s c). fold r in GT |- *. fold nf mfa mc in GT |- *. fold n in GT |- *.
      assert (E1 : efs_new (nf + n) = mfa + 262144).
      { unfold efs_new, round_up, kFreeArrayMapSize. clear - B GT NC. Z.div_mod_to_equations. tlia. }
      rewrite E1. split; [| split; [| split]].
      - change 7 with (Z.ones 3). rewrite Z.land_ones by (clear - B; tlia). change (2 ^ 3) with 8. clear - B M18. Z.div_mod_to_equations. tlia.
      - apply IM; clear - B; tlia.
      - change 7 with (Z.ones 3). rewrite Z.land_ones by (clear - B; tlia). change (2 ^ 3) with 8. clear - B M18. Z.div_mod_to_equations. tlia.
      - apply IM; clear - B; tlia. }

    assert (KB2 : 0 <= k <= cnt /\ mfa <= mfa' <= 536870912).
    { unfold kFreeArraySize in FROOM. revert FROOM. pose proof KR as KR'. fold mc in KR'. fold n in KR'. destruct KR' as [(-> & -> & _)|(-> & E & ->)]; [clear - B; intros; tlia|].
      unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize. destruct (Z.leb_spec (4 * (nf + n)) mfa) as [LE|GT]; [clear - B E; intros; tlia|]. clear - B E GT. intros FROOM. Z.div_mod_to_equations; tlia. }
    assert (SB2 : sh sb <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh (sb + 2 ^ 37 + 4096)).
    { unfold sh. change (2 ^ 37) with 137438953472. clear - B KB2. Z.div_mod_to_equations. tlia. }
    apply K. unfold cd_gpost, rstep_post.
    exists sA, t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    repeat match goal with |- _ /\ _ => split end; try reflexivity.
    - cbn [a_sb a_st]. unfold a_sb. cbn [a_st]. exact Fsb.
    - unfold a_pa. cbn [a_st]. exact Fpa.
    - intros sc Hsc. cbn [a_st] in Hsc. rewrite Fsec in Hsc. exact Hsc.
    - exact Fci.
    - intros c0 H0. cbn [a_st]. destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite Frg_c; reflexivity| rewrite (Frg_o c0 H0 NE); reflexivity].
    - exact OK2.
    - exact VIS2.
    - exact R2.
    - exact AWV2.
    - exact FX2.
    - exact AMX2.
    - exact NVS.
    - apply avmx_same; [exact VMM| cbn [a_st]; exact Fsec].
    - unfold depot_cov in DCOV |- *. rewrite VMM. exact DCOV.
    - exact DEP2.
    - unfold depot_placed in DPL |- *. cbn [a_thr a_sb a_ctx a_pa a_st]. unfold a_sb, a_pa in DPL |- *. cbn [a_st]. rewrite Fsb, Fpa, Fsec. exact DPL.
    - exact MI2.
    - exact ST2.
    -
      apply (acompl_of_munch s sA d lo (bv_unsigned sp) _ m m' MU). intros iv a Hiv Ha.
      unfold lcd_W in Hiv. unfold awrit. change (a_thr s) with TH. change (a_sb s) with sb.
      destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Ha; unfold kPageSize, kSpaceSize;
        first [ left; exact Ha
              | right; left; clear - Ha B KB2; tlia
              | right; right; left; clear - Ha B KB2; tlia
              | right; right; right; left; clear - Ha B KB2 SB2; tlia ].
    - apply avis_of_wmono. exact WM.
    - exact AGpend.
    -
      intros ch0 H0 _. cbn [a_st]. unfold chunk_list. rewrite Fch. exact H0.
    -
      intros a (ch0 & H0 & E0 & Ha). apply AG2.
      pose proof (record_extQ s _ _ OKQ ch0 H0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). pose proof (chunk_alignQ s _ _ OKQ ch0 H0) as (_ & _ & A3 & _).
      assert (RU : ch_used ch0 <= round_up (ch_used ch0) 8 /\ 0 <= nsh (ch_used ch0) /\ 8 * nsh (ch_used ch0) = round_up (ch_used ch0) 8)
        by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; tlia).
      destruct Ha as [Ha|Ha].
      + apply (ZC_rec s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO ch0 a H0). clear - Ha X3 X6 X7 X8 RU. tlia.
      + apply (ZC_rec_sh s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO ch0 (ch_user_beg ch0) (nsh (ch_used ch0)) a H0);
          [clear - X3 X6 X8; tlia| clear - X7 RU; tlia| clear - A3; Z.div_mod_to_equations; tlia| clear - RU; tlia| exact Ha].
    - exact MODEL.
  Qed.

End CDStep.
End HCW.
