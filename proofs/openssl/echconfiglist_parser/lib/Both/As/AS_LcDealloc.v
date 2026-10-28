(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AW_PoisonShadow AW_Leaves AllocWalkKit AW_MmapFixed AW_Efs AW_Populate AW_Gfa AW_LargeAlloc1 SecLazy AS_Refill1 AS_Refill2 AS_Refill3
     AW_Rta1 AW_MaybeRelease AW_Rta2 AS_Rta AW_LcDealloc AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocPerfKit AllocPerfKit2.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import PerfLia.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Lemma stk_of_u32arr : forall m A ws, u32arr asegs m A ws -> stk asegs m A (A + 4 * Z.of_nat (length ws)).
Proof.
  intros m A ws [(Ha & Hl & Hb) (_ & Hh & Hw)]. rewrite u32s_length, Nat2Z.inj_mul in Hl. change (Z.of_nat 4) with 4 in Hl.
  split; [tlia|]. split; [tlia|]. intros a Hr. split.
  - replace a with (A + (a - A))%Z by tlia. apply Hw. tlia.
  - replace a with (A + Z.of_nat (Z.to_nat (a - A)))%Z by tlia. rewrite Hb by (rewrite u32s_length; tlia).
    destruct (nth_error (u32s ws) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite u32s_length in E. tlia.
Qed.

Lemma wlist_rev_split : forall (k : nat) (l : list Z),
  wlist (rev l) = wlist (rev (skipn k l)) ++ wlist (rev (firstn k l)).
Proof. intros k l. unfold wlist. rewrite <- map_app, <- rev_app_distr, firstn_skipn. reflexivity. Qed.

(* [comment removed for export] *)
Definition lcd_W (lo sp P CA cnt1 R FAB TH nf mfa mfa' : Z) : list ivl :=
  [(lo, sp); (P, P + 4); (P + 16 + 4 * cnt1, P + 20 + 4 * cnt1); (CA + 2576, CA + 2584);
   (R, R + 8); (R + 16, R + 32); (R + 80, R + 88); (FAB + 4 * nf, FAB + mfa'); (sh (FAB + mfa), sh (FAB + mfa) + (mfa' - mfa) / 8); (TH + 2800, TH + 3168)]%Z.

(* [comment removed for export] *)
Definition cache_dealloc_post (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c P CA R rbeg FAB TH TSD CTX sb ARI p cnt mc nf mfa au mu : Z) (chunks fl : list Z) (q0 q1 q3 : word) (drained : bool)
    (msF' : machine_state) (mo' : Model) : Prop :=
  let n := mc / 2 in
  let k := (if drained then n else 0) in
  let cnt1 := cnt - k in
  let nf' := nf + k in
  let mfa' := (if drained then rta_mfa nf n mfa else mfa) in
  let kept := skipn (Z.to_nat k) chunks in
  let moved := firstn (Z.to_nat k) chunks in
  exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 q2 : word) m' L' S',
     lzok asegs L' S' Zr (mkCfg msF' mo')
  /\ restrict L' S' msF'
     = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
  /\ rf_ledger mo L S rbeg FAB mu mu mfa mfa' L' S' mo'
  /\ munch (lcd_W lo (bv_unsigned sp) P CA cnt1 R FAB TH nf mfa mfa') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ RENV tp TSD CTX TH sb ARI m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' P [C4 (wz (cnt1 + 1)); C4 (wz mc)]
  /\ u32arr asegs m' (P + 16) (wlist (rev (Z.shiftr (p - rbeg) kCompactPtrScale :: kept)))
  /\ stk asegs m' (P + 16 + 4 * (cnt1 + 1)) (P + 80)
  /\ rw_cells asegs m' (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs m' (TH + 2800) (TH + 3168)
  /\ rw_cells asegs m' R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf'); C8 (wz mfa'); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]
  /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev (moved ++ fl))) /\ stk asegs m' (FAB + 4 * nf') (FAB + mfa')
  /\ poisoned m' (FAB + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa.
End HCW.

Section LcDealloc.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  (* [comment removed for export] *)
  Variables (lo sb c TH CTX TSD p : Z).
  (* [comment removed for export] *)
  Variables (cnt mc csz : Z) (chunks : list Z) (q0 q1 q2 q3 : word).
  Variables (nf mfa au mu : Z) (fl : list Z).
  Let CA := TH + 208.
  Let P := CA + PCLASS_SIZE * c.
  Let ARI := sb + kSpaceSize.
  Let R := ARI + REGIONINFO_SIZE * c.
  Let rbeg := sb + c * 2^32.
  Let FAB := rbeg + kFreeArrayOffset.
  Let n := mc / 2.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 688 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil. Hypothesis SBA : hidden (sb mod 65536 = 0).
  Hypothesis TPR : 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis THA : hidden (TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis PR : rbeg <= p < rbeg + 2^32. Hypothesis PA : hidden (p mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis MCR : 2 <= mc <= 16. Hypothesis CNT : cnt = zlen chunks. Hypothesis CB : 0 <= cnt <= mc. Hypothesis CSZ : 0 <= csz < 2^64.
  (* [comment removed for export] *)
  Hypothesis NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize /\ 4 * (nf + n) <= kFreeArraySize. Hypothesis MFAA : hidden (mfa mod kFreeArrayMapSize = 0).
  Hypothesis AUR : 0 <= au <= mu /\ mu + kUserMapSize <= kFreeArrayOffset.
  Hypothesis FLL : length fl = Z.to_nat nf.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz AINST) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x199618) fc None m (seg_rom asegs).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ENV : RENV tp TSD CTX TH sb ARI m.
  Hypothesis PC1 : rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)].
  Hypothesis PC2 : rw_cells asegs m (P + 8) [C8 (wz csz)].
  Hypothesis PC3 : u32arr asegs m (P + 16) (wlist (rev chunks)).
  Hypothesis PC4 : stk asegs m (P + 16 + 4 * cnt) (P + 80).
  Hypothesis QST : rw_cells asegs m (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis RI : rw_cells asegs m R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)).
  Hypothesis FAJ : stk asegs m (FAB + 4 * nf) (FAB + mfa).
  (* [comment removed for export] *)
  Hypothesis RESF : forall (a k : word), AHI_LO <= bv_unsigned a -> region_free (vm_reserved (m_vmmaps mo)) a k = true.
  Hypothesis PRIM : forall (a k : word), rbeg <= bv_unsigned a -> bv_unsigned a + bv_unsigned k <= rbeg + 2^32 -> map_contains (vm_maps (m_vmmaps mo)) a k = true.
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis ZRP : forall x : word, rbeg <= bv_unsigned x < rbeg + 2^32 -> in_rangesb x Zr = false.
  Hypothesis ZRSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x Zr = true.
  Hypothesis LSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  Hypothesis BUD : cnt < mc \/ 4 * (nf + n) <= mfa \/ eager_used mo + pages_total S * 4096 + 303104 <= vm_limit (m_vmmaps mo).
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Ltac prepL :=
    unfold kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kFreeArrayOffset, kNumClasses in NFR, AUR, HC;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (LFL : length (wlist (rev fl)) = Z.to_nat nf) by (rewrite wlist_length, length_rev; exact FLL);
    assert (LCH : length (wlist (rev chunks)) = Z.to_nat cnt) by (rewrite wlist_length, length_rev; unfold zlen in CNT; clear - CNT; try acb; tlia);
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ bv_unsigned sp + 16 <= 140737488355328)
      by (clear - LO RNG SBR TPR SPT; try acb; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, kPageSize, AIMG_TOP in *; acb; aunf; tlia);
        region_sides; name_bands;
    assert (GEO : R = sb + 137438953472 + 128 * c /\ rbeg = sb + c * 4294967296 /\ FAB = rbeg + 3758096384 /\ ARI = sb + 137438953472 /\ P = CA + 80 * c /\ CA = TH + 208)
      by (subst R rbeg FAB ARI P CA; unfold kSpaceSize, REGIONINFO_SIZE, kFreeArrayOffset, PCLASS_SIZE; repeat split; reflexivity);
    destruct GEO as (ER & ERB & EFAB & EARI & EP & ECA);
    assert (NR1 : 1 <= n <= 8 /\ n + n <= mc) by (subst n; clear - MCR; try acb; Z.div_mod_to_equations; tlia);
    assert (CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0)   (* [comment removed for export] *)
      by (acb; destruct THA as [T16]; match goal with TB : akobj TH 4096 |- _ => clear - BND ECA T16 TB end; try acb; rewrite ECA;
          split; [eapply akobj_sub; [eassumption| tlia| tlia] | repeat split; [tlia| Z.div_mod_to_equations; tlia]]);
    assert (BNDL : sb + 137438953472 + 128 <= R /\ R + 128 <= sb + 137438953472 + 4096 /\ sb + 4294967296 <= rbeg /\ rbeg + 4294967296 <= sb + 137438953472
                   /\ FAB = rbeg + 3758096384 /\ TH + 288 <= P /\ P + 80 <= TH + 2768)
      by (clear - BND ER ERB EFAB EP ECA HC; try acb; rewrite ER, ERB, EP, ECA; repeat split; tlia).

  Lemma lcd_s_nodrain : cnt < mc ->
    (forall msF' mo', cache_dealloc_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c P CA R rbeg FAB TH TSD CTX sb ARI p cnt mc nf mfa au mu
                        chunks fl q0 q1 q3 false msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros LT K. prepL.
    pose proof (re_isb _ _ _ _ _ _ _ ENV) as ISB.
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply (lcd_head_nodrain ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c CA p cnt mc MI ST LO);
        try reflexivity; try eassumption. all: first [clear - HI; try acb; tlia | clear - PR BND BNDL HC; try acb; tlia | clear - MCR CB LT; try acb; aunf; tlia]. }
    clear OK VISE. cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (a5' & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    rewrite ?unsigned_lit in VIS1 by (clear - SPR BND HI; try acb; tlia).
    rrenv_img_at ENV MU1 WM1 ENV1. clear ENV ISB ST MI.
    transport_after_call asegs m m1 MU1 WM1.
    eapply (munch_weaken _ (lcd_W lo (bv_unsigned sp) P CA cnt R FAB TH nf mfa mfa)) in MU1; [| unfold lcd_W; rx_sub_fp_struct].
    pose proof (re_isb _ _ _ _ _ _ _ ENV1) as ISB1.
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF1 _ mo1 Q OK1 VIS1).
    { eapply (lcd_push ra sp gp tp _ t0 t1 t2 s1 _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 F fc m1 lo sb c CA p cnt mc csz chunks q0 q1 q2 q3 m1 MI1
                (munch_refl _ m1) (wmono_refl asegs m1) ST1 LO); try reflexivity; try eassumption.
      all: try first [clear - HI; try acb; tlia | clear - SBR; try acb; unfold AHI_LO, kSpaceSize, kPageSize in *; tlia | destruct PA as [PA']; exact PA' | clear - LT CB MCR; try acb; tlia].
      unfold CACHE_STATS. replace (CA + 2560) with (TH + 2768) by (rewrite ECA; clear; tlia). exact QST. }
    clear OK1 VIS1. cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & q2' & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & PC1' & PC3' & PC4' & QST').
    clear ISB1 PC1 PC3 PC4 QST ST1 FR1. unfold CACHE_STATS in QST'. replace (CA + 2560) with (TH + 2768) in QST' by (rewrite ECA; clear; tlia).
    rrenv_img_at ENV1 MU2 WM2 ENV2. clear ENV1.
    unfold lcd_W in MU1. transport_after_call asegs m1 m2 MU2 WM2.
    apply K. unfold cache_dealloc_post. cbv zeta. change (Z.to_nat 0) with 0%nat. cbn [skipn firstn app].
    rewrite !Z.sub_0_r, !Z.add_0_r.
    do 16 eexists. exists m2, L, S.
    split; [exact OK2|]. split; [exact VIS2|].
    split. { unfold rf_ledger. rewrite !Z.ltb_irrefl. cbn [app]. split; [reflexivity|]. split; [reflexivity|].
             split; [eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| apply nonvm_same_mat; exact SBM2]|].
             rewrite (same_but_materialized_vmmaps _ _ SBM2), (same_but_materialized_vmmaps _ _ SBM1), (same_but_materialized_eager _ _ SBM2), (same_but_materialized_eager _ _ SBM1).
             repeat (split; [reflexivity|]). clear; tlia. }
    split; [unfold lcd_W; exact MU1|]. split; [exact WM1|]. split; [exact MI2|]. split; [exact ENV2|]. split; [exact ST2|].
    split; [exact PC1'|]. split; [exact PC3'|]. split; [exact PC4'|]. split; [exact QST'|]. split; [exact TST|].
    split; [exact RI|]. split; [exact RST|]. split; [exact FARR|]. split; [exact FAJ|].
    rewrite Z.sub_diag. change (0 / 8) with 0. cbn [Z.to_nat].
    apply poisoned_0; unfold AHI_LO, sh, ASHADOW_BASE in *; acb.
    - clear - BND NFR BNDL; try acb. tlia.
    - destruct MFAA as [MFAA']. unfold kFreeArrayMapSize in MFAA'. destruct SBA as [S64]. destruct BNDL as (_ & _ & _ & _ & EF & _). rewrite EF, ERB.
      clear - S64 MFAA'; try acb. Z.div_mod_to_equations. tlia.
    - clear - BND NFR BNDL; try acb. tlia.
  Qed.

  Lemma lcd_s_drain : cnt = mc ->
    (forall msF' mo', cache_dealloc_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c P CA R rbeg FAB TH TSD CTX sb ARI p cnt mc nf mfa au mu
                        chunks fl q0 q1 q3 true msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros EQ K. prepL.
    destruct BUD as [LT | BUDd]. { exfalso. clear - LT EQ; try acb. tlia. }
    pose proof (re_isb _ _ _ _ _ _ _ ENV) as ISB.
    assert (E112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - SPR BND HI; try acb; tlia).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply (lcd_head_drain ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c CA p cnt mc MI ST LO);
        try reflexivity; try eassumption. all: first [clear - HI; try acb; tlia | clear - PR BND BNDL HC; try acb; tlia | clear - MCR CB EQ; try acb; aunf; tlia]. }
    clear OK VISE. cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (m1 & j8 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & FR0 & PC1').
    cbv zeta in VIS1, PC1'. fold n in VIS1, PC1'. rewrite ?unsigned_lit in VIS1 by (clear - SPR BND HI; try acb; tlia).
    rrenv_img_at ENV MU1 WM1 ENV1. clear ENV ISB ST MI PC1.
    transport_after_call asegs m m1 MU1 WM1.
    eapply (munch_weaken _ (lcd_W lo (bv_unsigned sp) P CA (cnt - n) R FAB TH nf mfa (rta_mfa nf n mfa))) in MU1; [| unfold lcd_W; rx_sub_fp_struct].
    (* [comment removed for export] *)
    rewrite (wlist_rev_split (Z.to_nat n) chunks) in PC3. apply u32arr_app in PC3. destruct PC3 as [PCK PCM].
    assert (LK : length (wlist (rev (skipn (Z.to_nat n) chunks))) = Z.to_nat (cnt - n)) by (rewrite wlist_length, length_rev, length_skipn; unfold zlen in CNT; clear - CNT NR1 CB EQ; try acb; tlia).
    assert (LM : length (wlist (rev (firstn (Z.to_nat n) chunks))) = Z.to_nat n) by (rewrite wlist_length, length_rev, firstn_length_le; [reflexivity|]; unfold zlen in CNT; clear - CNT NR1 CB EQ; try acb; tlia).
    rewrite LK in PCM. replace (P + 16 + 4 * Z.of_nat (Z.to_nat (cnt - n))) with (P + 16 + 4 * (cnt - n)) in PCM by (clear - NR1 CB EQ MCR; try acb; tlia).
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -104)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) + 8)) in VIS1 by (f_equal; rewrite E112; clear; tlia).
    eapply (rta_sreach L S Zr msF1 mo1 Q (wz 0x199a10) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (wz P) (wz CA) _ _ _ a7 (wz AINST) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m1 lo sb c (P + 16 + 4 * (cnt - n)) n TH CTX TSD nf mfa au mu fl (wlist (rev (firstn (Z.to_nat n) chunks))));
      rewrite ?E112; try eassumption; try exact OK1.
    all: try (clear - HI; try acb; tlia). all: try (clear - BND; try acb; tlia).
    { destruct SPA as [SPAq]. split. clear - SPAq SPR; try acb. Z.div_mod_to_equations. tlia. }
    { unfold kFreeArrayMapSize. clear - NR1; try acb. tlia. }
    { (* [comment removed for export] *)
      split; [eapply akobj_sub; [exact (proj1 CAR)| rewrite EP; clear - NR1 CB HC EQ MCR; try acb; tlia| rewrite EP; clear - NR1 CB HC EQ MCR; try acb; tlia]
            | clear - BND BNDL NR1 CB EQ MCR CAR EP; try acb; tlia]. }
    { destruct THA as [T16]. split. rewrite EP, ECA. clear - T16; try acb. Z.div_mod_to_equations. tlia. }
    { destruct PLC as [PLCq]. unfold kSpaceSize in PLCq. split. rewrite EP, ECA. unfold kFreeArraySize, kFreeArrayOffset, kSpaceSize.
      clear - BND BNDL NR1 CB EQ MCR NFR HC ERB PLCq; try acb. rewrite ERB in BNDL. repeat split; tlia. }
    { intros a k Ha. rewrite (same_but_materialized_vmmaps _ _ SBM1). apply RESF. exact Ha. }
    { intros a k H1 H2. rewrite (same_but_materialized_vmmaps _ _ SBM1). apply PRIM; assumption. }
    { rewrite (same_but_materialized_vmmaps _ _ SBM1). exact NW. }
    { rewrite (same_but_materialized_vmmaps _ _ SBM1). exact NWA. }
    { rewrite (same_but_materialized_vmmaps _ _ SBM1). exact NOV. }
    { intros x Hx. apply WM1. apply SVIS. exact Hx. }
    { rewrite (same_but_materialized_vmmaps _ _ SBM1), (same_but_materialized_eager _ _ SBM1). exact BUDd. }
    { rewrite (same_but_materialized_vmmaps _ _ SBM1). exact ATOP. }   (* [comment removed for export] *)
    clear OK1 VIS1. intros msF2 mo2 P2.
    destruct P2 as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & L2 & S2
                    & OK2 & VIS2 & LED2 & MU2 & WM2 & MI2 & ENV2 & ST2 & RI2 & RST2 & FARR2 & FAJ2 & SRC2 & TST2 & POI2).
    rewrite ?E112 in VIS2. rewrite ?E112 in MU2. rewrite ?E112 in ST2.
    replace (ret_pc (wz 0x199a10)) with (Z_to_bv 64 0x199a10) in VIS2 by (symmetry; apply ret_pc_even; [clear; tlia | reflexivity]).
    change (sb + kSpaceSize + REGIONINFO_SIZE * c) with R in MU2, RI2, RST2.
    change (sb + c * 2 ^ 32 + kFreeArrayOffset) with FAB in LED2, MU2, FARR2, FAJ2, POI2.
    clear ENV1 TST RI RST FARR FAJ ST1.
    (* [comment removed for export] *)
    assert (MF2 : mfa <= rta_mfa nf n mfa <= 536870912 /\ 4 * (nf + n) <= rta_mfa nf n mfa).
    { unfold rta_mfa. destruct (Z.leb_spec (4 * (nf + n)) mfa) as [FA|SL]; [clear - FA NFR; try acb; tlia|].
      destruct MFAA as [MFAA']. unfold kFreeArrayMapSize in MFAA'. unfold efs_new, round_up, kFreeArrayMapSize. clear - SL NFR NR1 MFAA'; try acb. Z.div_mod_to_equations. tlia. }
    assert (exists mfa2, mfa2 = rta_mfa nf n mfa) as [mfa2 EMF2] by (eexists; reflexivity). rewrite <- EMF2 in *.
    pose proof (I : region_rank (sh (FAB + mfa)) 1) as RXRsh.
    assert (SHR : 2148314624 <= sh (FAB + mfa) /\ sh (FAB + mfa) + (mfa2 - mfa) / 8 <= 17594333495296).
    { unfold sh, ASHADOW_BASE. destruct BNDL as (_ & _ & _ & _ & EF & _). rewrite EF, ERB. clear - BND NFR MF2 HC; try acb. Z.div_mod_to_equations. tlia. }
    unfold lcd_W in MU1. unfold rta_W in MU2. transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L2 S2 Zr _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (lcd_drain_tail sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 lo c CA p (cnt - n) (wz mc) (wz AINST) j8 MI2 ST2 LO);
        try eassumption. all: clear - HI NR1 CB EQ MCR; try acb; tlia. }
    clear OK2 VIS2. cbv beta. intros msF3 mo3 OK3 SBM3 HS3 P3.
    destruct P3 as (m3 & VIS3 & MU3 & WM3 & MI3 & ST3).
    rewrite ?unsigned_lit in VIS3 by (clear - SPR BND HI; try acb; tlia).
    replace (bv_unsigned sp - 160) with (bv_unsigned sp + -160) in MU3 by (clear; tlia). replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) in MU3 by (clear; tlia).
    clear FR0 ST2 MI2.
    rrenv_img_at ENV2 MU3 WM3 ENV3. clear ENV2.
    assert (POI3 := poisoned_transport _ m2 m3 _ _ _ POI2 MU3 WM3 ltac:(hci; cbn [disjoint_from]; split; [| exact I]; left; clear - SHR BND HI MF2; try acb; tlia)). clear POI2.
    transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3.
    (* [comment removed for export] *)
    pose proof (re_isb _ _ _ _ _ _ _ ENV3) as ISB3.
    assert (PC4' : stk asegs m3 (P + 16 + 4 * (cnt - n)) (P + 80)).
    { pose proof (stk_of_u32arr _ _ _ SRC2) as SK. rewrite LM in SK. replace (P + 16 + 4 * (cnt - n) + 4 * Z.of_nat (Z.to_nat n)) with (P + 16 + 4 * cnt) in SK by (clear - NR1; try acb; tlia).
      eapply stk_merge; [exact SK| exact PC4| clear - NR1 CB EQ MCR; try acb; tlia]. }
    clear SRC2 PC4.
    eapply (evt_sreach_lazy_at asegs L2 S2 Zr _ msF3 _ mo3 Q OK3 VIS3).
    { eapply (lcd_push ra sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 s3 s4 F fc m3 lo sb c CA p (cnt - n) mc csz
                (skipn (Z.to_nat n) chunks) q0 q1 q2 q3 m3 MI3 (munch_refl _ m3) (wmono_refl asegs m3) ST3 LO); try reflexivity; try eassumption.
      all: try first [clear - HI; try acb; tlia | clear - SBR; try acb; unfold AHI_LO, kSpaceSize, kPageSize in *; tlia | destruct PA as [PA']; exact PA' | clear - NR1 CB EQ MCR; try acb; tlia
                     | unfold zlen in CNT |- *; rewrite length_skipn; clear - CNT NR1 CB EQ; try acb; tlia].
      unfold CACHE_STATS. replace (CA + 2560) with (TH + 2768) by (rewrite ECA; clear; tlia). exact QST. }
    clear OK3 VIS3. cbv beta. intros msF4 mo4 OK4 SBM4 HS4 P4.
    destruct P4 as (u0' & u1' & u2' & v0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & q2' & m4 & VIS4 & MU4 & WM4 & MI4 & ST4 & PC1f & PC3f & PC4f & QSTf).
    clear ISB3 PC1' PCK PC4' QST ST3 FR1. unfold CACHE_STATS in QSTf. replace (CA + 2560) with (TH + 2768) in QSTf by (rewrite ECA; clear; tlia).
    replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) in MU4 by (clear; tlia).
    rrenv_img_at ENV3 MU4 WM4 ENV4. clear ENV3.
    assert (POI4 := poisoned_transport _ m3 m4 _ _ _ POI3 MU4 WM4 ltac:(hci; cbn [disjoint_from]; match goal with TB : akobj TH 4096 |- _ => clear - SHR BND BNDL HI NR1 CB EQ MCR MF2 TB end; try acb; aunf; repeat split; tlia)). clear POI3.   (* [comment removed for export] *)
    transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4.
    apply K. unfold cache_dealloc_post. cbv zeta. cbn [andb orb]. fold n. rewrite <- EMF2.
    do 16 eexists. exists m4, L2, S2.
    split; [exact OK4|]. split; [exact VIS4|].
    split. { clear - LED2 SBM1 SBM3 SBM4; try acb. unfold rf_ledger in *.
             rewrite (same_but_materialized_vmmaps _ _ SBM4), (same_but_materialized_vmmaps _ _ SBM3), (same_but_materialized_eager _ _ SBM4), (same_but_materialized_eager _ _ SBM3).
             rewrite (same_but_materialized_vmmaps _ _ SBM1), (same_but_materialized_eager _ _ SBM1) in LED2.
             destruct LED2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
             split; [exact A1|]. split; [exact A2|].
             split. { eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1|]. eapply nonvm_same_trans; [exact A3|].
                      eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM3| apply nonvm_same_mat; exact SBM4]. }
             split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9| exact A10]. }
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI4|]. split; [exact ENV4|]. split; [exact ST4|].
    split; [exact PC1f|]. split; [exact PC3f|]. split; [exact PC4f|]. split; [exact QSTf|]. split; [exact TST2|].
    split; [exact RI2|]. split; [exact RST2|].
    split. { unfold wlist in FARR2 |- *. rewrite rev_app_distr, map_app. exact FARR2. }
    split; [exact FAJ2| exact POI4].
  Qed.

  (* [comment removed for export] *)
  Theorem cache_dealloc_sreach :
    (forall msF' mo', cache_dealloc_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c P CA R rbeg FAB TH TSD CTX sb ARI p cnt mc nf mfa au mu
                        chunks fl q0 q1 q3 (cnt =? mc) msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. destruct (Z.eq_dec cnt mc) as [EQ|NE].
    - rewrite (proj2 (Z.eqb_eq _ _) EQ) in K. exact (lcd_s_drain EQ K).
    - rewrite (proj2 (Z.eqb_neq _ _) NE) in K. apply lcd_s_nodrain; [clear - NE CB; try acb; tlia| exact K].
  Qed.
End LcDealloc.

