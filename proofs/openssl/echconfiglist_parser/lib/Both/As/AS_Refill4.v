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
     AW_PoisonShadow AW_Leaves AllocWalkKit AW_MmapFixed AW_Efs AW_Populate AW_Gfa AW_InitCache AW_Refill AW_LargeAlloc1 SecLazy AS_Refill1 AS_Refill2 AS_Refill3 AllocTacX.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaRel2.
Local Ltac qlia ::= first [ solve [rx_prune; n8v_prune_plain2; qlia1] | rx_prune; qlia1 ].


Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section Refill.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  (* [comment removed for export] *)
  Variables (lo sb c CA TH CTX TSD : Z).
  Variables (nf mfa au mu : Z) (fl : list Z) (inited : bool).
  Let ARI := sb + kSpaceSize.
  Let R := ARI + REGIONINFO_SIZE * c.
  Let P := CA + PCLASS_SIZE * c.
  Let rbeg := sb + c * 2^32.
  Let FAB := rbeg + kFreeArrayOffset.
  Let n := rf_n c.
  Let csz := class_size c.

  (* [comment removed for export] *)
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 672 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis CAE : CA = TH + 208.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil. Hypothesis SBA : hidden (sb mod 65536 = 0).
  Hypothesis TPR : 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis THA : hidden (TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
  Hypothesis NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize. Hypothesis MFAA : hidden (mfa mod kFreeArrayMapSize = 0).
  Hypothesis AUR : 0 <= au <= mu /\ mu + kUserMapSize <= kFreeArrayOffset. Hypothesis MUA : hidden (mu mod kUserMapSize = 0).
  Hypothesis FLL : length fl = Z.to_nat nf.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz P) (wz AINST) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x19bdac) fc None m (seg_rom asegs).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ENV : RENV tp TSD CTX TH sb ARI m.
  Hypothesis LENF : Z.of_nat (length (wlist (rev fl))) = nf.
  (* [comment removed for export] *)
  Hypothesis PC1 : rw_cells asegs m P [C4 (wz 0); C4 (wz (if inited then max_count c else 0))].
  Hypothesis PCJ : stk asegs m (P + 16) (P + 80).
  Hypothesis FAM : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 cs]
                                             /\ (inited = true -> mc = wz (max_count c') /\ cs = wz (class_size c')).
  (* [comment removed for export] *)
  Variables (q0 q1 q2 q3 : word).
  Hypothesis QST : rw_cells asegs m (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  (* [comment removed for export] *)
  Hypothesis RI : rw_cells asegs m R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis RIJ : stk asegs m (R + 64) (R + 68).
  Hypothesis EXH : rw_cells asegs m (R + 68) [C1 (b8 0)].
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)).
  Hypothesis FAJ : stk asegs m (FAB + 4 * nf) (FAB + mfa).
  Hypothesis USJ : stk asegs m (rbeg + au) (rbeg + mu).
  (* [comment removed for export] *)
  Hypothesis RESF : forall (a k : word), AHI_LO <= bv_unsigned a -> region_free (vm_reserved (m_vmmaps mo)) a k = true.
  Hypothesis PRIM : forall (a k : word), rbeg <= bv_unsigned a -> bv_unsigned a + bv_unsigned k <= rbeg + 2^32 -> map_contains (vm_maps (m_vmmaps mo)) a k = true.
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis ZRP : forall x : word, rbeg <= bv_unsigned x < rbeg + 2^32 -> in_rangesb x Zr = false.
  Hypothesis ZRSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x Zr = true.
  Hypothesis LSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  Hypothesis BUD : eager_used mo + pages_total S * 4096 + 606208 <= vm_limit (m_vmmaps mo).
  (* [comment removed for export] *)
  Hypothesis TAIL : mu - au < csz + kUserMapSize. Hypothesis NFAU : csz * nf <= au.
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Ltac prepR :=
    unfold kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kFreeArrayOffset in NFR, AUR;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ bv_unsigned sp + 16 <= 140737488355328)
      by (clear - LO RNG SBR TPR SPT; try acb; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, kPageSize, AIMG_TOP in *; acb; aunf; lia);
        region_sides; name_bands;
    pose proof (max_count_facts c ltac:(hci; clear - HC; try acb; lia)) as MCF; fold n in MCF;
    assert (NR : 1 <= n <= 8 /\ n + n = max_count c) by (clear - MCF; try acb; subst n; unfold rf_n; destruct MCF as [M1 M2];
       destruct (proj1 (Z.even_spec _) M2) as [k Hk]; rewrite Hk in *; rewrite (Z.mul_comm 2 k), Z.div_mul by lia; lia);
    clear MCF;
    assert (CSZ : 32 <= csz <= 65536) by (subst csz; pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as CST; clear - CST HC; try acb; lia);
    assert (GEO : R = sb + 137438953472 + 128 * c /\ P = CA + 80 * c /\ rbeg = sb + c * 4294967296 /\ FAB = rbeg + 3758096384 /\ ARI = sb + 137438953472)
      by (subst R P rbeg FAB ARI; unfold kSpaceSize, REGIONINFO_SIZE, PCLASS_SIZE, kFreeArrayOffset; repeat split; reflexivity);
    destruct GEO as (ER & EP & ERB & EFAB & EARI);
    assert (DEFh : hidden (n = rf_n c /\ csz = class_size c)) by (split; split; reflexivity);
    (* [comment removed for export] *)
    assert (CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0)   (* [comment removed for export] *)
      by (acb; destruct THA as [T16]; match goal with TB : akobj TH 4096 |- _ => clear - BND CAE T16 TB end; try acb; subst CA;
          split; [eapply akobj_sub; [eassumption| lia| lia] | repeat split; [lia| Z.div_mod_to_equations; lia]]);
    assert (ARIR : AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND EARI S64; try acb; rewrite EARI;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);
    assert (SBR4 : AHI_LO <= sb /\ sb + 2^37 <= aceil /\ sb mod 4096 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND S64; try acb;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);
    assert (RR : AHI_LO <= R /\ R + 128 <= aceil /\ R mod 128 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND ER S64 HC; try acb; rewrite ER;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);
    assert (RBG : AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND ERB S64 HC; try acb; rewrite ERB;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);
    (* [comment removed for export] *)
    assert (ALh : hidden ((akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0) /\ (AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0)
                  /\ (AHI_LO <= sb /\ sb + 2^37 <= aceil /\ sb mod 4096 = 0) /\ (AHI_LO <= R /\ R + 128 <= aceil /\ R mod 128 = 0)
                  /\ (AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0)))
      by (split; exact (conj CAR (conj ARIR (conj SBR4 (conj RR RBG)))));
    clear CAR ARIR SBR4 RR RBG;
    assert (BNDL : sb + 137438953472 + 128 <= R /\ R + 256 <= sb + 137438953472 + 4096 /\ sb + 4294967296 <= rbeg /\ rbeg + 8589934592 <= sb + 137438953472
                   /\ FAB = rbeg + 3758096384 /\ TH + 288 <= P /\ P + 160 <= TH + 2768)
      by (clear - BND ER ERB EP EFAB CAE HC; try acb; subst CA; rewrite ER, ERB, EP; repeat split; lia).
  (* [comment removed for export] *)
  Ltac getAL CAR ARIR SBR4 RR RBG := lazymatch goal with H : hidden ((akobj _ _ /\ _) /\ _) |- _ =>
    pose proof H as X; destruct X as [(CAR & ARIR & SBR4 & RR & RBG)] end.

  (* [comment removed for export] *)
  Hypothesis NF : nf < n.
  Variable mu' : Z.
  Hypothesis MU' : rf_total c nf au <= mu' /\ mu <= mu' <= mu + kUserMapSize /\ hidden (mu' mod kUserMapSize = 0).
  Let nnew := (mu' - au) / csz.

  (* [comment removed for export] *)
  Lemma rf_tail : forall msF1 mo1 mfa',
    rf_mu' c nf au mu = mu' -> rf_mfa' c nf mfa au mu = mfa' ->
    rf4_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu mu' mfa' fl msF1 mo1 ->
    (forall msF' mo', rf_done L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R rbeg FAB TH nf mfa au mu fl msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 mfa' EMU EMFA A1 K. prepR.
    assert (E160 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; clear - SPR HI BND; try acb; lia).
    clear MI ST ENV PC1 PCJ FAM QST TST RI RIJ EXH RST FARR FAJ USJ VISE.
    destruct A1 as (rax & u0 & u1 & u2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x6 & x7 & x8 & x9 & s10' & s11' & u3 & u4 & u5 & u6 & q0' & q1' & q2' & q3' & j8 & j24 & m1 & L1 & S1
                    & OK1 & VIS1 & LED1 & MU & WM & MI1 & ENV1 & ST1 & F64 & FRG & FRR & PC0 & PCJ & FAMv & QST & TST & RI & RIJ & EXH & RST & FARR & FAJ & USJ & POIu & POIf).
    unfold kUserMapSize in TAIL, MU'. destruct MU' as (TOT & MUR & MUA2).
    assert (NNR : n - nf <= nnew /\ 1 <= nnew /\ csz * nnew <= mu' - au /\ 4 * nnew <= 65540).
    { subst nnew. unfold rf_total, rf_k in TOT. fold n csz in TOT. clear - TOT MUR TAIL CSZ NF NR AUR; try acb.
      assert (n - nf <= (mu' - au) / csz) by (apply Z.div_le_lower_bound; [lia| nia]).
      assert ((mu' - au) / csz <= 16385) by (apply Z.div_le_upper_bound; [lia|]; nia).
      split; [lia| split; [lia| split; [Z.div_mod_to_equations; nia| lia]]]. }
    assert (FAR : 4 * (nf + nnew) <= 469762048).
    { assert (X : nf + nnew <= mu' / csz).
      { subst nnew. replace mu' with (au + (mu' - au)) at 2 by (clear; lia). clear - NFAU CSZ AUR MUR NFR; try acb.
        rewrite <- (Z.div_add_l nf csz (mu' - au)) by lia. apply Z.div_le_mono; [lia| nia]. }
      assert (Y : mu' / csz <= 3758096384 / 32) by (eapply Z.le_trans; [apply Z.div_le_mono; [clear - CSZ; try acb; lia|]| apply Z.div_le_compat_l]; clear - AUR MUR CSZ; try acb; lia).
      change (3758096384 / 32) with 117440512 in Y. clear - X Y; try acb. lia. }
    (* [comment removed for export] *)
    assert (E2 : rf_nnew c nf au mu = nnew) by (unfold rf_nnew; fold n; rewrite (proj2 (Z.ltb_lt nf n) NF), EMU; reflexivity).
    assert (E4 : rf_nf1 c nf au mu = nf + nnew) by (unfold rf_nf1; rewrite E2; reflexivity).
    assert (E5 : rf_au' c nf au mu = au + nnew * csz) by (unfold rf_au'; rewrite E2; reflexivity).
    assert (E6 : rf_fl1 c nf au mu fl = carve_asc au csz 0 (Z.to_nat nnew) ++ fl) by (unfold rf_fl1; rewrite E2; reflexivity).
    assert (MFR : 4 * (nf + nnew) <= mfa' /\ mfa' <= kFreeArraySize /\ mfa <= mfa').
    { rewrite <- EMFA. unfold rf_mfa'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF), E4. unfold kFreeArraySize in NFR |- *.
      destruct (Z.leb_spec (4 * (nf + nnew)) mfa) as [LE|GT]; [clear - LE NFR; try acb; lia|].
      unfold efs_new, round_up, kFreeArrayMapSize. clear - GT NFR FAR; try acb. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (FAB + 4 * nf + 4 * nnew) _ FAJ ltac:(hci; clear - NFR NNR MFR; try acb; lia)) as [JK FAJ2]. clear FAJ.
    replace (Z_to_bv 64 (bv_unsigned sp + -224)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) + -64)) in VIS1
      by (f_equal; rewrite E160; clear; lia).
    fold csz in VIS1.
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF1 _ mo1 Q OK1 VIS1).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (pop_tail _ _ (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo R rbeg csz au mu' nf mfa');
        rewrite ?E160.
      all: replace (bv_unsigned sp + -160 + -64) with (bv_unsigned sp + -224) by (clear; lia).
      all: try eassumption. all: try reflexivity. all: try (clear - RR; try acb; tauto).
      { clear - HI; try acb; lia. }
      { unfold kFreeArrayOffset, kFreeArraySize in MFR |- *. fold nnew. unfold rf_total, rf_k in TOT. fold n csz in TOT.
        assert (X : csz <= csz * (n - nf)) by (clear - NF CSZ; try acb; nia). clear - AUR MUR NFR NNR MFR TOT NF CSZ X; try acb. lia. }
      { split. clear - BNDL HC ER; try acb. lia. } }
    clear OK1 VIS1. cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (v0 & v1 & v2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & v3 & v4 & v5 & v6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & RI2 & EXH2 & CARVE).
    rewrite ?E160 in VIS2. rewrite ?E160 in MU2. rewrite ?E160 in ST2.
    replace (bv_unsigned sp + -160 - 64) with (bv_unsigned sp + -224) in MU2 by (clear; lia).
    fold nnew in VIS2, MU2, RI2, CARVE. change (rbeg + kFreeArrayOffset) with FAB in MU2, CARVE.
    assert (LCV : Z.of_nat (length (wlist (rev (carve_asc au csz 0 (Z.to_nat nnew))))) = nnew) by (unfold wlist; rewrite length_map, length_rev, carve_asc_length; clear - NNR; try acb; lia).
    replace (ret_pc (wz 1687912)) with (Z_to_bv 64 1687912) in VIS2 by (unfold wz; symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    destruct MFR as (MF1 & MF2 & MF3). unfold kFreeArraySize in MF2.
    renv_at ENV1 MU2 WM2 ENV2. clear ENV1.
    assert (POIu2 := poisoned_transport _ m1 m2 _ _ _ POIu MU2 WM2
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; clear - BND BNDL MUR AUR NFR HI ER HC EFAB NNR MF1 MF2; try acb; repeat split; Z.div_mod_to_equations; lia)).
    assert (POIf2 := poisoned_transport _ m1 m2 _ _ _ POIf MU2 WM2
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; clear - BND BNDL MUR AUR NFR HI ER HC EFAB NNR MF1 MF2 MF3; try acb; repeat split; Z.div_mod_to_equations; lia)).
    clear POIu POIf.
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (CA + 80 * c' + 8) [C8 cs]
                                           /\ (mc = wz (max_count c') /\ cs = wz (class_size c')))
      by (intros c' Hc'; destruct (FAMv c' Hc') as [A B]; eexists _, _; split; [exact A| split; [exact B| split; reflexivity]]).
    clear FAMv.
    assert (FAM2 := fam_transport CA _ m1 m2 _ FAM1 MU2 WM2 ltac:(hci; intros cq Hcq; cbn [disjoint_from]; destruct PLC as [PLCq]; unfold kSpaceSize in PLCq;
                                                               clear - Hcq BND BNDL CAE HI PLCq ER HC NFR NNR MF1 MF2; try acb; subst CA; repeat split; lia)).
    clear FAM1 F64 RI EXH.
    unfold rf_W in MU. transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2 MI1.
    (* [comment removed for export] *)
    pose proof RI2 as RIx. unfold rinfo_cells in RIx.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RIx. destruct RIx as [RLK RIx].
    apply (proj1 (rw_cells_app asegs _ _ [_;_] _)) in RIx. destruct RIx as [RI8a RIx].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RIx. destruct RIx as [RNF RI24]. cbn [cells_size csize Nat.add length] in RLK, RI8a, RNF, RI24.
    replace (R + Z.of_nat 8) with (R + 8) in RI8a by (clear; lia).
    replace (R + Z.of_nat 8 + Z.of_nat 8) with (R + 16) in RNF by (clear; lia).
    replace (R + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (R + 24) in RI24 by (clear; lia). clear RI2.
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF2 _ mo2 Q OK2 VIS2).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (gfa_back _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10' s11' _ _ _ _ F fc m2 R (P + 16) (nf + nnew) n);
        [clear - NNR NR NF; try acb; lia | clear - NFR NNR FAR; try acb; lia | clear - RR; try acb; tauto | exact MI2 | exact RNF]. }
    clear OK2 VIS2. cbv beta. intros msF3 mo3 OK3 SBM3 HS3 P3. destruct P3 as (m3 & VIS3 & MU3 & WM3 & MI3 & RNF3).
    renv_at ENV2 MU3 WM3 ENV3. clear ENV2 RNF.
    assert (POIu3 := poisoned_transport _ m2 m3 _ _ _ POIu2 MU3 WM3
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; clear - BND BNDL MUR AUR; try acb; repeat split; Z.div_mod_to_equations; lia)).
    assert (POIf3 := poisoned_transport _ m2 m3 _ _ _ POIf2 MU3 WM3
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; clear - BND BNDL NFR EFAB MF2 MF3; try acb; repeat split; Z.div_mod_to_equations; lia)).
    clear POIu2 POIf2.
    assert (FAM3 := fam_transport CA _ m2 m3 _ FAM2 MU3 WM3 ltac:(hci; intros cq Hcq; cbn [disjoint_from]; destruct PLC as [PLCq]; unfold kSpaceSize in PLCq;
                                                               clear - Hcq BND BNDL CAE HI PLCq; try acb; subst CA; repeat split; lia)).
    clear FAM2.
    transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    (* [comment removed for export] *)
    assert (CHR : akobj (P + 16) 64 /\ P + 16 + 64 <= aceil /\ (P + 16) mod 16 = 0).   (* [comment removed for export] *)
    { acb. destruct THA as [T16]. match goal with TB : akobj TH 4096 |- _ => clear - BND BNDL EP CAE T16 HC TB end; try acb; try acb.
      split; [eapply akobj_sub; [eassumption| lia| lia]|]. split; [lia|]. rewrite EP, CAE. Z.div_mod_to_equations. lia. }
    assert (FABR : AHI_LO <= FAB /\ FAB + 4 * (nf + nnew - n + n) <= aceil /\ FAB mod 4096 = 0).
    { getAL CAR ARIR SBR4 RR RBG. unfold AHI_LO in *. acb. destruct RBG as (RB1 & RB2 & RB3).
      clear - BND BNDL RB1 RB2 RB3 NFR NR NNR MF1 MF2 EFAB; try acb. repeat split; [lia| lia|]. rewrite EFAB. Z.div_mod_to_equations. lia. }
    assert (SEPT : hidden ((P + 16 + 64 <= FAB \/ FAB + 4 * (nf + nnew - n + n) <= P + 16) /\ (P + 16 + 64 <= R \/ R + 128 <= P + 16) /\ (R + 128 <= FAB \/ FAB + 4 * (nf + nnew - n + n) <= R))).
    { split. destruct PLC as [PLC']. unfold kSpaceSize in PLC'. clear - BND BNDL NFR NR NNR MF1 MF2 PLC' CAE; try acb. repeat split; lia. }
    replace (P + 80) with (P + 16 + 64) in PCJ by (clear; lia).
    assert (FARR1 : u32arr asegs m3 FAB (wlist (rev (carve_asc au csz 0 (Z.to_nat nnew) ++ fl)))).
    { rewrite rev_app_distr. unfold wlist in FARR, CARVE, LENF |- *. rewrite map_app. apply (proj2 (u32arr_app _ _ _ _)). split; [exact FARR|]. rewrite LENF. exact CARVE. }
    assert (FLL1 : length (carve_asc au csz 0 (Z.to_nat nnew) ++ fl) = Z.to_nat (nf + nnew - n + n)) by (rewrite length_app, carve_asc_length, FLL; clear - NNR NFR; try acb; lia).
    clear FARR CARVE.
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF3 _ mo3 Q OK3 VIS3).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (gfa_tail _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10' s11' _ _ _ _ _ F fc m3 lo R (P + 16) FAB (nf + nnew - n) n (carve_asc au csz 0 (Z.to_nat nnew) ++ fl) j24);
        rewrite ?E160.
      all: try eassumption. all: try reflexivity.
      { clear - HI; try acb; lia. } { clear - NR; try acb; lia. } { clear - NNR NR NF; try acb; lia. } }
    clear OK3 VIS3. cbv beta. intros msF4 mo4 OK4 SBM4 HS4 P4.
    destruct P4 as (w0 & w1 & w2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & w3 & w4 & w5 & w6 & m4 & VIS4 & MU4 & WM4 & MI4 & ST4 & CHA & CHJ4 & FARR4 & LK4 & RST4).
    rewrite ?E160 in VIS4. rewrite ?E160 in MU4. rewrite ?E160 in ST4.
    replace (bv_unsigned sp + -160 + 128) with (bv_unsigned sp + -32) in * by (clear; lia).
    renv_at ENV3 MU4 WM4 ENV4. clear ENV3.
    assert (POIu4 := poisoned_transport _ m3 m4 _ _ _ POIu3 MU4 WM4
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDL MUR AUR HI NR TB end; try acb; aunf; repeat split; Z.div_mod_to_equations; lia)).
    assert (POIf4 := poisoned_transport _ m3 m4 _ _ _ POIf3 MU4 WM4
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDL NFR EFAB MF2 MF3 HI NR TB end; try acb; aunf; repeat split; Z.div_mod_to_equations; lia)).
    clear POIu3 POIf3.
    assert (FAM4 := fam_transport CA _ m3 m4 _ FAM3 MU4 WM4 ltac:(hci; intros cq Hcq; cbn [disjoint_from]; destruct PLC as [PLCq]; unfold kSpaceSize in PLCq;
                                                               clear - Hcq BND BNDL CAE EP HI PLCq NR NF NFR; try acb; subst CA P; repeat split; lia)).
    clear FAM3 RLK FRG PCJ.
    transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
    (* [comment removed for export] *)
    replace (ret_pc (wz 1687020)) with (Z_to_bv 64 1687020) in VIS4 by (unfold wz; symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF4 _ mo4 Q OK4 VIS4).
    { eapply (refill_back _ gp tp _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ F fc m4 j8 s1 s0 ra lo P n);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR HI BND; try acb; lia).
      all: try eassumption. all: try (match goal with TB : akobj TH 4096 |- akobj _ _ /\ _ => clear - BND BNDL TB EP CAE HC; split; [eapply akobj_sub; [exact TB| subst CA P; lia| subst CA P; lia] | subst CA P; lia] end).   (* [comment removed for export] *) all: clear - HI SPR BND NR; try acb; lia. }
    clear OK4 VIS4. cbv beta. intros msF5 mo5 OK5 SBM5 HS5 P5.
    destruct P5 as (m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & PC5).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in VIS5 by (clear - SPR HI BND; try acb; lia).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU5 by (clear - SPR HI BND; try acb; lia).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST5 by (clear - SPR HI BND; try acb; lia).
    replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) in * by (clear; lia).
    renv_at ENV4 MU5 WM5 ENV5. clear ENV4.
    assert (POIu5 := poisoned_transport _ m4 m5 _ _ _ POIu4 MU5 WM5
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDL MUR AUR HI TB end; try acb; aunf; repeat split; Z.div_mod_to_equations; lia)).
    assert (POIf5 := poisoned_transport _ m4 m5 _ _ _ POIf4 MU5 WM5
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDL NFR EFAB MF2 MF3 HI TB end; try acb; aunf; repeat split; Z.div_mod_to_equations; lia)).
    clear POIu4 POIf4.
    assert (FAM5 := fam_transport CA _ m4 m5 _ FAM4 MU5 WM5 ltac:(hci; intros cq Hcq; cbn [disjoint_from]; clear - Hcq BND BNDL CAE EP HI; try acb; subst CA P; repeat split; lia)).
    assert (LENCH : Z.of_nat (length (wlist (rev (take (Z.to_nat n) (carve_asc au csz 0 (Z.to_nat nnew) ++ fl))))) = n)
      by (unfold wlist; rewrite length_map, length_rev, length_firstn, FLL1; clear - NF NR NNR NFR; try acb; lia).
    assert (LENF1 : Z.of_nat (length (wlist (rev (carve_asc au csz 0 (Z.to_nat nnew) ++ fl)))) = nf + nnew)
      by (unfold wlist; rewrite length_map, length_rev, FLL1; clear - NF NR NNR NFR; try acb; lia).
    clear FAM4 PC0. transport_after_call asegs m4 m5 MU5 WM5. clear MU5 WM5 MI4.
    (* [comment removed for export] *)
    apply K. unfold rf_done. cbv zeta. rewrite !EMU, !EMFA, !E4, !E5, !E6. fold n.
    pose proof LED1 as LED. destruct LED as (EL1 & ES1 & NVS1 & VMM1 & VMR1 & VML1 & VMB1 & VBK1 & VMN1 & EAG1).
    do 18 eexists. exists m5, L1, S1.
    split; [exact OK5|]. split; [rewrite Z_to_bv_bv_unsigned in VIS5; exact VIS5|].
    split; [exact EL1|]. split; [exact ES1|].
    split; [eapply nonvm_same_trans; [exact NVS1| apply nonvm_same_mat; eapply same_but_materialized_trans; [| exact SBM5];
            eapply same_but_materialized_trans; [| exact SBM4]; eapply same_but_materialized_trans; [| exact SBM3]; exact SBM2]|].
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM2 SBM3) SBM4) SBM5) as SBM.
    rewrite (same_but_materialized_vmmaps _ _ SBM), (same_but_materialized_eager _ _ SBM).
    split; [exact VMM1|]. split; [exact VMR1|]. split; [exact VML1|]. split; [exact VMB1|]. split; [exact VBK1|]. split; [exact VMN1|]. split; [exact EAG1|].
    split; [unfold rf_W; exact MU|]. split; [exact WM|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PC5|].
    split. { intros cq Hcq. destruct (FAM5 cq Hcq) as (mc & cs & A & B & -> & ->). split; [exact A| exact B]. }
    split; [exact CHA|]. split; [replace (P + 80) with (P + 16 + 64) by (clear; lia); exact CHJ4|].
    split.
    { apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact LK4|]. cbn [cells_size csize Nat.add length].
      apply (proj2 (rw_cells_app asegs _ _ [_;_] _)). split; [replace (R + Z.of_nat 8) with (R + 8) by (clear; lia); exact RI8a|]. cbn [cells_size csize Nat.add length].
      apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [replace (R + Z.of_nat 8 + Z.of_nat 8) with (R + 16) by (clear; lia); exact RNF3|]. cbn [cells_size csize Nat.add length].
      replace (R + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (R + 24) by (clear; lia). exact RI24. }
    split; [exact RIJ|]. split; [exact EXH2|]. split; [exact RST4|]. split; [exact FARR4|].
    split; [replace (FAB + 4 * (nf + nnew)) with (FAB + 4 * nf + 4 * nnew) by (clear; lia); exact FAJ2|].
    split; [exact USJ|]. split; [exact POIu5|]. split; [exact POIf5|]. split; [exact QST| exact TST].
  Qed.
End Refill.

(* [comment removed for export] *)
Section RefillTop.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  (* [comment removed for export] *)
  Variables (lo sb c CA TH CTX TSD : Z).
  Variables (nf mfa au mu : Z) (fl : list Z) (inited : bool).
  Let ARI := sb + kSpaceSize.
  Let R := ARI + REGIONINFO_SIZE * c.
  Let P := CA + PCLASS_SIZE * c.
  Let rbeg := sb + c * 2^32.
  Let FAB := rbeg + kFreeArrayOffset.
  Let n := rf_n c.
  Let csz := class_size c.

  (* [comment removed for export] *)
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 672 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis CAE : CA = TH + 208.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil. Hypothesis SBA : hidden (sb mod 65536 = 0).
  Hypothesis TPR : 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis THA : hidden (TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
  Hypothesis NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize. Hypothesis MFAA : hidden (mfa mod kFreeArrayMapSize = 0).
  Hypothesis AUR : 0 <= au <= mu /\ mu + kUserMapSize <= kFreeArrayOffset. Hypothesis MUA : hidden (mu mod kUserMapSize = 0).
  Hypothesis FLL : length fl = Z.to_nat nf.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz P) (wz AINST) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x19bdac) fc None m (seg_rom asegs).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ENV : RENV tp TSD CTX TH sb ARI m.
  Hypothesis LENF : Z.of_nat (length (wlist (rev fl))) = nf.
  (* [comment removed for export] *)
  Hypothesis PC1 : rw_cells asegs m P [C4 (wz 0); C4 (wz (if inited then max_count c else 0))].
  Hypothesis PCJ : stk asegs m (P + 16) (P + 80).
  Hypothesis FAM : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 cs]
                                             /\ (inited = true -> mc = wz (max_count c') /\ cs = wz (class_size c')).
  (* [comment removed for export] *)
  Variables (q0 q1 q2 q3 : word).
  Hypothesis QST : rw_cells asegs m (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  (* [comment removed for export] *)
  Hypothesis RI : rw_cells asegs m R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis RIJ : stk asegs m (R + 64) (R + 68).
  Hypothesis EXH : rw_cells asegs m (R + 68) [C1 (b8 0)].
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)).
  Hypothesis FAJ : stk asegs m (FAB + 4 * nf) (FAB + mfa).
  Hypothesis USJ : stk asegs m (rbeg + au) (rbeg + mu).
  (* [comment removed for export] *)
  Hypothesis RESF : forall (a k : word), AHI_LO <= bv_unsigned a -> region_free (vm_reserved (m_vmmaps mo)) a k = true.
  Hypothesis PRIM : forall (a k : word), rbeg <= bv_unsigned a -> bv_unsigned a + bv_unsigned k <= rbeg + 2^32 -> map_contains (vm_maps (m_vmmaps mo)) a k = true.
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis ZRP : forall x : word, rbeg <= bv_unsigned x < rbeg + 2^32 -> in_rangesb x Zr = false.
  Hypothesis ZRSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x Zr = true.
  Hypothesis LSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  Hypothesis BUD : eager_used mo + pages_total S * 4096 + 606208 <= vm_limit (m_vmmaps mo).
  (* [comment removed for export] *)
  Hypothesis TAIL : mu - au < csz + kUserMapSize. Hypothesis NFAU : csz * nf <= au.
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  (* [comment removed for export] *)
  Theorem refill_sreach :
    (forall msF' mo', rf_done L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R rbeg FAB TH nf mfa au mu fl msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    eapply rf_head; try eassumption. cbv beta. intros msF1 mo1 A1.
    pose proof (max_count_facts c ltac:(hci; clear - HC; try acb; lia)) as MCF.
    assert (NR : 1 <= n <= 8 /\ n + n = max_count c) by (clear - MCF; try acb; subst n; unfold rf_n; destruct MCF as [M1 M2];
       destruct (proj1 (Z.even_spec _) M2) as [k Hk]; rewrite Hk in *; rewrite (Z.mul_comm 2 k), Z.div_mul by lia; lia).
    clear MCF.
    destruct (Z.le_gt_cases n nf) as [NF|NF].
    { eapply rf_fast; try eassumption. }
    eapply rf_pop_head; try eassumption. cbv beta. intros msF2 mo2 A2.
    unfold kUserMapSize in TAIL.
    pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as CST. assert (CSZ : 32 <= csz <= 65536) by (subst csz; clear - CST HC; try acb; lia). clear CST.
    pose proof (rf_batch_small c HC) as [BSM _]. fold n csz in BSM.
    pose proof AUR as AUR'. pose proof NFR as NFR'. unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in AUR', NFR'.
    assert (TOTB : au + csz <= rf_total c nf au <= au + 65536) by (unfold rf_total, rf_k; fold n csz; clear - BSM NF NR CSZ NFR'; try acb; nia).
    (* [comment removed for export] *)
    assert (MID : forall mu' msF3 mo3,
               rf_total c nf au <= mu' /\ mu <= mu' <= mu + kUserMapSize /\ hidden (mu' mod kUserMapSize = 0) -> rf_mu' c nf au mu = mu' ->
               rf3_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu mu' fl msF3 mo3 ->
               sreach asegs Q (mkCfg msF3 mo3)).
    { intros mu' msF3 mo3 MU' EMU A3.
      pose proof MU' as X. destruct X as (TOT & MUR & _). unfold kUserMapSize in MUR.
      assert (NNR : 4 * ((mu' - au) / csz) <= 65540).
      { clear - TOT MUR TAIL CSZ NF NR AUR'; try acb. assert ((mu' - au) / csz <= 16385) by (apply Z.div_le_upper_bound; [lia|]; nia). lia. }
      assert (E2 : rf_nnew c nf au mu = (mu' - au) / csz) by (unfold rf_nnew; fold n csz; rewrite (proj2 (Z.ltb_lt nf n) NF), EMU; reflexivity).
      assert (E4 : rf_nf1 c nf au mu = nf + (mu' - au) / csz) by (unfold rf_nf1; rewrite E2; reflexivity).
      destruct (Z.le_gt_cases (4 * (nf + (mu' - au) / csz)) mfa) as [FAST|SLOW].
      - eapply rf_mid_fast; try eassumption. cbv beta. intros msF4 mo4 A4.
        eapply rf_tail; try eassumption.
        unfold rf_mfa'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF), E4, (proj2 (Z.leb_le _ _) FAST). reflexivity.
      - eapply rf_mid_map; try eassumption. cbv beta. intros msF4 mo4 A4.
        eapply rf_tail; try eassumption.
        unfold rf_mfa'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF), E4, (proj2 (Z.leb_gt _ _) SLOW).
        pose proof MFAA as X; destruct X as [MFAA']. unfold efs_new, round_up, kFreeArrayMapSize in MFAA' |- *. clear - SLOW NNR NFR' MFAA'; try acb. Z.div_mod_to_equations. lia. }
    destruct (Z.le_gt_cases (rf_total c nf au) mu) as [TOT|TOT].
    - eapply rf_nomap; try eassumption. cbv beta. intros msF3 mo3 A3. apply (MID mu msF3 mo3); [| | exact A3].
      + split; [exact TOT|]. split; [unfold kUserMapSize; clear; lia| exact MUA].
      + unfold rf_mu'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF), (proj2 (Z.ltb_ge _ _) TOT). reflexivity.
    - assert (MS256 : pop_ms (rf_total c nf au) mu = 262144)
        by (unfold pop_ms, round_up, kUserMapSize; clear - TOTB TOT AUR' CSZ; try acb; Z.div_mod_to_equations; lia).
      eapply rf_umap; try eassumption. cbv beta. intros msF3 mo3 A3. apply (MID (mu + 262144) msF3 mo3); [| | exact A3].
      + split; [clear - TOTB TOT AUR' CSZ; try acb; lia|]. split; [unfold kUserMapSize; clear; lia|].
        destruct MUA as [MUA']. split. unfold kUserMapSize in *. clear - MUA'; try acb. Z.div_mod_to_equations. lia.
      + unfold rf_mu'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF), (proj2 (Z.ltb_lt _ _) TOT), MS256. reflexivity.
  Qed.
End RefillTop.
