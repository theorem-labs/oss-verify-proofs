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
     AW_PoisonShadow AW_Leaves AllocWalkKit AW_MmapFixed AW_Efs AW_Populate AW_Gfa AW_InitCache AW_Refill AW_LargeAlloc1 SecLazy AS_Refill1 AS_Refill2 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rf4_at (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu mu' mfa' : Z) (fl : list Z) (msF' : machine_state) (mo' : Model) : Prop :=
  exists (rax t0 t1 t2 y1 y2 y3 y4 y5 y6 y7 x6 x7 x8 x9 s10' s11' t3 t4 t5 t6 q0 q1 q2 q3 : word) (j8 j24 : list byte) m' L' S',
  let n := rf_n c in let nnew := (mu' - au) / class_size c in
     lzok asegs L' S' Zr (mkCfg msF' mo')
  /\ restrict L' S' msF'
     = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0 t1 t2 (wz R) (wz (nf + nnew)) (wz 1) y1 y2 y3 y4 y5 y6 y7
               (wz rbeg) (wz nnew) (wz (mu' - au)) (wz (class_size c)) x6 x7 x8 x9 s10' s11' t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c348) fc None m' (seg_rom asegs)
  /\ rf_ledger mo L S rbeg FAB mu mu' mfa mfa' L' S' mo'
  /\ munch (rf_W lo (bv_unsigned sp) P R FAB rbeg TH CA nf mfa mu mfa' mu') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ RENV tp TSD CTX TH sb ARI m'
  /\ stk asegs m' lo (bv_unsigned sp + -224)
  /\ rw_cells asegs m' (bv_unsigned sp + -224)
       [C8 (wz n); C8 (wz (P + 16)); C8 (wz FAB); C8 (wz (2^61)); C8 (wz (R + 8)); C8 (wz AINST); C8 (wz R); C8 (wz 0x19c168)]
  /\ rw_cells asegs m' (bv_unsigned sp + -160)
       [CB 24 j24; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 (wz n); C8 (wz P); C8 (wz 0x19bdec)]
  /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m' P [C4 (wz 0)] /\ stk asegs m' (P + 16) (P + 80)
  /\ (forall c', 1 <= c' <= 31 -> rw_cells asegs m' (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 (wz (class_size c'))])
  /\ rw_cells asegs m' (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs m' (TH + 2800) (TH + 3168)
  /\ rw_cells asegs m' R (rinfo_cells nf mfa' au mu')
  /\ stk asegs m' (R + 64) (R + 68) /\ rw_cells asegs m' (R + 68) [C1 (b8 0)] /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev fl)) /\ stk asegs m' (FAB + 4 * nf) (FAB + mfa') /\ stk asegs m' (rbeg + au) (rbeg + mu')
  /\ poisoned m' (rbeg + mu) (Z.to_nat ((mu' - mu) / 8)) 0xfa /\ poisoned m' (FAB + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa.

(* [comment removed for export] *)
Lemma poisoned_transport : forall W m m' A k v,
  poisoned m A k v -> munch W m m' -> wmono asegs m m' -> disjoint_from W (sh A) (Z.of_nat k) -> poisoned m' A k v.
Proof.
  intros W m m' A k v PZ MU WM D. unfold poisoned in *. eapply SHAD_transport; [exact PZ| exact MU| exact WM|].
  unfold poison_bytes. rewrite repeat_length. exact D.
Qed.

(* [comment removed for export] *)
Lemma rf_ledger_mat : forall mo L S rbeg FAB mu mu' mfa mfa' L' S' mo1 mo2,
  rf_ledger mo L S rbeg FAB mu mu' mfa mfa' L' S' mo1 -> same_but_materialized mo1 mo2 -> rf_ledger mo L S rbeg FAB mu mu' mfa mfa' L' S' mo2.
Proof.
  intros until mo2. intros (A & B & C & D & E & G & G2 & G3 & H & I) SBM. unfold rf_ledger.
  rewrite (same_but_materialized_vmmaps _ _ SBM), (same_but_materialized_eager _ _ SBM).
  split; [exact A|]. split; [exact B|]. split; [eapply nonvm_same_trans; [exact C| apply nonvm_same_mat; exact SBM]|].
  split; [exact D|]. split; [exact E|]. split; [exact G|]. split; [exact G2|]. split; [exact G3|]. split; [exact H| exact I].
Qed.
End HCW.

Section Refill.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
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
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.
  Let nnew := (mu' - au) / csz.


  (* [comment removed for export] *)
  Lemma rf_mid_fast : forall msF1 mo1, 4 * (nf + nnew) <= mfa ->
    rf3_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu mu' fl msF1 mo1 ->
    (forall msF' mo', rf4_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu mu' mfa fl msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 FAST A1 K. prepR.
    assert (E160 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; clear - SPR HI BND; try acb; lia).
    clear MI ST ENV PC1 PCJ FAM QST TST RI RIJ EXH RST FARR FAJ USJ VISE OK.
    destruct A1 as (rax & u0 & u1 & u2 & x1 & y1 & y2 & y4 & y5 & y6 & y7 & x3 & x6 & x7 & x8 & x9 & s10' & s11' & u3 & u4 & u5 & u6 & q0' & q1' & q2' & q3' & j8 & j24 & m1 & L1 & S1
                    & OK1 & VIS1 & LED1 & MU & WM & MI1 & ENV1 & ST1 & F64 & FRG & FRR & PC0 & PCJ & FAMv & QST & TST & RI & RIJ & EXH & RST & FARR & FAJ & USJ & POI1).
    unfold kUserMapSize in TAIL, MU'. destruct MU' as (TOT & MUR & MUA2).
    assert (NNR : n - nf <= nnew /\ 1 <= nnew /\ csz * nnew <= mu' - au /\ 4 * nnew <= 65540).
    { subst nnew. unfold rf_total, rf_k in TOT. fold n csz in TOT. clear - TOT MUR TAIL CSZ NF NR AUR; try acb.
      assert (n - nf <= (mu' - au) / csz) by (apply Z.div_le_lower_bound; [lia| nia]).
      assert ((mu' - au) / csz <= 16385) by (apply Z.div_le_upper_bound; [lia|]; nia).
      split; [lia| split; [lia| split; [Z.div_mod_to_equations; nia| lia]]]. }
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -224)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) + -64)) in VIS1
      by (f_equal; rewrite E160; clear; lia).
    fold csz in VIS1.
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF1 _ mo1 Q OK1 VIS1).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (pop_mid_fast _ (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo R rbeg csz au mu' nf mfa);
        rewrite ?E160.
      all: replace (bv_unsigned sp + -160 + -64) with (bv_unsigned sp + -224) by (clear; lia).
      all: try eassumption. all: try reflexivity. all: try (clear - RR; try acb; tauto).
      { clear - HI; try acb; lia. }
      { unfold kFreeArrayOffset, kFreeArraySize. fold nnew. clear - AUR MUR NFR FAST NNR; try acb. lia. } }
    clear OK1 VIS1. cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (rax2 & v0 & v1 & v2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & x6' & v3 & v4 & v5 & v6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & F64n).
    rewrite ?unsigned_lit in VIS2, MU2, ST2, F64n by (first [clear - BND HI; lia | lia]).
    replace (bv_unsigned sp + -160 - 112) with (bv_unsigned sp + -272) in MU2 by lia.
    replace (bv_unsigned sp + -160 + -64) with (bv_unsigned sp + -224) in * by lia.
    fold nnew in VIS2.
    renv_at ENV1 MU2 WM2 ENV2. clear ENV1.
    assert (POI2 := poisoned_transport _ m1 m2 _ _ _ POI1 MU2 WM2
                      ltac:(hci; cbn [disjoint_from]; split; [| exact I]; left; unfold sh, ASHADOW_BASE; clear - BND BNDL HI MUR AUR; try acb; Z.div_mod_to_equations; lia)).
    clear POI1.
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (CA + 80 * c' + 8) [C8 cs]
                                           /\ (mc = wz (max_count c') /\ cs = wz (class_size c')))
      by (intros c' Hc'; destruct (FAMv c' Hc') as [A B]; eexists _, _; split; [exact A| split; [exact B| split; reflexivity]]).
    clear FAMv.
    assert (FAM2 := fam_transport CA _ m1 m2 _ FAM1 MU2 WM2 ltac:(hci; intros cq Hcq; cbn [disjoint_from]; clear - Hcq BND BNDL CAE HI; try acb; subst CA; repeat split; lia)).
    clear FAM1 F64.
    unfold rf_W in MU. unfold rinfo_cells in RI. transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2 MI1. fold (rinfo_cells nf mfa au mu') in RI.
    apply K. unfold rf4_at. fold csz. fold nnew. do 27 eexists. exists m2, L1, S1.
    split; [exact OK2|]. split; [exact VIS2|]. split; [eapply rf_ledger_mat; [exact LED1| exact SBM2]|].
    split; [unfold rf_W; exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ENV2|]. split; [exact ST2|]. split; [exact F64n|]. split; [exact FRG|]. split; [exact FRR|].
    split; [exact PC0|]. split; [exact PCJ|].
    split. { intros cq Hcq. destruct (FAM2 cq Hcq) as (mc & cs & A & B & -> & ->). split; [exact A| exact B]. }
    split; [exact QST|]. split; [exact TST|]. split; [exact RI|]. split; [exact RIJ|]. split; [exact EXH|]. split; [exact RST|]. split; [exact FARR|]. split; [exact FAJ|].
    split; [exact USJ|]. split; [exact POI2|].
    getAL CAR ARIR SBR4 RR RBG.
    assert (MFQ : exists q, mfa = 262144 * q) by (destruct MFAA as [MFAA']; exists (mfa / kFreeArrayMapSize); unfold kFreeArrayMapSize in *; clear - MFAA'; try acb; Z.div_mod_to_equations; lia).
    destruct MFQ as [mfq MFQ].
    rewrite Z.sub_diag. change (0 / 8) with 0. cbn [Z.to_nat]. apply poisoned_0; unfold AHI_LO, sh, ASHADOW_BASE in *; acb;
        [clear - RBG NFR EFAB; try acb; lia | clear - RBG MFQ EFAB; try acb; destruct RBG as (_ & _ & RB3); rewrite EFAB; Z.div_mod_to_equations; lia | clear - RBG NFR EFAB; try acb; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rf_mid_map : forall msF1 mo1, mfa < 4 * (nf + nnew) ->
    rf3_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu mu' fl msF1 mo1 ->
    (forall msF' mo', rf4_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu mu' (mfa + 262144) fl msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 SLOW A1 K. prepR.
    assert (E160 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; clear - SPR HI BND; try acb; lia).
    clear MI ST ENV PC1 PCJ FAM QST TST RI RIJ EXH RST FARR FAJ USJ VISE.
    destruct A1 as (rax & u0 & u1 & u2 & x1 & y1 & y2 & y4 & y5 & y6 & y7 & x3 & x6 & x7 & x8 & x9 & s10' & s11' & u3 & u4 & u5 & u6 & q0' & q1' & q2' & q3' & j8 & j24 & m1 & L1 & S1
                    & OK1 & VIS1 & LED1 & MU & WM & MI1 & ENV1 & ST1 & F64 & FRG & FRR & PC0 & PCJ & FAMv & QST & TST & RI & RIJ & EXH & RST & FARR & FAJ & USJ & POI1).
    unfold kUserMapSize in TAIL, MU'. destruct MU' as (TOT & MUR & MUA2).
    assert (NNR : n - nf <= nnew /\ 1 <= nnew /\ csz * nnew <= mu' - au /\ 4 * nnew <= 65540).
    { subst nnew. unfold rf_total, rf_k in TOT. fold n csz in TOT. clear - TOT MUR TAIL CSZ NF NR AUR; try acb.
      assert (n - nf <= (mu' - au) / csz) by (apply Z.div_le_lower_bound; [lia| nia]).
      assert ((mu' - au) / csz <= 16385) by (apply Z.div_le_upper_bound; [lia|]; nia).
      split; [lia| split; [lia| split; [Z.div_mod_to_equations; nia| lia]]]. }
    assert (MFQ : exists q, mfa = 262144 * q) by (destruct MFAA as [MFAA']; exists (mfa / kFreeArrayMapSize); unfold kFreeArrayMapSize in *; clear - MFAA'; try acb; Z.div_mod_to_equations; lia).
    destruct MFQ as [mfq MFQ].
    assert (FAR : 4 * (nf + nnew) <= 469762048).
    { assert (X : nf + nnew <= mu' / csz).
      { subst nnew. replace mu' with (au + (mu' - au)) at 2 by (clear; lia). clear - NFAU CSZ AUR MUR NFR; try acb.
        rewrite <- (Z.div_add_l nf csz (mu' - au)) by lia. apply Z.div_le_mono; [lia| nia]. }
      assert (Y : mu' / csz <= 3758096384 / 32) by (eapply Z.le_trans; [apply Z.div_le_mono; [clear - CSZ; try acb; lia|]| apply Z.div_le_compat_l]; clear - AUR MUR CSZ; try acb; lia).
      change (3758096384 / 32) with 117440512 in Y. clear - X Y; try acb. lia. }
    assert (SZ : efs_new (nf + nnew) - mfa = 262144).
    { unfold efs_new, round_up, kFreeArrayMapSize. rewrite MFQ. clear - SLOW NNR NFR MFQ; try acb. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    pose proof (re_pmh _ _ _ _ _ _ _ ENV1) as PMH. pose proof (re_senv _ _ _ _ _ _ _ ENV1) as SE.
    pose proof (se_got _ _ _ _ _ SE) as GOT. pose proof (se_psc _ _ _ _ _ SE) as PSC. pose proof (se_dpm _ _ _ _ _ SE) as DPM. clear SE.
    replace (Z_to_bv 64 (bv_unsigned sp + -224)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) + -64)) in VIS1
      by (f_equal; rewrite E160; clear; lia).
    fold csz in VIS1.
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF1 _ mo1 Q OK1 VIS1).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (pop_mid_map _ (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo R rbeg csz au mu' nf mfa);
        rewrite ?E160.
      all: replace (bv_unsigned sp + -160 + -64) with (bv_unsigned sp + -224) by (clear; lia).
      all: try eassumption. all: try reflexivity. all: try (clear - RR; try acb; tauto).
      { clear - HI; try acb; lia. }
      { unfold kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize. fold nnew. destruct MFAA as [MFAA']. unfold kFreeArrayMapSize in MFAA'.
        clear - AUR MUR NFR SLOW FAR MFAA'; try acb. repeat split; try lia. } }
    clear OK1 VIS1. cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (m2 & j8' & j44 & VIS2 & MU2 & WM2 & MI2 & ST2 & F176 & F48 & F64n). cbv zeta in VIS2, F176.
    rewrite ?unsigned_lit in VIS2, MU2, ST2, F176, F48, F64n by (first [clear - BND HI; lia | lia]).
    replace (bv_unsigned sp + -160 + -240) with (bv_unsigned sp + -400) in * by lia.   (* [comment removed for export] *)
    replace (bv_unsigned sp + -160 + -112) with (bv_unsigned sp + -272) in * by lia.
    replace (bv_unsigned sp + -160 - 512) with (bv_unsigned sp + -672) in * by lia.
    replace (bv_unsigned sp + -160 + -64) with (bv_unsigned sp + -224) in * by lia.
    fold FAB in VIS2, F176. fold nnew in VIS2, F176, F48. rewrite SZ in VIS2, F176.
    assert (CURB : FAB <= FAB + mfa /\ FAB + mfa + 262144 <= rbeg + 4294967296 /\ (exists bq, FAB + mfa = 4096 * bq)).
    { getAL CAR ARIR SBR4 RR RBG. destruct RBG as (_ & _ & R3). unfold efs_new, round_up, kFreeArrayMapSize, kFreeArraySize in *.
      clear - NFR R3 MFQ EFAB FAR SLOW; try acb. split; [lia| split; [Z.div_mod_to_equations; lia| exists ((FAB + mfa) / 4096); rewrite EFAB, MFQ; Z.div_mod_to_equations; lia]]. }
    destruct CURB as (CUR1 & CUR2 & [bq BQ]).
    renv_at ENV1 MU2 WM2 ENV2. clear ENV1 PMH GOT PSC DPM.
    assert (POI2 := poisoned_transport _ m1 m2 _ _ _ POI1 MU2 WM2
                      ltac:(hci; cbn [disjoint_from]; split; [| exact I]; left; unfold sh, ASHADOW_BASE; clear - BND BNDL HI MUR AUR; try acb; Z.div_mod_to_equations; lia)).
    clear POI1.
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (CA + 80 * c' + 8) [C8 cs]
                                           /\ (mc = wz (max_count c') /\ cs = wz (class_size c')))
      by (intros c' Hc'; destruct (FAMv c' Hc') as [A B]; eexists _, _; split; [exact A| split; [exact B| split; reflexivity]]).
    clear FAMv.
    assert (FAM2 := fam_transport CA _ m1 m2 _ FAM1 MU2 WM2 ltac:(hci; intros c' Hc'; cbn [disjoint_from]; clear - Hc' BND BNDL CAE HI; try acb; subst CA; repeat split; lia)).
    clear FAM1 F64. unfold rinfo_cells in RI.
    (* [comment removed for export] *)
    unfold rf_W in MU. replace ((mfa - mfa) / 8) with 0 in MU by (clear; Z.div_mod_to_equations; lia).
    eapply (munch_weaken _ ((lo, bv_unsigned sp) :: (P, P + 4) :: (P + 16, P + 80) :: (R, R + 8) :: (R + 16, R + 40) :: (R + 48, R + 56) :: (R + 68, R + 69) :: (R + 72, R + 80)
                             :: (FAB + 4 * nf, FAB + mfa + 262144) :: (rbeg + mu, rbeg + mu') :: (sh (FAB + mfa), sh (FAB + mfa) + 32768)
                             :: (sh (rbeg + mu), sh (rbeg + mu) + (mu' - mu) / 8) :: (TH + 2792, TH + 3168) :: icW CA)) in MU; [| rx_sub_fp_struct].
    transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    eapply (sr_ecall_MS L1 S1 Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d1904 fc None m2 msF2 mo2 Q OK2 VIS2 ecall_1d697c).
    clear OK2 VIS2. intros msF3 OK3 VIS3 HS3.
    (* [comment removed for export] *)
    assert (NZ : page_round_up_Z (bv_unsigned (wz 262144)) = 262144) by (vm_compute; reflexivity).
    assert (ECUR : bv_unsigned (Z_to_bv 64 (FAB + mfa)) = FAB + mfa) by (apply unsigned_lit; clear - CUR1 CUR2 BND BNDL; try acb; lia).
    assert (E256 : bv_unsigned (Z_to_bv 64 262144) = 262144) by (apply unsigned_lit; clear; lia).
    pose proof LED1 as LED. destruct LED as (EL1 & ES1 & NVS1 & VMM1 & VMR1 & VML1 & VMB1 & VBK1 & VMN1 & EAG1).
    rewrite Z.ltb_irrefl in EL1, ES1, VMN1. cbn [app] in ES1.
    eapply (sr_mmap_commit_MS L1 S1 Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d1904 fc None m2 false msF3 mo2 Q OK3 VIS3 eq_refl);
      rewrite ?NZ, ?(same_but_materialized_vmmaps _ _ SBM2), ?(same_but_materialized_eager _ _ SBM2), ?VMM1, ?VMR1, ?VML1, ?VMN1; unfold wz; rewrite ?ECUR, ?E256.
    { apply wz_ne0. clear; lia. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { rewrite (nonvm_same_atop _ _ NVS1), ATOP. clear - CUR1 CUR2 BND BNDL; try acb. lia. }
    { unfold page_size. rewrite BQ. clear. Z.div_mod_to_equations. lia. }
    { clear - CUR1 BND BNDL; try acb. lia. }
    { apply RESF. unfold AHI_LO. rewrite ECUR. clear - CUR1 BND BNDL; try acb. lia. }
    { apply PRIM; rewrite ?ECUR, ?E256; clear - CUR1 CUR2 BNDL; try acb; lia. }
    { exact NW. }
    { destruct (mu <? mu'); [apply maps_subtract_nowrap; [exact NWA| clear - BND BNDL AUR; try acb; lia| clear - MUR; try acb; lia]| exact NWA]. }
    { exact NOV. }
    { intros _ x Hx. apply ZRP. clear - Hx CUR1 CUR2 BNDL; try acb. lia. }
    { intros X; discriminate X. } { intros X; discriminate X. }
    { intros _. 
      rewrite ES1. pose proof (pages_total_nonneg S) as PT.
      destruct (mu <? mu'); cbn [app].
      - rewrite pages_total_cons. pose proof (cl_bounds (wz (sh (rbeg + mu)), wz ((mu' - mu) / 8))) as CB. cbn [fst snd] in CB. unfold wz in CB |- *.
        rewrite (unsigned_lit ((mu' - mu) / 8)) in CB by (clear - MUR; try acb; Z.div_mod_to_equations; lia). unfold page_size in *.
        assert (DV : (mu' - mu) / 8 / 4096 <= 8) by (clear - MUR; try acb; Z.div_mod_to_equations; lia).
        destruct CB as (_ & _ & _ & _ & WB & _). clear - WB BUD EAG1 PT DV MUR; try acb. lia.
      - unfold page_size in *. clear - BUD EAG1 PT MUR; try acb. lia. }
    cbv zeta. intros msF4 OK4 VIS4 HS4 EAG4.
    change (1906948 + 4) with 1906952 in VIS4. cbn [fflags] in OK4, VIS4, HS4, EAG4 |- *.
    set (mo4 := commit_model (Z_to_bv 64 50) (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) false mo2) in *.
    set (L4 := maps_subtract L1 (FAB + mfa) (FAB + mfa + 262144)) in *.
    assert (VM4 : m_vmmaps mo4 = commit_vmmaps (m_vmmaps mo1) (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) false).
    { subst mo4. rewrite commit_model_vmmaps, (same_but_materialized_vmmaps _ _ SBM2). reflexivity. }
    (* [comment removed for export] *)
    getAL CAR ARIR SBR4 RR RBG.
    assert (SHB : sh AHI_LO <= sh (FAB + mfa) /\ sh (FAB + mfa) + 32768 <= sh aceil /\ 12599296 <= sh (FAB + mfa) /\ sh (FAB + mfa + 262144) = sh (FAB + mfa) + 32768
                  /\ sh aceil < AHI_LO).
    { unfold sh, ASHADOW_BASE, AHI_LO in *. acb. rewrite BQ. clear - CUR1 CUR2 BQ BND BNDL; try acb. Z.div_mod_to_equations. lia. }
    destruct SHB as (SHB1 & SHB2 & SHB3 & SHB4 & SHB5).
    clear CAR ARIR SBR4 RR RBG.
    (* [comment removed for export] *)
    set (W := (wz (sh (FAB + mfa)), wz 32768)).
    destruct (open_window_MS L4 S1 Zr W msF4 mo4 _ F _ fc None _ OK4 VIS4) as [OK5 VIS5].
    { intros x Hx. apply (zin_W (sh (FAB + mfa)) 32768) in Hx; [| clear - SHB3; try acb; lia | clear - SHB2 SHB5; try acb; unfold AHI_LO in *; lia | clear; lia]. apply ZRSH. clear - Hx SHB1 SHB2; try acb. lia. }
    { rewrite VM4. unfold commit_vmmaps. cbn [vm_limit]. rewrite VML1.
      rewrite pages_total_cons. pose proof (cl_bounds W) as CB. subst W. cbn [fst snd] in CB. unfold wz in CB |- *. rewrite (unsigned_lit 32768) in CB by (clear; lia).
      pose proof (pages_total_nonneg S) as PT. unfold page_size in *. change (32768 / 4096) with 8 in CB. destruct CB as (_ & _ & _ & _ & WB & _).
      assert (PT1 : pages_total S1 <= pages_total S + 10).
      { rewrite ES1. destruct (mu <? mu'); cbn [app]; [| clear; lia].
        rewrite pages_total_cons. pose proof (cl_bounds (Z_to_bv 64 (sh (rbeg + mu)), Z_to_bv 64 ((mu' - mu) / 8))) as CB1. cbn [fst snd] in CB1.
        rewrite (unsigned_lit ((mu' - mu) / 8)) in CB1 by (clear - MUR; try acb; Z.div_mod_to_equations; lia). unfold page_size in CB1.
        assert (DV : (mu' - mu) / 8 / 4096 <= 8) by (clear - MUR; try acb; Z.div_mod_to_equations; lia).
        destruct CB1 as (_ & _ & _ & _ & WB1 & _). clear - WB1 DV; try acb. unfold wz. lia. }
      clear - WB BUD EAG4 EAG1 PT PT1 MUR; try acb. lia. }
    clear OK4 VIS4.
    set (m4 := owin L4 S1 W (zfill (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) m2)) in VIS5.
    assert (MU4 : munch [(FAB + mfa, FAB + mfa + 262144); (sh (FAB + mfa), sh (FAB + mfa) + 32768)] m2 m4).
    { intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _). subst m4.
      rewrite (owin_munch L4 S1 (sh (FAB + mfa)) 32768 SHB3 ltac:(hci; clear - SHB2 SHB5; try acb; unfold AHI_LO in *; lia) ltac:(hci; clear; lia) _ x) by (cbn [outside]; (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])).
      apply (zfill_munch (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) m2 x). cbn [outside]. rewrite ECUR, E256. (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])]). }
    assert (WM4 : wmono asegs m2 m4).
    { subst m4. eapply wmono_trans; [apply zfill_wmono | apply owin_wmono]. }
    assert (MI4 : mem_inv asegs m4).
    { subst m4. apply owin_mem_inv; [exact SHB3| clear - SHB2 SHB5; try acb; unfold AHI_LO in *; lia| clear; lia|].
      apply zfill_mem_inv; [rewrite ECUR; clear - CUR1 BND BNDL; try acb; lia| exact MI2]. }
    assert (NEWJ : stk asegs m4 (FAB + mfa) (FAB + mfa + 262144)).
    { subst m4. eapply stk_transport_disjoint; [| apply (owin_munch L4 S1 (sh (FAB + mfa)) 32768); [exact SHB3| clear - SHB2 SHB5; try acb; unfold AHI_LO in *; lia| clear; lia] | apply owin_wmono |].
      - pose proof (zfill_stk (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) m2) as X. rewrite ECUR, E256 in X. apply X; clear - CUR1 CUR2 BND BNDL SHB3; try acb; lia.
      - cbn [disjoint_from]. split; [| exact I]. clear - SHB2 SHB5 CUR1 BND BNDL; try acb. unfold AHI_LO in *. lia. }
    assert (SHK : stk asegs m4 (sh (FAB + mfa)) (sh (FAB + mfa) + 32768)).
    { subst m4. apply owin_stk; [exact SHB3| clear - SHB2 SHB5; try acb; unfold AHI_LO in *; lia| clear; lia| |].
      - intros x Hx. subst L4. rewrite in_rangesb_zcovb, (zcovb_maps_subtract L1 _ _ _ (lazy_ranges_okb_nowrap _ _ (lzok_ranges OK3))) by (clear - CUR1 BND BNDL; try acb; lia).
        rewrite <- in_rangesb_zcovb.
        assert (XL : in_rangesb x L1 = true).
        { rewrite EL1. destruct (mu <? mu'); [| apply LSH; clear - Hx SHB1 SHB2; try acb; lia].
          rewrite in_rangesb_zcovb, (zcovb_maps_subtract L _ _ _ (lazy_ranges_okb_nowrap _ _ (lzok_ranges OK))) by (clear - AUR MUR BND BNDL; try acb; lia).
          rewrite <- in_rangesb_zcovb, (LSH x) by (clear - Hx SHB1 SHB2; try acb; lia). cbn [andb negb]. unfold zinb.
          destruct (Z.leb_spec (rbeg + mu) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (rbeg + mu')); cbn; try reflexivity.
          exfalso. clear - Hx H H0 SHB2 SHB5 BND BNDL AUR; try acb. unfold AHI_LO in *. lia. }
        rewrite XL. cbn [andb negb]. unfold zinb.
        destruct (Z.leb_spec (FAB + mfa) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (FAB + mfa + 262144)); cbn; try reflexivity.
        exfalso. clear - Hx H H0 SHB2 SHB5 CUR1 BND BNDL; try acb. unfold AHI_LO in *. lia.
      - intros x Hx HSx. apply zfill_wmono. apply WM.
        rewrite ES1 in HSx. destruct (mu <? mu'); [| apply SVIS; exact HSx].
        cbn [app] in HSx.
        rewrite in_rangesb_cons in HSx. apply orb_prop in HSx. destruct HSx as [HW1 | HSx]; [| apply SVIS; exact HSx].
        exfalso. unfold zin_rangeb in HW1. cbn [fst snd] in HW1. unfold wz in HW1.
        rewrite (unsigned_lit (sh (rbeg + mu))) in HW1 by (unfold sh, ASHADOW_BASE; clear - AUR BND BNDL; try acb; Z.div_mod_to_equations; lia).
        rewrite (unsigned_lit ((mu' - mu) / 8)) in HW1 by (clear - MUR; try acb; Z.div_mod_to_equations; lia).
        apply andb_prop in HW1. destruct HW1 as [HW1 HW2]. apply Z.leb_le in HW1. apply Z.ltb_lt in HW2.
        unfold sh, ASHADOW_BASE in *. clear - HW1 HW2 Hx AUR MUR CUR1 NFR EFAB; try acb. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (SHR : 2148314624 <= sh (FAB + mfa) /\ sh (FAB + mfa) + 32768 <= 17594333495296) by (clear - SHB1 SHB3 SHB2 SHB5; try acb; unfold AHI_LO, sh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    pose proof (I : region_rank (sh (FAB + mfa)) 1) as RXRsh.
    renv_at ENV2 MU4 WM4 ENV4. clear ENV2.
    assert (POI4 := poisoned_transport _ m2 m4 _ _ _ POI2 MU4 WM4
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; clear - BND BNDL MUR AUR CUR1 NFR; try acb; repeat split; Z.div_mod_to_equations; lia)).
    clear POI2.
    assert (FAM4 := fam_transport CA _ m2 m4 _ FAM2 MU4 WM4 ltac:(hci; intros cq Hcq; cbn [disjoint_from]; destruct PLC as [PLCq]; unfold kSpaceSize in PLCq;
                                                               match goal with TB : akobj TH 4096 |- _ => clear - Hcq BND BNDL CAE HI CUR1 CUR2 SHR PLCq TB end; try acb; subst CA; aunf; repeat split; (first [clear - PLCq Hcq CUR2 CUR1 BNDL SHR THB; lia | lia]))).
    clear FAM2.
    transport_after_call asegs m2 m4 MU4 WM4. clear MU4 WM4 MI2.
    (* [comment removed for export] *)
    destruct (stk_cells _ _ _ SHK ltac:(hci; clear; lia)) as [sbs SB]. clear SHK.
    replace (sh (FAB + mfa) + 32768 - sh (FAB + mfa)) with 32768 in SB by (clear; lia).
    assert (SBL : Z.of_nat (length sbs) = 262144 / 8) by (destruct SB as [[WF _] _]; rewrite (proj1 WF), Z2Nat.id by (clear; lia); reflexivity).
    apply u8arr_of_rw_cells in SB.
    pose proof (re_senv _ _ _ _ _ _ _ ENV4) as SE4. open_senv SE4.
    fold (rinfo_cells nf mfa au mu') in RI.
    replace (Z_to_bv 64 (bv_unsigned sp + -400)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) + -240)) in VIS5
      by (f_equal; rewrite E160; clear; lia).
    assert (CSZF : cells_size [C8 (wz n); C8 (wz (P + 16)); C8 (wz FAB); C8 (wz (2^61)); C8 (wz (R + 8)); C8 (wz AINST); C8 (wz R); C8 (wz 0x19c168)] = 64%nat) by reflexivity.
    eapply (evt_sreach_lazy_at asegs L4 (W :: S1) Zr _ msF4 _ mo4 Q OK5 VIS5).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (pop_mid_map2 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4
                lo R rbeg csz au mu' nnew nf mfa (FAB + mfa) 262144 (efs_new (nf + nnew)) TSD CTX TH j8' j44 sbs);
        rewrite ?E160.
      all: replace (bv_unsigned sp + -160 + -240) with (bv_unsigned sp + -400) by (clear; lia).
      all: replace (bv_unsigned sp + -160 + -112) with (bv_unsigned sp + -272) by (clear; lia).
      all: replace (bv_unsigned sp + -160 + -64) with (bv_unsigned sp + -224) by (clear; lia).
      all: try eassumption. all: try reflexivity. all: try (clear - RR; try acb; tauto).
      { clear - HI; try acb; lia. } { clear - BND; try acb; lia. }
      { destruct SPA as [SPAq]; clear - SPAq SPR; try acb; Z.div_mod_to_equations; lia. }
      { clear - RBG CUR1 CUR2 BQ SZ NFR BNDL; try acb; destruct RBG as (R1 & R2 & R3); unfold AHI_LO in *; acb; Z.div_mod_to_equations; (first [clear - H5 H4 H0 H R2 R1 BQ CUR2 CUR1 SZ BNDL; lia | lia]). }
      { clear - BND; try acb; unfold AIMG_TOP; lia. }
      { destruct PLC as [PLCq]; unfold kSpaceSize in PLCq; clear - PLCq BND BNDL CUR1 CUR2 HC ER; try acb; split. repeat split; lia. } }
    clear OK5 VIS5. cbv beta. intros msF6 mo6 OK6 SBM6 HS6 P6.
    destruct P6 as (v0 & v1 & v2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & v3 & v4 & v5 & v6 & m6 & VIS6 & MU6 & WM6 & MI6 & ST6 & RI6 & POI6 & TST6 & F64n6).
    rewrite ?unsigned_lit in VIS6, MU6, ST6, F64n6 by (first [clear - BND HI; lia | lia]).
    replace (bv_unsigned sp + -160 - 272) with (bv_unsigned sp + -432) in MU6 by lia.
    replace (bv_unsigned sp + -160 + -64) with (bv_unsigned sp + -224) in * by lia.
    change (262144 / 8) with 32768 in MU6, POI6, SBL.
    clear TST RI F64n F176 F48 ST2 Etsdi Etp Etsd Ectx Ecan Egot Eshb Ehme Ethresh Emlim Edpm Erms Epsc Ename SB.
    renv_at ENV4 MU6 WM6 ENV6. clear ENV4.
    assert (POI7 := poisoned_transport _ m4 m6 _ _ _ POI4 MU6 WM6
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE; match goal with TB : akobj TH 4096 |- _ => clear - BND BNDL MUR AUR CUR1 NFR HI ER HC TB end;
                            try acb; aunf; repeat split; Z.div_mod_to_equations; (first [clear - H5 H4 H0 H MUR BNDL BND AUR HI H10 H9 CUR1 ACEILB0 THB; lia | lia]))).   (* [comment removed for export] *)
    clear POI4.
    assert (FAM6 := fam_transport CA _ m4 m6 _ FAM4 MU6 WM6 ltac:(hci; intros cq Hcq; cbn [disjoint_from]; destruct PLC as [PLCq]; unfold kSpaceSize in PLCq;
                                                               match goal with TB : akobj TH 4096 |- _ => clear - Hcq BND BNDL CAE HI CUR1 CUR2 SHR PLCq ER HC TB end; try acb; subst CA; aunf; repeat split; (first [clear - HI BND Hcq THB SHR PLCq BNDL; lia | lia]))).
    clear FAM4.
    transport_after_call asegs m4 m6 MU6 WM6. clear MU6 WM6 MI4.
    apply K. unfold rf4_at. fold csz. fold nnew. do 27 eexists. exists m6, L4, (W :: S1).
    split; [exact OK6|]. split; [exact VIS6|].
    split. { unfold rf_ledger. rewrite (proj2 (Z.ltb_lt mfa (mfa + 262144))) by (clear; lia).
             split; [subst L4; rewrite EL1; f_equal; clear; lia|]. split; [rewrite ES1; subst W; cbn [app]; do 2 f_equal; f_equal; clear; Z.div_mod_to_equations; lia|].
             split. { eapply nonvm_same_trans; [exact NVS1|]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM2|].
                      eapply nonvm_same_trans; [| apply nonvm_same_mat; exact SBM6]. subst mo4. apply nonvm_same_commit. }
             rewrite (same_but_materialized_vmmaps _ _ SBM6), VM4. unfold commit_vmmaps. cbn [vm_maps vm_reserved vm_limit vm_mmap_base vm_brk vm_noaccess app].
             rewrite ?ECUR, ?E256. rewrite VMM1, VMR1, VML1, VMB1, VBK1, VMN1. repeat (split; [first [reflexivity | f_equal; clear; lia]|]).
             rewrite (same_but_materialized_eager _ _ SBM6). clear - EAG4 EAG1; try acb. lia. }
    split. { unfold rf_W. replace (FAB + (mfa + 262144)) with (FAB + mfa + 262144) by (clear; lia). replace ((mfa + 262144 - mfa) / 8) with 32768 by (clear; Z.div_mod_to_equations; lia). exact MU. }
    split; [exact WM|]. split; [exact MI6|]. split; [exact ENV6|]. split; [exact ST6|]. split; [exact F64n6|]. split; [exact FRG|]. split; [exact FRR|].
    split; [exact PC0|]. split; [exact PCJ|].
    split. { intros cq Hcq. destruct (FAM6 cq Hcq) as (mc & cs & A & B & -> & ->). split; [exact A| exact B]. }
    split; [exact QST|]. split; [exact TST6|]. split; [unfold efs_new, kFreeArrayMapSize in SZ |- *; replace (mfa + 262144) with (round_up (4 * (nf + nnew)) 262144) by (clear - SZ; try acb; lia); exact RI6|].
    split; [exact RIJ|]. split; [exact EXH|]. split; [exact RST|]. split; [exact FARR|].
    split. { replace (FAB + (mfa + 262144)) with (FAB + mfa + 262144) by (clear; lia). eapply stk_merge; [exact FAJ| exact NEWJ| clear - NFR; try acb; lia]. }
    split; [exact USJ|]. split; [exact POI7|].
    replace (mfa + 262144 - mfa) with 262144 by (clear; lia). exact POI6.
  Qed.
End Refill.

