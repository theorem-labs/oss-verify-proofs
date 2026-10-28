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
     AW_Rta1 AW_MaybeRelease AW_Rta2 AllocTacX.
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

(* [comment removed for export] *)
Definition rta_mfa (nf n mfa : Z) : Z := if 4 * (nf + n) <=? mfa then mfa else efs_new (nf + n).

(* [comment removed for export] *)
Definition rta_W (lo sp R FAB TH nf mfa mfa' : Z) : list ivl :=
  [(lo, sp); (R, R + 8); (R + 16, R + 32); (R + 80, R + 88); (FAB + 4 * nf, FAB + mfa'); (sh (FAB + mfa), sh (FAB + mfa) + (mfa' - mfa) / 8); (TH + 2800, TH + 3168)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta1_at (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu : Z) (fl : list Z) (ws : list word) (msF' : machine_state) (mo' : Model) : Prop :=
  exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (j16 : list byte) L' S',
     lzok asegs L' S' Zr (mkCfg msF' mo')
  /\ restrict L' S' msF'
     = MS (mkR (wz 0x199cb4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz R) (wz nf) (wz AINST) (wz R) (wz rbeg) (wz (nf + n)) a4 a5 a6 a7
               (wz c) a1 (wz AINST) (wz n) (wz CH) (wz (nf + n)) (wz (2^61)) (wz FAB) (wz (2^60 + 2^20 - 1)) (wz (2^60)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x199e78) fc None m' (seg_rom asegs)
  /\ rf_ledger mo L S rbeg FAB mu mu mfa mfa L' S' mo'
  /\ munch (rta_W lo (bv_unsigned sp) R FAB TH nf mfa mfa) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ RENV tp TSD CTX TH sb ARI m'
  /\ stk asegs m' lo (bv_unsigned sp + -128)
  /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 16 j16; C8 (wz (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m' R (rinfo_cells nf mfa au mu)
  /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev fl)) /\ stk asegs m' (FAB + 4 * nf) (FAB + mfa)
  /\ u32arr asegs m' CH ws
  /\ stk asegs m' (TH + 2800) (TH + 3168).

(* [comment removed for export] *)
Definition rta2_at (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu mfa' : Z) (fl : list Z) (ws : list word) (msF' : machine_state) (mo' : Model) : Prop :=
  exists (rax t0 t1 t2 y1 y2 y3 y4 y5 a6 a7 t3 t4 t5 t6 : word) m' (j16 : list byte) L' S',
     lzok asegs L' S' Zr (mkCfg msF' mo')
  /\ restrict L' S' msF'
     = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz R) (wz nf) (wz 1) y1 y2 y3 y4 y5 a6 a7
               (wz c) a1 (wz AINST) (wz n) (wz CH) (wz (nf + n)) (wz (2^61)) (wz FAB) (wz (2^60 + 2^20 - 1)) (wz (2^60)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x199cb4) fc None m' (seg_rom asegs)
  /\ rf_ledger mo L S rbeg FAB mu mu mfa mfa' L' S' mo'
  /\ munch (rta_W lo (bv_unsigned sp) R FAB TH nf mfa mfa') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ RENV tp TSD CTX TH sb ARI m'
  /\ stk asegs m' lo (bv_unsigned sp + -128)
  /\ rw_cells asegs m' (bv_unsigned sp + -128) [CB 16 j16; C8 (wz (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m' R (rinfo_cells nf mfa' au mu)
  /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev fl)) /\ stk asegs m' (FAB + 4 * nf) (FAB + mfa')
  /\ u32arr asegs m' CH ws
  /\ stk asegs m' (TH + 2800) (TH + 3168)
  /\ poisoned m' (FAB + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa.

(* [comment removed for export] *)
Definition rta_post (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu mfa' : Z) (fl : list Z) (ws : list word) (msF' : machine_state) (mo' : Model) : Prop :=
  exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' L' S',
     lzok asegs L' S' Zr (mkCfg msF' mo')
  /\ restrict L' S' msF'
     = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
  /\ rf_ledger mo L S rbeg FAB mu mu mfa mfa' L' S' mo'
  /\ munch (rta_W lo (bv_unsigned sp) R FAB TH nf mfa mfa') m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ RENV tp TSD CTX TH sb ARI m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (nf + n)); C8 (wz mfa'); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]
  /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev fl) ++ ws) /\ stk asegs m' (FAB + 4 * (nf + n)) (FAB + mfa')
  /\ u32arr asegs m' CH ws
  /\ stk asegs m' (TH + 2800) (TH + 3168)
  /\ poisoned m' (FAB + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa.
End HCW.

Section Rta.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  (* [comment removed for export] *)
  Variables (lo sb c CH n TH CTX TSD : Z).
  Variables (nf mfa au mu : Z) (fl : list Z) (ws : list word).
  Let ARI := sb + kSpaceSize.
  Let R := ARI + REGIONINFO_SIZE * c.
  Let rbeg := sb + c * 2^32.
  Let FAB := rbeg + kFreeArrayOffset.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 576 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil. Hypothesis SBA : hidden (sb mod 65536 = 0).
  Hypothesis TPR : 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis THA : hidden (TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
  Hypothesis NR : 1 <= n /\ 4 * n <= kFreeArrayMapSize. Hypothesis WSL : length ws = Z.to_nat n.
  Hypothesis CHR : akobj CH (4 * n) /\ CH + 4 * n <= aceil. Hypothesis CHA : hidden (CH mod 4 = 0).
  Hypothesis PLCH : hidden ((CH + 4 * n <= FAB + 4 * nf \/ FAB + kFreeArraySize <= CH) /\ (CH + 4 * n <= ARI \/ ARI + 4096 <= CH)
                            /\ (CH + 4 * n <= TH + 2800 \/ TH + 3168 <= CH)).
  (* [comment removed for export] *)
  Hypothesis NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize /\ 4 * (nf + n) <= kFreeArraySize. Hypothesis MFAA : hidden (mfa mod kFreeArrayMapSize = 0).
  Hypothesis AUR : 0 <= au <= mu /\ mu + kUserMapSize <= kFreeArrayOffset.
  Hypothesis FLL : length fl = Z.to_nat nf.
  (* [comment removed for export] *)
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz AINST) a1 a2 (wz c) (wz CH) (wz n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x199b50) fc None m (seg_rom asegs).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ENV : RENV tp TSD CTX TH sb ARI m.
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  (* [comment removed for export] *)
  Hypothesis RI : rw_cells asegs m R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)).
  Hypothesis FAJ : stk asegs m (FAB + 4 * nf) (FAB + mfa).
  Hypothesis SRC : u32arr asegs m CH ws.
  (* [comment removed for export] *)
  Hypothesis RESF : forall (a k : word), AHI_LO <= bv_unsigned a -> region_free (vm_reserved (m_vmmaps mo)) a k = true.
  Hypothesis PRIM : forall (a k : word), rbeg <= bv_unsigned a -> bv_unsigned a + bv_unsigned k <= rbeg + 2^32 -> map_contains (vm_maps (m_vmmaps mo)) a k = true.
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis ZRP : forall x : word, rbeg <= bv_unsigned x < rbeg + 2^32 -> in_rangesb x Zr = false.
  Hypothesis ZRSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x Zr = true.
  Hypothesis LSH : forall x : word, sh AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x L = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  Hypothesis BUD : 4 * (nf + n) <= mfa \/ eager_used mo + pages_total S * 4096 + 303104 <= vm_limit (m_vmmaps mo).
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Let CHE : 4096 <= CH /\ CH + 4 * n <= aceil. Proof. exact (akobj_env _ _ (proj1 CHR) ltac:(tlia)). Qed.   (* [comment removed for export] *)
  Ltac prepR :=
    unfold kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kFreeArrayOffset, kNumClasses in NFR, AUR, NR, HC;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (LFL : length (wlist (rev fl)) = Z.to_nat nf) by (rewrite wlist_length, length_rev; exact FLL);
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ bv_unsigned sp + 16 <= 140737488355328
               /\ 4096 <= CH /\ CH + 4 * n <= aceil)
      by (clear - LO RNG SBR TPR SPT CHR; try acb; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, kPageSize, AIMG_TOP in *; acb; aunf; tlia);
        region_sides; name_bands;
    assert (GEO : R = sb + 137438953472 + 128 * c /\ rbeg = sb + c * 4294967296 /\ FAB = rbeg + 3758096384 /\ ARI = sb + 137438953472)
      by (subst R rbeg FAB ARI; unfold kSpaceSize, REGIONINFO_SIZE, kFreeArrayOffset; repeat split; reflexivity);
    destruct GEO as (ER & ERB & EFAB & EARI);
    assert (ARIR : AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND EARI S64; try acb; rewrite EARI;
          repeat split; [tlia| tlia| Z.div_mod_to_equations; tlia]);
    assert (SBR4 : AHI_LO <= sb /\ sb + 2^37 <= aceil /\ sb mod 4096 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND S64; try acb;
          repeat split; [tlia| tlia| Z.div_mod_to_equations; tlia]);
    assert (RR : AHI_LO <= R /\ R + 128 <= aceil /\ R mod 128 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND ER S64 HC; try acb; rewrite ER;
          repeat split; [tlia| tlia| Z.div_mod_to_equations; tlia]);
    assert (RBG : AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND ERB S64 HC; try acb; rewrite ERB;
          repeat split; [tlia| tlia| Z.div_mod_to_equations; tlia]);
    assert (ALh : hidden ((AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0)
                  /\ (AHI_LO <= sb /\ sb + 2^37 <= aceil /\ sb mod 4096 = 0) /\ (AHI_LO <= R /\ R + 128 <= aceil /\ R mod 128 = 0)
                  /\ (AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0)))
      by (split; exact (conj ARIR (conj SBR4 (conj RR RBG))));
    clear ARIR SBR4 RR RBG;
    assert (BNDL : sb + 137438953472 + 128 <= R /\ R + 128 <= sb + 137438953472 + 4096 /\ sb + 4294967296 <= rbeg /\ rbeg + 4294967296 <= sb + 137438953472
                   /\ FAB = rbeg + 3758096384)
      by (clear - BND ER ERB EFAB HC; try acb; rewrite ER, ERB; repeat split; tlia).
  Ltac getAL ARIR SBR4 RR RBG := lazymatch goal with H : hidden ((AHI_LO <= _ /\ _) /\ _) |- _ =>
    pose proof H as X; destruct X as [(ARIR & SBR4 & RR & RBG)] end.

  (* [comment removed for export] *)
  Lemma rta_s_head :
    (forall msF' mo', rta1_at L S Zr mo ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu fl ws msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. prepR.
    pose proof (re_isb _ _ _ _ _ _ _ ENV) as ISB. pose proof (re_iri _ _ _ _ _ _ _ ENV) as IRI.
    assert (NFN : 0 <= nf /\ nf + n < 2^32) by (clear - NFR NR; try acb; tlia). assert (NNR : 0 <= n) by (clear - NR; try acb; tlia).
    assert (CHR64 : 0 <= CH < 2^64) by (clear - BND NR; try acb; tlia).
    change ([C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)])
      with ([C8 (wz 0)] ++ [C4 (wz 0); C4 (wz 0)] ++ [C8 (wz nf)] ++ [C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]) in RI.
    apply rw_cells_app in RI. destruct RI as [RI0 RIr]. apply rw_cells_app in RIr. destruct RIr as [RI8 RIr]. apply rw_cells_app in RIr. destruct RIr as [RI16 RI24].
    cbn [cells_size csize Nat.add app] in RI8, RI16, RI24. change (Z.of_nat 8) with 8 in RI8, RI16, RI24. change (Z.of_nat 16) with 16 in RI24.
    replace (R + 8 + 8) with (R + 16) in RI16, RI24 by (clear; tlia). replace (R + 16 + 8) with (R + 24) in RI24 by (clear; tlia).
    getAL ARIR SBR4 RR RBG.
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply (rta_head ra sp gp tp t0 t1 t2 s0 s1 a1 a2 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sb ARI c CH nf n MI ST LO);
        try reflexivity; try eassumption. all: clear - HI HC; try acb; tlia. }
    clear OK VISE. cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (x5 & x6 & x7 & y4 & y5 & y6 & y7 & m1 & j16 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & RLK1).
    rewrite ?unsigned_lit in VIS1, MU1, ST1, FR1 by (clear - SPR BND HI; try acb; tlia).
    clear RI0 ST MI.
    rrenv_img_at ENV MU1 WM1 ENV1. clear ENV ISB IRI.
    transport_after_call asegs m m1 MU1 WM1.
    apply K. unfold rta1_at. do 11 eexists. exists m1, j16, L, S.
    split; [exact OK1|]. split; [exact VIS1|].
    split. { unfold rf_ledger. rewrite !Z.ltb_irrefl. cbn [app]. split; [reflexivity|]. split; [reflexivity|]. split; [apply nonvm_same_mat; exact SBM1|].
             rewrite (same_but_materialized_vmmaps _ _ SBM1), (same_but_materialized_eager _ _ SBM1). repeat (split; [reflexivity|]). clear; tlia. }
    split. { eapply munch_weaken; [| exact MU1]. unfold rta_W. rx_sub_fp_struct. }
    split; [exact WM1|]. split; [exact MI1|]. split; [exact ENV1|]. split; [exact ST1|]. split; [exact FR1|].
    split. { unfold rinfo_cells.
             change ([C8 (wz kWriterLock); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)])
               with ([C8 (wz kWriterLock)] ++ [C4 (wz 0); C4 (wz 0)] ++ [C8 (wz nf)] ++ [C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]).
             apply rw_cells_app; split; [exact RLK1|]. apply rw_cells_app; split; [exact RI8|]. apply rw_cells_app; split; cbn [cells_size csize Nat.add app];
             [ change (Z.of_nat 8) with 8; replace (R + 8 + 8) with (R + 16) by (clear; tlia); exact RI16
             | change (Z.of_nat 8) with 8; replace (R + 8 + 8 + 8) with (R + 24) by (clear; tlia); exact RI24 ]. }
    split; [exact RST|]. split; [exact FARR|]. split; [exact FAJ|]. split; [exact SRC| exact TST].
  Qed.

  (* [comment removed for export] *)
  Lemma rta_s_fast : forall msF1 mo1, 4 * (nf + n) <= mfa ->
    rta1_at L S Zr mo ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu fl ws msF1 mo1 ->
    (forall msF' mo', rta2_at L S Zr mo ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu mfa fl ws msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 FAST A1 K. prepR.
    assert (E128 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; clear - SPR HI BND; try acb; tlia).
    clear MI ST ENV TST RI RST FARR FAJ SRC VISE OK.
    destruct A1 as (x5 & x6 & x7 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m1 & j16 & L1 & S1
                    & OK1 & VIS1 & LED1 & MU & WM & MI1 & ENV1 & ST1 & FR1 & RI & RST & FARR & FAJ & SRC & TST).
    getAL ARIR SBR4 RR RBG.
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF1 _ mo1 Q OK1 VIS1).
    { eapply (efs_fast_spec _ (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo R (nf + n) nf mfa au mu MI1);
        rewrite ?E128; try reflexivity; try eassumption.
      { clear - HI; try acb; tlia. } { clear - RR; try acb; tauto. } { unfold kFreeArraySize. clear - NFR FAST NR; try acb; tlia. } }
    clear OK1 VIS1. cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (z1 & z2 & z3 & z4 & z5 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2).
    rewrite E128 in MU2. rewrite E128 in ST2.
    replace (ret_pc (wz 0x199cb4)) with (Z_to_bv 64 0x199cb4) in VIS2 by (symmetry; apply ret_pc_even; [clear; tlia | reflexivity]).
    replace (bv_unsigned sp + -128 - 48) with (bv_unsigned sp + -176) in MU2 by (clear; tlia).
    rrenv_img_at ENV1 MU2 WM2 ENV2. clear ENV1.
    unfold rta_W in MU. unfold rinfo_cells in RI. transport_after_call asegs m1 m2 MU2 WM2. fold (rinfo_cells nf mfa au mu) in RI.
    apply K. unfold rta2_at. do 15 eexists. exists m2, j16, L1, S1.
    split; [exact OK2|]. split; [exact VIS2|]. split; [eapply rf_ledger_mat; [exact LED1| exact SBM2]|].
    split; [unfold rta_W; exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ENV2|]. split; [exact ST2|]. split; [exact FR1|].
    split; [exact RI|]. split; [exact RST|]. split; [exact FARR|]. split; [exact FAJ|]. split; [exact SRC|]. split; [exact TST|].
    rewrite Z.sub_diag. change (0 / 8) with 0. cbn [Z.to_nat].
    apply poisoned_0; unfold AHI_LO, sh, ASHADOW_BASE in *; acb.
    - clear - RBG NFR BNDL; try acb. tlia.
    - destruct MFAA as [MFAA']. unfold kFreeArrayMapSize in MFAA'. destruct RBG as (_ & _ & RB3). destruct BNDL as (_ & _ & _ & _ & EF). rewrite EF.
      clear - RB3 MFAA'; try acb. Z.div_mod_to_equations. tlia.
    - clear - RBG NFR BNDL; try acb. tlia.
  Qed.

  (* [comment removed for export] *)
  Lemma rta_s_tail : forall msF1 mo1 mfa', 4 * (nf + n) <= mfa' -> mfa <= mfa' <= kFreeArraySize ->
    rta2_at L S Zr mo ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu mfa' fl ws msF1 mo1 ->
    (forall msF' mo', rta_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu mfa' fl ws msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 mfa' ROOM MFR A1 K. prepR. unfold kFreeArraySize in MFR.
    assert (E128 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; clear - SPR HI BND; try acb; tlia).
    clear MI ST ENV TST RI RST FARR FAJ SRC VISE OK.
    destruct A1 as (rax & x5 & x6 & x7 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m1 & j16 & L1 & S1
                    & OK1 & VIS1 & LED1 & MU & WM & MI1 & ENV1 & ST1 & FR1 & RI & RST & FARR & FAJ & SRC & TST & POI1).
    getAL ARIR SBR4 RR RBG.
    pose proof (re_isb _ _ _ _ _ _ _ ENV1) as ISB. pose proof (re_iri _ _ _ _ _ _ _ ENV1) as IRI.
    pose proof (re_senv _ _ _ _ _ _ _ ENV1) as SE. pose proof (se_got _ _ _ _ _ SE) as GOT. pose proof (se_psc _ _ _ _ _ SE) as PSC. clear SE.
    assert (CHR3 : akobj CH (4 * n) /\ CH + 4 * n <= aceil /\ CH mod 4 = 0) by (destruct CHA as [CHA']; clear - CHR CHA'; tauto).   (* [comment removed for export] *)
    assert (FABR : AHI_LO <= FAB /\ FAB + mfa' <= aceil /\ FAB mod 4096 = 0).
    { unfold AHI_LO in *; acb. destruct RBG as (R1 & R2 & R3). destruct BNDL as (_ & _ & _ & _ & EF). rewrite EF.
      clear - R1 R2 R3 MFR NFR; try acb. repeat split; [tlia| tlia| Z.div_mod_to_equations; tlia]. }
    assert (SEP : hidden ((CH + 4 * n <= FAB + 4 * nf \/ FAB + 4 * (nf + n) <= CH) /\ (CH + 4 * n <= R \/ R + 128 <= CH) /\ (R + 128 <= FAB \/ FAB + mfa' <= R))).
    { destruct PLCH as [(P1 & P2 & P3)]. unfold kFreeArraySize in P1. rewrite EARI in P2. split. clear - P1 P2 NFR MFR BNDL BND HC ER ERB NR; try acb. repeat split; tlia. }
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF1 _ mo1 Q OK1 VIS1).
    { eapply (rta_tail ra sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 lo sb ARI c CH FAB nf n mfa' au mu ws fl j16 MI1 ST1 LO);
        try eassumption. { clear - HI; try acb; tlia. } { clear - NR; try acb; tlia. } { unfold kFreeArraySize. clear - NFR ROOM MFR; try acb; tlia. } }
    clear OK1 VIS1. cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & RI2 & RST2 & FARR2 & FAJ2 & SRC2).
    clear ISB IRI GOT PSC RI RST FARR FAJ SRC ST1 FR1.
    rrenv_img_at ENV1 MU2 WM2 ENV2. clear ENV1.
    assert (POI2 := poisoned_transport _ m1 m2 _ _ _ POI1 MU2 WM2
                      ltac:(hci; cbn [disjoint_from]; unfold sh, ASHADOW_BASE, AHI_LO in *; acb;
                            clear - BND BNDL HI MFR NFR NR RBG; try acb; repeat split; Z.div_mod_to_equations; tlia)).
    clear POI1.
    unfold rta_W in MU. transport_after_call asegs m1 m2 MU2 WM2.
    apply K. unfold rta_post. do 15 eexists. exists m2, L1, S1.
    split; [exact OK2|]. split; [exact VIS2|]. split; [eapply rf_ledger_mat; [exact LED1| exact SBM2]|].
    split; [unfold rta_W; exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ENV2|]. split; [exact ST2|].
    split; [exact RI2|]. split; [exact RST2|]. split; [exact FARR2|]. split; [exact FAJ2|]. split; [exact SRC2|]. split; [exact TST| exact POI2].
  Qed.

  (* [comment removed for export] *)
  Lemma rta_s_map : forall msF1 mo1, mfa < 4 * (nf + n) ->
    rta1_at L S Zr mo ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu fl ws msF1 mo1 ->
    (forall msF' mo', rta2_at L S Zr mo ra sp gp tp a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu (mfa + 262144) fl ws msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 SLOW A1 K. prepR.
    assert (E128 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; clear - SPR HI BND; try acb; tlia).
    destruct BUD as [FAST | BUDm]. { exfalso. clear - FAST SLOW; try acb. tlia. }
    clear MI ST ENV TST RI RST FARR FAJ SRC VISE OK.
    destruct A1 as (x5 & x6 & x7 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m1 & j16 & L1 & S1
                    & OK1 & VIS1 & LED1 & MU & WM & MI1 & ENV1 & ST1 & FR1 & RI & RST & FARR & FAJ & SRC & TST).
    assert (MFQ : exists q, mfa = 262144 * q) by (destruct MFAA as [MFAA']; exists (mfa / kFreeArrayMapSize); unfold kFreeArrayMapSize in *; clear - MFAA'; try acb; Z.div_mod_to_equations; tlia).
    destruct MFQ as [mfq MFQ].
    assert (SZ : efs_new (nf + n) - mfa = 262144).
    { unfold efs_new, round_up, kFreeArrayMapSize. rewrite MFQ. clear - SLOW NR NFR MFQ; try acb. Z.div_mod_to_equations. tlia. }
    (* [comment removed for export] *)
    pose proof (re_pmh _ _ _ _ _ _ _ ENV1) as PMH. pose proof (re_senv _ _ _ _ _ _ _ ENV1) as SE.
    pose proof (se_got _ _ _ _ _ SE) as GOT. pose proof (se_psc _ _ _ _ _ SE) as PSC. pose proof (se_dpm _ _ _ _ _ SE) as DPM. clear SE.
    getAL ARIR SBR4 RR RBG.
    eapply (evt_sreach_lazy_at asegs L1 S1 Zr _ msF1 _ mo1 Q OK1 VIS1).
    { eapply (efs_seg1 _ (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo R rbeg (nf + n) nf mfa au mu MI1);
        rewrite ?E128; try reflexivity; try eassumption.
      { clear - HI; try acb; tlia. } { clear - RR; try acb; tauto. }
      { unfold kFreeArraySize, kFreeArrayMapSize. destruct MFAA as [MFAA']. unfold kFreeArrayMapSize in MFAA'. clear - NFR SLOW NR MFAA'; try acb. repeat split; tlia. } }
    clear OK1 VIS1. cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (m2 & j8 & j44 & VIS2 & MU2 & WM2 & MI2 & ST2 & F176 & F48). cbv zeta in VIS2, F176.
    rewrite E128 in MU2. rewrite ?E128 in ST2. rewrite ?E128 in F176. rewrite ?E128 in F48. rewrite ?E128 in VIS2.
    replace (bv_unsigned sp + -128 + -176) with (bv_unsigned sp + -304) in * by (clear; tlia).   (* [comment removed for export] *)
    replace (bv_unsigned sp + -128 + -48) with (bv_unsigned sp + -176) in * by (clear; tlia).
    replace (bv_unsigned sp + -128 - 448) with (bv_unsigned sp + -576) in * by (clear; tlia).
    fold FAB in VIS2, F176. rewrite SZ in VIS2, F176.
    assert (CURB : FAB <= FAB + mfa /\ FAB + mfa + 262144 <= rbeg + 4294967296 /\ (exists bq, FAB + mfa = 4096 * bq)).
    { destruct RBG as (_ & _ & R3). unfold kFreeArraySize in *.
      clear - NFR R3 MFQ EFAB SLOW NR; try acb. split; [tlia| split; [Z.div_mod_to_equations; tlia| exists ((FAB + mfa) / 4096); rewrite EFAB, MFQ; Z.div_mod_to_equations; tlia]]. }
    destruct CURB as (CUR1 & CUR2 & [bq BQ]).
    rrenv_img_at ENV1 MU2 WM2 ENV2. clear ENV1 PMH GOT PSC DPM.
    unfold rinfo_cells in RI. unfold rta_W in MU. replace ((mfa - mfa) / 8) with 0 in MU by (clear; Z.div_mod_to_equations; tlia).
    (* [comment removed for export] *)
    eapply (munch_weaken _ ((lo, bv_unsigned sp) :: (R, R + 8) :: (R + 16, R + 32) :: (R + 80, R + 88) :: (FAB + 4 * nf, FAB + mfa + 262144)
                             :: (sh (FAB + mfa), sh (FAB + mfa) + 32768) :: (TH + 2800, TH + 3168) :: nil)) in MU; [| rx_sub_fp_struct].
    transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    eapply (sr_ecall_MS L1 S1 Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d1904 fc None m2 msF2 mo2 Q OK2 VIS2 ecall_1d697c).
    clear OK2 VIS2. intros msF3 OK3 VIS3 HS3.
    (* [comment removed for export] *)
    assert (NZ : page_round_up_Z (bv_unsigned (wz 262144)) = 262144) by (vm_compute; reflexivity).
    assert (ECUR : bv_unsigned (Z_to_bv 64 (FAB + mfa)) = FAB + mfa) by (apply unsigned_lit; clear - CUR1 CUR2 BND BNDL; try acb; tlia).
    assert (E256 : bv_unsigned (Z_to_bv 64 262144) = 262144) by (apply unsigned_lit; clear; tlia).
    pose proof LED1 as LED. destruct LED as (EL1 & ES1 & NVS1 & VMM1 & VMR1 & VML1 & VMB1 & VBK1 & VMN1 & EAG1).
    rewrite !Z.ltb_irrefl in EL1, ES1, VMN1. cbn [app] in ES1.
    eapply (sr_mmap_commit_MS L1 S1 Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d1904 fc None m2 false msF3 mo2 Q OK3 VIS3 eq_refl);
      rewrite ?NZ, ?(same_but_materialized_vmmaps _ _ SBM2), ?(same_but_materialized_eager _ _ SBM2), ?VMM1, ?VMR1, ?VML1, ?VMN1; unfold wz; rewrite ?ECUR, ?E256.
    { apply wz_ne0. clear; tlia. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { rewrite (nonvm_same_atop _ _ NVS1), ATOP. clear - CUR1 CUR2 BND BNDL; try acb; tlia. }
    { unfold page_size. rewrite BQ. clear. Z.div_mod_to_equations. tlia. }
    { clear - CUR1 BND BNDL; try acb. tlia. }
    { apply RESF. unfold AHI_LO. rewrite ECUR. clear - CUR1 BND BNDL; try acb. tlia. }
    { apply PRIM; rewrite ?ECUR, ?E256; clear - CUR1 CUR2 BNDL; try acb; tlia. }
    { exact NW. }
    { exact NWA. }
    { exact NOV. }
    { intros _ x Hx. apply ZRP. clear - Hx CUR1 CUR2 BNDL; try acb. tlia. }
    { intros X; discriminate X. } { intros X; discriminate X. }
    { intros _. rewrite ES1. pose proof (pages_total_nonneg S) as PT. unfold page_size in *. clear - BUDm EAG1 PT; try acb. tlia. }
    cbv zeta. intros msF4 OK4 VIS4 HS4 EAG4.
    change (1906948 + 4) with 1906952 in VIS4. cbn [fflags] in OK4, VIS4, HS4, EAG4 |- *.
    set (mo4 := commit_model (Z_to_bv 64 50) (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) false mo2) in *.
    set (L4 := maps_subtract L1 (FAB + mfa) (FAB + mfa + 262144)) in *.
    assert (VM4 : m_vmmaps mo4 = commit_vmmaps (m_vmmaps mo1) (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) false).
    { subst mo4. rewrite commit_model_vmmaps, (same_but_materialized_vmmaps _ _ SBM2). reflexivity. }
    (* [comment removed for export] *)
    assert (SHB : sh AHI_LO <= sh (FAB + mfa) /\ sh (FAB + mfa) + 32768 <= sh aceil /\ 12599296 <= sh (FAB + mfa) /\ sh (FAB + mfa + 262144) = sh (FAB + mfa) + 32768
                  /\ sh aceil < AHI_LO).
    { unfold sh, ASHADOW_BASE, AHI_LO in *. acb. rewrite BQ. clear - CUR1 CUR2 BQ BND BNDL; try acb. Z.div_mod_to_equations. tlia. }
    destruct SHB as (SHB1 & SHB2 & SHB3 & SHB4 & SHB5).
    clear ARIR SBR4 RR RBG.
    (* [comment removed for export] *)
    set (W := (wz (sh (FAB + mfa)), wz 32768)).
    destruct (open_window_MS L4 S1 Zr W msF4 mo4 _ F _ fc None _ OK4 VIS4) as [OK5 VIS5].
    { intros x Hx. apply (zin_W (sh (FAB + mfa)) 32768) in Hx; [| clear - SHB3; try acb; tlia | clear - SHB2 SHB5; try acb; unfold AHI_LO in *; tlia | clear; tlia]. apply ZRSH. clear - Hx SHB1 SHB2; try acb. tlia. }
    { rewrite VM4. unfold commit_vmmaps. cbn [vm_limit]. rewrite VML1.
      rewrite pages_total_cons. pose proof (cl_bounds W) as CB. subst W. cbn [fst snd] in CB. unfold wz in CB |- *. rewrite (unsigned_lit 32768) in CB by (clear; tlia).
      pose proof (pages_total_nonneg S) as PT. unfold page_size in *. change (32768 / 4096) with 8 in CB. destruct CB as (_ & _ & _ & _ & WB & _).
      rewrite ES1. clear - WB BUDm EAG4 EAG1 PT; try acb. tlia. }
    clear OK4 VIS4.
    set (m4 := owin L4 S1 W (zfill (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) m2)) in VIS5.
    assert (MU4 : munch [(FAB + mfa, FAB + mfa + 262144); (sh (FAB + mfa), sh (FAB + mfa) + 32768)] m2 m4).
    { intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _). subst m4.
      rewrite (owin_munch L4 S1 (sh (FAB + mfa)) 32768 SHB3 ltac:(hci; clear - SHB2 SHB5; try acb; unfold AHI_LO in *; tlia) ltac:(hci; clear; tlia) _ x) by (cbn [outside]; tauto).
      apply (zfill_munch (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) m2 x). cbn [outside]. rewrite ECUR, E256. tauto. }
    assert (WM4 : wmono asegs m2 m4).
    { subst m4. eapply wmono_trans; [apply zfill_wmono | apply owin_wmono]. }
    assert (MI4 : mem_inv asegs m4).
    { subst m4. apply owin_mem_inv; [exact SHB3| clear - SHB2 SHB5; try acb; unfold AHI_LO in *; tlia| clear; tlia|].
      apply zfill_mem_inv; [rewrite ECUR; clear - CUR1 BND BNDL; try acb; tlia| exact MI2]. }
    assert (NEWJ : stk asegs m4 (FAB + mfa) (FAB + mfa + 262144)).
    { subst m4. eapply stk_transport_disjoint; [| apply (owin_munch L4 S1 (sh (FAB + mfa)) 32768); [exact SHB3| clear - SHB2 SHB5; try acb; unfold AHI_LO in *; tlia| clear; tlia] | apply owin_wmono |].
      - pose proof (zfill_stk (Z_to_bv 64 (FAB + mfa)) (Z_to_bv 64 262144) m2) as X. rewrite ECUR, E256 in X. apply X; clear - CUR1 CUR2 BND BNDL SHB3; try acb; tlia.
      - cbn [disjoint_from]. split; [| exact I]. clear - SHB2 SHB5 CUR1 BND BNDL; try acb. unfold AHI_LO in *. tlia. }
    assert (SHK : stk asegs m4 (sh (FAB + mfa)) (sh (FAB + mfa) + 32768)).
    { subst m4. apply owin_stk; [exact SHB3| clear - SHB2 SHB5; try acb; unfold AHI_LO in *; tlia| clear; tlia| |].
      - intros x Hx. subst L4. rewrite in_rangesb_zcovb, (zcovb_maps_subtract L1 _ _ _ (lazy_ranges_okb_nowrap _ _ (lzok_ranges OK3))) by (clear - CUR1 BND BNDL; try acb; tlia).
        rewrite <- in_rangesb_zcovb.
        assert (XL : in_rangesb x L1 = true) by (rewrite EL1; apply LSH; clear - Hx SHB1 SHB2; try acb; tlia).
        rewrite XL. cbn [andb negb]. unfold zinb.
        destruct (Z.leb_spec (FAB + mfa) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (FAB + mfa + 262144)); cbn; try reflexivity.
        exfalso. clear - Hx H H0 SHB2 SHB5 CUR1 BND BNDL; try acb. unfold AHI_LO in *. tlia.
      - intros x Hx HSx. apply zfill_wmono. apply WM. apply SVIS. rewrite ES1 in HSx. exact HSx. }
    (* [comment removed for export] *)
    assert (SHR : 2148314624 <= sh (FAB + mfa) /\ sh (FAB + mfa) + 32768 <= 17594333495296) by (clear - SHB1 SHB3 SHB2 SHB5; try acb; unfold AHI_LO, sh, ASHADOW_BASE in *; Z.div_mod_to_equations; tlia).   (* [comment removed for export] *)
    pose proof (I : region_rank (sh (FAB + mfa)) 1) as RXRsh.
    rrenv_img_at ENV2 MU4 WM4 ENV4. clear ENV2.
    transport_after_call asegs m2 m4 MU4 WM4. clear MU4 WM4 MI2.
    (* [comment removed for export] *)
    destruct (stk_cells _ _ _ SHK ltac:(hci; clear; tlia)) as [sbs SB]. clear SHK.
    replace (sh (FAB + mfa) + 32768 - sh (FAB + mfa)) with 32768 in SB by (clear; tlia).
    assert (SBL : Z.of_nat (length sbs) = 262144 / 8) by (destruct SB as [[WF _] _]; rewrite (proj1 WF), Z2Nat.id by (clear; tlia); reflexivity).
    apply u8arr_of_rw_cells in SB.
    pose proof (re_senv _ _ _ _ _ _ _ ENV4) as SE4. open_senv SE4.
    fold (rinfo_cells nf mfa au mu) in RI.
    replace (Z_to_bv 64 (bv_unsigned sp + -304)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) + -176)) in VIS5
      by (f_equal; rewrite E128; clear; tlia).
    getAL ARIR SBR4 RR RBG.
    eapply (evt_sreach_lazy_at asegs L4 (W :: S1) Zr _ msF4 _ mo4 Q OK5 VIS5).
    { eapply (efs_seg2 (wz 0x199cb4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4
                lo R (FAB + mfa) 262144 (efs_new (nf + n)) nf mfa au mu TSD CTX TH j8 j44 sbs MI4);
        rewrite ?E128.
      all: replace (bv_unsigned sp + -128 + -176) with (bv_unsigned sp + -304) by (clear; tlia).
      all: replace (bv_unsigned sp + -128 + -48) with (bv_unsigned sp + -176) by (clear; tlia).
      all: try eassumption. all: try reflexivity. all: try (clear - RR; try acb; tauto).
      { clear - HI; try acb; tlia. } { clear - BND; try acb; tlia. }
      { destruct SPA as [SPAq]; clear - SPAq SPR; try acb; Z.div_mod_to_equations; tlia. }
      { clear - RBG CUR1 CUR2 BQ SZ NFR BNDL NR; try acb; destruct RBG as (R1 & R2 & R3); unfold AHI_LO, efs_new, round_up, kFreeArrayMapSize in *; acb;
        Z.div_mod_to_equations; tlia. }
      { clear - BND; try acb; unfold AIMG_TOP; tlia. }
      { destruct PLC as [PLCq]; unfold kSpaceSize in PLCq; clear - PLCq BND BNDL CUR1 CUR2 HC ER; try acb; split. repeat split; tlia. } }
    clear OK5 VIS5. cbv beta. intros msF6 mo6 OK6 SBM6 HS6 P6.
    destruct P6 as (v0 & v1 & v2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & v3 & v4 & v5 & v6 & m6 & VIS6 & MU6 & WM6 & MI6 & ST6 & RI6 & POI6 & TST6).
    rewrite ?E128 in VIS6. rewrite ?E128 in MU6. rewrite ?E128 in ST6.
    replace (ret_pc (wz 0x199cb4)) with (Z_to_bv 64 0x199cb4) in VIS6 by (symmetry; apply ret_pc_even; [clear; tlia | reflexivity]).
    replace (bv_unsigned sp + -128 - 208) with (bv_unsigned sp + -336) in MU6 by (clear; tlia).
    change (262144 / 8) with 32768 in MU6, POI6, SBL.
    clear TST RI F176 F48 ST2 Etsdi Etp Etsd Ectx Ecan Egot Eshb Ehme Ethresh Emlim Edpm Erms Epsc Ename SB.
    rrenv_img_at ENV4 MU6 WM6 ENV6. clear ENV4.
    transport_after_call asegs m4 m6 MU6 WM6. clear MU6 WM6 MI4.
    apply K. unfold rta2_at. do 15 eexists. exists m6, j16, L4, (W :: S1).
    split; [exact OK6|]. split; [exact VIS6|].
    split. { unfold rf_ledger. rewrite (proj2 (Z.ltb_lt mfa (mfa + 262144))) by (clear; tlia). rewrite !Z.ltb_irrefl.
             split; [subst L4; rewrite EL1; f_equal; clear; tlia|]. split; [rewrite ES1; subst W; cbn [app]; do 2 f_equal; f_equal; clear; Z.div_mod_to_equations; tlia|].
             split. { eapply nonvm_same_trans; [exact NVS1|]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM2|].
                      eapply nonvm_same_trans; [| apply nonvm_same_mat; exact SBM6]. subst mo4. apply nonvm_same_commit. }
             rewrite (same_but_materialized_vmmaps _ _ SBM6), VM4. unfold commit_vmmaps. cbn [vm_maps vm_reserved vm_limit vm_mmap_base vm_brk vm_noaccess app].
             rewrite ?ECUR, ?E256. rewrite VMM1, VMR1, VML1, VMB1, VBK1, VMN1. repeat (split; [first [reflexivity | f_equal; clear; tlia]|]).
             rewrite (same_but_materialized_eager _ _ SBM6). clear - EAG4 EAG1; try acb. tlia. }
    split. { unfold rta_W. replace (FAB + (mfa + 262144)) with (FAB + mfa + 262144) by (clear; tlia). replace ((mfa + 262144 - mfa) / 8) with 32768 by (clear; Z.div_mod_to_equations; tlia). exact MU. }
    split; [exact WM|]. split; [exact MI6|]. split; [exact ENV6|]. split; [exact ST6|]. split; [exact FR1|].
    split; [unfold efs_new, kFreeArrayMapSize in SZ |- *; replace (mfa + 262144) with (round_up (4 * (nf + n)) 262144) by (clear - SZ; try acb; tlia); exact RI6|].
    split; [exact RST|]. split; [exact FARR|].
    split. { replace (FAB + (mfa + 262144)) with (FAB + mfa + 262144) by (clear; tlia). eapply stk_merge; [exact FAJ| exact NEWJ| clear - NFR; try acb; tlia]. }
    split; [exact SRC|]. split; [exact TST6|].
    replace (mfa + 262144 - mfa) with 262144 by (clear; tlia). exact POI6.
  Qed.

  (* [comment removed for export] *)
  Theorem rta_sreach :
    (forall msF' mo', rta_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c R rbeg FAB CH TH TSD CTX sb ARI nf n mfa au mu (rta_mfa nf n mfa) fl ws msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. unfold rta_mfa in K. apply rta_s_head. intros msF1 mo1 A1.
    pose proof NFR as NFR0. pose proof NR as NR0. unfold kFreeArraySize, kFreeArrayMapSize in NFR0, NR0.
    destruct (Z.leb_spec (4 * (nf + n)) mfa) as [FAST | SLOW].
    - eapply rta_s_fast; [exact FAST| exact A1|]. intros msF2 mo2 A2.
      eapply rta_s_tail; [exact FAST| | exact A2| exact K]. unfold kFreeArraySize. clear - NFR0; try acb. tlia.
    - assert (MFQ : exists q, mfa = 262144 * q)
        by (destruct MFAA as [MFAA']; exists (mfa / kFreeArrayMapSize); unfold kFreeArrayMapSize in *; clear - MFAA'; try acb; Z.div_mod_to_equations; tlia).
      destruct MFQ as [mfq MFQ].
      assert (SZ : efs_new (nf + n) = mfa + 262144).
      { unfold efs_new, round_up, kFreeArrayMapSize. rewrite MFQ. clear - SLOW NR0 NFR0 MFQ; try acb. Z.div_mod_to_equations. tlia. }
      rewrite SZ in K.
      eapply rta_s_map; [exact SLOW| exact A1|]. intros msF2 mo2 A2.
      eapply rta_s_tail; [| | exact A2| exact K]. { clear - SLOW NR0 NFR0; try acb. tlia. }
      unfold kFreeArraySize. rewrite MFQ. clear - SLOW NR0 NFR0 MFQ; try acb. Z.div_mod_to_equations. tlia.
  Qed.
End Rta.

