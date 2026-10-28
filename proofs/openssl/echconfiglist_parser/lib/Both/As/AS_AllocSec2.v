(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AsDepotHash AsDepotPut AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_AllocBase AW_LargeAlloc1 AW_SysconfPg
     SecLazy AS_LargeAlloc AS_CombinedLarge AW_AllocSec1 AW_AllocSec2 AS_AllocSec1 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section AllocSec.
  Context {HCEIL : HeapCeil}.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  (* [comment removed for export] *)
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).   (* [comment removed for export] *)
  Variables (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j8 : list byte).
  Variables (lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 nT id : Z) (chunks T : list Z) (rest : list word) (d : depot).
  Hypothesis DEFS : hidden (needed = round_up (Z.max size 8) 8 + 4096 /\ msz = round_up needed 4096 + 4096 /\ size = 8 * q8 + r8
                            /\ nT = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 768 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0). Hypothesis SPH : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 64512 < size < 2^32. Hypothesis R8 : 0 <= r8 < 8.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC0 : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)).
  Hypothesis PLCD0 : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ (pa + kPtrArrayReserve <= d_nb d \/ d_nb d + 16 * 65536 <= pa) /\ (pa + kPtrArrayReserve <= d_sb d \/ d_sb d + 8 * 131072 <= pa)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20. Hypothesis NRQ : exists q, nres = 512 * q.
  Hypothesis LEN : zlen chunks = nch.
  Hypothesis NR : 1 <= nT <= 254. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + nT + 1 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  (* [comment removed for export] *)
  Hypothesis AEN : AENV tp TSD CTX TH sb SO T rest m.
  Hypothesis SEN : SENV tp TSD CTX TH m.
  Hypothesis FR : aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m j8.
  Hypothesis INST64 : rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m (AINST + 112) [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk asegs m (AINST + 136) (AINST + 680).
  Hypothesis MTX : rw_cells asegs m (AINST + 680) [C8 (wz 0)].
  Hypothesis GST : stk asegs m (AINST + 688) (AINST + 728).
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis PAJ : stk asegs m (pa + 8 * nch) (pa + 8 * nres).
  Hypothesis DEP : DEPOT asegs d m.
  (* [comment removed for export] *)
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis BUD : eager_used mo + pages_total S * page_size + msz + (msz / 32768 + 2) * page_size + 0x20000 <= vm_limit (m_vmmaps mo).
  Hypothesis GAP : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true.
  (* [comment removed for export] *)
  Hypothesis IMGR : forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved (m_vmmaps mo)) = true.
  Hypothesis SHLAND : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.
  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.   (* [comment removed for export] *)
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  Hypothesis TMAPS : forall x : word, TH <= bv_unsigned x < TH + 4096 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis CMAPS : forall x : word, CTX <= bv_unsigned x < CTX + 160 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PMAPS : forall x : word, pa <= bv_unsigned x < pa + kPtrArrayReserve -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis SBMAPS : forall x : word, sb <= bv_unsigned x < sb + kSpaceSize -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis DNMAPS : forall x : word, d_nb d <= bv_unsigned x < d_nb d + 16 * 65536 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis DSMAPS : forall x : word, d_sb d <= bv_unsigned x < d_sb d + 8 * 131072 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PAMC : nch = nres -> map_contains (vm_maps (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PARF : nch = nres -> region_free (vm_reserved (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PAZR : nch = nres -> forall x : word, pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 0x20000 -> in_rangesb x Zr = false.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR (wz 0x19709c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 0) (wz size) (wz AINST) (wz (TH + 208)) (wz needed) (wz 8) x14 x15 x16 x17
              (wz 8) (wz needed) (wz 2048) (wz size) (wz AINST) (wz SO) (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) x28 x29 x30 x31)
         F (Z_to_bv 64 0x19b65c) fc None m (seg_rom asegs).

  Let PAE : 12599296 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let POST := alloc_sec_sr_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb SO pa nres nch id nT chunks T rest d.
  Let MID := alloc_sec_mid L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 id nT chunks T rest d.

  (* [comment removed for export] *)
  Lemma alloc_sec_small : forall msF3 mo3,
    MID msF3 mo3 ->
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF3 mo3).
  Proof using HCEIL L S Zr mo Q ra sp gp tp F fc m s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 nT id chunks T rest d DEFS LO HI SPA SPH SZ R8 TPR RNG PLC0 PLCD0 SBR SOR PAR NCH LEN DLO TMAPS CMAPS PMAPS SBMAPS DNMAPS DSMAPS.
    intros msF3 mo3 M K.
    pose proof DEFS as D; destruct D as [(DNEED & DMSZ & DSZ & DNT & DID)].
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof SPA as R; destruct R as [SPA'].
    assert (GEO : size + 8 <= needed - 4088 /\ needed <= size + 4096 + 8 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ 8 * q8 <= size /\ size < 8 * q8 + 8
                  /\ needed = 8 * q8 + (if r8 =? 0 then 0 else 8) + 4096)
      by (clear - DNEED DMSZ DSZ SZ R8; try acb; subst needed msz; unfold round_up; destruct (Z.eqb_spec r8 0); Z.div_mod_to_equations; nia).
    destruct GEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (ND : exists nd8, needed = 8 * nd8) by (clear - DNEED SZ; try acb; rewrite DNEED; unfold round_up; exists ((Z.max size 8 + 8 - 1) / 8 + 512); Z.div_mod_to_equations; nia).
    destruct ND as [nd8 ND8].
    pose proof LO as LO'. acb.
    destruct M as (a & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & j8' & sbsU & ob0 & gb & hb1 & t8 & m3
                 & AHI & CE & AL & FREE & OK3 & VIS3 & MO2 & MU & WM & MI3 & AEN3 & FR3 & ST3 & CHDR3 & HB1R & HB1M & LRZ3 & USR3 & SHL3 & SBU3 & SBUN
                 & GB3 & GBFA & SHT3 & T8 & INST3 & NRES2 & SST2 & MTX2 & GST2 & PA2 & PAJ2 & LHDR3 & HDR32 & SHA2 & TST3 & DEP3).
    remember (if nch =? nres then nres + 16384 else nres) as nres' eqn:EN.
    remember (if nch =? nres then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L) as L' eqn:EL.
    assert (NB : nres <= nres' <= nres + 16384) by (destruct (nch =? nres); (first [clear - EN; lia | lia])).
    set (W := (wz (sh a), wz (msz / 8))) in *.
    unfold as_W, depot_W in MU. unfold aframe in FR3.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof SBR as R; destruct R as [SBR']. pose proof SOR as R; destruct R as [SOR'].
    pose proof PLCD0 as R; destruct R as [PLCD']. pose proof PAR as PAR'.
    unfold AHI_LO, AIMG_TOP, kPtrArrayReserve, kSpaceSize in RNG', TPR', SBR', PLCD', PAR', AHI. acb.
    pose proof (aapp_env _ _ AHI ltac:(clear - G1 G3 SZ; lia)) as [ALO _]. pose proof (aapp_lit _ _ AHI) as ALIT.   (* [comment removed for export] *)
    change (2^47) with 140737488355328 in SOR'.
    assert (MQ : exists mq, msz = 4096 * mq) by (clear - DMSZ; try acb; exists (round_up needed 4096 / 4096 + 1); rewrite DMSZ; unfold round_up; Z.div_mod_to_equations; lia).
    destruct MQ as [mq MQ].
    assert (PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX))).
    { destruct PLC0 as [(P0 & _ & _)]. constructor. split; [exact P0|]. split.
      - pose proof (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) TMAPS). (first [clear - H; lia | lia]).
      - pose proof (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) CMAPS). (first [clear - H; lia | lia]). }
    assert (SBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a)).
    { constructor. unfold kSpaceSize. apply (free_vs_mapped _ _ a msz sb 137438953472 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) SBMAPS). }
    assert (PLCP : hidden ((a + msz <= pa \/ pa + 8388608 <= a) /\ (pa + 8388608 <= TH \/ TH + 4096 <= pa) /\ (pa + 8388608 <= CTX \/ CTX + 160 <= pa))).
    { destruct PLC0 as [(_ & P1 & P2)]. constructor. split; [| unfold kPtrArrayReserve in P1, P2; split; [exact P1| exact P2]].
      apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; lia) PMAPS). }
    assert (PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (a + msz <= d_nb d \/ d_nb d + 16 * 65536 <= a) /\ (a + msz <= d_sb d \/ d_sb d + 8 * 131072 <= a)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072))).
    { destruct PLCD' as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8). constructor. unfold AHI_LO. split; [exact D1|]. split; [exact D2|]. split; [|split; [| exact (conj D3 (conj D4 (conj D7 D8)))]].
      - apply (free_vs_mapped _ _ a msz (d_nb d) (16 * 65536) FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - D7; aunf; lia) ltac:(hci; clear - D7; aunf; lia) ltac:(hci; lia) DNMAPS).
      - apply (free_vs_mapped _ _ a msz (d_sb d) (8 * 131072) FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - D8; aunf; lia) ltac:(hci; clear - D8; aunf; lia) ltac:(hci; lia) DSMAPS). }
    assert (PLCDP : hidden ((pa + 8388608 <= d_nb d \/ d_nb d + 16 * 65536 <= pa) /\ (pa + 8388608 <= d_sb d \/ d_sb d + 8 * 131072 <= pa))).
    { destruct PLCD' as (_ & _ & _ & _ & D5 & D6 & _). constructor. exact (conj D5 D6). }
    assert (DBND : 12599296 <= d_nb d /\ 12599296 <= d_sb d) by (clear - PLCD'; try acb; aunf; lia).   (* [comment removed for export] *)
    assert (BND : 2148314624 <= sh a /\ sh a + msz / 8 <= 17594332446720 /\ sh (a + 4096) = sh a + 512 /\ sh (a + msz) = sh a + 512 * mq /\ msz / 8 = 512 * mq
                  /\ sh (a + 6144) = sh a + 768 /\ sh (a + 4096 + needed) = sh a + 512 + nd8).
    { unfold sh, ASHADOW_BASE. rewrite MQ. assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); Z.div_mod_to_equations; (first [clear - H AL; lia | lia])).
      destruct AQ as [aq AQ]. rewrite AQ, ND8. clear - ALO CE MQ AQ G3 SZ ND8; try acb. Z.div_mod_to_equations. lia. }
    destruct BND as (BND1 & BND2 & SH1 & SH2 & SH3 & SH4 & SH5).
    assert (ABND : 12599296 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil) by (clear - ALO CE; try acb; lia).   (* [comment removed for export] *)
    region_sides. name_bands.
    unfold AINST in *. change (6976152 + 64) with 6976216 in *. change (6976152 + 112) with 6976264 in *. change (6976152 + 136) with 6976288 in *.
    change (6976152 + 680) with 6976832 in *. change (6976152 + 688) with 6976840 in *. change (6976152 + 728) with 6976880 in *.
    assert (LENW' : Z.of_nat (length (wlist (chunks ++ [a]))) = nch + 1) by (unfold wlist; rewrite length_map, length_app; cbn [length]; unfold zlen in LEN; lia).
    assert (SHB : 2148314624 <= sh (a + 4096) /\ sh (a + msz) <= 17594332446720 /\ 2148314624 <= sh (a + 6144)) by (first [clear - SH4 SH3 SH2 SH1 BND2 BND1; lia | lia]).
    region_table.
    pose proof MO2 as MO; unfold la_model in MO. cbv beta iota zeta in MO.
    destruct MO as (NV2 & VM2 & VR2 & VL2 & VB2 & VK2 & VS2 & VA2 & EAG2).
    assert (U8 : (a + 6144) mod 8 = 0 /\ (8 * q8) mod 8 = 0 /\ 8 * q8 / 8 = q8) by (clear - AL; try acb; Z.div_mod_to_equations; lia).
    destruct U8 as (U8 & Q8M & Q8D).
    assert (Q8S : size / 8 = q8) by (clear - DSZ R8; try acb; Z.div_mod_to_equations; lia).
    pose proof AEN3 as E3. open_env E3.
    assert (HI3 : lo + 64 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128))) by (rewrite unsigned_lit by (first [clear - RXb0 SOR' LO' HI; lia | lia]); lia).
    assert (ST3' : stk asegs m3 lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)))) by (rewrite unsigned_lit by (first [clear - RXb0 SOR' LO' HI; lia | lia]); exact ST3).
    assert (AR14 : (AHI_LO <= a + 6144 \/ 0 <= a + 6144 /\ a + 6144 + 8 * q8 <= ALOWSH_LO) /\ 1 <= q8 /\ a + 6144 + 8 * q8 <= aceil /\ (a + 6144) mod 8 = 0)
      by (unfold AHI_LO, ALOWSH_LO; acb; clear - ALO ALIT CE G1 G2 G3 G5 G6 SZ U8; try acb; lia).   (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L' (W :: S) Zr _ msF3 _ mo3 Q OK3 VIS3).
    { apply (poison_shadow_specK _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 lo (a + 6144) (sh (a + 6144)) q8 0 sbsU
               MI3 ST3' LO HI3 eq_refl eq_refl eq_refl eq_refl AR14 ltac:(hci; clear; lia) SBU3 SBUN Ecan Egot Eshb Ehme Ethresh Erms). }
    cbv beta. intros msF4 mo4 OK4 SBM4 HS4 P4.
    destruct P4 as (z0 & z1 & z2 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & m4 & VIS4 & MU4 & WM4 & MI4 & ST4 & ZER4).
    rewrite unsigned_lit in MU4, ST4 by (first [clear - RXb0 SOR' LO' HI; lia | lia]).
    replace (ret_pc (wz 1667764)) with (Z_to_bv 64 1667764) in VIS4 by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Eso Etr.
    clear ST3'.   (* [comment removed for export] *)
    aenv_at AEN3 MU4 WM4 AEN4. clear AEN3 ST3 SBU3.
    eapply (DEPOT_transport asegs _ m3 m4) in DEP3; [| exact MU4 | exact WM4 | solve_depot_avoid].
    transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4.
    (* [comment removed for export] *)
    assert (SHL4 : u8arr asegs m4 (sh (a + 4096)) (repeat (b8 250) 256 ++ repeat (b8 0) (Z.to_nat q8))).
    { apply u8arr_app. split; [exact SHL3|]. rewrite repeat_length. replace (sh (a + 4096) + Z.of_nat 256) with (sh (a + 6144)) by (first [clear - SH4 SH1; lia | lia]). exact ZER4. }
    clear SHL3 ZER4.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L' (W :: S) Zr _ msF4 _ mo4 Q OK4 VIS4).
    { eapply (alloc_sec_t2 ra sp gp tp F fc lo size SO T rest TSD CTX TH sb s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a msz needed q8 r8 id);
        try eassumption; try (unfold aframe; eassumption).
      + constructor. exact (conj DNEED (conj DMSZ DSZ)).
      + first [split; [exact AHI| split; [exact CE| exact AL]] | unfold AHI_LO; acb; lia]. }
    cbv beta. intros msF5 mo5 OK5 SBM5 HS5 P5.
    destruct P5 as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & b1 & m5
                    & VIS5 & MU5 & WM5 & MI5 & ST5 & CH5 & B1OK & MAG5 & LRZ5 & FILL5 & USR5 & SHD5 & TST5).
    clear CHDR3 LRZ3 USR3 GB3 SHT3 TST3 ST4 FR3.
    aenv_at AEN4 MU5 WM5 AEN5. clear AEN4.
    eapply (DEPOT_transport asegs _ m4 m5) in DEP3; [| exact MU5 | exact WM5 | solve_depot_avoid].
    transport_after_call asegs m4 m5 MU5 WM5. clear MU5 WM5.
    (* [comment removed for export] *)
    apply K. unfold POST, alloc_sec_sr_post.
    exists a, w0, w1, w2, w11, w12, w13, w14, w15, w16, w17, w3, w4, w5, w6, b1, m5.
    rewrite <- EN. rewrite <- EL. cbv beta iota zeta. fold W.
    split; [exact AHI|]. split; [acb; lia|]. split; [lia|]. split; [exact FREE|].
    split; [exact OK5|]. split; [exact VIS5|].
    split.
    { (* [comment removed for export] *)
      apply (as_model_mat _ _ _ _ _ _ mo3 _); [| exact (same_but_materialized_trans _ _ _ SBM4 SBM5)].
      unfold as_model. repeat (split; [assumption|]). exact EAG2. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI5|].
    unfold AINST. change (6976152 + 64) with 6976216. change (6976152 + 112) with 6976264. change (6976152 + 136) with 6976288.
    change (6976152 + 680) with 6976832. change (6976152 + 688) with 6976840. change (6976152 + 728) with 6976880.
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End AllocSec.
