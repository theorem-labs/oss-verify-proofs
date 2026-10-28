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
     SecLazy AS_LargeAlloc AS_CombinedLarge AW_AllocSec1 AW_AllocSec2 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Lemma aenv_transport : forall tp TSD CTX TH sb SO T rest m m' W,
  AENV tp TSD CTX TH sb SO T rest m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W 6988128 8 -> disjoint_from W (bv_unsigned tp + -88) 8 -> disjoint_from W TSD 8 -> disjoint_from W (CTX + 152) 8 ->
  disjoint_from W (bv_unsigned tp + 32) 4 -> disjoint_from W 0x5e8490 8 -> disjoint_from W TH 8 -> disjoint_from W (CTX + 8) 4 ->
  disjoint_from W 6993368 1 -> disjoint_from W 7523168 3 -> disjoint_from W 6988124 1 -> disjoint_from W 6191096 120 ->
  disjoint_from W 6990072 8 -> disjoint_from W 6993376 24 -> disjoint_from W 7586976 8 -> disjoint_from W 6204016 8 ->
  disjoint_from W 6979876 12 -> disjoint_from W 6979917 1 -> disjoint_from W 7586752 80 -> disjoint_from W 6976184 8 ->
  disjoint_from W 6979768 16 -> disjoint_from W SO 16 -> disjoint_from W (SO + 16) (8 * Z.of_nat (length (map wz T ++ rest))) ->
  AENV tp TSD CTX TH sb SO T rest m'.
Proof.
  intros until W. intros E MU WM; intros; destruct E; constructor;
    try (eapply rw_cells_transport; [eassumption | exact MU | exact WM | ];
         unfold AGOT_VALS; cbn [cells_size csize length map repeat Nat.add Nat.mul]; assumption).
  eapply u64arr_transport; [eassumption | exact MU | exact WM | assumption].
Qed.

End HCW.

Ltac aenv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with AENV ?tp ?TSD ?CTX ?TH ?sb ?SO ?T ?rest m =>
      region_table; region_hull_memo W;   (* [comment removed for export] *)
      assert (E' : AENV tp TSD CTX TH sb SO T rest m');
      [ apply (aenv_transport tp TSD CTX TH sb SO T rest m m' W E MU WM); cbn [disjoint_from]; simpl_sizes; rewrite ?u32s_length, ?u64s_length, ?upd_length; region_decide | ]   (* [comment removed for export] *)
    end end.

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition as_W (lo : Z) (sp : word) (a msz pa nch nres TH : Z) (d : depot) : list ivl :=
  (lo, bv_unsigned sp) :: (a, a + msz) :: (sh a, sh a + msz / 8) :: (pa + 8 * nch, pa + 8 * (nres + 16384)) :: (AINST + 112, AINST + 728)
  :: (TH + 2800, TH + 3168) :: depot_W d.

(* [comment removed for export] *)
Definition as_model (mo : Model) (a msz pa nres : Z) (committed : bool) (mo' : Model) : Prop :=
  let h := m_vmmaps mo in let h' := m_vmmaps mo' in
  let na1 := if committed then maps_subtract (vm_noaccess h) (pa + 8 * nres) (pa + 8 * nres + 0x20000) else vm_noaccess h in
     nonvm_same mo mo'
  /\ vm_maps h' = (wz a, wz msz) :: vm_maps h
  /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h
  /\ vm_brk h' = vm_brk h /\ vm_start_brk h' = vm_start_brk h
  /\ vm_noaccess h' = na1
  /\ eager_used mo' <= eager_used mo + msz + (if committed then 0x20000 else 0).

Lemma as_model_mat : forall mo a msz pa nres c mo1 mo2,
  as_model mo a msz pa nres c mo1 -> same_but_materialized mo1 mo2 -> as_model mo a msz pa nres c mo2.
Proof.
  intros until mo2. intros (NV & REST) SB. unfold as_model.
  rewrite (same_but_materialized_vmmaps _ _ SB), (same_but_materialized_eager _ _ SB).
  split; [| exact REST]. eapply nonvm_same_trans; [exact NV| apply nonvm_same_mat; exact SB].
Qed.

Definition alloc_sec_sr_post (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo size needed msz TSD CTX TH sb SO pa nres nch id nT : Z) (chunks T : list Z) (rest : list word) (d : depot)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (a : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (b1 : Z) (m' : mem),
    let committed := nch =? nres in
    let nres' := if committed then nres + 16384 else nres in
    let L' := if committed then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L in
    let W := (wz (sh a), wz (msz / 8)) in
       aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0    (* [comment removed for export] *)
    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true
    /\ lzok asegs L' (W :: S) Zr (mkCfg msF' mo')
    /\ restrict L' (W :: S) msF'
       = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a + 6144)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_model mo a msz pa nres committed mo'
    /\ munch (as_W lo sp a msz pa nch nres TH d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AENV tp TSD CTX TH sb SO T rest m'
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' (AINST + 112) [C8 (wz nres'); C8 (wz (nch + 1)); C8 (wz 0)]
    /\ stk asegs m' (AINST + 136) (AINST + 680) /\ rw_cells asegs m' (AINST + 680) [C8 (wz 0)] /\ stk asegs m' (AINST + 688) (AINST + 728)
    /\ u64arr asegs m' pa (wlist (chunks ++ [a])) /\ stk asegs m' (pa + 8 * (nch + 1)) (pa + 8 * nres')
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz needed); C8 (wz nch)] /\ stk asegs m' (a + 32) (a + 4096)
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (a + 6128) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)] /\ b1_ok b1
    /\ rw_cells asegs m' (a + 4096) [C8 (wz kAllocBegMagic); C8 (wz (a + 6128))] /\ stk asegs m' (a + 4112) (a + 6128)
    /\ u8arr asegs m' (a + 6144) (repeat (b8 0xbe) 4096)
    /\ stk asegs m' (a + 6144 + 4096) (a + msz)
    /\ u8arr asegs m' (sh a) (repeat (b8 0xfa) 512) /\ u8arr asegs m' (sh (a + 4096)) (sec_shadow size msz)
    (* [comment removed for export] *)
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs (d_put d (depot_hash T) nT) m'.

(* [comment removed for export] *)
Definition alloc_sec_mid (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo size needed msz TSD CTX TH sb SO pa nres nch q8 r8 id nT : Z) (chunks T : list Z) (rest : list word) (d : depot)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (a : Z) (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (j8 sbsU : list byte) (ob0 gb : byte) (hb1 t8 : Z) (m' : mem),
    let committed := nch =? nres in
    let nres' := if committed then nres + 16384 else nres in
    let L' := if committed then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L in
    let W := (wz (sh a), wz (msz / 8)) in
       aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0    (* [comment removed for export] *)
    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true
    /\ lzok asegs L' (W :: S) Zr (mkCfg msF' mo')
    /\ restrict L' (W :: S) msF'
       = MS (mkR (wz 0x1972b4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp y5 y6 y7 (wz (msz - 4096)) (wz size) (wz (a + 6144)) (wz (8 * q8)) (wz 0) y13 y14 y15 y16 y17
                  (wz (a + 4096)) (wz needed) (wz (a + 6144)) (wz (a + 6128)) (wz (8 * q8)) (wz SO) (wz 0) (wz (a + 6144 + size + 7)) (wz TH) (wz 1) y28 y29 y30 y31)
            F (Z_to_bv 64 0x1c06e0) fc None m' (seg_rom asegs)
    /\ la_model mo a msz pa nres committed mo'
    /\ munch (as_W lo sp a msz pa nch nres TH d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ AENV tp TSD CTX TH sb SO T rest m'
    /\ aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m' j8 /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m' (a + 6128) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); C8 (wz id)] /\ 0 <= hb1 < 256 /\ b1_ok (Z.land hb1 243)
    /\ stk asegs m' (a + 4096) (a + 6128) /\ stk asegs m' (a + 6144) (a + msz)
    /\ u8arr asegs m' (sh (a + 4096)) (repeat (b8 0xfa) 256)
    /\ u8arr asegs m' (sh (a + 6144)) sbsU /\ Z.of_nat (length sbsU) = q8
    /\ rw_cells asegs m' (sh (a + 6144) + q8) [C1 gb] /\ (r8 = 0 -> gb = b8 0xfa)
    /\ u8arr asegs m' (sh (a + 6144) + q8 + 1) (repeat (b8 0xfa) (Z.to_nat t8)) /\ t8 = sh (a + msz) - (sh (a + 6144) + q8 + 1)
    /\ rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' (AINST + 112) [C8 (wz nres'); C8 (wz (nch + 1)); C8 (wz 0)]
    /\ stk asegs m' (AINST + 136) (AINST + 680) /\ rw_cells asegs m' (AINST + 680) [C8 (wz 0)] /\ stk asegs m' (AINST + 688) (AINST + 728)
    /\ u64arr asegs m' pa (wlist (chunks ++ [a])) /\ stk asegs m' (pa + 8 * (nch + 1)) (pa + 8 * nres')
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz needed); C8 (wz nch)] /\ stk asegs m' (a + 32) (a + 4096)
    /\ u8arr asegs m' (sh a) (repeat (b8 0xfa) 512)
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs (d_put d (depot_hash T) nT) m'.
End HCW2.

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
  Lemma alloc_sec_head :
    (forall msF' mo', MID msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
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
    (* [comment removed for export] *)
    eapply (combined_large_sreach L S Zr msF mo Q _ (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              lo needed msz nd8 TSD CTX TH pa nres nch chunks); rewrite ?unsigned_lit by (first [clear - ACEILB LO' SPR HI; lia | lia]); [idtac | exact MI | exact ST | exact LO' | idtac | idtac | idtac | idtac | idtac | idtac | idtac | exact TPR | exact RNG | exact PLC0 | exact PAR | exact NCH | exact NRQ | exact LEN | exact SEN | exact INST64 | exact NRES | exact SST | exact MTX | exact GST | exact TST | exact PA | exact PAJ | exact NW | exact NWA | exact NOV | exact BUD | exact GAP | exact IMGR | exact SHLAND | exact ATOP | exact ZRSH | exact SVIS | exact TMAPS | exact CMAPS | exact PMAPS | exact PAMC | exact PARF | exact PAZR | exact OK | exact VISE | idtac]; try reflexivity; try (first [lia0 | qlia]).   (* [comment removed for export] *)
    { constructor. exact DMSZ. }
    { constructor. replace (bv_unsigned sp + -128) with (bv_unsigned sp + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact SPA'. }
    cbv beta. intros msF2 mo2 P2.
    destruct P2 as (a & u0 & u1 & u2 & v2 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & AHI & CE & AL & FREE & OK2 & VIS2 & MO2
                    & MU2 & WM2 & MI2 & ST2 & ENV2 & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & PAJ2 & HDR2 & HDR32 & USR2 & SHA2 & SHM2 & SHT2 & TST2).
    unfold la_W in MU2. rewrite unsigned_lit in MU2, ST2 by (first [clear - ACEILB LO' SPR HI; lia | lia]).
    remember (if nch =? nres then nres + 16384 else nres) as nres' eqn:EN.
    remember (if nch =? nres then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L) as L' eqn:EL.
    assert (NB : nres <= nres' <= nres + 16384) by (destruct (nch =? nres); lia).
    replace (ret_pc (wz 1667228)) with (Z_to_bv 64 1667228) in VIS2 by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    pose proof (munch_refl (as_W lo sp a msz pa nch nres TH d) m) as MU. unfold as_W, depot_W, AINST in MU.
    change (6976152 + 112) with 6976264 in MU. change (6976152 + 728) with 6976880 in MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    unfold aframe in FR.
    eapply (DEPOT_transport asegs d m m2) in DEP; [| exact MU2 | exact WM2 | solve_depot_avoid].
    aenv_at AEN MU2 WM2 AEN2.
    clear SEN INST64 NRES SST MTX GST TST PA PAJ.
    transport_after_call asegs m m2 MU2 WM2. clear MU2 WM2.
    set (W := (wz (sh a), wz (msz / 8))) in *.
    replace (sh a + 512) with (sh (a + 4096)) in SHM2 by lia. replace (sh (a + 4096) + nd8) with (sh (a + 4096) + needed / 8) in SHM2 by (rewrite ND8; clear; Z.div_mod_to_equations; lia).
    replace (sh (a + 4096 + needed)) with (sh (a + 4096) + needed / 8) in SHT2 by (rewrite SH5, ND8, SH1; clear; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L' (W :: S) Zr _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (alloc_sec_t1 ra sp gp tp F fc lo size SO T rest d TSD CTX TH sb pa nch s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a msz needed q8 r8 nT id);
        try eassumption; try (unfold aframe, AINST; first [eassumption | change (6976152 + 64) with 6976216; eassumption]).
      all: try (split; [exact AHI| split; [exact CE| exact AL]]); try (split; [exact AHI| exact CE]); unfold AHI_LO; acb; lia. }
    cbv beta. intros msF3 mo3 OK3 SBM3 HS3 P3.
    destruct P3 as (y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & j8' & sbsU & ob0 & gb & hb1 & t8 & m3
                    & VIS3 & MU3 & WM3 & MI3 & AEN3 & FR3 & ST3 & CHDR3 & HB1R & HB1M & LRZ3 & USR3 & SHL3 & SBU3 & SBUN & GB3 & GBFA & SHT3 & T8 & INST3 & LHDR3 & TST3 & DEP3).
    unfold depot_W in MU3. unfold AINST in INST3. change (6976152 + 64) with 6976216 in INST3. unfold aframe in FR3.
    clear AEN2 ENV2 FR ST2 INST2 HDR2 USR2 SHM2 SHT2 TST2 DEP.
    transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3.
    apply K. unfold MID, alloc_sec_mid. rewrite <- EN, <- EL. fold W.
    exists a, y5, y6, y7, y13, y14, y15, y16, y17, y28, y29, y30, y31, j8', sbsU, ob0, gb, hb1, t8, m3.
    split; [exact AHI|]. split; [acb; lia|]. split; [lia|]. split; [exact FREE|].
    split; [exact OK3|]. split; [exact VIS3|].
    split; [exact (la_model_mat _ _ _ _ _ _ _ _ MO2 SBM3)|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|].
    unfold AINST, aframe. change (6976152 + 64) with 6976216. change (6976152 + 112) with 6976264. change (6976152 + 136) with 6976288.
    change (6976152 + 680) with 6976832. change (6976152 + 688) with 6976840. change (6976152 + 728) with 6976880.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: clear - HB1R; try acb; lia.
  Qed.
End AllocSec.

