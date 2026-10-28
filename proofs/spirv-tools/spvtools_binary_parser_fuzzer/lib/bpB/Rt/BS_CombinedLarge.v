(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BAllocSim BMmapSim BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit B_memset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_Leaves BW_PoisonShadow BW_MmapFixed BW_SecMmap BidBits BecMsb BW_Combined BW_AllocBase BW_LargeAlloc1 BW_LargeAlloc2 BW_LargeAlloc3 BW_LargeAlloc4 BW_CombinedLarge BW_MallocBase BecLazy BS_LargeAlloc BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition combined_large_post (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo size msz size8 TSD CTX TH pa nres nch : Z) (chunks : list Z)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (a : Z) (t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    let committed := nch =? nres in
    let nres' := if committed then nres + 16384 else nres in
    let L' := if committed then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L in
    let W := (wz (sh a), wz (msz / 8)) in
       aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0
    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true
    /\ lzok asegs L' (W :: S) Zr (mkCfg msF' mo')
    /\ restrict L' (W :: S) msF'
       = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a + 4096)) (wz 9) a2 (wz 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ la_model mo a msz pa nres committed mo'
    /\ munch (la_W lo sp a msz pa nch nres TH) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ SENV tp TSD CTX TH m'
    /\ rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' (AINST + 112) [C8 (wz nres'); C8 (wz (nch + 1)); C8 (wz 0)]
    /\ stk asegs m' (AINST + 136) (AINST + 680) /\ rw_cells asegs m' (AINST + 680) [C8 (wz 0)] /\ stk asegs m' (AINST + 688) (AINST + 728)
    /\ u64arr asegs m' pa (wlist (chunks ++ [a])) /\ stk asegs m' (pa + 8 * (nch + 1)) (pa + 8 * nres')
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz size); C8 (wz nch)] /\ stk asegs m' (a + 32) (a + 4096)
    /\ stk asegs m' (a + 4096) (a + msz)
    /\ u8arr asegs m' (sh a) (repeat (b8 0xfa) 512) /\ stk asegs m' (sh a + 512) (sh a + 512 + size8)
    /\ u8arr asegs m' (sh (a + 4096 + size)) (repeat (b8 0xfa) (Z.to_nat ((msz - 4096 - size) / 8)))
    /\ stk asegs m' (TH + 2800) (TH + 3168).

Section CombinedLarge.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size msz size8 TSD CTX TH pa nres nch : Z) (chunks : list Z).
  Hypothesis DEFS : hidden (msz = round_up size 4096 + 4096).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 512 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0). Hypothesis SPH : bv_unsigned sp + 16 <= 2^47.
  Hypothesis Ha0 : a0 = wz AINST. Hypothesis Ha2 : a2 = wz size. Hypothesis Ha3 : a3 = wz 8.
  Hypothesis SZ : 0x10000 < size /\ size <= 2^41 /\ size = 8 * size8.
  Hypothesis TPR : hidden (6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6762288 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC0 : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20. Hypothesis NRQ : exists q, nres = 512 * q.
  Hypothesis LEN : zlen chunks = nch.
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis INST64 : rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m (AINST + 112) [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk asegs m (AINST + 136) (AINST + 680).
  Hypothesis MTX : rw_cells asegs m (AINST + 680) [C8 (wz 0)].
  Hypothesis GST : stk asegs m (AINST + 688) (AINST + 728).
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis PAJ : stk asegs m (pa + 8 * nch) (pa + 8 * nres).
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis BUD : eager_used mo + pages_total S * page_size + msz + (msz / 32768 + 2) * page_size + 0x20000 <= vm_limit (m_vmmaps mo).
  Hypothesis GAP : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true.

  Hypothesis IMGR : forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved (m_vmmaps mo)) = true.
  Hypothesis SHLAND : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.

  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.
  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  Hypothesis TMAPS : forall x : word, TH <= bv_unsigned x < TH + 4096 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis CMAPS : forall x : word, CTX <= bv_unsigned x < CTX + 160 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PMAPS : forall x : word, pa <= bv_unsigned x < pa + kPtrArrayReserve -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PAMC : nch = nres -> map_contains (vm_maps (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PARF : nch = nres -> region_free (vm_reserved (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PAZR : nch = nres -> forall x : word, pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 0x20000 -> in_rangesb x Zr = false.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x96bf4) fc None m (seg_rom asegs).

  Let PAE : 7241728 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.
  Let POST := combined_large_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size msz size8 TSD CTX TH pa nres nch chunks.

  Theorem combined_large_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof SPA as R; destruct R as [SPA'].

    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply combined_large_seg1; try eassumption; lia. }
    cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR'].
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    unfold AHI_LO, AIMG_TOP, kPtrArrayReserve in RNG', TPR'. pose proof PAR as PAR'. unfold AHI_LO, kPtrArrayReserve in PAR'.
    acb.
    unfold AINST in *. change (1628632 + 64) with 1628696 in *. change (1628632 + 112) with 1628744 in *. change (1628632 + 136) with 1628768 in *.
    change (1628632 + 680) with 1629312 in *. change (1628632 + 688) with 1629320 in *. change (1628632 + 728) with 1629360 in *.
    region_table.
    senv_at ENV MU1 WM1 ENV1.
    transport_after_call asegs m m1 MU1 WM1.

    eapply (large_alloc_sreach L S Zr msF1 mo1 Q _ (Z_to_bv 64 (bv_unsigned sp + -48)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
              lo size msz size8 TSD CTX TH pa nres nch chunks DEFS MI1); rewrite ?unsigned_lit by lia;
      rewrite ?(same_but_materialized_vmmaps _ _ SBM1), ?(same_but_materialized_eager _ _ SBM1); try eassumption; try reflexivity; try (first [lia0 | qlia]).
    { constructor. replace (bv_unsigned sp + -48) with (bv_unsigned sp + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact SPA'. }
    { intros x Hx. apply WM1. apply SVIS. exact Hx. }
    { rewrite Ha2, Ha3. exact VIS1. }
    cbv beta. intros msF2 mo2 P2.
    destruct P2 as (a & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & AHI & CE & AL & FREE & OK2 & VIS2 & MO2
                    & MU2 & WM2 & MI2 & ST2 & ENV2 & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & PAJ2 & HDR2 & HDR32 & USR2 & SHA2 & SHM2 & SHT2 & TST2).
    unfold la_W in MU2. rewrite unsigned_lit in MU2, ST2 by lia.
    remember (if nch =? nres then nres + 16384 else nres) as nres' eqn:EN.
    assert (NB : nres <= nres' <= nres + 16384) by (destruct (nch =? nres); lia).
    replace (ret_pc (wz 617628)) with (Z_to_bv 64 617628) in VIS2 by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    pose proof DEFS as D; destruct D as [DMSZ].
    assert (MSZ : size + 4096 <= msz /\ msz < size + 8192 /\ exists q, msz = 4096 * q).
    { rewrite DMSZ. unfold round_up. split; [|split]; try (Z.div_mod_to_equations; lia). exists ((size + 4096 - 1) / 4096 + 1). lia. }
    destruct MSZ as (MSZ1 & MSZ2 & mq & MQ).
    pose proof (aapp_env _ _ AHI ltac:(clear - SZ MSZ1; lia)) as [ALO _]. acb.
    assert (BND : 7241728 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil /\ 2148356096 <= sh a /\ sh a + msz / 8 <= 17594332446720).
    { unfold sh, ASHADOW_BASE. rewrite MQ. assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); Z.div_mod_to_equations; lia).
      destruct AQ as [aq AQ]. rewrite AQ. clear - ALO CE MQ AQ MSZ1 SZ; try acb. Z.div_mod_to_equations. lia. }
    region_sides. name_bands.
    unfold AINST in MU2. change (1628632 + 112) with 1628744 in MU2. change (1628632 + 728) with 1629360 in MU2.
    region_table.
    pose proof (munch_refl (la_W lo sp a msz pa nch nres TH) m) as MU. unfold la_W, AINST in MU.
    change (1628632 + 112) with 1628744 in MU. change (1628632 + 728) with 1629360 in MU.
    pose proof (wmono_refl asegs m) as WM.
    clear ENV INST64 NRES SST MTX GST TST PA PAJ ST1 ENV1.
    transport_after_call asegs m m1 MU1 WM1. clear MU1 WM1.
    transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.

    eapply (evt_sreach_lazy_at asegs _ (_ :: S) Zr _ msF2 _ mo2 Q OK2 VIS2).
    { eapply combined_large_seg2; try eassumption; lia. }
    cbv beta. intros msF3 mo3 OK3 SBM3 HS3 P3. destruct P3 as (m3 & VIS3 & MU3 & WM3 & MI3 & ST3).
    clear ST2 FR1.
    assert (SHB7 : sh (a + 4096 + size) = sh a + 512 + size8).
    { unfold sh, ASHADOW_BASE. assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); Z.div_mod_to_equations; lia).
      destruct AQ as [aq AQ]. rewrite AQ. clear - AQ SZ; try acb. Z.div_mod_to_equations. lia. }
    assert (LENW' : Z.of_nat (length (wlist (chunks ++ [a]))) = nch + 1) by (unfold wlist; rewrite length_map, length_app; cbn [length]; unfold zlen in LEN; lia).
    unfold AINST in INST2, NRES2, SST2, MTX2, GST2. change (1628632 + 64) with 1628696 in INST2. change (1628632 + 112) with 1628744 in NRES2.
    change (1628632 + 136) with 1628768 in SST2. change (1628632 + 680) with 1629312 in SST2, MTX2. change (1628632 + 688) with 1629320 in GST2.
    change (1628632 + 728) with 1629360 in GST2.

    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) in SHT2 by (clear - SZ MQ; Z.div_mod_to_equations; lia).
    senv_at ENV2 MU3 WM3 ENV3. clear ENV2.
    transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3.
    apply K. unfold POST, combined_large_post.
    exists a, u0, u1, u2, v2, v4, v5, v6, v7, u3, u4, u5, u6, m3.
    split; [exact AHI|]. split; [acb; lia|]. split; [lia|].
    split; [rewrite <- (same_but_materialized_vmmaps _ _ SBM1); exact FREE|].
    split; [exact OK3|]. split; [exact VIS3|].
    split.
    { apply (la_model_mat _ _ _ _ _ _ mo2 _); [| exact SBM3].
      destruct MO2 as (NV & REST). split.
      - eapply nonvm_same_trans; [apply (nonvm_same_mat _ _ SBM1)| exact NV].
      - rewrite (same_but_materialized_vmmaps _ _ SBM1), (same_but_materialized_eager _ _ SBM1) in REST. exact REST. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. rewrite <- EN.
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) by (clear - SZ MQ; Z.div_mod_to_equations; lia).
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End CombinedLarge.

End HCW.

