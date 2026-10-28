(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.As Require Import AW_Leaves AW_PoisonShadow AW_MmapFixed AW_SecMmap CidBits SecMsb AW_Combined AW_AllocBase
     AW_LargeAlloc1 AW_LargeAlloc2 AW_LargeAlloc3 AW_LargeAlloc4 AW_CombinedLarge AW_MallocBase SecLazy AllocTacX. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition la_W (lo : Z) (sp : word) (a msz pa nch nres TH : Z) : list ivl :=
  [(lo, bv_unsigned sp); (a, a + msz); (sh a, sh a + msz / 8); (pa + 8 * nch, pa + 8 * (nres + 16384)); (AINST + 112, AINST + 728); (TH + 2800, TH + 3168)]%Z.

(* [comment removed for export] *)
Definition la_model (mo : Model) (a msz pa nres : Z) (committed : bool) (mo' : Model) : Prop :=
  let h := m_vmmaps mo in let h' := m_vmmaps mo' in
     nonvm_same mo mo'
  /\ vm_maps h' = (wz a, wz msz) :: vm_maps h
  /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h
  /\ vm_brk h' = vm_brk h /\ vm_start_brk h' = vm_start_brk h
  /\ vm_noaccess h' = (if committed then maps_subtract (vm_noaccess h) (pa + 8 * nres) (pa + 8 * nres + 0x20000) else vm_noaccess h)
  /\ eager_used mo' <= eager_used mo + msz + (if committed then 0x20000 else 0).

Lemma la_model_mat : forall mo a msz pa nres c mo1 mo2,
  la_model mo a msz pa nres c mo1 -> same_but_materialized mo1 mo2 -> la_model mo a msz pa nres c mo2.
Proof.
  intros mo a msz pa nres c mo1 mo2 (NV & REST) SB. unfold la_model.
  rewrite (same_but_materialized_vmmaps _ _ SB), (same_but_materialized_eager _ _ SB).
  split; [| exact REST]. eapply nonvm_same_trans; [exact NV| apply nonvm_same_mat; exact SB].
Qed.

(* [comment removed for export] *)
Definition la_mid (L S Zr : list (word * word)) (mo : Model) (sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo size msz size8 TSD CTX TH pa nres nch : Z) (chunks : list Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra stat : word)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (a : Z) (t0 t1 t2 a1 a2 a5 a6 a7 t3 t4 t5 t6 : word) (j8 : list byte) (m' : mem),
    let W := (wz (sh a), wz (msz / 8)) in
       aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0    (* [comment removed for export] *)
    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true
    /\ lzok asegs L (W :: S) Zr (mkCfg msF' mo')
    /\ restrict L (W :: S) msF'
       = MS (mkR (wz 0x1a0b34) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2
                 stat (wz (AINST + 64)) (wz (a + 4096)) a1 a2 (wz nch) (wz nres) a5 a6 a7
                 (wz msz) (wz (clzbits msz)) (wz a) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1a0c6c) fc None m' (seg_rom asegs)
    /\ la_model mo a msz pa nres false mo'
    /\ munch (la_W lo sp a msz pa nch nres TH) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ laframe sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra m' j8
    /\ u8arr asegs m' (sh a) (repeat (b8 0xfa) 512)
    /\ stk asegs m' (sh a + 512) (sh a + 512 + size8)
    /\ u8arr asegs m' (sh (a + 4096 + size)) (repeat (b8 0xfa) (Z.to_nat ((msz - 4096 - size) / 8)))
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz size)]
    /\ stk asegs m' (a + 24) (a + 4096)
    /\ stk asegs m' (a + 4096) (a + msz)
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m' (AINST + 680) [C4 (wz 1); C4 (wz 0)]
    /\ SENV tp TSD CTX TH m'
    /\ rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' (AINST + 112) [C8 (wz nres); C8 (wz nch); C8 (wz 0)]
    /\ stk asegs m' (AINST + 136) (AINST + 680)
    /\ stk asegs m' (AINST + 688) (AINST + 728)
    /\ u64arr asegs m' pa (wlist chunks)
    /\ stk asegs m' (pa + 8 * nch) (pa + 8 * nres).

(* [comment removed for export] *)
Lemma cb8_word : forall m A bs cs, rw_cells asegs m A (CB 8 bs :: cs) -> exists w, rw_cells asegs m A (C8 w :: cs).
Proof.
  intros m A bs cs R. assert (L : length bs = 8%nat) by (destruct R as [[[L _] _] _]; exact L).
  destruct (le8_surj bs L) as [w Hw]. exists w. destruct R as [[[_ W] B] R']. refine (conj (conj (conj I W) _) R').
  cbn [cells_bytes cbytes] in *. rewrite Hw. exact B.
Qed.
End HCW.

(* [comment removed for export] *)
Section GrantBand.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Lemma grant_aapp_of : forall (res maps : list (word * word)) (a : word) (n : Z),
    (forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x res = true) ->
    (forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x maps = true) ->
    bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + n <= aceil -> 0xF000 < n ->
    region_free (res ++ maps) a (wz n) = true -> aapp (bv_unsigned a) n.
  Proof.
    intros res maps a n IMGR SHLAND AL POS CE BIG FREE.
    pose proof aceil_facts as AF.
    assert (NW : bv_unsigned (wz n) = n) by (unfold wz; apply unsigned_lit; lia).
    assert (NOTIN : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + n ->
                     in_rangesb x res = false /\ in_rangesb x maps = false).
    { intros x Hx. pose proof (LazyNodes.region_free_not_in _ a (wz n) x FREE ltac:(rewrite NW; exact Hx)) as NI.
      rewrite in_rangesb_app in NI. apply Bool.orb_false_iff in NI. exact NI. }
    assert (A4096 : 4096 <= bv_unsigned a) by (unfold page_size in AL; Z.div_mod_to_equations; lia).
    destruct (Z.lt_ge_cases (bv_unsigned a) AIMG_TOP) as [LOWIMG|ABOVE].
    - exfalso. destruct (Z.lt_ge_cases (bv_unsigned a) AIMG_LO) as [BELOW|INIMG].
      + destruct (NOTIN (wz AIMG_LO)) as [R _]; [unfold wz; rewrite unsigned_lit by (unfold AIMG_LO; lia); unfold AIMG_LO in *; lia|].
        rewrite (IMGR (wz AIMG_LO)) in R; [discriminate|]. unfold wz; rewrite unsigned_lit by (unfold AIMG_LO; lia). unfold AIMG_LO, AIMG_TOP; lia.
      + destruct (NOTIN a) as [R _]; [lia|]. rewrite (IMGR a) in R; [discriminate| lia].
    - destruct (Z.le_gt_cases (bv_unsigned a + n) ALOWSH_LO) as [LO2|NOTLO].
      + left. split; assumption.
      + destruct (Z.lt_ge_cases (bv_unsigned a) AHI_LO) as [INLAND|HI].
        * exfalso. destruct (Z.lt_ge_cases (bv_unsigned a) ALOWSH_LO) as [B|B].
          -- destruct (NOTIN (wz ALOWSH_LO)) as [_ M]; [unfold wz; rewrite unsigned_lit by (unfold ALOWSH_LO; lia); lia|].
             rewrite (SHLAND (wz ALOWSH_LO)) in M; [discriminate|]. unfold wz; rewrite unsigned_lit by (unfold ALOWSH_LO; lia).
             unfold ALOWSH_LO, AHI_LO; lia.
          -- destruct (NOTIN a) as [_ M]; [lia|]. rewrite (SHLAND a) in M; [discriminate| lia].
        * right. split; assumption.
  Qed.
End GrantBand.
Section HCW.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition large_alloc_post (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo size msz size8 TSD CTX TH pa nres nch : Z) (chunks : list Z)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (a : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    let committed := nch =? nres in
    let nres' := if committed then nres + 16384 else nres in
    let L' := if committed then maps_subtract L (pa + 8 * nres) (pa + 8 * nres + 0x20000) else L in
    let W := (wz (sh a), wz (msz / 8)) in
       aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0    (* [comment removed for export] *)
    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true
    /\ lzok asegs L' (W :: S) Zr (mkCfg msF' mo')
    /\ restrict L' (W :: S) msF'
       = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a + 4096)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
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
End HCW.

Section LargeAlloc.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size msz size8 TSD CTX TH pa nres nch : Z) (chunks : list Z).
  Hypothesis DEFS : hidden (msz = round_up size 4096 + 4096).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 464 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0). Hypothesis SPH : bv_unsigned sp + 16 <= 2^47.
  Hypothesis Ha0 : a0 = wz (AINST + 64). Hypothesis Ha1 : a1 = wz (AINST + 688). Hypothesis Ha2 : a2 = wz size. Hypothesis Ha3 : a3 = wz 8.
  Hypothesis SZ : 0x10000 < size /\ size <= 2^41 /\ size = 8 * size8.
  Hypothesis TPR : hidden (11899400 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (11899312 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
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
  (* [comment removed for export] *)
  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  (* [comment removed for export] *)
  Hypothesis BUD : eager_used mo + pages_total S * page_size + msz + (msz / 32768 + 2) * page_size + 0x20000 <= vm_limit (m_vmmaps mo).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis GAP : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true.
  (* [comment removed for export] *)
  Hypothesis IMGR : forall x : word, AIMG_LO <= bv_unsigned x < AIMG_TOP -> in_rangesb x (vm_reserved (m_vmmaps mo)) = true.
  Hypothesis SHLAND : forall x : word, ALOWSH_LO <= bv_unsigned x < AHI_LO -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  (* [comment removed for export] *)
  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.
  (* [comment removed for export] *)
  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SVIS : forall x : word, in_rangesb x S = true -> wview asegs m x <> None.
  (* [comment removed for export] *)
  Hypothesis TMAPS : forall x : word, TH <= bv_unsigned x < TH + 4096 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis CMAPS : forall x : word, CTX <= bv_unsigned x < CTX + 160 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PMAPS : forall x : word, pa <= bv_unsigned x < pa + kPtrArrayReserve -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  (* [comment removed for export] *)
  Hypothesis PAMC : nch = nres -> map_contains (vm_maps (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PARF : nch = nres -> region_free (vm_reserved (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PAZR : nch = nres -> forall x : word, pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 0x20000 -> in_rangesb x Zr = false.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x1a0a0c) fc None m (seg_rom asegs).

  Let PAE : 12386304 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let MID := la_mid L S Zr mo sp gp tp s10 s11 F fc m lo size msz size8 TSD CTX TH pa nres nch chunks s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra a1.
  Let POST := large_alloc_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size msz size8 TSD CTX TH pa nres nch chunks.

  Lemma large_alloc_head : (forall msF' mo', MID msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    pose proof DEFS as D; destruct D as [DMSZ].
    assert (MSZ : size + 4096 <= msz /\ msz < size + 8192 /\ exists q, msz = 4096 * q).
    { subst msz. unfold round_up. split; [|split]; try (Z.div_mod_to_equations; lia). exists ((size + 4096 - 1) / 4096 + 1). lia. }
    destruct MSZ as (MSZ1 & MSZ2 & mq & MQ).
    assert (NZ : page_round_up_Z (bv_unsigned (wz msz)) = msz).
    { unfold wz. rewrite unsigned_lit by lia. apply page_round_up_Z_aligned; [lia|]. unfold page_size. rewrite MQ, Z.mul_comm. apply Z_mod_mult. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply large_alloc_seg1; try eassumption; lia. }
    intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (m1 & j8 & j12 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & MOFR1).
    (* [comment removed for export] *)
    eapply (sr_ecall_MS L S Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d69dc fc None m1 msF1 mo1 Q OK1 VIS1 ecall_1d697c).
    intros msF2 OK2 VIS2 HS2.
    (* [comment removed for export] *)
    eapply (sr_mmap_kernel_MS L S Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d69dc fc None m1 false false msF2 mo1 Q OK2 VIS2 eq_refl);
      rewrite ?NZ, ?(same_but_materialized_vmmaps _ _ SBM1), ?(same_but_materialized_eager _ _ SBM1).
    { apply wz_ne0. lia. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { exact NW. }
    { intros _ _. pose proof (pages_total_nonneg S). unfold page_size in *. lia. }
    { exact GAP. }
    { intros X; discriminate X. }
    cbn [kflags orb andb negb app].
    intros aw msF3 AL POS CE0 FREE OK3 VIS3 HS3 EAG3.
    assert (CE : bv_unsigned aw + msz <= aceil).
    { apply grant_below_aceil; [unfold page_size in AL; exact AL| rewrite MQ, Z.mul_comm; apply Z_mod_mult| rewrite <- ATOP; exact CE0]. }
    clear CE0.
    (* [comment removed for export] *)
    pose proof (grant_aapp_of _ _ aw msz IMGR SHLAND AL POS CE ltac:(clear - SZ MSZ1; lia) FREE) as AB.
    pose proof (aapp_env _ _ AB ltac:(clear - SZ MSZ1; lia)) as [ALO _]. pose proof (aapp_lit _ _ AB) as ALIT.
    set (a := bv_unsigned aw) in *.
    assert (AW : aw = wz a) by (subst a; symmetry; apply Z_to_bv_bv_unsigned). clearbody a. subst aw.
    change (1927644 + 4) with 1927648 in VIS3.
    set (mo3 := grant_model (Z_to_bv 64 34) (wz a) (Z_to_bv 64 msz) false mo1) in *.
    assert (VM3 : m_vmmaps mo3 = grant_vmmaps (m_vmmaps mo) (wz a) (wz msz) false).
    { subst mo3. rewrite grant_model_vmmaps, (same_but_materialized_vmmaps _ _ SBM1). reflexivity. }
    (* [comment removed for export] *)
    assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); unfold page_size in AL; Z.div_mod_to_equations; lia).
    destruct AQ as [aq AQ].
    assert (SHB : ((sh AHI_LO <= sh a /\ sh a + msz / 8 <= sh aceil) \/ (sh AIMG_TOP <= sh a /\ sh a + msz / 8 <= sh ALOWSH_LO))
                  /\ sh a + msz / 8 <= sh aceil /\ 12386304 <= sh a /\ sh (a + msz) = sh a + msz / 8
                  /\ msz / 8 = 512 * mq /\ sh aceil < AHI_LO /\ sh (a + 4096 + size) = sh a + 512 + size8).   (* [comment removed for export] *)
    { unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP, ALOWSH_LO in *. acb. rewrite MQ, AQ.
      clear - ALIT ALO CE MQ AQ MSZ1 SZ; try acb. Z.div_mod_to_equations. lia. }
    destruct SHB as (SHB1 & SHB2 & SHB3 & SHB4 & SHB5 & SHB6 & SHB7).
    assert (SH64 : sh a + msz / 8 <= 2^64) by (clear - SHB2 SHB6; unfold AHI_LO in *; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (W := (wz (sh a), wz (msz / 8))).
    destruct (open_window_MS L S Zr W msF3 mo3 _ F _ fc None _ OK3 VIS3) as [OK4 VIS4].
    { intros x Hx. apply (zin_W (sh a) (msz / 8)) in Hx; [| lia | clear - SHB2 SHB6; unfold AHI_LO in *; lia | lia]. apply ZRSH. clear - Hx SHB1. lia. }
    { rewrite VM3. cbn [vm_limit grant_vmmaps].
      rewrite pages_total_cons. pose proof (cl_bounds W) as CB. subst W. cbn [fst snd] in CB. unfold wz in CB. rewrite (unsigned_lit (msz / 8)) in CB by (first [clear - SH64 SHB3 MSZ1 SZ; lia | lia]).
      pose proof (pages_total_nonneg S). unfold page_size in *.
      replace (msz / 8 / 4096) with (msz / 32768) in CB by (rewrite Z.div_div by lia; reflexivity). clear - CB BUD EAG3 H; try acb. unfold wz in *. lia. }
    clear OK3 VIS3.
    set (m3 := owin L S W (zfill (wz a) (Z_to_bv 64 msz) m1)) in VIS4.
    assert (MU3 : munch [(a, a + msz); (sh a, sh a + msz / 8)] m1 m3).
    { intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _). subst m3.
      rewrite (owin_munch L S (sh a) (msz / 8) SHB3 ltac:(hci; (first [clear - SH64; lia | lia])) ltac:(hci; (first [clear - MSZ1 SZ; lia | lia])) _ x) by (cbn [outside]; (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])])])).
      apply (zfill_munch (wz a) (wz msz) m1 x). cbn [outside]. unfold wz. rewrite !unsigned_lit by (first [clear - ALO CE MSZ1 SZ SPH HI LO MSZ2; lia | lia]). (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])])]). }
    assert (WM3 : wmono asegs m1 m3).
    { subst m3. eapply wmono_trans; [apply zfill_wmono | apply owin_wmono]. }
    assert (MI3 : mem_inv asegs m3).
    { subst m3. apply owin_mem_inv; [exact SHB3| lia| lia|]. apply zfill_mem_inv; [unfold wz; rewrite unsigned_lit by lia; lia| exact MI1]. }
    assert (CHK : stk asegs m3 a (a + msz)).
    { subst m3. eapply stk_transport_disjoint; [| apply (owin_munch L S (sh a) (msz / 8)); lia | apply owin_wmono |].
      - pose proof (zfill_stk (wz a) (wz msz) m1) as X. unfold wz in X. rewrite !unsigned_lit in X by (first [clear - ALO CE MSZ1 SZ SPH HI LO MSZ2; lia | lia]). apply X; lia.
      - cbn [disjoint_from]. split; [|exact I]. clear - ALO ALIT MSZ1 MSZ2 SZ; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia. }   (* [comment removed for export] *)
    assert (SHK : stk asegs m3 (sh a) (sh a + msz / 8)).
    { subst m3. apply owin_stk; [exact SHB3| lia| lia| |].
      - intros x Hx. apply (lzok_ZrL OK4). apply ZRSH. clear - Hx SHB1. lia.
      - intros x Hx HS. apply zfill_wmono. apply WM1. apply SVIS. exact HS. }
    (* [comment removed for export] *)
    acb.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR'].
    unfold AHI_LO, AIMG_TOP, kPtrArrayReserve in *.
    assert (PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX))).
    { destruct PLC0 as [(P0 & _ & _)]. constructor. split; [exact P0|]. split.
      - pose proof (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) TMAPS). (first [clear - H; lia | lia]).
      - pose proof (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) CMAPS). (first [clear - H; lia | lia]). }
    assert (PLCP : hidden ((a + msz <= pa \/ pa + 8388608 <= a) /\ (pa + 8388608 <= TH \/ TH + 4096 <= pa) /\ (pa + 8388608 <= CTX \/ CTX + 160 <= pa))).
    { destruct PLC0 as [(_ & P1 & P2)]. constructor. split; [| split; [exact P1| exact P2]].
      apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; lia) PMAPS). }
    (* [comment removed for export] *)
    assert (BND : 12386304 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil /\ 2148314624 <= sh a /\ sh a + msz / 8 <= 17594332446720).
    { unfold sh, ASHADOW_BASE in *. clear - ALO CE SHB2; try acb. Z.div_mod_to_equations. lia. }
    unfold AINST in *. change (6765656 + 64) with 6765720 in *. change (6765656 + 112) with 6765768 in *. change (6765656 + 136) with 6765792 in *.
    change (6765656 + 680) with 6766336 in *. change (6765656 + 688) with 6766344 in *. change (6765656 + 728) with 6766384 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    region_sides. name_bands.
    region_table.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + msz); (sh a, sh a + msz / 8); (pa + 8 * nch, pa + 8 * (nres + 16384));
                            (6765768, 6766384); (TH + 2800, TH + 3168)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    senv_at ENV MU1 WM1 ENV1. unfold laframe in FR1.
    transport_after_call asegs m m1 MU1 WM1. clear MU1 WM1.
    senv_at ENV1 MU3 WM3 ENV3. clear ENV1.
    transport_after_call asegs m1 m3 MU3 WM3. clear MU3 WM3.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ a (a + 4096) (a + msz) CHK ltac:(hci; lia)) as [HDR USR]. clear CHK.
    destruct (stk_split asegs _ (sh a) (sh a + 512) (sh a + msz / 8) SHK ltac:(hci; lia)) as [SH1 SHR]. clear SHK.
    destruct (stk_split asegs _ (sh a + 512) (sh a + 512 + size8) (sh a + msz / 8) SHR ltac:(hci; lia)) as [SHM SH3]. clear SHR.
    destruct (stk_cells _ _ _ SH1 ltac:(hci; lia)) as [sbs1 SB1]. clear SH1. replace (sh a + 512 - sh a) with 512 in SB1 by lia.
    assert (SB1L : Z.of_nat (length sbs1) = 512) by (destruct SB1 as [[WF _] _]; rewrite (proj1 WF); reflexivity). apply u8arr_of_rw_cells in SB1.
    destruct (stk_cells _ _ _ SH3 ltac:(hci; lia)) as [sbs3 SB3]. clear SH3. replace (sh a + msz / 8 - (sh a + 512 + size8)) with ((msz - 4096 - size) / 8) in SB3 by (first [clear - SZ; lia | lia]).
    assert (SB3L : Z.of_nat (length sbs3) = (msz - 4096 - size) / 8) by (destruct SB3 as [[WF _] _]; rewrite (proj1 WF); (first [clear - MSZ1; lia | lia])). apply u8arr_of_rw_cells in SB3.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L (W :: S) Zr _ msF3 _ mo3 Q OK4 VIS4).
    { eapply (large_alloc_seg2 sp gp tp t0 t1 t2 a6 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m3 s0 s1 s2 s3 s5 s8 ra a1 j8 j12
                lo size msz a (sh a) (sh a + 512 + size8) size8 TSD CTX TH pa nres nch sbs1 sbs3); try eassumption;
        try (split; [exact AB| exact CE]); try (unfold AHI_LO; acb; (lia_guard; (first [clear - HI; lia | lia]))).
      - constructor. split; [exact DMSZ|]. split; [reflexivity| symmetry; exact SHB7].
      - constructor. unfold page_size in AL. exact AL. }
    cbv beta. intros msF4 mo4 OK5 SBM4 HS4 P4.
    destruct P4 as (u0 & u1 & u2 & v1 & v2 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & j8' & m4 & VIS5 & MU4 & WM4 & MI4 & ST4 & FR4 & SHA4 & SHT4 & HDR4 & HDR24 & TST4 & MTX4).
    unfold AINST in MU4, MTX4. change (6765656 + 680) with 6766336 in MU4, MTX4. change (6765656 + 684) with 6766340 in MU4.
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) in * by (first [clear - SZ; lia | lia]).
    senv_at ENV3 MU4 WM4 ENV4. clear ENV3.
    transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4.
    apply K. unfold MID, la_mid.
    exists a, u0, u1, u2, v1, v2, v5, v6, v7, u3, u4, u5, u6, j8', m4.
    split; [exact AB|]. split; [acb; lia|]. split; [(first [clear - AQ; lia | lia])|]. split; [exact FREE|].
    split; [exact OK5|]. split; [exact VIS5|].
    split.
    { (* [comment removed for export] *)
      unfold la_model. pose proof (same_but_materialized_vmmaps _ _ SBM4) as V4. rewrite V4, VM3. cbn [vm_maps vm_reserved vm_limit vm_mmap_base vm_brk vm_start_brk vm_noaccess grant_vmmaps].
      split. { eapply nonvm_same_trans; [apply (nonvm_same_mat _ _ SBM1)|]. eapply nonvm_same_trans; [apply nonvm_same_grant| apply (nonvm_same_mat _ _ SBM4)]. }
      repeat (split; [reflexivity|]). rewrite (same_but_materialized_eager _ _ SBM4). lia. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI4|].
    rewrite SHB7. replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) by (first [clear - SZ; lia | lia]).
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma large_alloc_tail_room : forall msF4 mo4, nch < nres -> MID msF4 mo4 ->
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 LT M4 K.
    destruct M4 as (a & u0 & u1 & u2 & v1 & v2 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & j8 & m4 & AHI & CE & AL & FREE & OK4 & VIS4 & MO4
                    & MU & WM & MI4 & ST4 & FR4 & SHA & SHM & SHT & HDR & HDR2 & USR & TST4 & MTX4 & ENV4 & INST4 & NRES4 & SST4 & GST4 & PA4 & PAJ4).
    pose proof DEFS as D; destruct D as [DMSZ].
    assert (MSZ : size + 4096 <= msz /\ msz < size + 8192 /\ exists q, msz = 4096 * q).
    { rewrite DMSZ. unfold round_up. split; [|split]; try (Z.div_mod_to_equations; (first [clear - H0 H; lia | lia])). exists ((size + 4096 - 1) / 4096 + 1). lia. }
    destruct MSZ as (MSZ1 & MSZ2 & mq & MQ).
    pose proof (aapp_env _ _ AHI ltac:(clear - SZ MSZ1; lia)) as [ALO _]. pose proof (aapp_lit _ _ AHI) as ALIT.   (* [comment removed for export] *)
    assert (L2 : 16 <= Z.log2 msz <= 41).
    { split. - replace 16 with (Z.log2 (2^16)) by reflexivity. apply Z.log2_le_mono. lia.
      - replace 41 with (Z.log2 (2^41 + 8192)) by reflexivity. apply Z.log2_le_mono. lia. }
    assert (SHB : 2148314624 <= sh a /\ sh a + msz / 8 <= 17594332446720 /\ sh (a + 4096 + size) = sh a + 512 + size8 /\ msz / 8 = 512 * mq).
    { unfold sh, ASHADOW_BASE, AHI_LO in *. acb. rewrite MQ.
      assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); Z.div_mod_to_equations; lia). destruct AQ as [aq AQ]. rewrite AQ.
      clear - AHI CE MQ AQ MSZ1 SZ; try acb. aunf. Z.div_mod_to_equations. lia. }
    destruct SHB as (SHB3 & SHB2 & SHB7 & SHB5).
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof PLC0 as R; destruct R as [(P0 & P1 & P2)].
    acb. unfold AHI_LO, AIMG_TOP, kPtrArrayReserve in *.
    assert (PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX)
                          /\ (a + msz <= pa \/ pa + 8388608 <= a) /\ (pa + 8388608 <= TH \/ TH + 4096 <= pa) /\ (pa + 8388608 <= CTX \/ CTX + 160 <= pa))).
    { constructor. split; [exact P0|]. split; [| split; [| split; [| split; [exact P1| exact P2]]]].
      - pose proof (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) TMAPS). (first [clear - H; lia | lia]).
      - pose proof (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) CMAPS). lia.
      - apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; lia) PMAPS). }
    clear P0 P1 P2.
    assert (BND : 12386304 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil) by (clear - AHI CE; aunf; lia).   (* [comment removed for export] *)
    unfold AINST in *. change (6765656 + 64) with 6765720 in *. change (6765656 + 112) with 6765768 in *. change (6765656 + 136) with 6765792 in *.
    change (6765656 + 680) with 6766336 in *. change (6765656 + 688) with 6766344 in *. change (6765656 + 728) with 6766384 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    region_sides. name_bands.
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) in * by (first [clear - SZ PAE MSZ1 MQ ALO SHB7 SHB5 ACEILB SPR RXb0; lia | lia]).
    unfold la_W in MU. unfold AINST in MU. change (6765656 + 112) with 6765768 in MU. change (6765656 + 728) with 6766384 in MU.
    region_table.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (pa + 8 * nch) (pa + 8 * nch + 8) (pa + 8 * nres) PAJ4 ltac:(hci; lia)) as [SL PAJ5]. clear PAJ4.
    destruct (stk_cells _ _ _ SL ltac:(hci; lia)) as [jsl SLOT]. clear SL. replace (pa + 8 * nch + 8 - (pa + 8 * nch)) with 8 in SLOT by lia.
    change (Z.to_nat 8) with 8%nat in SLOT. destruct (cb8_word _ _ _ _ SLOT) as [jslot SLOT']. clear SLOT.
    destruct (stk_split asegs _ (a + 24) (a + 32) (a + 4096) HDR2 ltac:(hci; lia)) as [HD3 HDR3].
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L (_ :: S) Zr _ msF4 _ mo4 Q OK4 VIS4).
    { eapply evt_cut. { eapply large_alloc_seg2c; [exact MI4| lia]. }
      cbv beta. intros ms' (E & _ & _ & _). subst ms'.
      eapply (large_alloc_seg3 sp gp tp u0 u1 u2 v1 v2 (wz nres) v5 v6 v7 s10 s11 u3 u4 u5 u6 F fc m4 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra a1 (wz a) (wz 0x1a0b34) j8 jslot
                lo size msz a pa (pa + 8 * nch) (6765824 + 8 * Z.log2 msz) nres nch chunks); try eassumption; try reflexivity;
        try (split; [exact AHI| exact CE]); try (split; [exact (proj1 PAR)| clear - PAE; unfold kPtrArrayReserve in *; try acb; lia]); try (unfold AHI_LO, kPtrArrayReserve; acb; (first [clear - HI SZ MSZ2 MSZ1 LT NCH; lia | lia])).
      constructor. destruct PLC as [X]. clear - X; try acb. unfold kPtrArrayReserve. tauto. }
    cbv beta. intros msF5 mo5 OK5 SBM5 HS5 P5.
    destruct P5 as (w0 & w1 & w2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & w3 & w4 & w5 & w6 & m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & NRES5 & PA5 & HDR5 & SST5 & MTX5 & GST5).
    clear HDR2 ST4 NRES4 PA4 SST4 GST4 MTX4 SLOT' HD3 FR4.
    senv_at ENV4 MU5 WM5 ENV5. clear ENV4.
    transport_after_call asegs m4 m5 MU5 WM5. clear MU5 WM5.
    apply K. unfold POST, large_alloc_post.
    exists a, w0, w1, w2, x1, x2, x3, x4, x5, x6, x7, w3, w4, w5, w6, m5.
    replace (nch =? nres) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
    split; [exact AHI|]. split; [acb; lia|]. split; [lia|]. split; [exact FREE|].
    split; [exact OK5|]. split; [exact VIS5|]. split; [exact (la_model_mat _ _ _ _ _ _ _ _ MO4 SBM5)|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI5|].
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) by (first [clear - SZ; lia | lia]). replace (pa + 8 * (nch + 1)) with (pa + 8 * nch + 8) by lia.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma large_alloc_tail_commit : forall msF4 mo4, nch = nres -> MID msF4 mo4 ->
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 EQ M4 K.
    destruct M4 as (a & u0 & u1 & u2 & v1 & v2 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & j8 & m4 & AHI & CE & AL & FREE & OK4 & VIS4 & MO4
                    & MU & WM & MI4 & ST4 & FR4 & SHA & SHM & SHT & HDR & HDR2 & USR & TST4 & MTX4 & ENV4 & INST4 & NRES4 & SST4 & GST4 & PA4 & PAJ4).
    pose proof DEFS as D; destruct D as [DMSZ].
    assert (MSZ : size + 4096 <= msz /\ msz < size + 8192 /\ exists q, msz = 4096 * q).
    { rewrite DMSZ. unfold round_up. split; [|split]; try (Z.div_mod_to_equations; (first [clear - H0 H; lia | lia])). exists ((size + 4096 - 1) / 4096 + 1). lia. }
    destruct MSZ as (MSZ1 & MSZ2 & mq & MQ).
    pose proof (aapp_env _ _ AHI ltac:(clear - SZ MSZ1; lia)) as [ALO _]. pose proof (aapp_lit _ _ AHI) as ALIT.   (* [comment removed for export] *)
    assert (L2 : 16 <= Z.log2 msz <= 41).
    { split. - replace 16 with (Z.log2 (2^16)) by reflexivity. apply Z.log2_le_mono. (first [clear - MSZ1 SZ; lia | lia]).
      - replace 41 with (Z.log2 (2^41 + 8192)) by reflexivity. apply Z.log2_le_mono. lia. }
    assert (SHB : 2148314624 <= sh a /\ sh a + msz / 8 <= 17594332446720 /\ sh (a + 4096 + size) = sh a + 512 + size8 /\ msz / 8 = 512 * mq).
    { unfold sh, ASHADOW_BASE, AHI_LO in *. acb. rewrite MQ.
      assert (AQ : exists aq, a = 4096 * aq) by (exists (a / 4096); Z.div_mod_to_equations; lia). destruct AQ as [aq AQ]. rewrite AQ.
      clear - AHI CE MQ AQ MSZ1 SZ; try acb. aunf. Z.div_mod_to_equations. lia. }
    destruct SHB as (SHB3 & SHB2 & SHB7 & SHB5).
    pose proof NRQ as R; destruct R as [nq NQ].
    assert (BEGAL : (pa + 8 * nres) mod 4096 = 0).
    { rewrite NQ. replace (pa + 8 * (512 * nq)) with (pa + nq * 4096) by lia. rewrite Z_mod_plus_full. destruct PAR as (_ & _ & E). exact E. }
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof PLC0 as R; destruct R as [(P0 & P1 & P2)].
    acb. unfold AHI_LO, AIMG_TOP, kPtrArrayReserve in *.
    assert (PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX)
                          /\ (a + msz <= pa \/ pa + 8388608 <= a) /\ (pa + 8388608 <= TH \/ TH + 4096 <= pa) /\ (pa + 8388608 <= CTX \/ CTX + 160 <= pa))).
    { constructor. split; [exact P0|]. split; [| split; [| split; [| split; [exact P1| exact P2]]]].
      - pose proof (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) TMAPS). (first [clear - H; lia | lia]).
      - pose proof (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) CMAPS). lia.
      - apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; lia) PMAPS). }
    clear P0 P1 P2.
    assert (BND : 12386304 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil) by (clear - AHI CE; aunf; lia).   (* [comment removed for export] *)
    unfold AINST in *. change (6765656 + 64) with 6765720 in *. change (6765656 + 112) with 6765768 in *. change (6765656 + 136) with 6765792 in *.
    change (6765656 + 680) with 6766336 in *. change (6765656 + 688) with 6766344 in *. change (6765656 + 728) with 6766384 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; (first [clear - LEN; lia | lia])).
    region_sides. name_bands.
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) in * by (first [clear - SZ; lia | lia]).
    unfold la_W in MU. unfold AINST in MU. change (6765656 + 112) with 6765768 in MU. change (6765656 + 728) with 6766384 in MU.
    region_table.
    replace (wz nch) with (wz nres) in VIS4 by (f_equal; lia). replace (wz nch) with (wz nres) in NRES4 by (f_equal; lia).
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L (_ :: S) Zr _ msF4 _ mo4 Q OK4 VIS4).
    { eapply (large_alloc_seg2b sp gp tp u0 u1 u2 v1 v2 v5 v6 v7 s10 s11 u3 u4 u5 u6 F fc m4 a1 lo size msz a pa nres TSD CTX TH);
        try eassumption; try (split; [exact AHI| exact CE]); try (split; [exact (proj1 PAR)| clear - PAE; unfold kPtrArrayReserve in *; try acb; lia]); try (unfold AHI_LO, kPtrArrayReserve; acb; lia). }
    cbv beta. intros msF5 mo5 OK5 SBM5 HS5 P5.
    destruct P5 as (m5 & j44 & VIS5 & MU5 & WM5 & MI5 & ST5 & FR5).
    clear ST4. unfold laframe in FR4.
    senv_at ENV4 MU5 WM5 ENV5. clear ENV4.
    transport_after_call asegs m4 m5 MU5 WM5. clear MU5 WM5.
    (* [comment removed for export] *)
    eapply (sr_ecall_MS L (_ :: S) Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d69dc fc None m5 msF5 mo5 Q OK5 VIS5 ecall_1d697c).
    intros msF6 OK6 VIS6 HS6.
    (* [comment removed for export] *)
    assert (NZ : page_round_up_Z (bv_unsigned (wz 131072)) = 131072) by reflexivity.
    pose proof MO4 as MO; unfold la_model in MO. cbv beta iota zeta in MO.
    destruct MO as (NV4 & VM4 & VR4 & VL4 & VB4 & VK4 & VS4 & VA4 & EAG4).
    eapply (sr_mmap_commit_MS L (_ :: S) Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0x1d69dc fc None m5 false msF6 mo5 Q OK6 VIS6 eq_refl);
      rewrite ?NZ, ?(same_but_materialized_vmmaps _ _ SBM5), ?(same_but_materialized_eager _ _ SBM5); unfold wz; rewrite ?(unsigned_lit (pa + 8 * nres)) by (first [clear - ACEILB PAE NCH; lia | lia]).
    { apply wz_ne0. lia. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { rewrite (nonvm_same_atop _ _ NV4), ATOP. acb. lia. }
    { exact BEGAL. }
    { lia. }
    { rewrite VR4. exact (PARF EQ). }
    { rewrite VM4. apply map_contains_cons. exact (PAMC EQ). }
    { rewrite VM4. apply entries_nowrap_cons'; [| exact NW]. unfold entry_nowrap, LazyLedger.hi, LazyLedger.lo. cbn [fst snd]. unfold wz. rewrite !unsigned_lit by lia. lia. }
    { rewrite VA4. exact NWA. }
    { rewrite VM4. apply nooverlap_cons_free; [exact (region_free_app_r _ _ _ _ FREE)| exact NOV]. }
    { intros _. exact (PAZR EQ). }
    { intros X; discriminate X. }
    { intros X; discriminate X. }
    { intros _. rewrite VL4. rewrite pages_total_cons. pose proof (cl_bounds (Z_to_bv 64 (sh a), Z_to_bv 64 (msz / 8))) as CB. cbn [fst snd] in CB.
      rewrite (unsigned_lit (msz / 8)) in CB by (first [clear - SHB2 SHB3 MSZ1 SZ; lia | lia]). pose proof (pages_total_nonneg S). unfold page_size in *.
      replace (msz / 8 / 4096) with (msz / 32768) in CB by (rewrite Z.div_div by lia; reflexivity). clear - CB BUD EAG4 H; try acb. lia. }
    cbn [app]. intros msF7 OK7 VIS7 HS7 EAG7. change (1927644 + 4) with 1927648 in VIS7.
    set (mo7 := commit_model _ _ _ _ mo5) in *.
    set (m7 := zfill (Z_to_bv 64 (pa + 8 * nres)) (Z_to_bv 64 131072) m5) in *.
    assert (MU7 : munch [(pa + 8 * nres, pa + 8 * nres + 131072)] m5 m7).
    { pose proof (zfill_munch (Z_to_bv 64 (pa + 8 * nres)) (Z_to_bv 64 131072) m5) as X. rewrite !unsigned_lit in X by (first [clear - ACEILB PAE NCH; lia | lia]). exact X. }
    assert (WM7 : wmono asegs m5 m7) by (apply zfill_wmono).
    assert (MI7 : mem_inv asegs m7) by (apply zfill_mem_inv; [rewrite unsigned_lit by (first [clear - ACEILB PAE NCH; lia | lia]); (first [clear - PAE NCH; lia | lia])| exact MI5]).
    assert (NEWJ : stk asegs m7 (pa + 8 * nres) (pa + 8 * nres + 131072)).
    { pose proof (zfill_stk (Z_to_bv 64 (pa + 8 * nres)) (Z_to_bv 64 131072) m5) as X. rewrite !unsigned_lit in X by lia. apply X; lia. }
    senv_at ENV5 MU7 WM7 ENV7. clear ENV5.
    transport_after_call asegs m5 m7 MU7 WM7. clear MU7 WM7.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (pa + 8 * nres) (pa + 8 * nres + 8) (pa + 8 * nres + 131072) NEWJ ltac:(hci; lia)) as [SL PAJ7]. clear NEWJ.
    destruct (stk_cells _ _ _ SL ltac:(hci; lia)) as [jsl SLOT]. clear SL. replace (pa + 8 * nres + 8 - (pa + 8 * nres)) with 8 in SLOT by lia.
    change (Z.to_nat 8) with 8%nat in SLOT. destruct (cb8_word _ _ _ _ SLOT) as [jslot SLOT']. clear SLOT.
    replace (pa + 8 * nres) with (pa + 8 * nch) in SLOT' by lia.
    destruct (stk_split asegs _ (a + 24) (a + 32) (a + 4096) HDR2 ltac:(hci; lia)) as [HD3 HDR3].
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs _ (_ :: S) Zr _ msF7 _ mo7 Q OK7 VIS7).
    { eapply (large_alloc_seg4 sp gp tp u0 u1 u2 _ _ _ _ _ v6 _ s10 s11 u3 u4 u5 u6 F fc m7 a1 j44 lo size msz a pa nres TSD CTX TH);
        try eassumption; try (split; [exact AHI| exact CE]); try (split; [exact (proj1 PAR)| clear - PAE; unfold kPtrArrayReserve in *; try acb; lia]); try (unfold AHI_LO, kPtrArrayReserve; acb; lia). }
    cbv beta. intros msF8 mo8 OK8 SBM8 HS8 P8.
    destruct P8 as (y1 & y2 & y4 & y5 & m8 & VIS8 & MU8 & WM8 & MI8 & ST8 & NRES8).
    replace (wz nres) with (wz nch) in NRES8, VIS8 by (f_equal; lia).
    clear NRES4 ST5 FR5.
    senv_at ENV7 MU8 WM8 ENV8. clear ENV7.
    transport_after_call asegs m7 m8 MU8 WM8. clear MU8 WM8.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs _ (_ :: S) Zr _ msF8 _ mo8 Q OK8 VIS8).
    { eapply (large_alloc_seg3 sp gp tp u0 u1 u2 y1 y2 y4 y5 v6 (Z_to_bv 64 222) s10 s11 u3 u4 u5 u6 F fc m8 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra a1
                (wz (a + 4096)) (wz 0x1a0e68) j8 jslot lo size msz a pa (pa + 8 * nch) (6765824 + 8 * Z.log2 msz) (nres + 16384) nch chunks);
        try eassumption; try reflexivity; try (split; [exact AHI| exact CE]); try (split; [exact (proj1 PAR)| clear - PAE; unfold kPtrArrayReserve in *; try acb; lia]); try (unfold AHI_LO, kPtrArrayReserve; acb; (first [clear - HI SZ MSZ2 MSZ1 NCH; lia | (lia_guard; lia)])).
      constructor. destruct PLC as [X]. clear - X; try acb. unfold kPtrArrayReserve. (first [clear; solve [repeat split; exact I] | tauto]). }
    cbv beta. intros msF9 mo9 OK9 SBM9 HS9 P9.
    destruct P9 as (w0 & w1 & w2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & w3 & w4 & w5 & w6 & m9 & VIS9 & MU9 & WM9 & MI9 & ST9 & NRES9 & PA9 & HDR9 & SST9 & MTX9 & GST9).
    clear HDR2 PA4 SST4 GST4 MTX4 SLOT' HD3 FR4 PAJ4 ST8 NRES8.
    senv_at ENV8 MU9 WM9 ENV9. clear ENV8.
    transport_after_call asegs m8 m9 MU9 WM9. clear MU9 WM9.
    apply K. unfold POST, large_alloc_post.
    exists a, w0, w1, w2, x1, x2, x3, x4, x5, x6, x7, w3, w4, w5, w6, m9.
    replace (nch =? nres) with true by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta.
    split; [exact AHI|]. split; [acb; lia|]. split; [lia|]. split; [exact FREE|].
    split; [exact OK9|]. split; [exact VIS9|].
    split.
    { (* [comment removed for export] *)
      apply (la_model_mat _ _ _ _ _ _ mo7 _); [| exact (same_but_materialized_trans _ _ _ SBM8 SBM9)]. unfold la_model. subst mo7.
      rewrite commit_model_vmmaps, (same_but_materialized_vmmaps _ _ SBM5). cbn [vm_maps vm_reserved vm_limit vm_mmap_base vm_brk vm_start_brk vm_noaccess commit_vmmaps app].
      rewrite VM4, VR4, VL4, VB4, VK4, VS4, VA4. rewrite !unsigned_lit by lia.
      split. { eapply nonvm_same_trans; [exact NV4|]. eapply nonvm_same_trans; [apply (nonvm_same_mat _ _ SBM5)| apply nonvm_same_commit]. }
      repeat (split; [reflexivity|]). clear - EAG4 EAG7; try acb. lia. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI9|].
    replace ((msz - 4096 - size) / 8) with (msz / 8 - 512 - size8) by (first [clear - SZ; lia | lia]).
    replace (pa + 8 * (nch + 1)) with (pa + 8 * nres + 8) by (first [clear - EQ; lia | lia]). replace (pa + 8 * (nres + 16384)) with (pa + 8 * nres + 131072) by lia.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
  (* [comment removed for export] *)
  Theorem large_alloc_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. apply large_alloc_head. intros msF4 mo4 M4.
    destruct (Z.lt_ge_cases nch nres) as [LT|GE].
    - exact (large_alloc_tail_room msF4 mo4 LT M4 K).
    - apply (large_alloc_tail_commit msF4 mo4 ltac:(hci; lia) M4 K).
  Qed.
End LargeAlloc.

