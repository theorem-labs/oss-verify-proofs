(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3; internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AsDepotHash AsDepotPut AsUnwind AllocWalkKit F_memset.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_AllocBase AW_MallocBase AW_LargeAlloc1 AW_SysconfPg
     AW_MallocPre AW_MallocRet AW_AllocPreSec AW_AllocSec1 AW_AllocSec2 SecLazy AS_LargeAlloc AS_AllocSec1 AS_AllocSec AS_MallocLarge1 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition ml_W (lo : Z) (sp : word) (a msz pa nch nres TH : Z) (d : depot) : list ivl :=
  (lo, bv_unsigned sp) :: (TH + 3168, TH + 3169) :: (a, a + msz) :: (sh a, sh a + msz / 8) :: (pa + 8 * nch, pa + 8 * (nres + 16384))
  :: (AINST + 112, AINST + 728) :: (TH + 2800, TH + 3168) :: depot_W d.

(* [comment removed for export] *)
Definition malloc_large_post (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo size needed msz TSD CTX TH sb pa nres nch : Z) (chunks T : list Z) (d : depot)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (a : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (b1 : Z) (rest : list word) (m' : mem),
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
    /\ munch (ml_W lo sp a msz pa nch nres TH d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AENV tp TSD CTX TH sb (bv_unsigned sp + -2128) T rest m'
    /\ rw_cells asegs m' (TH + 3168) [C1 (b8 0)]
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' (AINST + 112) [C8 (wz nres'); C8 (wz (nch + 1)); C8 (wz 0)]
    /\ stk asegs m' (AINST + 136) (AINST + 680) /\ rw_cells asegs m' (AINST + 680) [C8 (wz 0)] /\ stk asegs m' (AINST + 688) (AINST + 728)
    /\ u64arr asegs m' pa (wlist (chunks ++ [a])) /\ stk asegs m' (pa + 8 * (nch + 1)) (pa + 8 * nres')
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz needed); C8 (wz nch)] /\ stk asegs m' (a + 32) (a + 4096)
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (a + 6128) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz (d_putid d (depot_hash T)))] /\ b1_ok b1
    /\ rw_cells asegs m' (a + 4096) [C8 (wz kAllocBegMagic); C8 (wz (a + 6128))] /\ stk asegs m' (a + 4112) (a + 6128)
    /\ u8arr asegs m' (a + 6144) (repeat (b8 0xbe) 4096)
    /\ stk asegs m' (a + 6144 + 4096) (a + msz)
    /\ u8arr asegs m' (sh a) (repeat (b8 0xfa) 512) /\ u8arr asegs m' (sh (a + 4096)) (sec_shadow size msz)
    (* [comment removed for export] *)
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs (d_put d (depot_hash T) (Z.of_nat (length T))) m'.

End HCW.


(* [comment removed for export] *)
Ltac region_retable :=
  repeat match goal with
         | H : region_tabled |- _ => clear H | H : region_psep _ _ _ |- _ => clear H | H : region_fam _ _ |- _ => clear H
         | H : region_rank _ _ |- _ => clear H | H : region_lb _ _ |- _ => clear H | H : region_ub _ _ |- _ => clear H end;
  region_table.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Section MallocLarge.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size needed msz : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT sb pa nres nch : Z) (CH : list (Z * Z)) (chunks : list Z).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x07351c (bv_unsigned sp) TOP BOT 30 CHI.
  Hypothesis DEFS : hidden (needed = round_up (Z.max size 8) 8 + 4096 /\ msz = round_up needed 4096 + 4096).
  (* [comment removed for export] *)
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2912 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis SZ : 64512 < size < 2^32.
  Hypothesis TPR : hidden (6337480 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6337392 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis PLC0 : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)).
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 262144 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 262144 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 262144 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 262144)).
  Hypothesis PLCDP : hidden ((pa + kPtrArrayReserve <= d_nb d \/ d_nb d + 16 * 65536 <= pa) /\ (pa + kPtrArrayReserve <= d_sb d \/ d_sb d + 8 * 262144 <= pa)).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 262144 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 262144.
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20. Hypothesis NRQ : exists q, nres = 512 * q.
  Hypothesis LEN : zlen chunks = nch.
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.
  (* [comment removed for export] *)
  Hypothesis IEN : IENV tp TSD CTX TH sb TOP BOT m.
  Hypothesis SEN : SENV tp TSD CTX TH m.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis UNW : rw_cells asegs m (TH + 3168) [C1 (b8 0)].
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
  (* #38: old text is the first four conjuncts, unchanged; the fifth is the
     window premise [Checks.Placement.linux_place_exists] consumes, which
     [SecGap.gap_witness_fit_top_window] supplies at AHI_LO = 0x10007fff8000
     > task_unmapped_base = 0x2aaaaab000.  Pins no kernel field. *)
  Hypothesis GAP : exists g : word, bv_unsigned g mod page_size = 0 /\ 0 < bv_unsigned g /\ bv_unsigned g + msz <= alloc_top (m_vmmaps mo)
                                    /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) g (wz msz) = true
                                    /\ (bv_unsigned g + msz <= mmap_top (m_vmmaps mo) \/ task_unmapped_base <= bv_unsigned g).
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
  Hypothesis DSMAPS : forall x : word, d_sb d <= bv_unsigned x < d_sb d + 8 * 262144 -> in_rangesb x (vm_maps (m_vmmaps mo)) = true.
  Hypothesis PAMC : nch = nres -> map_contains (vm_maps (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PARF : nch = nres -> region_free (vm_reserved (m_vmmaps mo)) (wz (pa + 8 * nres)) (wz 0x20000) = true.
  Hypothesis PAZR : nch = nres -> forall x : word, pa + 8 * nres <= bv_unsigned x < pa + 8 * nres + 0x20000 -> in_rangesb x Zr = false.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x073454) fc None m (seg_rom asegs).

  Let PAE : 6811648 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let POST := malloc_large_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed msz TSD CTX TH sb pa nres nch chunks T d.
Scheme kc__1 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AllocWalkKit.hidden Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.
Scheme kc__4 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__5 := Elimination for OSSVerify.Proofs.boost_beast.http_request.lib.As.AW_AllocBase.AENV Sort Prop.

  (* [comment removed for export] *)
  Theorem malloc_large_sreach :
    (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    (* LPS revision repair (#38 / 75d69e00, checker 2c6b6db8).  The As/ twin of the Bo/ repair
       landed in the same commit.  The recorded KReplay term for [malloc_large_sreach] was typed
       against the pre-revision contract: it transports [GAP] from [mo] to [mo1] with an
       [eq_ind_r] whose motive is the OLD FOUR-conjunct GAP, applied to this Section's
       FIVE-conjunct [GAP] (:142-144).  The Bo/ mirror shows the kernel's own words - "Illegal
       application, eq_ind_r at VmMaps", Bo/AS_MallocLarge.v:185:309905-309909, in
       a farm round at source; this
       file was NEVER ATTEMPTED in that round (no dune rule line), blocked behind
       As/AsanNodesMmB.v:1265, so its defect is inferred from the mirror and from the blob
       carrying the same four-conjunct motive, not read from a kernel message of its own.
       A KReplay body cannot be amended in part: its [|constr:(...)|] table carries only global
       constants, and the motive's conjunction structure lives in the encoded string, so adding
       the fifth conjunct there would be re-encoding, which is forbidden.  Nor can the premise
       be weakened back: [mmap_top h = Z.min (vm_mmap_base h) (page_round_down_Z (alloc_top h))]
       (75d69e00 State.v:3466) admits a region-free page-aligned [g] satisfying the four
       conjuncts and neither disjunct of the fifth, so four does not imply five.
       The proof is therefore re-authored as explicit text, ported from the name-for-name
       identical Section of openssl/echconfiglist_parser As/AS_MallocLarge.v:166-254 - the same
       donor tree Bo/AS_LargeAlloc.v:211-361 used for [large_alloc_head].  [asegs] kept; every
       binary-specific literal re-keyed from THIS mirror's own statements: AINST 0x125e18
       (As/AllocRep.v:29) for the donor's 0x673c58, hence 1203736 + {64,112,136,680,688,728};
       the malloc-entry pc 0x07351c and the inner frame's return address 0x4edc0 from
       As/AS_MallocLarge1.v:39,54; the pointer-array floor 6811648 from [PAE] (:169); the shadow
       floor 2148302336 from As/AG_Free2.v:137; the depot span 8 * 262144 from [PLCD]
       (:104-107).  Shared with the donor and deliberately left alone: 8388608 =
       kPtrArrayReserve, 17594333495296, 140735332483072, 2^47.
       [GAP] itself needs no edit: explicit text reaches [alloc_sec_sreach]'s five-conjunct GAP
       premise through [rewrite ?(same_but_materialized_vmmaps _ _ SBM1) ...; try eassumption],
       which is insensitive to the number of conjuncts where the recorded [eq_ind_r] motive was
       not.  No statement moves: Statements.v, Shapes.v, every Proof.v, and this file's own
       Section text and [malloc_large_sreach] statement are untouched.  Nothing is decoded and
       nothing is re-encoded. *)
    intros K.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof SBR as R; destruct R as [SBR']. pose proof SPT as R; destruct R as [SPT'].
    pose proof SPA as R; destruct R as [SPA']. pose proof PAR as R; destruct R as (PLO & PHI & PAL). pose proof PLCD as R; destruct R as [PLCD']. pose proof NCH as R; destruct R as (NLO & NHI).
    unfold AHI_LO, AIMG_TOP, kSpaceSize, kPtrArrayReserve in RNG', TPR', SBR', PLO, PHI, PLCD'. acb.
    pose proof LO as LO'. acb. change (2^47) with 140737488355328 in SPT'.
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    unfold AINST in *. change (1203736 + 64) with 1203800 in *. change (1203736 + 112) with 1203848 in *. change (1203736 + 136) with 1203872 in *.
    change (1203736 + 680) with 1204416 in *. change (1203736 + 688) with 1204424 in *. change (1203736 + 728) with 1204464 in *.
    region_table.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply (malloc_large_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size needed d TSD CTX TH TOP BOT CH sb);
        try eassumption. { destruct DEFS as [(D1 & D2)]. constructor. exact D1. } clear - HI; try acb; lia. }
    cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & jk & j8 & rest & m1 & VIS1 & MU1 & WM1 & MI1 & AEN1 & LR1 & TR1 & NT1 & ST1 & AFR1 & FRI1 & TFB1 & F41 & UNW1 & DEP1).
    fold CHI in AEN1, LR1, TR1, NT1. fold T in AEN1, LR1, TR1, NT1.
    senv_at SEN MU1 WM1 SEN1.
    assert (SVIS1 : forall x : word, in_rangesb x S = true -> wview asegs m1 x <> None) by (intros x Hx; apply WM1; exact (SVIS x Hx)).
    clear SEN ST UNW IEN.
    transport_after_call asegs m m1 MU1 WM1.
    replace (bv_unsigned sp + -2272) with (bv_unsigned sp + -2144 + -128) in VIS1, ST1 by lia.
    (* [comment removed for export] *)
    eapply (alloc_sec_sreach L S Zr msF1 mo1 Q (wz 0x4edc0) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp F fc m1
              sp (wz size) (wz 0x07351c) (wz 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 j8 lo size needed msz TSD CTX TH sb (bv_unsigned sp + -2128) pa nres nch (size / 8) (size mod 8)
              (Z.of_nat (length T)) (d_putid d (depot_hash T)) chunks T rest d);
      rewrite ?unsigned_lit by (first [clear - RXb2 LO' SPT' HI; lia | lia]); rewrite ?(same_but_materialized_vmmaps _ _ SBM1), ?(same_but_materialized_eager _ _ SBM1); try eassumption.
    { destruct DEFS as [(D1 & D2)]. constructor. repeat split; try assumption; try reflexivity. clear - SZ; try acb; Z.div_mod_to_equations; lia. }
    { clear - HI; try acb; lia. }
    { constructor. replace (bv_unsigned sp + -2144) with (bv_unsigned sp + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact SPA'. }
    { clear - SPT'; try acb; lia. }
    { clear - SZ; try acb; Z.div_mod_to_equations; lia. }
    { destruct PLCDP as [(Q1 & Q2)]. constructor. destruct PLCD' as (E1 & E2 & _ & _ & E5 & E6 & E7 & E8). exact (conj E1 (conj E2 (conj E5 (conj E6 (conj Q1 (conj Q2 (conj E7 E8))))))). }
    { constructor. clear - SPT'; try acb; lia. }
    { clear - NT1; try acb; lia. }
    { clear - DCAP NT1; try acb; lia. }
    cbv beta. intros msF2 mo2 P2.
    destruct P2 as (a & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & b1 & m2 & AHI & CE & AL & FREE & OK2 & VIS2 & MO2 & MU2 & WM2 & MI2 & ST2 & AEN2
                    & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & PAJ2 & LHDR2 & LHJ2 & CH2 & B1 & MAG2 & MAGJ2 & FILL2 & SLK2 & SHA2 & SHU2 & TST2 & DEP2).
    rewrite ?unsigned_lit in MU2, ST2 by lia. unfold as_W in MU2. rewrite ?unsigned_lit in MU2 by (first [clear - HI PAE SPR ACEILB LO' ACEILB0 RXb2; lia | lia]).
    replace (ret_pc (wz 323008)) with (Z_to_bv 64 323008) in VIS2 by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    rewrite unsigned_lit in ST2 by (first [clear - HI PAE SPR ACEILB LO' ACEILB0 RXb2; lia | lia]). unfold depot_W in MU2.
    unfold AINST in MU2, INST2, NRES2, SST2, MTX2, GST2. change (1203736 + 64) with 1203800 in INST2. change (1203736 + 112) with 1203848 in MU2, NRES2.
    change (1203736 + 136) with 1203872 in SST2. change (1203736 + 680) with 1204416 in SST2, MTX2. change (1203736 + 688) with 1204424 in GST2. change (1203736 + 728) with 1204464 in MU2, GST2.
    (* [comment removed for export] *)
    pose proof CE as CE'. acb.
    assert (MSZ : size + 4096 <= msz) by (destruct DEFS as [(D1 & D2)]; clear - D1 D2 SZ; try acb; subst needed msz; unfold round_up; Z.div_mod_to_equations; lia).
    pose proof (aapp_env _ _ AHI ltac:(clear - MSZ SZ; lia)) as [AHI' _]. pose proof (aapp_lit _ _ AHI) as ALIT.   (* [comment removed for export] *)
    assert (PLCA : hidden ((TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX) /\ (a + msz <= pa \/ pa + 8388608 <= a)
                           /\ (a + msz <= d_nb d \/ d_nb d + 16 * 65536 <= a) /\ (a + msz <= d_sb d \/ d_sb d + 8 * 262144 <= a))).
    { rewrite (same_but_materialized_vmmaps _ _ SBM1) in FREE. constructor. split; [| split; [| split; [| split]]].
      - pose proof (free_vs_mapped _ _ a msz TH 4096 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) TMAPS). (first [clear - H; lia | lia]).
      - pose proof (free_vs_mapped _ _ a msz CTX 160 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; (first [clear - SZ PAE SPR ACEILB RXb2 NT1 CE' ACEILB1 AHI'; lia | lia])) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; clear - RNG'; aunf; lia) ltac:(hci; lia) CMAPS). (first [clear - H; lia | lia]).
      - apply (free_vs_mapped _ _ a msz pa 8388608 FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; clear - PAE; try acb; unfold kPtrArrayReserve in *; lia) ltac:(hci; lia)). unfold kPtrArrayReserve in PMAPS. exact PMAPS.
      - apply (free_vs_mapped _ _ a msz (d_nb d) (16 * 65536) FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; lia) DNMAPS).
      - apply (free_vs_mapped _ _ a msz (d_sb d) (8 * 262144) FREE ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; clear - PLCD'; aunf; lia) ltac:(hci; lia) DSMAPS). }
    assert (DBND : 6811648 <= d_nb d /\ 6811648 <= d_sb d) by (clear - PLCD'; try acb; aunf; lia).   (* [comment removed for export] *)
    assert (SHB : 2148302336 <= sh a /\ sh a + msz / 8 <= 17594333495296) by (clear - AHI' CE'; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (ABND : 6811648 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil) by (clear - AHI' CE'; try acb; lia).   (* [comment removed for export] *)
    region_retable.
    apply (munch_weaken _ (ml_W lo sp a msz pa nch nres TH d)) in MU1; [| unfold ml_W, depot_W, sub_fp; cbn [outside]; clear; intros; tauto]. unfold ml_W, depot_W in MU1.
    unfold AINST in MU1. change (1203736 + 112) with 1203848 in MU1. change (1203736 + 728) with 1204464 in MU1.
    senv_at SEN1 MU2 WM2 SEN2. clear SEN1 ST1 AFR1 DEP1 SVIS1 INST64 NRES SST MTX GST TST PA PAJ.
    transport_after_call asegs m1 m2 MU2 WM2.
    (* [comment removed for export] *)
    pose proof AEN2 as E2. open_env E2.
    eapply (evt_sreach_lazy_at asegs _ _ Zr _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (malloc_ret sp ra s0 s1 s2 s3 s4 s5 (wz 0x4edc0) gp tp _ _ _ sp (wz size) _ _ _ _ _ _ _ (wz 0x07351c) (wz 1)
                (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 lo (a + 6144) T rest jk);
        try eassumption. { clear - HI; try acb; lia. } { clear - AHI' CE' MSZ SZ; try acb; lia. } }
    cbv beta. intros msF3 mo3 OK3 SBM3 HS3 P3. destruct P3 as [VIS3 ST3].
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Eso Etr.
    (* [comment removed for export] *)
    apply K. unfold POST, malloc_large_post.
    exists a, y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, b1, rest, m2.
    cbv zeta. unfold ml_W, depot_W, AINST. change (1203736 + 64) with 1203800. change (1203736 + 112) with 1203848. change (1203736 + 136) with 1203872.
    change (1203736 + 680) with 1204416. change (1203736 + 688) with 1204424. change (1203736 + 728) with 1204464.
    split; [exact AHI|]. split; [exact CE|]. split; [exact AL|]. split; [rewrite <- (same_but_materialized_vmmaps _ _ SBM1); exact FREE|].
    split; [exact OK3|]. split; [exact VIS3|].
    split.
    { apply (as_model_mat _ _ _ _ _ _ mo2); [| exact SBM3].
      pose proof MO2 as MO; unfold as_model in MO |- *. cbv beta iota zeta in MO |- *.
      rewrite <- (same_but_materialized_vmmaps _ _ SBM1), <- (same_but_materialized_eager _ _ SBM1).
      destruct MO as (NV2 & REST). split; [| exact REST]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| exact NV2]. }
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI2|]. split; [exact ST3|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End MallocLarge.

End HCW2.

