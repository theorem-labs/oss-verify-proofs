(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_tables MallocInv_hints MallocInv_ameta_iface MallocInv_ametax_iface MallocSureCap MallocSurePot.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocInv_aslot_iface () := "C46Stdlib5Lists4List2hdc69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface@alloc_slot_specWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;MallocTreeW5tsallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5mbindC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface?alloc_slot_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;MallocTreeW>tsall_of_tsafeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;MallocTreeW>tsafe_of_tsallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree5tsafeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I69OSSVerify5KrLib6Common8MallocngEMallocInv_ameta_iface2II00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common8Mallocng<MallocLayout:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib6Common8Mallocng?MallocInv_hints9nest_rankC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6of_natI69OSSVerify5KrLib6Common8Mallocng=MallocInv_ops2FR00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng:MallocTree6ms_memC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface:aslot_fail00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface8aslot_vm00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface8aslot_ok00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5cslot0>C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5a_ctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8a_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notI47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6a_metaC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7mt_roleC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5mrole04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5mt_scC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7mt_lastC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs9mt_strideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs9mt_maplenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZI47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib6Common8Mallocng9MallocOps<m_alloc_slotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface<aslot_noroomC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface;aslot_growSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface=aslot_noroomSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface>aslot_had_idleC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6astate00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng:MallocTree6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib6Common8Mallocng9MallocOps3wm1C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs8meta_rec00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7slot_st00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5mrole00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7slot_st02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng;MallocTreeW5wmode01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng;MallocTreeW5wmode00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng;MallocTreeW5wmode03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng;MallocTreeW5wmode02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6a_liveC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs3domC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7a_areasC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7a_pagesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7a_xmapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mt_w32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6mt_memC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib6Common8MallocngEMallocInv_ameta_iface5spareC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundk69OSSVerify5KrLib6Common8MallocngEMallocInv_aslot_iface:aslot_keep01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs5mrole03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7slot_st01C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs4w_scC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_r".
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record aslot_keep (A A' : astate) (sc : Z) (m0 : word -> option byte) : Prop := {
  (* [comment removed for export] *)
  ak_live : a_live A' = a_live A;
  (* [comment removed for export] *)
  ak_dead : forall x mt, a_meta A x = Some mt -> mt_role mt = RDead -> a_meta A' x = Some mt;
  (* [comment removed for export] *)
  ak_dom : forall x, dom A x -> dom A' x;
  ak_newdom : forall x, dom A' x -> dom A x \/ m0 (Z_to_bv 64 x) = None \/ (exists pg, (In pg (a_areas A') \/ In pg (a_pages A')) /\ pg <= x < pg + 4096);
  (* [comment removed for export] *)
  ak_act : forall c, c <> sc -> nest_rank c <= nest_rank sc -> a_active A' c = a_active A c;
  (* [comment removed for export] *)
  ak_xmaps : a_xmaps A' = a_xmaps A;
  (* [comment removed for export] *)
  ak_grp : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib' sl', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl' /\
      mt_w32 mt' = mt_w32 mt /\ mt_mem mt' = mt_mem mt /\ length sl' = length sl /\
      (forall j st, nth_error sl j = Some st -> st <> SIdle -> nth_error sl' j = Some st);
  (* [comment removed for export] *)
  ak_acct : (a_areas A = [] \/ 4 - nest_rank sc <= spare A) ->
    (a_areas A' = a_areas A /\ spare A - (4 - nest_rank sc) <= spare A') \/
    (a_areas A = [] /\ (exists pg, a_areas A' = [pg]) /\ 100 - (4 - nest_rank sc) <= spare A')
}.

(* [comment removed for export] *)
Record aslot_fail (A A' : astate) (sc : Z) (m0 : word -> option byte) : Prop := {
  af_keep : aslot_keep A A' sc m0;
  af_slots : forall x mt aib sl, a_meta A x = Some mt -> mt_role mt = RGroup aib sl ->
    exists mt' aib', a_meta A' x = Some mt' /\ mt_role mt' = RGroup aib' sl;
  af_grp_back : forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    exists mt aib, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl';
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  af_acct0 : (a_areas A' = a_areas A /\ spare A <= spare A') \/
             (spare A < 4 - nest_rank sc /\ (exists pg, a_areas A' = a_areas A ++ [pg]) /\ 100 <= spare A')
}.

(* [comment removed for export] *)
Record aslot_ok (A A' : astate) (sc req g idx : Z) (m0 : word -> option byte) (s' : mstate) : Prop := {
  ao_keep : aslot_keep A A' sc m0;
  (* [comment removed for export] *)
  ao_grp_back : forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl) \/
    x = g \/ (x <> g /\ mt_sc mt' < 48 /\ nest_rank sc < nest_rank (mt_sc mt'));
  (* [comment removed for export] *)
  ao_idle : forall mt aib sl, a_meta A g = Some mt -> mt_role mt = RGroup aib sl -> nth_error sl (Z.to_nat idx) = Some SIdle;
  (* [comment removed for export] *)
  ao_gfresh : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (forall mt aib sl, a_meta A g = Some mt -> mt_role mt <> RGroup aib sl) ->
    idx = 0 /\ sl' = STaken :: repeat SIdle (Z.to_nat (mt_last mt'));
  (* [comment removed for export] *)
  ao_nonest : 2032 < 16 * size_class sc -> forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' -> x <> g ->
    exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl;
  (* [comment removed for export] *)
  ao_single : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    (forall mt aib sl, a_meta A g = Some mt -> mt_role mt <> RGroup aib sl) ->
    38 < sc -> sc mod 4 <> 3 -> usage_of A sc = 0 ->
    (16384 <= page_round_up_Z (req + 20) \/ page_round_up_Z (req + 20) < 16 * size_class sc + 16) ->
    mt_last mt' = 0 /\ 0 < mt_maplen mt' /\ mt_stride mt' + 16 = page_round_up_Z (req + 20);
  (* [comment removed for export] *)
  ao_zero : forall mt' aib' sl', a_meta A' g = Some mt' -> mt_role mt' = RGroup aib' sl' ->
    mt_stride mt' < 16 * size_class sc ->
    forall a : word, slot_start mt' 0 <= u a < slot_end mt' 0 -> ms_mem s' a = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  ao_acct1 : 2032 < 16 * size_class sc ->
    (a_areas A' = a_areas A /\ spare A - 1 <= spare A') \/
    (spare A < 4 - nest_rank sc /\ (exists pg, a_areas A' = a_areas A ++ [pg]) /\ 99 <= spare A')
}.

(* [comment removed for export] *)
Record aslot_vm (A : astate) (sc : Z) (s s' : mstate) : Prop := {
  av_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s'));
  av_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true -> region_free (vm_noaccess (ms_vm s')) b sz = true;
  av_budget : (a_areas A = [] \/ 4 - nest_rank sc <= spare A) ->
    vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s) + (4 - nest_rank sc) * 2^21
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition refusal (h : VmMaps) : Prop :=
  exists len, 0 < len <= 2^21 /\ forall a, mmap_grant_ok MMrw h a len = false.

(* [comment removed for export] *)
Definition aslot_noroom (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) : Prop :=
  (4 <= spare A -> refusal (ms_vm s)) /\
  (a_areas A = [] ->
     ~ (vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s) /\
        (0 < a_ctx A KAac \/ exists a, grant_ok_na_vm (ms_vm s) a 8192 = true))
     \/ exists h2, am_delta (ms_vm s) h2 /\ refusal h2).

(* [comment removed for export] *)
Definition aslot_had_idle (A : astate) : Prop :=
  exists x mt aib sl j, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_sc mt < 48 /\ nth_error sl j = Some SIdle.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aslot_growS (sc : Z) (A A' : astate) (s s' : mstate) : Prop :=
  sgrow (5 - nest_rank sc) ((4 - nest_rank sc) * 8192 + grp_cap sc) (4 - nest_rank sc) A A' (ms_vm s) (ms_vm s') /\
  (* [comment removed for export] *)
  pgrow (acostS sc) A A' (ms_vm s) (ms_vm s').

(* [comment removed for export] *)
Definition aslot_noroomS (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (sc : Z) (A : astate) (s : mstate) : Prop :=
  snoroom sp0 argv envp cb (4 - nest_rank sc) ((4 - nest_rank sc) * 8192 + grp_cap sc) (4 - nest_rank sc) 0 (grp_cap sc) A s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition alloc_slot_specW : Prop :=
  forall (fuel : nat) (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (sc req : Z) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    0 <= sc < 48 -> 0 <= req -> req + 4 <= 16 * size_class sc ->
    4 - nest_rank sc <= Z.of_nat fuel ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_fail A A' sc (ms_mem s) -> aslot_vm A sc s s' ->
       (W = WOk -> aslot_noroom sp0 argv envp cb A s) ->
       (* [comment removed for export] *)
       aslot_growS sc A A' s s' -> (W <> WFail -> aslot_noroomS sp0 argv envp cb sc A s) ->
       tsall W (K wm1 s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (g idx : Z) mt aib slots,
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_ok A A' sc req g idx (ms_mem s) s' -> aslot_vm A sc s s' ->
       a_ctx A' (KActive sc) = g -> g = hd 0 (a_active A' sc) -> a_active A' sc <> [] ->
       a_meta A' g = Some mt -> mt_role mt = RGroup aib slots -> mt_sc mt = sc ->
       0 <= idx <= mt_last mt -> nth_error slots (Z.to_nat idx) = Some STaken ->
       req + 4 <= mt_stride mt ->
       (16 * size_class sc <= mt_stride mt \/ (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z (req + 20))) ->
       (W = WFail -> aslot_had_idle A) ->
       (* [comment removed for export] *)
       aslot_growS sc A A' s s' ->
       tsall W (K (Z_to_bv 64 idx) s') P) ->
    tsall W ((x <- m_alloc_slot fuel sp (Z_to_bv 64 sc) (Z_to_bv 64 req) ;; K x) s) P.

(* [comment removed for export] *)
Definition alloc_slot_spec : Prop :=
  forall (fuel : nat) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (sc req : Z) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    0 <= sc < 48 -> 0 <= req -> req + 4 <= 16 * size_class sc ->
    4 - nest_rank sc <= Z.of_nat fuel ->
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_fail A A' sc (ms_mem s) -> aslot_vm A sc s s' ->
       tsafe (K wm1 s') P) ->
    (forall s' A' (g idx : Z) mt aib slots,
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> aslot_ok A A' sc req g idx (ms_mem s) s' -> aslot_vm A sc s s' ->
       a_ctx A' (KActive sc) = g -> g = hd 0 (a_active A' sc) -> a_active A' sc <> [] ->
       a_meta A' g = Some mt -> mt_role mt = RGroup aib slots -> mt_sc mt = sc ->
       0 <= idx <= mt_last mt -> nth_error slots (Z.to_nat idx) = Some STaken ->
       req + 4 <= mt_stride mt ->
       (16 * size_class sc <= mt_stride mt \/ (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z (req + 20))) ->
       tsafe (K (Z_to_bv 64 idx) s') P) ->
    tsafe ((x <- m_alloc_slot fuel sp (Z_to_bv 64 sc) (Z_to_bv 64 req) ;; K x) s) P.

Lemma alloc_slot_spec_of_W : alloc_slot_specW -> alloc_slot_spec.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_aslot_iface ()) ["WithLayout"] "h02A'h12s'h22H1h32H2h42H3h52H4h62_Hh73_H0h83aibh91gh:3idxh;2mth<5slotsh=1Ah>1Dh?3H10h@3H11hA3H12hB3H13hC3H14hD2H5hE2H6hF2H7hG2H8hH2H9hI2HFhJ3HIIhK2HShL2HWhM4HfithN5HfuelhO4HreqhP3HschQ1KhR1PhS1RhT3_H1hU4argvhV2cbhW4envphX4fuelhY3reqhZ1sh[2sch\2sph]3sp0h^1xp;1p;9p;2p;5p;4p;3p;8p;6p;7p-1g0000R0p4p710p8g000GR1p61651111001R2p1001bp4p710p8P2g002hR3p4p710R4p8P2g003iR5p4p7210R6p8g004nR7p6164111001R8P4p8P8g006HR4p4p710p8P8g007WR9p4p710p8P8P6p8P8g008fR6p4p710p8P8P2p8g009kj10Tg00:Pj1RTg00:nj1DTg00;Qj1<TP3j1dTg00<1l96Tg00=@j22Tg00=\j1ITg00>Aj1=Tg00>_j2JTg00?;j25Tg00?Vj24Tg00@3j1@Tg00A?j2>Tg00A\j1bTg00Bjj2`Tg00CGj1\Tg00Cgj5:Tg00Dnj18Tg00F4j4LTg00GKj47TP6j3KTg00H`j8HTg00J5j1GTg00K@j2FTg00LIj29TP0j3ETg00MUj1YTg00N5j31Tg00NOj1?Tg00Nhj1CTg00OJj2XTg00PTj2BTg00Q6j1WTg00RAj2VTg00SLj1UTg00TUj1ATg00U`j1STg00V@j3TTg00V^j1QTg00Wkj1cTg00Y8j1PTg00Z6j2OTg00ZPj2;Tg00[6j5aTP5j5_Tg00\Aj6]Tg00]Xj5MTg00^nj7[TP4j5NTg00`Fj1^TP9j4ZTg00a_R9f1R4f0R531p=3g00b=g00b\R0#0R6#0R3#0R2#0R:#0#0#RR;#DR<%R2#D#<R2#<R=%<9R>g00cAR?g00dMR@f;RA#d\<p-0\@\Ap,2MLRBp,2HTRCPAf:RDf9REf8RFf7RGf6RHf5RIM96g00eURJf4RK'2RL%I0#0#0#0#0#=,JK'5%=3R3,4I%=:R:%@H'>'2%bG,`3fAR0#\'2PBPCfBRMP0f@RNf?ROf>RPP5P4M96PBPPf=RQP4f2RRD:POPRf<RS%8PCLPNPQPOPKC7fGRTPSg00f3RUPIO2;KA[[[[^0?^1@g00g5RVg00hCRW#<RXPBPCfHRYPTfFRZfER[fDR\PIPHM96PBP\fCR]PHPGD:P[PGPMP0PHPI%8\PFGHPZP]P[PEC7%G\,FE/3F19D[9E9J,3E19AZ%Y9R^51>#?%CV1XSA1BVE31R_g00iP%WD1VEF31R`%UARafIRb'312JQ%AS,2Q'5Rc%CW%SP9TWAg00j[,BW31RWfKRd/43%QPRe'2fMRf#@,>:%QORg'2%AO=19JRh%cO,JJRi14g:RjfLRk%I6#0#0#=R6'4#P'3'5'5'OfWPk1;;0P\O2;Kd[[[[[[[[[[[[[[]<^89];^:9^99^0?^1@P]P<P]PBP\PA1;;D1;;EDaPEP5O1X^<PSD_PGP[P\g00khRlP]PMP0PNPOPPPQPSPAPDPEPFPGPHPIPKf3RmPRPBPCP\P]PMP0PNP5P4M96PBPNPOP4PRD:P0PRPP%8NCLPMPOP0PKC7g00m0R4g00n871lPbPYPTPZP\P]E][P0P\PIP]PHDMg00o@914lR4#?PdfJRdPbPYP]PZP[F[[PkPlP0PUPFO2PNPDPFPGPHPIPKPmO6DNWTW7W6W5W4W3W2X0?X1@PBPCPbPYPTPZP[PIPHM96PBP[P\PHPGD:PZPGP]PMPHPI%8[PFGHPTP\PZPEC7%G[,FE/3F19DZ9E9J,3E19AT=1>^#?13ad14k3/2efNRe#@,>:/2g14f6#P,3j,5i,5h'OfSRh#^\4fPPhP\fRP[DMfZPlfO1;;]PZO2PePTPZP[P\P]PMP0PNPOPPPQPSPAPDPEPFPGPHPIPKPmPROEDNW7W6WCWBXAWX@cW?XH`XG_WFWEWDW5W4W3W2X<XX89X;VX:9X99X0?X1@OFCZWKWIWNWMXOLWPWJWRWQXY9X[9X\<WZW=W>XV2XW=WUW]XS8WXP7eXL1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma aslot_keep_refl : forall A sc m0, 0 <= nest_rank sc <= 3 -> aslot_keep A A sc m0.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_aslot_iface ()) ["WithLayout"] "h01Hh11jh22sth31xh42H0h53sl'h64__p1h74__x1h84__x2h94aib'h:2mth;2pgh<1Ah=2Hrh>3Hr'h?2Hxh@2_HhA7__arithhB4__ffhC8__varmaphD5__withE3aibhF1chG2m0hH3mt'hI2schJ2slp;1p;2p;3p;4p;6p;7p;8p;<g009kj19Tg00:Pj1OTg00:nj1LTg00Nhj1CTg00A\j1HTg00=@j22Tg00=\j1PTg00>Aj1FTg00?;j21Tg010Hj1]Tg011Rj25Tg00OJj2;Tg00PTj26Tg00N5j30Tg00Q6j18Tg011lj2VTg00ZPj2eTg0133j1QTg013Uj1GTg014`j3XTg0157j1`Tg00Z6j2ITg00?Vj2_Tg00>_j2^Tg016Bj2?Tg016\j3NTg00NOj1MTg00;Qj1DTg00LIj2\Tg0176j2[Tg017Vj1ZTg00RAj2BTg018aj1ATg019kj1@Tg01;5j2>Tg01;Uj4=Tg01<0j4KTg00MUj1YTg00Bjj27Tg01<Jj1JTg01=Zj3qTg01>:j2pTg01>Xj1oTg01?6j4nTg01?Tj1hTg01@2j1gTg01@]j6fTg01AAj2TTg01Adj2RTg01BGj4WTg01C2j7dTg01CVj3UTg01D9j8cTg01D]j2bTg01E?j2iTg01Ekj3aTg01FJj4jTg01G<l<kTg00V@j3lTg01HSj7mTf0R0#9#9p=:f2R1f1R2/10'1p=Eg00a_R3?020p=4g00hCR4?l20p=<f3R5?012/10p=3P2g01I7R6g01IVR7P7g01J6R8P0g01JVFmp=Sg00cAg00b\R9#9R:#9R;#9R<#9#:R=#OR>#L%O<#LR<#CR?[g00eUR@%H2RA'2%P9RB#FRC,2A'1P5P5P1P2%C3\3%]5'5g00g5RD%CDREf5RF/;216D030g00iPRG%82g01K630P2W4W0W:X33f4RH/V0RIP0W0X331VF2P51e>2O1%Q<50?f6R?#G9X30%`?9X30'I1201%:=#:#:#F,_0,^13EX;3,?3'I;N0X0IX331405#M%HHRI,2A%D3RA1\?1'5W4W0XF31[33#D%Z5'5%D4R=f7R</;516D1R>50E%851B1250GPDPEf<f8';P>PG%811B20R>%A1%A<'4%@1%@<'4g00b=RJ1>40RK1>4F%C4RL1<<21640RM30g01LA9042#MRN1<H51641RO50L[RP[^24^1JC33EC3C3X5=,?=X93,?3XHDPHP3PEf;/;<16D?PG%8?P>%A?R>/4>%@?R>/4>PJPK1>4H1<?2=0LMPP[^24^1JC33EC3C3X5=,?=X93P5P=PEf:/;?16DFPG%8F1BH0%AFR>/4>%@FR>/4>PJPK1>451<F2=0LMPP[^24^1JC33EC3C3X5=P1f9/;F16DH50E%8H1B5150GRG%AHRE/4ER=%@HRP/4PRK1>41R>=0J>R<1<H2=0LMRM1<?5=0LO\N[^24^1JRO'1RL'1R?'1RQ'1P2PGPQP0P=P?153EPKPL153PP<PO15J>P2X4NX0MX24X1JC=C=C=C=C=CKCKCKW>W?WJXE3X:DX33%G5%Y3RD50A%F;R;%H1'7%J5'2'I%GHRJ=0AJR4%JHRM%H5,7;R5'7/2MRN'1PAPJPD%GFAq30D50AX;3,?3%:B#P#:#F/75/2M'1C3P4PN15AJp-0RJg01MNRA#Y%DAP31p31P2%o3Cn%h3%g3RAP6P7P7P8PAP6P7P7P8PAP6P7P7P8PHEfP31T3:R:g01N:RH1R3CCW,SAFd%Q7P31T39R91R3;=U3:5U3PHP9CW,SAGc1bA8P0P1g01NaRAg01OAR8'51i01=0A8dAa3@2CjbBbCbDX73X83W6122C,1117;1,72/22[^73^83^6JP012@IPI%JFP1O4bAC=3NW@M<kW=WGXI3W<o"). Qed.

Lemma aslot_had_idle_transfer : forall A A',
  (forall x mt' aib' sl', a_meta A' x = Some mt' -> mt_role mt' = RGroup aib' sl' ->
     exists mt aib, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl' /\ mt_w32 mt = mt_w32 mt') ->
  aslot_had_idle A' -> aslot_had_idle A.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_aslot_iface ()) ["WithLayout"] "p'0h01jh13aibh21Hh32slh42mth51xi001xh64aib'h73mt'h83sl'h91Ah:2A'h;2Hbh<2Hjh=2Hrh>3Hr0h?3Hsch@2HwhA2HxhB3Hx0hC1ehD1zp;1p;2p;4p;6p;3g00;Qj1VTg00Nhj1QTg00RAj22Tg00Q6j1?Tg018aj1:Tg016BR0j21Tg00`Fj15Tg00=\j1UTg009kj1FTg00>Aj1TTg00PTj2PTg00?;R1j24Tg01Oaj1JTg00>_j2DTg01;Uj4GTg01Pij6RTg01<0j4ATg00OJj2ITg00N5j39Tg00SLj1HTg00V@j3OTg00g5R2f0R3'Pp=3f3R4f2R5f1R6'I;93p=@g00iPR7%?6;93p=Cg00a_R8%:3796p=712569974/43p==f4R91I45;96/43p=01183p=8%H6/D3p=Bg00hCR:?O56=943p=<1463,45p=Eg00b=R;/13p=6%H5/D6/43p=;A9756/43p=N%?5=976/43p=>AO:63p=MA9563,44p=L12639975p=K1D56/43p=Sg00cAR7%V:R<%Q2R=P9P4%35R>C@1256R?,C4R@P=f9RAf7RB%36RC%?6RDP3P9%:6REf6RF'7C=D0X18#8X42,12[[]8^68^72^58%56P0P8P=PBP9%34RGg00b\#U#F#F#F#F#TRH,B4%Q:RIP6P3g01LA,P:R:C<RJ5E@R@D0X0;#6X3<,1<X18#8X42,12X58%59P3P=PAP9PGP@D0X0;#6X3<,1<X18#8X42,12P0P2P=f:RKf5RLPGP@D0X0;#6X3<,1<X18#8X42f8RM#5P3P=f<RNPBPGP@D0X0;#6X3<,1<X18#8P0P8P=f=ROPM%39RP%?9RQA;9HJ7N?D0X0;#6X3<,1<X18%5NP3P=f?RRPK%3FA;FHJ9>F?D0X0;#6X3<,1<P0P<P=f@RSf;RT%3BRU1246A;BHJ5>BD0X0;#6X3<%5SP3P=fBR4PO%3A%?ARVPLP6A;AHJC=D0X0;#6P0P;P=fCRWf>RX%3K12F5PIP5P3P:C<9;KH5>KD0X0;fDRF#5P3P=fERYPS%3N12M9PIP9P3P:C<9;NH5>ND0P1P=fFRZfAR[%3OR\C@%?OR]PAPL1BOHR^PI1ML6P:CLC=fHR_#5P3P=P_PW%3RR_C@%?SR`PNPM1BSHRaPI1MM9P:CLC=P112OA,C[PIPAPLP:C<9;[HfLRb#5P312RT,CWPIPNPMP:C<9;FHP11BYHPIPOPAP:C<fPRc#5P3fGRd/BHPIPSPNP:C<fQRefMRffIRgPYP[PAPLO6P=fURYfORhPCPDP3PWfK,7EC=D0X18#8X42,12P0P2P=fVRWPcPCPDP3PF17EbC=D0X18#8X42%5YP3P=fXRbfRRFPCPDP3PZfNRZ,7EC=D0X18#8P0P8P=fYR0fSREP>123d%:5/7h5>5D0X18%50P3P=f[PYPPPQP3Pg%:9/7eC=D0P1P=f\PW%3LC@fJ,26%:L/7F5>Lf]#5P3P=f^RePbPUC@129f%:M/7Y5>MP1AKVLZ%:A/7WfaRW#5P312Bc,CT%:N/70P8P=fiP9PGP@D0X0;#6X3<,1<X18#8X42,12X58PeP2P=fhfbPGP@D0X0;#6X3<,1<X18#8X42POP8P=fgPW%3S14aJ9N`?D0X0;#6X3<,1<X18PAP<P=fff`P_12T6A;RHJ5>RD0X0;#6X3<PFP;P=fef_%3XC@RR12KE,CXRKPIPEP3P:C<9;XH3EX0;PZP8fZ#:RX%J3PIPEPhP:C<7SH9ERKXD8P=fdPeP\C@R\AK]AFR]%JX/DHRHPIPFPZP:C<R:'4RZ'4PLP]PZP6PHP:P4P[CGCGCG%:OP3ER14^:9E\]eCACACACACAW@W>P6P3O2n2001000000121000000W2WBP6P3O2n2001000000121000000W2X18P6P3O2n2001000000121100000W2X42P6P3O2n2001000000121100000bCW<W?P6P3O2n2001000000121000000W2W=P6P3O2n2001000000121000000W2WAP6P3O2n2001000000121000000W2X0;P6P3O2n2001000000121100000W2X8<P6P3O2n2001000000121100000W2X68P6P3O2n2001000000121100000W2X72P6P3O2n2001000000121100000W2X58P6P3O2n2001000000121100000W2W;X:7W9o"). Qed.

End WithLayout.
