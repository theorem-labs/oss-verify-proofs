(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0StepLib As0Tables
     ArtMem ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b BatByteCell_b BatCARSpec_b BatAlloc3Pure_b BatDepot_b BatUnwind_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocH_b BatWrapMallocA_b BatWrapMallocX_b BatWrapMallocC_b BatWrapMalloc_b
     BatLeaf_b BatAllocG_b BatPoison_b BatRzLog_b BatAllocA_b BatDepotA_b BatMallocTop3_b BatAllocate3A16_b BatAlignedTop3_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5fac4_60344_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_alloc3_fp_rs16 : forall sp t spb ris qs c km ab rz n rs l2 blk x,
  art_alloc3_fp sp t spb ris qs c km ab rz n rs l2 blk x -> art_alloc3_fp sp t spb ris qs c km ab rz n (rs + 16) l2 blk x.
Proof.
  intros sp t spb ris qs c km ab rz n rs l2 blk x F. unfold art_alloc3_fp in *.
  assert (E : (rs + 16) / 8 = rs / 8 + 2) by (replace (rs + 16) with (rs + 2 * 8) by lia; apply Z.div_add; lia).
  rewrite E. destruct F as [F|[F|[F|[F|F]]]]; [left; exact F|right; left; exact F|right; right; left; exact F|right; right; right; left; lia|do 4 right; exact F].
Qed.

(* [comment removed for export] *)
Definition art_al16_post (L : asan_layout) (ar : asan_run) (scfg : SpuriousCfg) (HI : asan_iface) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet) : Prop :=
  forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)) (u : Z),
    getr R' 10%bv = Z_to_bv 64 u ->
    regs_preserved R R' ->
    ablock_range L ar u n -> blocks_apart u n LB -> fframes_apart u n (FF ++ LK) ->
    defined M' u n -> shadow_blk M' u n ->
    aheap_pres L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_aligned L) M M' ->
    model_rt model model' -> incl A A' -> MInv A' model' ->
    ri_inv HI ((u, n) :: LB) FF LK (adebit L cr n) A' M' (vml_of model') ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K.

(* [comment removed for export] *)
Definition art_aligned16_small_spec (L : asan_layout) (ar : asan_run) (scfg : SpuriousCfg) (HI : asan_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n : Z) (K : ShapeAlg.TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= 4096 -> n mod 16 = 0 -> acredit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L ar M (hl_scr_aligned L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    art_al16_post L ar scfg HI fx R M model LB FF LK cr A n K ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_aligned_thunk : forall regs (M rom : word -> option byte), msteps ASEGS (mkst regs (0x79820 : word) M rom) (mkst regs (0x79f60 : word) M rom).
Proof. intros regs M rom. stepj F_79408 D_79408. apply mst_refl. Qed.
End FPX.

Section Entry.
Variable FSG : Type.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_wa16_entry :
  forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
         (Sp n rl rz qz rs qr qn m8 q16 km top bot : Z) (kb : nat),
    let c := AsanTab.class_id (rs + 16 + rz) in
    let cl := g_cls FSG G c in
    let w := art_ca_cptr c cl in
    let ab := rn_spb rn + c * 2 ^ 32 + w * 16 in
    art_alloc_rep FSG rn G LB Mr -> cellA Mr 0x104c0 1 4 ->
    getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 16 -> getr R 11 = Z_to_bv 64 n ->
    8 <= n -> n mod 16 = 0 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
    n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> rs = 16 * q16 -> n <= rs <= n + 7 -> rs + 16 + rz <= 65536 ->
    rn_HI rn + 4096 <= Sp - 4096 -> Sp <= 2 ^ 47 -> Sp mod 16 = 0 ->
    top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
    wrA Mr (Sp - 4096) 4096 -> readable8 Mr Sp top ->
    g_depot FSG G = Datatypes.S kb -> cl_mu cl = 262144 * km ->
    (cl_cache cl = [] -> art_cls_needs_populate c cl = true ->
       cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912) ->
    art_evok_list EVOK log (art_ca_events (rn_spb rn) c cl) ->
    (forall regs' (Mr' : word -> option byte) (b1 : Z),
        getr regs' 10 = Z_to_bv 64 (ab + rz) -> getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
        (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
        art_malloc_out rn Mr Mr' Sp n rz qz (rs + 16) (qr + 2) qn m8 km kb cl b1 ->
        Q (log ++ art_ca_events (rn_spb rn) c cl) (mkst regs' raw0 Mr' rom)) ->
    aruns ASEGS EVOK GR Q log (mkst R (0x79f60 : word) Mr rom).
Proof.
  intros Q log R Mr rom raw0 rn G LB Sp n rl rz qz rs qr qn m8 q16 km top bot kb c cl w ab
         REP C1046 H1 Hret H2 H4 H10 H11 Hn Hn16 Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W RD0 Edep Emu Room EV K.
  pose proof (AsanTab.class_id_ok (rs + 16 + rz) ltac:(lia)) as (Hc & _). fold c in Hc.
  destruct REP as (ROK & ST & TH & (PH & PRIM & Wsh) & CH & _ & _ & DEP & _).
  rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & _ & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16).
  destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & T7). rewrite <- Etop in T3. rewrite <- Ebot in T4.
  destruct (PRIM c Hc) as (RC & OK & Hin & _). fold cl in RC, OK, Hin.
  specialize (CH c Hc). cbv zeta in CH. destruct CH as (I & II & _ & III). fold cl in I, II, III.
  unfold art_rt_depot in DEP. rewrite Edep in DEP.
  pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & _ & _ & Hfor & _).
  assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + c * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
  apply (art_aligned16_3 EVOK GR Q log R Mr rom raw0 Sp (rn_HI rn) n (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_loff rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
           (rn_l2 rn) (rn_blk rn) top bot rl rz qz rs qr qn m8 q16 kb (g_inited FSG G) cl
           H1 Hret H2 H4 H10 H11 Hn Hn16 Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
           Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs W RD0 Wt Wsh RO C1046 RZ L T PC C1 C2 C3 C4 C5 C6 C8 C10 C11 C12 T7 T1 T2 C13 C14 T6 T5 T3 T4
           PH RC OK Hin Emu Room EV).
  - (* [comment removed for export] *)
    intros y Hy. pose proof (I (8 * y) Hy ltac:(replace (8 * y) with (y * 8) by lia; apply Z_mod_mult)) as B. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  - (* [comment removed for export] *)
    intros v Hv. pose proof (proj1 (Forall_forall _ _) Hfor v Hv) as V. specialize (III v V). rewrite (II v Hv) in III. destruct III as (_ & B).
    replace (rn_spb rn + c * 2 ^ 32 + 16 * v) with (rn_spb rn + c * 2 ^ 32 + 8 * (2 * v)) in B by lia. rewrite ES in B.
    apply art_cell1_of_byte; [lia|exact B].
  - exact DEP.
  - exact DR.
  - intros regs' Mr' b1 P10 P2 P1 PK GRW FR DI' PH' RC' OK' CP' Hb1 Hty CL1 CL3 CL4 CL2 SAB SHZ SHP PSH LCH.
    apply (K regs' Mr' b1 P10 P2 P1 PK). unfold art_malloc_out. fold c. fold cl. fold w. fold ab.
    split; [exact GRW|]. split; [intros x N; apply FR; intros F; apply N; [left; exact F|right; exact (art_alloc3_fp_rs16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F)]|]. split; [exact DI'|]. split; [exact PH'|]. split; [exact RC'|]. split; [exact OK'|]. split; [exact CP'|].
    split; [exact Hb1|]. split; [exact Hty|]. split; [exact CL1|]. split; [exact CL3|]. split; [exact CL4|]. split; [exact CL2|]. split; [exact SAB|].
    split; [exact SHZ|]. split; [exact SHP|]. split; [intros E1 E2 j Hj Hex; apply (PSH E1 E2 j Hj); intros X; apply Hex; revert X; clear; repeat match goal with x := _ |- _ => subst x end; cbv zeta; intros X; lia|exact LCH].
Qed.
End Entry.

Section Wrap.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLscr : hl_scr_aligned L = 4096.
(* [comment removed for export] *)
Hypothesis H1046 : forall G LB M, art_alloc_rep FSG rn G LB M -> cellA M 0x104c0 1 4.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, 0x211b08 <= a < 0x661b28 -> hl_rt_static L a.
Hypothesis HLk : 3 <= hl_k_per_malloc L.
Hypothesis HLlin : 0 <= hl_b_lin L.
Hypothesis HLov : 2 ^ 20 <= hl_b_overhead L.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
Context {fx : PropExec.FPState}.
#[using="Halloc Hwx STATIC HLsegs HLscr H1046 HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN"] Theorem art_wrap_aligned16_primary :
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
         (n rl rz qz rs qr qn m8 q16 : Z) (K : ShapeAlg.TSet),
    art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    getr R 10 = Z_to_bv 64 16 -> getr R 11 = Z_to_bv 64 n -> 0 < n -> n mod 16 = 0 ->
    rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 -> n = 8 * qn + m8 -> 0 <= m8 <= 7 -> rs = 8 * qr -> rs = 16 * q16 -> n <= rs <= n + 7 ->
    rs + 16 + rz <= 65536 ->                                                          (* [comment removed for export] *)
    acredit_ok L cr n -> getr R 4 = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1) ->
    astack_ok L (rn_ar rn) M (hl_scr_aligned L) (U (getr R 2)) ->
    art_al16_post L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn) fx R M model LB FF LK cr A n K ->
    srealizes ASEGS scfg (mkCfg (mkst R (0x79820 : word) M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A n rl rz qz rs qr qn m8 q16 K RI Hhalt HMI H10 H11 Hn Hn16 Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim ACR H4 Hret AST POST.
  assert (Hn8 : 8 <= n). { pose proof (Z.div_mod n 16 ltac:(lia)) as D. rewrite Hn16 in D. clear - D Hn. lia. }
  assert (Ers' : rs + 16 = 8 * (qr + 2)) by (clear - Ers; lia). assert (Hnrs' : n <= rs + 16) by (clear - Hrs; lia).
  destruct RI as (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in REPr, BV, LZ, EG.
  pose proof (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hhalt HMI) as B0.
  pose proof REPr as (ROK & _ & _ & (_ & PRIM & _) & _). pose proof ROK as ROK'. rok_open ROK'. pose proof GEO as GEO'. geo_open GEO'.
  set (Sp := U (getr R 2)) in *. assert (H2 : getr R 2 = Z_to_bv 64 Sp) by (unfold Sp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite HLscr in AST. destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof CLI as (_ & _ & _ & _ & CS1 & CS2 & CS3 & CS4 & CS5 & CS6). rewrite HIeq in CS1, CS2.
  set (c := AsanTab.class_id (rs + 16 + rz)). pose proof (AsanTab.class_id_ok (rs + 16 + rz) ltac:(lia)) as (Hc & _). fold c in Hc.
  set (cl := g_cls FSG G c). destruct (PRIM c Hc) as (_ & OK & _ & (km & Emu) & _). fold cl in OK, Emu.
  pose proof CRED as (CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7 & CR8). destruct ACR as (AC1 & AC2).
  destruct (g_depot FSG G) as [|kb] eqn:Edep; [exfalso; cbn in CR6; lia|].
  destruct (CR8 c Hc) as (RM1 & RM2). fold cl in RM1, RM2.
  pose proof (art_nq_nonneg (g_qt FSG G ++ g_qg FSG G)) as Hnq0. unfold art_nret in CR7, RM2.
  assert (Room : cl_cache cl = [] -> art_cls_needs_populate c cl = true -> cl_mu cl + 262144 <= 3758096384
                 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912).
  { intros _ _. apply (art_room_of_credit c cl 1 Hc OK ltac:(lia)); lia. }
  pose proof OK as (_ & (Hau0 & Haumu) & _).
  assert (EV : art_evok_list (art_EVOK (art_RES rn) BUDGET LENMAX KMAX) (g_log FSG G) (art_ca_events (rn_spb rn) c cl)).
  { apply (art_ca_evok (art_RES rn) BUDGET LENMAX KMAX (g_log FSG G) (rn_spb rn) (rn_qs rn) (rn_kbase rn) c cl km Hc OK Espb ltac:(lia) ltac:(lia)
             ltac:(left; reflexivity) Emu ltac:(lia) Room). assert (0 <= hl_b_lin L * n) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (OKpre : art_cls_ok c (art_ca_pre c cl)) by (apply art_cls_ok_ca_pre; assumption).
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  set (Mr0 := mrestrict (mkH (m_vm_lazy model) A) M) in *.
  assert (W0 : wrA Mr0 (Sp - 4096) 4096). { apply (art_stack_wr FSG rn G A (m_vm_lazy model) M Sp 4096 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). rewrite <- HLsegs. exact SWR. }
  assert (RD0 : readable8 Mr0 Sp (ar_stack_top (rn_ar rn))). { apply (art_stack_readable FSG rn G A (m_vm_lazy model) M Sp (ar_stack_top (rn_ar rn)) ROK LZ ltac:(lia) ltac:(lia) SDEF). }
  assert (Hn1 : 1 <= n) by lia.
  set (raw0 := getr R 1) in *. set (w := art_ca_cptr c cl). set (ab := rn_spb rn + c * 2 ^ 32 + w * 16). set (u := ab + rz).
  assert (H4' : getr R 4 = Z_to_bv 64 (rn_tp rn)) by (rewrite <- HLtp; exact H4).
  set (Qm := fun (log' : list aev) (st : machine_state) =>
     exists regs' (Mr' : word -> option byte) b1, st = mkst regs' raw0 Mr' (seg_rom ASEGS) /\ log' = g_log FSG G ++ art_ca_events (rn_spb rn) c cl
       /\ getr regs' 10 = Z_to_bv 64 u /\ getr regs' 2 = Z_to_bv 64 Sp
       /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r)
       /\ art_malloc_out rn Mr0 Mr' Sp n rz qz (rs + 16) (qr + 2) qn m8 km kb cl b1).
  apply (aruns_srealizes_h ASEGS scfg Halloc Hwx MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BASE BUDGET LENMAX KMAX STATIC Qm K model A M model (g_log FSG G))
    with (log := g_log FSG G) (s := restrict (bhid A model) (mkst R (0x79820 : word) M (seg_rom ASEGS))) (A := A) (model := model);
    [ | | reflexivity | exact B0 | apply bmodel_rt_refl | apply bhist_refl ].
  2: { (* [comment removed for export] *)
    rewrite restrict_mkst. change (mrestrict (bhid A model) M) with Mr0.
    eapply ar_steps; [apply art_aligned_thunk|].
    apply (art_wa16_entry FSG _ _ Qm (g_log FSG G) R Mr0 (seg_rom ASEGS) raw0 rn G LB Sp n rl rz qz rs qr qn m8 q16 km (ar_stack_top (rn_ar rn)) (ar_stack_bottom (rn_ar rn)) kb
             REPr (H1046 _ _ _ REPr) eq_refl Hret H2 H4' H10 H11 Hn8 Hn16 Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim ltac:(lia) ltac:(lia) S16 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             W0 RD0 Edep Emu Room EV).
    intros regs' Mr' b1 P10 P2 P1 PK OUT. exists regs', Mr', b1. split; [reflexivity|]. split; [reflexivity|]. split; [exact P10|]. split; [exact P2|]. split; [exact PK|exact OUT]. }
  (* [comment removed for export] *)
  intros log' A' ms' model' B1 RT BH (regs' & Mr' & b1 & Est & Elog & P10 & P2 & PK & OUT).
  destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr). set (M1 := ms_mem ms') in *. rewrite Ems. subst Mr'.
  pose proof (art_mrep_new_shadow FSG rn G LB Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz (rs + 16) (qr + 2) qn m8 km kb b1 REPr Hn1 Erz16 Hqz En Hm8 Ers' Hnrs' Hprim ltac:(lia) Emu Edep OUT LIVE OKpre) as NSH.      (* [comment removed for export] *)
  destruct (art_mrep_bundle FSG rn G LB Mr0 (mrestrict (bhid A' model') M1) Sp n rz qz (rs + 16) (qr + 2) qn m8 km kb b1 REPr Hn1 Erz16 Hqz En Hm8 Ers' Hnrs' Hprim ltac:(lia) Emu Edep OUT LIVE OKpre)
    as (REP' & BA & FRL & NFPB & NFPW & NFPS & NFPI & GFS & GSH & GTH & NUM).
  fold c in REP', FRL, NFPB, NFPW, NFPS, NFPI, NUM. fold cl in REP', FRL, NFPB, NFPW, NFPS, NFPI, NUM. fold w in REP', FRL, NFPB, NFPW, NFPS, NFPI, NUM. fold ab in REP'. fold u in REP', BA.
  destruct NUM as (_ & Hfit & Hsz & Hw0 & Hwsz & Haumu' & Hmu3').
  set (FPL := art_malloc_fp_lin Sp (rn_t rn) (rn_spb rn) (rn_qs rn) c km w qz (qr + 2) n (rn_l2 rn) (rn_blk rn)) in *.
  set (cl' := art_cls_pop (art_ca_pre c cl)).
  pose proof REP' as (_ & _ & _ & (_ & PRIM' & _) & CH' & _).
  destruct (PRIM' c Hc) as (RC' & _). cbn [art_gs_malloc g_cls] in RC'. rewrite Z.eqb_refl in RC'. fold cl' in RC'.
  destruct RC' as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wfa' & Wu')).
  pose proof OUT as (GRW & _ & _ & _ & _ & _ & CPw & _). fold c in CPw. fold cl in CPw. fold w in CPw.
  destruct (art_wmc_mem FSG rn G A A' M M1 model model' log' Sp n rz qz (rs + 16) (qr + 2) km cl' ROK Hc OK Emu Erz16 Ers' Room eq_refl Elog BH GRW FRL Wu' Wfa') as (FRF & GRF & VIS).
  pose proof BH as (sfx & Esfx & INC & BH2 & _ & BH4 & BH5).
  assert (Esfx' : sfx = art_ca_events (rn_spb rn) c cl). { rewrite Elog in Esfx. apply app_inv_head in Esfx. symmetry. exact Esfx. }
  (* [comment removed for export] *)
  assert (LZ' : art_lazy_ok FSG rn (art_gs_malloc G (rn_spb rn) c w u n kb) A' (m_vm_lazy model')).
  { apply (art_wmx_lazy FSG rn G A (m_vm_lazy model) A' (m_vm_lazy model') c w u n kb LZ INC).
    - intros x Hx. exact (proj1 (BH2 x Hx)).
    - intros wd Hwd. destruct (BH4 wd Hwd) as [Hin|(len & r & Hev & _)]; [exact Hin|]. exfalso. rewrite Esfx' in Hev. exact (art_ca_events_no_null _ _ _ _ _ Hev).
    - intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. rewrite Esfx' in Hev. exact (art_ca_events_no_nr _ _ _ _ _ Hev).
    - intros x. cbv zeta. exact (VIS x). }
  (* [comment removed for export] *)
  specialize (CH' c Hc). cbv zeta in CH'. destruct CH' as (_ & _ & _ & III').
  assert (CPw' : art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG (art_gs_malloc G (rn_spb rn) c w u n kb) c)) w).
  { cbn [art_gs_malloc g_cls]. rewrite Z.eqb_refl. exact CPw. }
  specialize (III' w CPw'). cbn [art_gs_malloc g_st] in III'. rewrite !Z.eqb_refl in III'. cbn [andb] in III'. destruct NSH as (SHz & SHp).
  assert (SHu : shadow_blk M1 u n).
  { split; [intros j Hj; exact (art_byte_unrestrict _ _ _ _ (SHz j Hj))|intros Hm; exact (art_byte_unrestrict _ _ _ _ (SHp Hm))]. }
  assert (Hu1 : rn_spb rn + 2 ^ 32 + 16 <= u) by (unfold u, ab; lia).
  assert (Hu2 : u + n <= rn_spb rn + 2 ^ 37) by (unfold u, ab; lia).
  assert (DEFu : defined M1 u n).
  { intros i Hi. pose proof (art_wr_wview ASEGS (mrestrict (bhid A' model') M1) (rn_spb rn + c * 2 ^ 32) (cl_mu cl') ltac:(clear - G4 Hc; lia) ltac:(unfold cl'; cbn [art_cls_pop cl_mu]; clear - G2 G6 Eris Hmu3' Hc; lia) Wu' (Z_to_bv 64 (u + i))) as V.
    rewrite art_u_lit in V by (unfold u, ab; clear - Hi G1 G2 G4 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hsz Hrs Hqz Erz16 Hn1; lia). specialize (V ltac:(unfold cl'; cbn [art_cls_pop cl_mu]; unfold u, ab; clear - Hi G1 G2 G4 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hsz Hrs Hqz Erz16 Hn1; lia)).
    rewrite art_wview_off in V by (rewrite art_u_lit by (unfold u, ab; clear - Hi G1 G2 G4 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hsz Hrs Hqz Erz16 Hn1; lia); right; unfold u, ab; clear - Hi G1 G2 G4 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hsz Hrs Hqz Erz16 Hn1; lia). unfold mrestrict in V. destruct (bhid A' model' (Z_to_bv 64 (u + i))); [exfalso; apply V; reflexivity|exact V]. }
  assert (Hu16 : u mod 16 = 0). { unfold u, ab. rewrite Espb, Erz16. replace (65536 * rn_qs rn + c * 2 ^ 32 + w * 16 + 16 * qz) with ((4096 * rn_qs rn + c * 2 ^ 28 + w + qz) * 16) by lia. apply Z_mod_mult. }
  assert (SCR : forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None).
  { intros a Ha. assert (WM : wrA M (Sp - 4096) 4096) by (intros d k Hd Hk; rewrite <- HLsegs; apply SWR; assumption).
    pose proof (art_wr_wview ASEGS M (Sp - 4096) 4096 ltac:(clear - SHI G1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI G1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
    rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI G1 SLE STOP; lia); right; clear - Ha SHI G1; lia). exact V. }
  assert (EG' : art_eager_ok ((u, n) :: LB) A' (m_vm_lazy model')).
  { apply (art_wmx_eager FSG rn (art_gs_malloc G (rn_spb rn) c w u n kb) LB A (m_vm_lazy model) A' (m_vm_lazy model') u n EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) LZ').
    - intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. rewrite Esfx' in Hev. exact (art_ca_events_no_nr _ _ _ _ _ Hev).
    - exact G4.
    - exact Abk.
    - lia.
    - exact Hu2.
    - assert (CMu : forall a, u <= a < u + n -> rn_spb rn + c * 2 ^ 32 <= a < rn_spb rn + c * 2 ^ 32 + cl_mu cl').
      { intros a Ha. unfold cl'. cbn [art_cls_pop cl_mu]. unfold u, ab in Ha. clear - Ha Hrs Hfit Hw0 Hwsz Haumu' Erz16 Hqz. lia. }
      intros a Ha. right; left. exists c. split; [exact Hc|]. left. cbn [art_gs_malloc g_cls]. rewrite Z.eqb_refl. exact (CMu a Ha). }
  destruct LZ' as (LZ1 & LZ2 & LZ3 & LZ4).
  destruct (art_wmc_client L HLlo HLhi HLst rn LB FF LK A A' M M1 FPL Sp u n ROK CLI INC GRF FRF BA NFPB NFPW NFPS NFPI GFS GSH (FS_IN _ _ _ _ FS) SCR Hu1 Hu2 Hu16 Hn DEFu SHu LZ3)
    as (CLI' & ABR & FFA & AHP).
  (* [comment removed for export] *)
  assert (RI' : art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn ((u, n) :: LB) FF LK (adebit L cr n) A' M1 (vml_of model')).
  { exists (art_gs_malloc G (rn_spb rn) c w u n kb). cbn [vml_of fst snd].
    split; [exact REP'|]. split.
    { cbn [art_gs_malloc g_fs]. apply (FSLAW rn (g_fs FSG G) FF LK M M1 FS GRF). intros x Hz. apply FRF.
      exact (art_fs_zone_out rn FPL x ROK NFPW NFPI GFS GSH GTH (fun a k => art_mgap_dtls rn a k ROK) Hz). }
    split. { cbn [art_gs_malloc g_log]. pose proof B1 as B1'. rewrite Elog in B1'. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1'). }
    split. { unfold adebit. apply (art_wmx_credit FSG BUDGET rn G LB cr c w u n kb _ _ Hc OK CRED Edep); [lia|].
             assert (0 <= hl_b_lin L * n) by (apply Z.mul_nonneg_nonneg; lia). lia. }
    split; [exact CLI'|]. split; [exact KN|]. split; [repeat split; assumption|exact EG']. }
  unfold art_al16_post in POST. rewrite <- HLsegs.
  apply (POST regs' M1 model' A' u P10).
  - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
  - exact ABR.
  - exact BA.
  - exact FFA.
  - exact DEFu.
  - exact SHu.
  - rewrite HLscr. exact AHP.
  - exact RT.
  - exact INC.
  - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
  - exact RI'.
Qed.
End Wrap.

(* [comment removed for export] *)
Lemma art_req_quantities16 : forall n, 0 < n <= 4096 -> n mod 16 = 0 ->
  exists rl rz qz qr qn q16,
    rl = AsanTab.rz_log n /\ rz = 16 * 2 ^ rl /\ rz = 16 * qz /\ 1 <= qz <= 128 /\ n = 8 * qn + 0 /\ n = 8 * qr /\ n = 16 * q16 /\ n + 16 + rz <= 65536.
Proof.
  intros n Hn H16. pose proof (Z.div_mod n 16 ltac:(lia)) as D. rewrite H16 in D.
  assert (CASES : exists k, AsanTab.rz_log n = k /\ (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4)).
  { unfold AsanTab.rz_log. repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end; eexists; (split; [reflexivity|]); lia. }
  destruct CASES as (k & Ek & CK).
  exists k, (16 * 2 ^ k), (2 ^ k), (2 * (n / 16)), (2 * (n / 16)), (n / 16).
  split; [symmetry; exact Ek|]. split; [reflexivity|]. split; [reflexivity|]. clear Ek.
  destruct CK as [E|[E|[E|[E|E]]]]; rewrite E;
    match goal with |- context [2 ^ ?c] => let v := eval compute in (2 ^ c) in change (2 ^ c) with v end; repeat split; clear - D Hn; lia.
Qed.

Section WrapAll.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable L : asan_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLaligned : hl_aligned_alloc L = 0x79820.
Hypothesis HLscr : hl_scr_aligned L = 4096.
Hypothesis H1046 : forall G LB M, art_alloc_rep FSG rn G LB M -> cellA M 0x104c0 1 4.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLk : 3 <= hl_k_per_malloc L.
Hypothesis HLlin : 2 <= hl_b_lin L.
Hypothesis HLov : 2 ^ 20 <= hl_b_overhead L.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).

#[using="Halloc Hwx STATIC HLsegs HLaligned HLscr H1046 HLtp HLlo HLhi HLst HLk HLlin HLov FSLAW FS_IN"] Theorem art_wrap_aligned16 : art_aligned16_small_spec L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn).
Proof.
  intros fx0 R M model LB FF LK cr A n K RI Hhalt HMI H10 H11 Hn Hn16 ACR H4 Hret AST K0 POST.
  destruct (art_req_quantities16 n Hn Hn16) as (rl & rz & qz & qr & qn & q16 & Erl & Erz & Erz16 & Hqz & En & Ers & Ers16 & Hprim).
  rewrite HLsegs, HLaligned. replace (Z_to_bv 64 497696) with (0x79820%bv : word) by (apply bv_eq; reflexivity).
  exact (art_wrap_aligned16_primary FSG FSINV MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg L Halloc Hwx STATIC HLsegs HLscr H1046 HLtp HLlo HLhi
           (fun a Ha => HLst a (or_intror (or_intror (or_introl Ha)))) HLk ltac:(lia) HLov FSLAW FS_IN (fx:=fx0)
           R M model LB FF LK cr A n rl rz qz n qr qn 0 q16 K RI Hhalt HMI H10 H11 (proj1 Hn) Hn16 Erl Erz Erz16 Hqz En ltac:(lia) Ers Ers16 ltac:(lia) Hprim ACR H4 Hret AST POST).
Qed.
End WrapAll.
