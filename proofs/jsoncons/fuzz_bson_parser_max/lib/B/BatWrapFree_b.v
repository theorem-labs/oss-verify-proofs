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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatInv_b BatInvMallocPure_b BatInvMalloc_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocH_b BatWrapMallocX_b BatWrapMallocC_b BatWrapMalloc_b BatIfaceLaws_b
     BatFxQ_b BatFxBatch2_b BatFxBatch3_b BatFxDrain_b BatFxImg_b BatImgCell_b BatFreeTop3_b BatInvFreePure_b BatInvFree_b BatInvRepX_b BatInvDrain_b BatWrapFreeA_b BatWrapFreeC_b BatWrapFreeR_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5fac4_60344_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_free_thunk : forall regs (M rom : word -> option byte), msteps ASEGS (mkst regs (0x79814 : word) M rom) (mkst regs (0x79824 : word) M rom).
Proof. intros regs M rom. stepj F_793fc D_793fc. apply mst_refl. Qed.
End FPX.

Lemma art_batch_list_first : forall (M0 : word -> option byte) bs f l, bs <> [] -> art_batch_list M0 bs f l -> exists b0, In b0 bs /\ f = bt_addr b0.
Proof. intros M0 [|b0 r] f l NE BL; [contradiction|]. cbn [art_batch_list] in BL. destruct BL as (E & _). exists b0. split; [left; reflexivity|exact E]. Qed.

Section DrainRun.
Variable FSG : Type.
Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_wf_drain_run : forall (R regs' : bvmap 5 word) (M10 rom : word -> option byte) (raw0 : word) (rn : art_run) (Gq : art_gs FSG) (LB' : list (Z * Z)) (Sp u bound : Z),
  art_alloc_rep_b FSG bound rn Gq LB' M10 -> g_qt FSG Gq <> [] ->
  art_batches_bytes (g_qg FSG Gq) + art_batches_bytes (g_qt FSG Gq) <= 2 ^ 28 ->
  getr regs' 1 = (0x56a84 : bv 64)%bv -> getr regs' 2 = Z_to_bv 64 (Sp - 2208) -> getr regs' 10 = Z_to_bv 64 0x13c8b0 -> getr regs' 11 = Z_to_bv 64 (rn_t rn + 80) ->
  (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
  ret_ok raw0 -> rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 -> 0 <= u < 2 ^ 64 ->
  art_free3_epi M10 Sp u raw0 R -> wrA M10 (Sp - 4096) 4096 ->
  exists ft lt fg lg regsF (M' : word -> option byte),
    msteps ASEGS (mkst regs' (0x542b0 : word) M10 rom) (mkst regsF raw0 M' rom)
    /\ getr regsF 2 = Z_to_bv 64 Sp /\ getr regsF 1 = raw0
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsF r = getr R r)
    /\ art_batch_list M10 (g_qt FSG Gq) ft lt /\ cellA M10 (0x13c8b0 + 168) 8 fg /\ art_batch_list M10 (g_qg FSG Gq) fg lg
    /\ mem_grows M10 M' /\ art_agree (art_drain_W FSG rn Gq (Sp - 2208) lg) M10 M'
    /\ (cellA M' (rn_t rn + 80) 8 0 /\ cellA M' (rn_t rn + 80 + 8) 8 0 /\ cellA M' (rn_t rn + 80 + 16) 8 0 /\ cellA M' (rn_t rn + 80 + 24) 8 0
        /\ cellA M' (0x13c8b0 + 160) 8 (Z.of_nat (length (g_qg FSG Gq)) + Z.of_nat (length (g_qt FSG Gq))) /\ cellA M' (0x13c8b0 + 176) 8 lt
        /\ cellA M' (0x13c8b0 + 184) 8 (art_batches_bytes (g_qg FSG Gq) + art_batches_bytes (g_qt FSG Gq)) /\ cellA M' (0x13c8b0 + 152) 4 0
        /\ (Z.of_nat (length (g_qg FSG Gq)) = 0 -> cellA M' (0x13c8b0 + 168) 8 ft) /\ (Z.of_nat (length (g_qg FSG Gq)) <> 0 -> cellA M' lg 8 ft)).
Proof.
  intros R regs' M10 rom raw0 rn Gq LB' Sp u bound REPB NEq NR Q1 Q2 Q10 Q11 QK Hret HHI HS47 Hu EPI W10.
  pose proof REPB as (ROK & ST & TH & (_ & PRIM & _) & CH & SECR & QR & _). rok_open14 ROK. geo_open GEO.
  destruct QR as ((ft & lt & Ct80 & Ct88 & Ct96 & Ct104 & BLt) & (fg & lg & Cg160 & Cg168 & Cg176 & Cg184 & BLg) & _ & _ & Cmx & _ & _ & ITEMS & _ & BCH).
  destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C16 & _).
  destruct TH as (Wt & _).
  destruct (PRIM 24 ltac:(lia)) as (RC24 & OK24 & _). pose proof OK24 as (_ & (_ & Haumu24) & _ & _ & _ & Hmu324 & _). destruct RC24 as [_ RR24].
  pose proof RR24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu24).
  (* [comment removed for export] *)
  assert (POS : forall b it, In b (g_qt FSG Gq ++ g_qg FSG Gq) -> In it (bt_items b) -> 0 <= snd it).
  { intros b it Hb Hit. destruct (ITEMS b it Hb Hit) as [(c & w & Hc & V & St)|(s & Hs & Hq & Esu & Esn)].
    - specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III. destruct III as (_ & _ & (bb & _ & _ & _ & _ & Hn0) & _). lia.
    - destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (SALL i s Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
      rewrite Hq in P9. destruct P9 as ((bb & _ & _ & _ & _ & Hn0) & _). rewrite <- Esn. lia. }
  destruct (art_batches_bytes_ge (g_qt FSG Gq) (fun b it Hb Hi => POS b it (in_or_app _ _ _ (or_introl Hb)) Hi)) as (BYt & _).
  destruct (art_batches_bytes_ge (g_qg FSG Gq) (fun b it Hb Hi => POS b it (in_or_app _ _ _ (or_intror Hb)) Hi)) as (BYg & _).
  assert (ADDRB : forall b0, In b0 (g_qt FSG Gq ++ g_qg FSG Gq) -> rn_spb rn + 24 * 2 ^ 32 <= bt_addr b0 /\ bt_addr b0 + 8192 <= rn_spb rn + 24 * 2 ^ 32 + cl_mu (g_cls FSG Gq 24)).
  { intros b0 Hb0. destruct (BCH b0 Hb0) as (w0 & Ew0 & (V0 & V1 & _) & _). rewrite art_class_size_24 in V1. rewrite Ew0. clear - V0 V1 Haumu24. lia. }
  destruct (art_batch_list_first M10 _ ft lt NEq BLt) as (bf & Hbf & Eft). destruct (ADDRB bf (in_or_app _ _ _ (or_introl Hbf))) as (F0 & F1).
  pose proof (art_batch_list_last M10 _ ft lt NEq BLt) as Elt.
  destruct (ADDRB (art_lastb (g_qt FSG Gq)) (in_or_app _ _ _ (or_introl (BatFxQ_b.art_last_in _ _ _ NEq)))) as (T0 & T1).
  assert (HL : 1 <= Z.of_nat (length (g_qt FSG Gq))) by (destruct (g_qt FSG Gq); [contradiction|cbn [length]; lia]).
  assert (HGB : Z.of_nat (length (g_qg FSG Gq)) <> 0 -> 0x696000 <= lg /\ lg + 8 < 2 ^ 64 /\ apart (Sp - 2208 - 48) 48 lg 8 /\ apart (rn_t rn + 80) 32 lg 8 /\ wrA M10 lg 8
                                                      /\ lg + 8192 <= rn_HI rn).
  { intros NG. assert (NEg : g_qg FSG Gq <> []) by (intros E; apply NG; rewrite E; reflexivity).
    pose proof (art_batch_list_last M10 _ fg lg NEg BLg) as Elg.
    destruct (ADDRB (art_lastb (g_qg FSG Gq)) (in_or_app _ _ _ (or_intror (BatFxQ_b.art_last_in _ _ _ NEg)))) as (L0 & L1). rewrite <- Elg in L0, L1.
    unfold apart in G11 |- *. split; [clear - L0 G4; lia|]. split; [clear - L1 Hmu324 G6 G2 Eris; lia|]. split; [clear - L1 Hmu324 G6 Eris HHI; lia|]. split; [clear - L0 L1 Hmu324 G11; lia|].
    split; [eapply wr_sub; [exact Wu24| |]; clear - L0 L1; lia|clear - L1 Hmu324 G6 Eris; lia]. }
  destruct (art_drain_nr_run regs' M10 rom (0x56a84 : bv 64)%bv (Sp - 2208) (rn_t rn + 80) (Z.of_nat (length (g_qt FSG Gq))) ft lt (art_batches_bytes (g_qt FSG Gq))
              (Z.of_nat (length (g_qg FSG Gq))) lg (art_batches_bytes (g_qg FSG Gq))
              Q1 ltac:(unfold ret_ok; bveq) Q2 Q10 Q11 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - G7; lia) ltac:(clear - G8 G2; lia) ltac:(clear - G9; lia)
              ltac:(unfold apart; clear - G8 HHI; lia) ltac:(clear - HL BYt BYg NR; lia) ltac:(rewrite Eft; clear - F0 F1 G4 Hmu324 G6 G2 Eris; lia) ltac:(rewrite Elt; clear - T0 T1 G4 Hmu324 G6 G2 Eris; lia)
              ltac:(clear - BYt; lia) ltac:(clear - BYg; lia) NR ltac:(clear; lia) ltac:(clear - BYt BYg NR; lia)
              ltac:(intros NG; destruct (HGB NG) as (X1 & X2 & X3 & X4 & X5 & _); repeat split; assumption)
              ltac:(eapply wr_sub; [exact W10| |]; clear; lia) ltac:(eapply wr_sub; [exact Wt| |]; clear; lia) (art_img_wr M10 (0x13c8b0 + 152) 40 ltac:(lia) ltac:(lia) ltac:(lia))
              Cmx C16 Ct80 ltac:(replace (rn_t rn + 80 + 8) with (rn_t rn + 88) by lia; exact Ct88) ltac:(replace (rn_t rn + 80 + 16) with (rn_t rn + 96) by lia; exact Ct96)
              ltac:(replace (rn_t rn + 80 + 24) with (rn_t rn + 104) by lia; exact Ct104) Cg160 ltac:(intros _; exact Cg176) Cg184)
    as (regs2 & M' & RUN1 & P2 & P1 & PK2 & GRW2 & AGR & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  assert (AGR' : art_agree (art_drain_W FSG rn Gq (Sp - 2208) lg) M10 M') by exact AGR.
  (* [comment removed for export] *)
  assert (TEPI : forall a v, Sp - 2208 <= a -> a + 8 <= Sp -> cellA M10 a 8 v -> cellA M' a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_tr _ M10 M' a 8%nat v AGR'); [|clear - Ha HHI G1; lia|clear - Ha' HS47; cbn; lia|exact C].
    unfold art_drain_W. cbn [art_gap fst snd]. unfold apart. destruct (Z.eqb_spec (Z.of_nat (length (g_qg FSG Gq))) 0) as [E|NG].
    - clear - Ha Ha' HHI G1 G8. cbn. repeat split; try exact I; lia.
    - destruct (HGB NG) as (_ & _ & _ & _ & _ & X6). clear - Ha Ha' HHI G1 G8 X6. cbn. repeat split; try exact I; lia. }
  assert (EPI' : art_free3_epi M' Sp u raw0 R).
  { destruct EPI as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15). unfold art_free3_epi.
    repeat split; (apply TEPI; [clear; lia|clear; lia|assumption]). }
  destruct (art_free3_tail R regs2 M' rom raw0 Sp u P2 Hret ltac:(clear - HHI G1; lia) HS47 Hu
              ltac:(intros r Hr; rewrite PK2 by (cbn [In] in Hr |- *; clear - Hr; tauto); apply QK; exact Hr) EPI') as (regsF & RUN2 & PF2 & PF1 & PKF).
  exists ft, lt, fg, lg, regsF, M'. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|]. split; [exact PF2|]. split; [exact PF1|]. split; [exact PKF|].
  split; [exact BLt|]. split; [exact Cg168|]. split; [exact BLg|]. split; [exact GRW2|]. split; [exact AGR'|].
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8|]. split; [exact E9|exact E10].
Qed.
End DrainRun.

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
Hypothesis HLfree : hl_free L = 0x79814.
Hypothesis HLscr : hl_scr_free L = 4096.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis FSLAW2 : forall gfs FF LK (M M' : word -> option byte), FSINV rn gfs FF LK M -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) ->
  (forall a : word, in_shadow_rw (U a) -> M' a <> None) -> FSINV rn gfs FF LK M'.

#[using="Halloc Hwx STATIC HLsegs HLfree HLscr HLtp HLlo HLhi HLst FSLAW FS_IN FSLAW2"] Theorem art_wrap_free : afree_spec L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn).
Proof.
  intros fx R M model LB FF LK cr A u n K RI Hhalt HMI Hin H10 H4 Hret AST K0 POST.
  rewrite HLsegs, HLfree. replace (Z_to_bv 64 497684) with (0x79814%bv : word) by (apply bv_eq; reflexivity).
  destruct RI as (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in REPr, BV, LZ, EG.
  pose proof (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hhalt HMI) as B0.
  pose proof REPr as (ROK & _ & _ & (_ & PRIM & _) & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
  set (Sp := U (getr R 2)) in *. assert (H2 : getr R 2 = Z_to_bv 64 Sp) by (unfold Sp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite HLscr in AST. destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof CLI as (CB & CND & _ & _ & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & _ & CSP & _). rewrite HIeq in CS1, CS2.
  destruct (CB (u, n) Hin) as (Bu1 & Bu2 & Bu3 & Bu4 & Bu5 & _). cbn [fst snd] in Bu1, Bu2, Bu3, Bu4, Bu5. rewrite HIeq in Bu5.
  apply NoDup_ListNoDup in CND.
  assert (Hother : forall b0, In b0 (lb_remove u LB) -> In b0 LB /\ fst b0 <> u) by (intros b0 Hb0; split; [exact (art_lb_remove_in u LB b0 Hb0)|exact (art_lb_remove_gone u LB b0 CND Hb0)]).
  (* [comment removed for export] *)
  set (Mr0 := mrestrict (mkH (m_vm_lazy model) A) M) in *.
  destruct (art_wfa_kind FSG rn G LB Mr0 REPr u n Hin) as (k & KIND).
  destruct (art_wfa_hdr FSG rn G LB Mr0 REPr u n k KIND) as ((b1 & Hb1 & Hty & Chw & Cn & Hn) & SHBr).
  set (q16 := u / 16). assert (Eu : u = 16 * q16). { unfold q16. pose proof (Z.div_mod u 16 ltac:(lia)) as D. rewrite Bu3 in D. lia. }
  set (qr := (n + 7) / 8). assert (Hqr : n <= 8 * qr <= n + 7). { unfold qr. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
  (* [comment removed for export] *)
  set (cl24 := g_cls FSG G 24). destruct (PRIM 24 ltac:(lia)) as (_ & OK & _ & (km & Emu) & _). fold cl24 in OK, Emu.
  set (newb := art_free_newb (g_qt FSG G)).
  pose proof CRED as (CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7 & CR8).
  assert (HLB : 1 <= Z.of_nat (length LB)) by (destruct LB; [contradiction|cbn [length]; lia]).
  destruct (g_depot FSG G) as [|kb] eqn:Edep; [exfalso; cbn in CR6; lia|].
  destruct (CR8 24 ltac:(lia)) as (RM1 & RM2). fold cl24 in RM1, RM2.
  pose proof (art_nq_nonneg (g_qt FSG G ++ g_qg FSG G)) as Hnq0. unfold art_nret in CR7, RM2.
  assert (Room : newb = true -> cl_cache cl24 = [] -> art_cls_needs_populate 24 cl24 = true -> cl_mu cl24 + 262144 <= 3758096384
                 /\ art_cls_mfa' cl24 (Z.of_nat (length (cl_free cl24)) + art_cls_new 24 cl24) <= 536870912).
  { intros _ _ _. apply (art_room_of_credit 24 cl24 1 ltac:(lia) OK ltac:(lia)); lia. }
  assert (OKpre : newb = true -> art_cls_ok 24 (art_ca_pre 24 cl24)) by (intros E; apply art_cls_ok_ca_pre; [lia|exact OK|exact (Room E)]).
  pose proof OK as (_ & (Hau0 & Haumu) & _).
  assert (EV : art_evok_list (art_EVOK (art_RES rn) BUDGET LENMAX KMAX) (g_log FSG G) (art_enq_events newb (rn_spb rn) cl24)).
  { unfold art_enq_events. destruct newb eqn:En; [|constructor].
    apply (art_ca_evok (art_RES rn) BUDGET LENMAX KMAX (g_log FSG G) (rn_spb rn) (rn_qs rn) (rn_kbase rn) 24 cl24 km ltac:(lia) OK Espb ltac:(lia) ltac:(lia)
             ltac:(left; reflexivity) Emu ltac:(lia) (Room eq_refl)). lia. }
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  destruct (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) as (LO & _ & PW).
  assert (LIVE2 : forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p')) by (intros p p' Hp Hp' N; exact (PW p p' Hp Hp' N)).
  assert (LIVE3 : forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0) by (intros p Hp; destruct (LO p Hp) as (_ & _ & X1 & X2 & _); split; assumption).
  assert (W0 : wrA Mr0 (Sp - 4096) 4096). { apply (art_stack_wr FSG rn G A (m_vm_lazy model) M Sp 4096 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). rewrite <- HLsegs. exact SWR. }
  assert (RD0 : readable8 Mr0 Sp (ar_stack_top (rn_ar rn))). { apply (art_stack_readable FSG rn G A (m_vm_lazy model) M Sp (ar_stack_top (rn_ar rn)) ROK LZ ltac:(lia) ltac:(lia) SDEF). }
  set (raw0 := getr R 1) in *.
  assert (H4' : getr R 4 = Z_to_bv 64 (rn_tp rn)) by (rewrite <- HLtp; exact H4).
  assert (HS47 : Sp < 2 ^ 47) by (clear - SLE CSP; lia).
  assert (HHI : rn_HI rn + 4096 <= Sp - 4096) by (clear - SHI; lia).
  set (Qm := fun (log' : list aev) (st : machine_state) =>
     exists regs' (Mr' : word -> option byte), st = mkst regs' raw0 Mr' (seg_rom ASEGS)
       /\ getr regs' 2 = Z_to_bv 64 Sp
       /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r)
       /\ ((exists (d : bool) (lg : Z), log' = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl24 /\ art_free_pkg FSG rn G LB Sp u n q16 qr km kb k d lg Mr0 Mr')
           \/ exists (G' : art_gs FSG) (evs : list aev), log' = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl24 ++ evs /\ art_free_pkg3 FSG rn G LB Sp u n q16 qr km kb k Mr0 Mr' G' evs)).
  apply (aruns_srealizes_h ASEGS scfg Halloc Hwx MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BASE BUDGET LENMAX KMAX STATIC Qm K model A M model (g_log FSG G))
    with (log := g_log FSG G) (s := restrict (bhid A model) (mkst R (0x79814 : word) M (seg_rom ASEGS))) (A := A) (model := model);
    [ | | reflexivity | exact B0 | apply bmodel_rt_refl | apply bhist_refl ].
  2: { (* [comment removed for export] *)
    rewrite restrict_mkst. change (mrestrict (bhid A model) M) with Mr0.
    eapply ar_steps; [apply art_free_thunk|].
    apply (art_wf_entry FSG _ _ Qm (g_log FSG G) R Mr0 (seg_rom ASEGS) raw0 rn G LB Sp u n q16 qr b1 km (ar_stack_top (rn_ar rn)) (ar_stack_bottom (rn_ar rn)) kb k
             REPr KIND eq_refl Hret H2 H4' H10 Eu Hn Hqr Hb1 Hty Chw Cn SHBr HHI HS47 S16 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             W0 RD0 Edep Emu Room OKpre EV LIVE LIVE2 LIVE3).
    - (* [comment removed for export] *)
      intros regs' Mr' P2 P1 PK Hby OUT. exists regs', Mr'. split; [reflexivity|]. split; [exact P2|]. split; [exact PK|]. left. exists false, 0. split; [reflexivity|].
      exact (art_wf_pkg1 FSG rn G LB Mr0 Mr' Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother 0 Hby).
    - (* [comment removed for export] *)
      intros regs' Mr10 Q1 Q2 Q10 Q11 Q12 Q13 QK Hby OUT EPI W10.
      destruct (art_wf_pkg_fpl FSG rn G LB Mr0 Mr10 Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother) as (REPB & EBY & _).
      assert (NEq : g_qt FSG (art_gs_free G (rn_spb rn) k u n kb) <> []).
      { intros E. rewrite E in EBY. change (art_batches_bytes (@nil art_batch)) with 0 in EBY. clear - EBY Hby. lia. }
      destruct (Z_le_gt_dec (art_batches_bytes (g_qg FSG (art_gs_free G (rn_spb rn) k u n kb)) + art_batches_bytes (g_qt FSG (art_gs_free G (rn_spb rn) k u n kb))) (2 ^ 28)) as [NR|BIG].
      + (* [comment removed for export] *)
        destruct (art_wf_drain_run FSG R regs' Mr10 (seg_rom ASEGS) raw0 rn _ _ Sp u (2 ^ 29) REPB NEq NR Q1 Q2 Q10 Q11 QK Hret HHI HS47
                    ltac:(clear - Bu1 Bu4 Bu5 G2; lia) EPI W10)
          as (ft & lt & fg & lg & regsF & Mr' & RUN & PF2 & PF1 & PKF & BLt & Gf & BLg & GRW2 & AGR & DPOST).
        eapply ar_steps; [exact RUN|]. apply ar_done.
        exists regsF, Mr'. split; [reflexivity|]. split; [exact PF2|]. split; [exact PKF|]. left. exists true, lg. split; [reflexivity|].
        exact (art_wf_pkg2 FSG rn G LB Mr0 Mr10 Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother Mr' ft lt fg lg
                 NEq BLt Gf BLg NR GRW2 AGR DPOST).
      + (* [comment removed for export] *)
        destruct (art_wf_pkg_fpl FSG rn G LB Mr0 Mr10 Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother)
          as (_ & _ & GRW & FRL & NFPB & NFPS & NFPI & NFS & NDT & NTH & NSH & UF).
        set (Gfr0 := art_gs_free G (rn_spb rn) k u n kb) in *.
        assert (ELIVE : art_live (g_log FSG Gfr0) = art_live (g_log FSG G)) by (unfold Gfr0; apply art_frep_live_eq).
        pose proof (art_wfx_credit FSG BUDGET rn G LB cr u n kb k false OK CRED Edep Hin) as CRfr. cbv zeta in CRfr. fold Gfr0 in CRfr.
        destruct CRfr as (X1 & X2 & _ & _ & _ & _ & X7 & X8). unfold art_nret in X7, X8. pose proof (art_nq_nonneg (g_qt FSG Gfr0 ++ g_qg FSG Gfr0)) as Xnq.
        change (g_log FSG G ++ art_enq_events newb (rn_spb rn) cl24) with (g_log FSG Gfr0).
        apply (art_wf_rcy_aruns FSG (art_RES rn) BUDGET LENMAX KMAX _ Qm R regs' Mr10 (seg_rom ASEGS) raw0 rn Gfr0 (lb_remove u LB) Sp u (2 ^ 29) REPB NEq ltac:(clear - BIG; lia) (art_alloc_rep_b_ghost FSG _ _ _ _ _ REPB)).
        * intros p Hp. rewrite ELIVE in Hp. exact (LIVE p Hp).
        * intros p p' Hp Hp'. rewrite ELIVE in Hp, Hp'. exact (LIVE2 p p' Hp Hp').
        * intros p Hp. rewrite ELIVE in Hp. exact (LIVE3 p Hp).
        * intros p Hp. rewrite ELIVE in Hp. destruct (LIVE p Hp) as (L0 & L1 & L2 & L3 & _). destruct (LIVE3 p Hp) as (A1 & A2).
          eapply wr_grows; [exact GRW|]. exact (art_live_shadow_wr MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log FSG G) A M model p B0 Hp L0 L1 ltac:(clear - L2 G2; lia) L3 A1 A2).
        * intros c0 Hc0. destruct (X8 c0 Hc0) as (_ & Y). clear - Y X1 Xnq. lia.
        * clear - X7 X1. lia.
        * exact Q1.
        * exact Q2.
        * rewrite QK by (cbn [In]; tauto). exact H4'.
        * exact Q10.
        * exact Q11.
        * exact Q12.
        * exact Q13.
        * exact QK.
        * exact Hret.
        * exact HHI.
        * exact HS47.
        * clear - Bu1 Bu4 Bu5 G2. lia.
        * exact EPI.
        * exact W10.
        * intros regsF Mr' G' evs PF2 PKF RPOST. exists regsF, Mr'. split; [reflexivity|]. split; [exact PF2|]. split; [exact PKF|]. right. exists G', evs.
          split; [unfold Gfr0; cbn [art_gs_free g_log]; rewrite <- app_assoc; reflexivity|]. exists Mr10. split; [|exact RPOST].
          unfold art_fpl_bundle. cbv zeta. repeat (split; [assumption|]). exact UF. }
  (* [comment removed for export] *)
  intros log' A' ms' model' B1 RT BH (regs' & Mr' & Est & P2 & PK & PKGS).
  destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr). set (M1 := ms_mem ms') in *. rewrite Ems. subst Mr'.
  destruct PKGS as [(d & lg & Elog & PKG)|(G' & evs & Elog & PKG3)].
  2: { (* [comment removed for export] *)
    destruct (art_wf_finish3 FSG FSINV MAPS0 RESV0 NOACC0 BASE BUDGET rn L HLlo HLhi HLst FSLAW2 FS_IN G LB FF LK cr A A' M M1 model model' log' Sp u n q16 qr km kb k G' evs
                ROK OK Emu Room FS CRED CLI KN LZ EG Edep Hin ltac:(clear - Hn Hqr; lia) HHI HS47 LIVE Elog B1 BH PKG3) as (RI' & AHP).
    rewrite <- HLsegs. apply (POST regs' M1 model' A').
    - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
    - rewrite HLscr. exact AHP.
    - exact RT.
    - destruct BH as (sfx & _ & INC & _). exact INC.
    - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
    - exact RI'. }
  set (Gfr := art_gs_free G (rn_spb rn) k u n kb) in *. set (Gfin := if d then art_gs_drain Gfr else Gfr).
  set (FPT := art_free_fpt FSG rn G Sp u n q16 qr km kb k d lg).
  destruct PKG as (REP' & GRr & FRr & NFPB & NFPS & NFPI & NFS & NDT & NTH & NSH & UF). fold Gfr in REP'. fold Gfin in REP'. fold FPT in FRr, NFPB, NFPS, NFPI, NFS, NDT, NTH, NSH.
  assert (ECLS : g_cls FSG Gfin 24 = art_enq_cls newb cl24) by (unfold Gfin; destruct d; reflexivity).
  pose proof REP' as (_ & _ & _ & (_ & PRIM' & _) & _).
  destruct (PRIM' 24 ltac:(lia)) as (RC' & _). rewrite ECLS in RC'. destruct RC' as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wfa' & Wu')).
  destruct (art_wfc_mem FSG rn G A A' M M1 model model' log' Sp u n q16 qr km kb k d lg ROK OK Emu Room Elog BH GRr FRr Wu' Wfa') as (FRF & GRF & VIS).
  pose proof BH as (sfx & Esfx & INC & BH2 & _ & BH4 & BH5).
  assert (Esfx' : sfx = art_enq_events newb (rn_spb rn) cl24). { rewrite Elog in Esfx. apply app_inv_head in Esfx. symmetry. exact Esfx. }
  assert (NONULL : forall len r, ~ In (AMmapNull len r) sfx).
  { intros len r Hev. rewrite Esfx' in Hev. unfold art_enq_events in Hev. destruct newb; [exact (art_ca_events_no_null _ _ _ _ _ Hev)|destruct Hev]. }
  assert (NONR : forall a l, ~ In (AMmapFixedNR a l) sfx).
  { intros a l Hev. rewrite Esfx' in Hev. unfold art_enq_events in Hev. destruct newb; [exact (art_ca_events_no_nr _ _ _ _ _ Hev)|destruct Hev]. }
  assert (B5' : forall x : word, page_in_ranges (page_base x) (m_vm_lazy model') = true -> page_in_ranges (page_base x) (m_vm_lazy model) = true).
  { intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. exact (NONR _ _ Hev). }
  (* [comment removed for export] *)
  assert (LZ' : art_lazy_ok FSG rn Gfin A' (m_vm_lazy model')).
  { apply (art_lazy_ok_step FSG rn G Gfin A (m_vm_lazy model) A' (m_vm_lazy model') LZ INC).
    - intros x Hx. exact (proj1 (BH2 x Hx)).
    - intros wd Hwd. destruct (BH4 wd Hwd) as [Hi|(len & r & Hev & _)]; [exact Hi|]. exfalso. exact (NONULL _ _ Hev).
    - exact B5'.
    - intros x C. destruct (art_free_committed FSG rn G u n kb k d (U x) C) as [C0|V]; [left; exact C0|right; exact (VIS x V)]. }
  assert (EG' : art_eager_ok (lb_remove u LB) A' (m_vm_lazy model')) by exact (art_eager_ok_remove LB A (m_vm_lazy model) A' (m_vm_lazy model') u EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) B5').
  (* [comment removed for export] *)
  assert (SCR : forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None).
  { intros a Ha. assert (WM : wrA M (Sp - 4096) 4096) by (intros dd kk Hd Hk; rewrite <- HLsegs; apply SWR; assumption).
    pose proof (art_wr_wview ASEGS M (Sp - 4096) 4096 ltac:(lia) ltac:(lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by lia. specialize (V ltac:(lia)).
    rewrite art_wview_off in V by (rewrite art_u_lit by lia; right; lia). exact V. }
  assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
  destruct (art_wfc_client L HLlo HLhi HLst rn LB FF LK A A' M M1 FPT Sp u n qr ROK CLI INC GRF FRF NFPB NFPS NFPI NFS NSH UF Hq0 (FS_IN _ _ _ _ FS) SCR) as (CLI' & AHP).
  (* [comment removed for export] *)
  assert (EFS : g_fs FSG Gfin = g_fs FSG G) by (unfold Gfin; destruct d; reflexivity).
  assert (ELOG : g_log FSG Gfin = log') by (rewrite Elog; unfold Gfin; destruct d; reflexivity).
  assert (RI' : art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn (lb_remove u LB) FF LK cr A' M1 (vml_of model')).
  { exists Gfin. cbn [vml_of fst snd].
    split; [exact REP'|]. split.
    { rewrite EFS. apply (FSLAW rn (g_fs FSG G) FF LK M M1 FS GRF). intros x Hz. apply FRF. destruct UF as (U1 & U2 & Uf). unfold apart, FS_BYTES in *.
      destruct Hz as [Z|[Z|[Z|[(Z & NS)|[Z|Z]]]]].
      - apply NFS. unfold FS_BYTES. exact Z.
      - apply NTH. exact Z.
      - apply (NSH (ar_fs (rn_ar rn)) 0xb09000 (U x)); [clear - Flo; lia|clear; lia|clear - Fhi G2; lia|clear - Afkb; lia|clear - Uf Hq0; lia|].
        pose proof (art_S_pred (ar_fs (rn_ar rn) + 0xb09000)). clear - Z H. unfold FS_BYTES in Z. lia.
      - apply NFPI; [exact Z|exact NS].
      - apply (NSH 0x10000 (0x696000 - 0x10000) (U x)); [clear; lia|clear; lia|clear; lia|left; clear - G4 Kspb; lia|left; clear - U1; lia|].
        pose proof (art_S_pred 0x696000). replace (0x10000 + (0x696000 - 0x10000) - 1) with (0x696000 - 1) by lia. clear - Z H. lia.
      - apply NDT. exact Z. }
    split. { rewrite ELOG. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
    split; [exact (art_wfx_credit FSG BUDGET rn G LB cr u n kb k d OK CRED Edep Hin)|].
    split; [exact CLI'|]. split; [exact KN|]. split; [exact LZ'|exact EG']. }
  rewrite <- HLsegs.
  apply (POST regs' M1 model' A').
  - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
  - rewrite HLscr. exact AHP.
  - exact RT.
  - exact INC.
  - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
  - exact RI'.
Qed.
End Wrap.
