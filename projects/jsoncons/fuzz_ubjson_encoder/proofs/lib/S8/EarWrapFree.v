(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtTac EatInitCache EatPopulate1 ArtRuns ArtRunsMem EatCls EatFp EatClsRep EatClsGfa2 EatClsRefill EatCellEx EatByteCell EatCARSpec EatAlloc3Pure EatDepot EatUnwind ArtBridge EatAllocate3 EarInv EatInvMallocPure EarInvMalloc EatLift EatWrapPure EarWrapKit EatWrapMallocH EarWrapMallocX EarWrapMallocC EarWrapMalloc EarIfaceLaws EatFxQ EatFxBatch2 EatFxBatch3 EatFxDrain EatFxImg EatImgCell EarFreeTop3 EarInvFreePure EarInvFree EarInvRepX EarInvDrain EarWrapFreeA EarWrapFreeC EarWrapFreeR.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EatHdrW.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r5fac4_60344.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EarCreditQ EarCredit EarCreditT EarCreditF EarUkey EarInvDrain EarCreditR EarWrapFreeR EarInvRecycleA EarFreeTop3P EarInvFreeP EarWrapFreeP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_free_thunk : forall regs (M rom : word -> option byte), msteps ASEGS (mkst regs (0x7a198 : word) M rom) (mkst regs (0x7a1a8 : word) M rom).
Proof. intros regs M rom. stepj F_7a148 D_7a148. apply mst_refl. Qed.
End FPX.

Lemma art_batch_list_first : forall (M0 : word -> option byte) bs f l, bs <> [] -> art_batch_list M0 bs f l -> exists b0, In b0 bs /\ f = bt_addr b0.
Proof. intros M0 [|b0 r] f l NE BL; [contradiction|]. cbn [art_batch_list] in BL. destruct BL as (E & _). exists b0. split; [left; reflexivity|exact E]. Qed.

Section DrainRun.
Variable FSG : Type.
Context {fx : PropExec.FPState}.

Lemma art_repb_keys : forall rn D (G : art_gs FSG) bound LB M, art_alloc_rep_b FSG bound rn G LB M -> DInvK (rn_l2 rn) (rn_blk rn) (g_depot FSG G) D M ->
  art_alloc_rep_b FSG bound (art_rn_k rn D) G LB M.
Proof.
  intros rn D G bound LB M REP DK. unfold art_alloc_rep_b in *.
  destruct REP as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|]. split; [exact C7|]. split; [exact DK|]. exact C9.
Qed.
#[using="Type"] Lemma art_wf_drain_run : forall (R regs' : bvmap 5 word) (M10 rom : word -> option byte) (raw0 : word) (rn : art_run) (Gq : art_gs FSG) (LB' : list (Z * Z)) (Sp u bound : Z),
  art_alloc_rep_b FSG bound rn Gq LB' M10 -> g_qt FSG Gq <> [] ->
  art_batches_bytes (g_qg FSG Gq) + art_batches_bytes (g_qt FSG Gq) <= 2 ^ 28 ->
  getr regs' 1 = (0x5726c : bv 64)%bv -> getr regs' 2 = Z_to_bv 64 (Sp - 2208) -> getr regs' 10 = Z_to_bv 64 0x13e670 -> getr regs' 11 = Z_to_bv 64 (rn_t rn + 80) ->
  (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
  ret_ok raw0 -> rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 -> 0 <= u < 2 ^ 64 ->
  art_free3_epi M10 Sp u raw0 R -> wrA M10 (Sp - 4096) 4096 ->
  exists ft lt fg lg regsF (M' : word -> option byte),
    msteps ASEGS (mkst regs' (0x54a98 : word) M10 rom) (mkst regsF raw0 M' rom)
    /\ getr regsF 2 = Z_to_bv 64 Sp /\ getr regsF 1 = raw0
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsF r = getr R r)
    /\ art_batch_list M10 (g_qt FSG Gq) ft lt /\ cellA M10 (0x13e670 + 168) 8 fg /\ art_batch_list M10 (g_qg FSG Gq) fg lg
    /\ mem_grows M10 M' /\ art_agree (art_drain_W FSG rn Gq (Sp - 2208) lg) M10 M'
    /\ (cellA M' (rn_t rn + 80) 8 0 /\ cellA M' (rn_t rn + 80 + 8) 8 0 /\ cellA M' (rn_t rn + 80 + 16) 8 0 /\ cellA M' (rn_t rn + 80 + 24) 8 0
        /\ cellA M' (0x13e670 + 160) 8 (Z.of_nat (length (g_qg FSG Gq)) + Z.of_nat (length (g_qt FSG Gq))) /\ cellA M' (0x13e670 + 176) 8 lt
        /\ cellA M' (0x13e670 + 184) 8 (art_batches_bytes (g_qg FSG Gq) + art_batches_bytes (g_qt FSG Gq)) /\ cellA M' (0x13e670 + 152) 4 0
        /\ (Z.of_nat (length (g_qg FSG Gq)) = 0 -> cellA M' (0x13e670 + 168) 8 ft) /\ (Z.of_nat (length (g_qg FSG Gq)) <> 0 -> cellA M' lg 8 ft)).
Proof.
  intros R regs' M10 rom raw0 rn Gq LB' Sp u bound REPB NEq NR Q1 Q2 Q10 Q11 QK Hret HHI HS47 Hu EPI W10.
  pose proof REPB as (ROK & ST & TH & (_ & PRIM & _) & CH & SECR & QR & _). rok_open14 ROK. geo_open GEO.
  destruct QR as ((ft & lt & Ct80 & Ct88 & Ct96 & Ct104 & BLt) & (fg & lg & Cg160 & Cg168 & Cg176 & Cg184 & BLg) & _ & _ & Cmx & _ & _ & ITEMS & _ & BCH).
  destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C16 & _).
  destruct TH as (Wt & _).
  destruct (PRIM 24 ltac:(lia)) as (RC24 & OK24 & _). pose proof OK24 as (_ & (_ & Haumu24) & _ & _ & _ & Hmu324 & _). destruct RC24 as [_ RR24].
  pose proof RR24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu24).

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
  destruct (ADDRB (art_lastb (g_qt FSG Gq)) (in_or_app _ _ _ (or_introl (EatFxQ.art_last_in _ _ _ NEq)))) as (T0 & T1).
  assert (HL : 1 <= Z.of_nat (length (g_qt FSG Gq))) by (destruct (g_qt FSG Gq); [contradiction|cbn [length]; lia]).
  assert (HGB : Z.of_nat (length (g_qg FSG Gq)) <> 0 -> 0x698000 <= lg /\ lg + 8 < 2 ^ 64 /\ apart (Sp - 2208 - 48) 48 lg 8 /\ apart (rn_t rn + 80) 32 lg 8 /\ wrA M10 lg 8
                                                      /\ lg + 8192 <= rn_HI rn).
  { intros NG. assert (NEg : g_qg FSG Gq <> []) by (intros E; apply NG; rewrite E; reflexivity).
    pose proof (art_batch_list_last M10 _ fg lg NEg BLg) as Elg.
    destruct (ADDRB (art_lastb (g_qg FSG Gq)) (in_or_app _ _ _ (or_intror (EatFxQ.art_last_in _ _ _ NEg)))) as (L0 & L1). rewrite <- Elg in L0, L1.
    unfold apart in G11 |- *. split; [clear - L0 G4; lia|]. split; [clear - L1 Hmu324 G6 G2 Eris; lia|]. split; [clear - L1 Hmu324 G6 Eris HHI; lia|]. split; [clear - L0 L1 Hmu324 G11; lia|].
    split; [eapply wr_sub; [exact Wu24| |]; clear - L0 L1; lia|clear - L1 Hmu324 G6 Eris; lia]. }
  destruct (art_drain_nr_run regs' M10 rom (0x5726c : bv 64)%bv (Sp - 2208) (rn_t rn + 80) (Z.of_nat (length (g_qt FSG Gq))) ft lt (art_batches_bytes (g_qt FSG Gq))
              (Z.of_nat (length (g_qg FSG Gq))) lg (art_batches_bytes (g_qg FSG Gq))
              Q1 ltac:(unfold ret_ok; bveq) Q2 Q10 Q11 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) ltac:(clear - G7; lia) ltac:(clear - G8 G2; lia) ltac:(clear - G9; lia)
              ltac:(unfold apart; clear - G8 HHI; lia) ltac:(clear - HL BYt BYg NR; lia) ltac:(rewrite Eft; clear - F0 F1 G4 Hmu324 G6 G2 Eris; lia) ltac:(rewrite Elt; clear - T0 T1 G4 Hmu324 G6 G2 Eris; lia)
              ltac:(clear - BYt; lia) ltac:(clear - BYg; lia) NR ltac:(clear; lia) ltac:(clear - BYt BYg NR; lia)
              ltac:(intros NG; destruct (HGB NG) as (X1 & X2 & X3 & X4 & X5 & _); repeat split; assumption)
              ltac:(eapply wr_sub; [exact W10| |]; clear; lia) ltac:(eapply wr_sub; [exact Wt| |]; clear; lia) (art_img_wr M10 (0x13e670 + 152) 40 ltac:(lia) ltac:(lia) ltac:(lia))
              Cmx C16 Ct80 ltac:(replace (rn_t rn + 80 + 8) with (rn_t rn + 88) by lia; exact Ct88) ltac:(replace (rn_t rn + 80 + 16) with (rn_t rn + 96) by lia; exact Ct96)
              ltac:(replace (rn_t rn + 80 + 24) with (rn_t rn + 104) by lia; exact Ct104) Cg160 ltac:(intros _; exact Cg176) Cg184)
    as (regs2 & M' & RUN1 & P2 & P1 & PK2 & GRW2 & AGR & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  assert (AGR' : art_agree (art_drain_W FSG rn Gq (Sp - 2208) lg) M10 M') by exact AGR.

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
Hypothesis HLfree : hl_free L = 0x7a198.
Hypothesis HLscr : hl_scr_free L = 4096.
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x698000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis FSLAW : art_fsinv_frame_law FSG FSINV.
Hypothesis FSKEYS : forall rn D g FF LK M, FSINV rn g FF LK M -> FSINV (art_rn_k rn D) g FF LK M.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
Hypothesis FSKEYS_DN : forall rn D g FF LK M, FSINV (art_rn_k rn D) g FF LK M -> FSINV rn g FF LK M.

#[using="Type"] Lemma art_rep_keys_dn : forall D (G : art_gs FSG) LB M,
  art_alloc_rep FSG (art_rn_k rn D) G LB M -> incl (rn_keys rn) D -> art_alloc_rep FSG rn G LB M.
Proof.
  intros D G LB M (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HD.
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact R7|].
  split; [exact (DInvK_incl _ _ _ _ _ _ R8 HD)|]. split; [exact R9|]. split; [exact R10|exact R11].
Qed.
#[using="FSKEYS_DN"] Lemma art_ri_inv_keys_dn : forall D LB FF LK cr A M V,
  art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV (art_rn_k rn D) LB FF LK cr A M V -> incl (rn_keys rn) D ->
  art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn LB FF LK cr A M V.
Proof.
  intros D LB FF LK cr A M V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) HD.
  exists G. split; [exact (art_rep_keys_dn D G _ _ REP HD)|]. split; [exact (FSKEYS_DN rn D _ _ _ _ FS)|]. split; [exact BV|]. split; [exact CRED|].
  split; [exact CLI|]. split; [exact KN|]. split; [exact LZ|exact EG].
Qed.

Hypothesis FSLAW2 : forall gfs FF LK (M M' : word -> option byte), FSINV rn gfs FF LK M -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) ->
  (forall a : word, in_shadow_rw (U a) -> M' a <> None) -> FSINV rn gfs FF LK M'.

#[using="Halloc Hwx STATIC HLsegs HLfree HLscr HLtp HLlo HLhi HLst FSLAW FS_IN FSLAW2 FSKEYS"] Theorem art_wrap_freeU :
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (u n : Z) (K : ShapeAlg.TSet) (Kz : list Z) (warm : bool),
    ri_inv (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn) LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
    In (u, n) LB -> getr R 10%bv = Z_to_bv 64 u ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) -> Hoare.ret_ok (getr R 1%bv) ->
    astack_ok L (rn_ar rn) M (hl_scr_free L) (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (warm = true -> In Kz (rn_keys rn)) ->
    ukeyG L (rn_ar rn) 0x7a2e0 (mrestrict (mkH (m_vm_lazy model) A) M) (bv_unsigned (getr R 2%bv)) (bv_unsigned (getr R 1%bv)) (bv_unsigned (getr R 8%bv)) Kz ->
    HeapIfaceAEr.HAR.afree_postG L (rn_ar rn) scfg (fun D => art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV (art_rn_k rn D)) (Kz :: rn_keys rn)
         (if warm then (fst cr + 1, snd cr) else cr) fx R M model LB FF LK A u K ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros fx R M model LB FF LK cr A u n K Kz warm RI Hhalt HMI Hin H10 H4 Hret AST K0 WK UKz POST.
  rewrite HLsegs, HLfree. replace (Z_to_bv 64 500120) with (0x7a198%bv : word) by (apply bv_eq; reflexivity).
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

  set (Mr0 := mrestrict (mkH (m_vm_lazy model) A) M) in *.
  destruct (art_wfa_kind FSG rn G LB Mr0 REPr u n Hin) as (k & KIND).
  destruct (art_wfa_hdr FSG rn G LB Mr0 REPr u n k KIND) as ((b1 & Hb1 & Hty & Chw & Cn & Hn0w) & SHBr).
  pose proof Hn0w as (Hn0 & Hlink & _).
  set (q16 := u / 16). assert (Eu : u = 16 * q16). { unfold q16. pose proof (Z.div_mod u 16 ltac:(lia)) as D. rewrite Bu3 in D. lia. }
  set (qr := (n + 7) / 8). assert (Hqr : n <= 8 * qr <= n + 7). { unfold qr. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }

  set (cl24 := g_cls FSG G 24). destruct (PRIM 24 ltac:(lia)) as (_ & OK & _ & (km & Emu) & _). fold cl24 in OK, Emu.
  set (newb := art_free_newb (g_qt FSG G)).

  assert (CLSOK : forall c0, 1 <= c0 <= 30 -> art_cls_ok c0 (g_cls FSG G c0)) by (intros c0 Hc0; exact (proj1 (proj2 (PRIM c0 Hc0)))).
  assert (HLB : 1 <= Z.of_nat (length LB)) by (destruct LB; [contradiction|cbn [length]; lia]).
  destruct (art_cr_kbU FSG G warm Kz (rn_keys rn) (art_cr_depot_lb FSG BUDGET rn G LB cr CRED HLB) WK) as (kb0 & kb & Edep0 & EdepW & HKB & KBW).
  assert (HK1 : In Kz (rn_keys rn) \/ (1 <= Datatypes.S kb0)%nat) by (right; clear; Lia.lia).
  assert (Room : newb = true -> cl_cache cl24 = [] -> art_cls_needs_populate 24 cl24 = true -> cl_mu cl24 + 262144 <= 3758096384
                 /\ art_cls_mfa' cl24 (Z.of_nat (length (cl_free cl24)) + art_cls_new 24 cl24) <= 536870912).
  { intros _ _ NP. exact (art_cr_room FSG rn G LB _ REPr BUDGET cr CRED 24 ltac:(lia) NP). }
  assert (OKpre : newb = true -> art_cls_ok 24 (art_ca_pre 24 cl24)) by (intros E; apply art_cls_ok_ca_pre; [lia|exact OK|exact (Room E)]).
  pose proof OK as (_ & (Hau0 & Haumu) & _).
  assert (EV : art_evok_list (art_EVOK (art_RES rn) BUDGET LENMAX KMAX) (g_log FSG G) (art_enq_events newb (rn_spb rn) cl24)).
  { unfold art_enq_events. destruct newb eqn:En; [|constructor].
    apply (art_ca_evok (art_RES rn) BUDGET LENMAX KMAX (g_log FSG G) (rn_spb rn) (rn_qs rn) (rn_kbase rn) 24 cl24 km ltac:(lia) OK Espb ltac:(lia) ltac:(lia)
             ltac:(left; reflexivity) Emu ltac:(lia) (Room eq_refl)). exact (art_cr_budget_ca FSG BUDGET rn G LB cr CRED CLSOK). }
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

  destruct (Z_le_gt_dec n (2 ^ 28)) as [HnS|HnP].
  2: {
    destruct k as [c w|i].
    { exfalso. destruct KIND as (Hc & V & St). pose proof REPr as (_ & _ & _ & _ & CH & _). specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III).
      specialize (III w V). rewrite St in III. destruct III as (_ & X2 & X3 & _). pose proof (art_class_size_facts c Hc) as (S1 & _). clear - X2 X3 S1 HnP. lia. }
    destruct KIND as (s & KINDs). assert (HnPP : 2 ^ 28 < n <= 2 ^ 34) by (clear - HnP Hn0; lia).
    set (evs := EatRecycle2C.art_flush_events (sc_map s) (sc_msize s) ++ [AMunmap (sc_map s) (sc_msize s)]).
    assert (LIVESH : forall p, In p (art_live (g_log FSG G)) -> wrA Mr0 (EatPoison.SB + fst p / 8) (snd p / 8)).
    { intros p Hp. destruct (LIVE p Hp) as (L0 & L1 & L2 & L3 & _). destruct (LIVE3 p Hp) as (A1 & A2).
      exact (art_live_shadow_wr MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log FSG G) A M model p B0 Hp L0 L1 ltac:(clear - L2 G2; lia) L3 A1 A2). }
    assert (SEV : art_evok_list (art_EVOK (art_RES rn) BUDGET LENMAX KMAX) (g_log FSG G) evs).
    { pose proof REPr as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _).
      destruct (PER i s (proj1 KINDs)) as (_ & P2 & _). destruct (LIVE3 _ P2) as (A1 & A2). destruct (LIVE _ P2) as (L0 & L1 & _). cbn [fst snd] in A1, A2, L0, L1.
      destruct (EatRecycle1.art_flush_range (sc_map s) (sc_msize s) A1 A2 ltac:(clear - L0; lia) ltac:(clear - L1; lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
      unfold evs, EatRecycle2C.art_flush_events. destruct (EatRecycle1.art_flush_beg (sc_map s) <? EatRecycle1.art_flush_end (sc_map s) (sc_msize s)) eqn:EL; cbn [app art_evok_list].
      - apply Z.ltb_lt in EL. split.
        + cbn [art_EVOK]. split; [exact F1|]. split; [exact F3|]. split; [clear - EL; lia|].
          exists (art_shlo (sc_map s), art_shhi (sc_map s) (sc_msize s)). split; [exact (EarInvRecycleE.art_log_window _ _ _ (EarInvRecycleE.art_live_in_log _ _ _ P2))|]. cbn [fst snd]. clear - F7 F8. lia.
        + split; [|exact I]. cbn [art_EVOK]. rewrite art_live_snoc. cbn [art_ev_live]. exact P2.
      - split; [|exact I]. cbn [art_EVOK]. exact P2. }
    set (QmP := fun (log' : list aev) (st : machine_state) =>
       exists regs' (Mr' : word -> option byte), st = mkst regs' raw0 Mr' (seg_rom ASEGS)
         /\ getr regs' 2 = Z_to_bv 64 Sp
         /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r)
         /\ log' = g_log FSG G ++ evs
         /\ exists M7, art_free3P_out Mr0 M7 Mr' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 (rn_parr rn) (sc_map s) (sc_msize s) (map art_sec_b (g_sec FSG G)) i kb (Kz :: rn_keys rn)).
    apply (aruns_srealizes_h ASEGS scfg Halloc Hwx MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BASE BUDGET LENMAX KMAX STATIC QmP K model A M model (g_log FSG G))
      with (log := g_log FSG G) (s := restrict (bhid A model) (mkst R (0x7a198 : word) M (seg_rom ASEGS))) (A := A) (model := model);
      [ | exact K0 | | reflexivity | exact B0 | apply bmodel_rt_refl | apply bhist_refl ].
    2: { rewrite restrict_mkst. change (mrestrict (bhid A model) M) with Mr0.
      eapply ar_steps; [apply art_free_thunk|].
      apply (art_wf_entryPU FSG _ _ QmP (g_log FSG G) R Mr0 (seg_rom ASEGS) raw0 rn G LB Sp u n q16 qr b1 km (ar_stack_top (rn_ar rn)) (ar_stack_bottom (rn_ar rn)) kb i s L Kz (Datatypes.S kb0)
               REPr KINDs eq_refl Hret H2 H4' H10 Eu HnPP Hqr Hb1 Hty Hlink Chw Cn SHBr HHI HS47 S16 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               W0 HLsegs UKz Edep0 HK1 HKB Emu Room OKpre EV SEV LIVE LIVE2 LIVE3 LIVESH).
      intros regs' M7 Mr' P2 P1 PK OUT. exists regs', Mr'. split; [reflexivity|]. split; [exact P2|]. split; [exact PK|]. split; [reflexivity|]. exists M7. exact OUT. }

    intros log' A' ms' model' B1 RT BH (regs' & Mr' & Est & P2 & PK & Elog & M7 & OUT).
    destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr). set (M1 := ms_mem ms') in *. rewrite Ems. subst Mr'.
    pose proof (art_frepP_credit FSG BUDGET rn G LB u n kb i s cr warm (proj1 KINDs) CRED CND Hin KBW) as CREDp.
    destruct (art_wf_finishP FSG FSINV MAPS0 RESV0 NOACC0 BASE BUDGET rn L HLlo HLhi HLst FSLAW2 FS_IN G LB FF LK (if warm then (fst cr + 1, snd cr) else cr)
                A A' M M1 model model' log' Sp u n q16 qr b1 kb i s (Kz :: rn_keys rn) M7
                REPr KINDs Eu Hn0 Hqr Hb1 HHI HS47 EdepW ltac:(apply incl_tl; apply incl_refl) FS CREDp CLI KN LZ EG Hin Hother LIVE LIVE2 LIVE3 W0 Elog B1 BH OUT) as (RI' & DIz & AHP).
    cbv beta zeta delta [HeapIfaceAEr.HAR.afree_postG] in POST. rewrite <- HLsegs.
    apply (POST regs' M1 model' A').
    - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
    - rewrite HLscr. exact AHP.
    - exact RT.
    - destruct BH as (sfx & _ & INC & _). exact INC.
    - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
    - apply (art_ri_inv_keys FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV FSKEYS rn (Kz :: rn_keys rn) _ _ _ _ _ _ _ RI').
      intros k1 H1. exact (art_dk_up _ _ _ _ _ _ _ H1 DIz). }
  assert (Hn : 1 <= n <= 2 ^ 28) by (clear - Hn0 HnS; lia).
  assert (Hb1w := Hb1). clear Hb1. assert (Hb1 : 0 <= b1 < 256) by (apply (art_b1_small b1 n Hb1w Hlink); clear - Hn; lia).
  set (Qm := fun (log' : list aev) (st : machine_state) =>
     exists regs' (Mr' : word -> option byte), st = mkst regs' raw0 Mr' (seg_rom ASEGS)
       /\ getr regs' 2 = Z_to_bv 64 Sp
       /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r)
       /\ DInvK (rn_l2 rn) (rn_blk rn) kb (Kz :: rn_keys rn) Mr'
       /\ ((exists (d : bool) (lg : Z), log' = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl24 /\ art_free_pkg FSG rn G LB Sp u n q16 qr km kb k d lg Mr0 Mr'
                                         /\ (d = true -> 2 ^ 20 < art_batches_bytes (g_qt FSG (art_gs_free G (rn_spb rn) k u n kb))))
           \/ exists (G' : art_gs FSG) (evs : list aev), log' = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl24 ++ evs
                /\ 2 ^ 20 < art_batches_bytes (g_qt FSG (art_gs_free G (rn_spb rn) k u n kb)) /\ art_free_pkg3 FSG (art_rn_k rn (Kz :: rn_keys rn)) G LB Sp u n q16 qr km kb k Mr0 Mr' G' evs)).
  apply (aruns_srealizes_h ASEGS scfg Halloc Hwx MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BASE BUDGET LENMAX KMAX STATIC Qm K model A M model (g_log FSG G))
    with (log := g_log FSG G) (s := restrict (bhid A model) (mkst R (0x7a198 : word) M (seg_rom ASEGS))) (A := A) (model := model);
    [ | exact K0 | | reflexivity | exact B0 | apply bmodel_rt_refl | apply bhist_refl ].
  2: {
    rewrite restrict_mkst. change (mrestrict (bhid A model) M) with Mr0.
    eapply ar_steps; [apply art_free_thunk|].
    apply (art_wf_entryU FSG _ _ Qm (g_log FSG G) R Mr0 (seg_rom ASEGS) raw0 rn G LB Sp u n q16 qr b1 km (ar_stack_top (rn_ar rn)) (ar_stack_bottom (rn_ar rn)) kb k L Kz (Datatypes.S kb0)
             REPr KIND eq_refl Hret H2 H4' H10 Eu Hn Hqr Hb1 Hty Chw Cn SHBr HHI HS47 S16 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             W0 HLsegs UKz Edep0 HK1 HKB Emu Room OKpre EV LIVE LIVE2 LIVE3).
    -
      intros regs' Mr' P2 P1 PK Hby OUT DIz. exists regs', Mr'. split; [reflexivity|]. split; [exact P2|]. split; [exact PK|]. split; [exact DIz|]. left. exists false, 0. split; [reflexivity|]. split; [|discriminate].
      exact (art_wf_pkg1 FSG rn G LB Mr0 Mr' Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu EdepW OUT LIVE LIVE2 LIVE3 OKpre Hother 0 Hby).
    -
      intros regs' Mr10 Q1 Q2 Q10 Q11 Q12 Q13 QK Hby OUT DIz EPI W10.
      destruct (art_wf_pkg_fpl FSG rn G LB Mr0 Mr10 Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu EdepW OUT LIVE LIVE2 LIVE3 OKpre Hother) as (REPB & EBY & _).
      assert (NEq : g_qt FSG (art_gs_free G (rn_spb rn) k u n kb) <> []).
      { intros E. rewrite E in EBY. change (art_batches_bytes (@nil art_batch)) with 0 in EBY. clear - EBY Hby. lia. }
      destruct (Z_le_gt_dec (art_batches_bytes (g_qg FSG (art_gs_free G (rn_spb rn) k u n kb)) + art_batches_bytes (g_qt FSG (art_gs_free G (rn_spb rn) k u n kb))) (2 ^ 28)) as [NR|BIG].
      +
        destruct (art_wf_drain_run FSG R regs' Mr10 (seg_rom ASEGS) raw0 rn _ _ Sp u (2 ^ 29) REPB NEq NR Q1 Q2 Q10 Q11 QK Hret HHI HS47
                    ltac:(clear - Bu1 Bu4 Bu5 G2; lia) EPI W10)
          as (ft & lt & fg & lg & regsF & Mr' & RUN & PF2 & PF1 & PKF & BLt & Gf & BLg & GRW2 & AGR & DPOST).
        eapply ar_steps; [exact RUN|]. apply ar_done.
        exists regsF, Mr'. split; [reflexivity|]. split; [exact PF2|]. split; [exact PKF|]. split.
        { assert (HSPk : rn_HI (art_rn_k rn (Kz :: rn_keys rn)) <= Sp - 2208 - 48) by (change (rn_HI (art_rn_k rn (Kz :: rn_keys rn))) with (rn_HI rn); clear - HHI; lia).
          exact (art_drn_depot FSG (art_rn_k rn (Kz :: rn_keys rn)) _ _ Mr10 Mr' _ (Sp - 2208) fg lg (art_repb_keys FSG rn (Kz :: rn_keys rn) _ _ _ Mr10 REPB DIz) BLg HSPk AGR). }
        left. exists true, lg. split; [reflexivity|]. split; [|intros _; clear - EBY Hby; lia].
        exact (art_wf_pkg2 FSG rn G LB Mr0 Mr10 Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu EdepW OUT LIVE LIVE2 LIVE3 OKpre Hother Mr' ft lt fg lg
                 NEq BLt Gf BLg NR GRW2 AGR DPOST).
      +
        destruct (art_wf_pkg_fpl FSG rn G LB Mr0 Mr10 Sp u n q16 qr b1 km kb k REPr Hin Eu Hn Hqr Hb1 Hty Cn KIND HHI Emu EdepW OUT LIVE LIVE2 LIVE3 OKpre Hother)
          as (_ & _ & GRW & FRL & NFPB & NFPS & NFPI & NFS & NDT & NTH & NSH & UF).
        set (Gfr0 := art_gs_free G (rn_spb rn) k u n kb) in *.
        assert (ELIVE : art_live (g_log FSG Gfr0) = art_live (g_log FSG G)) by (unfold Gfr0; apply art_frep_live_eq).
        assert (HBYd : true = true -> 2 ^ 20 < art_batches_bytes (g_qt FSG Gfr0)) by (intros _; clear - EBY Hby; lia).
        pose proof (art_wfx_creditU FSG BUDGET rn G LB cr CRED CLSOK CND (proj1 (proj1 (art_items_pos_app _ _) (art_cr_items_pos FSG rn G LB _ REPr))) warm u n kb k true KBW Hin ltac:(clear - Hn; lia) HBYd) as CREDd.
        cbv zeta in CREDd. fold Gfr0 in CREDd.
        change (g_log FSG G ++ art_enq_events newb (rn_spb rn) cl24) with (g_log FSG Gfr0).
        apply (art_wf_rcy_aruns FSG (art_RES rn) BUDGET LENMAX KMAX _ Qm R regs' Mr10 (seg_rom ASEGS) raw0 (art_rn_k rn (Kz :: rn_keys rn)) Gfr0 (lb_remove u LB) Sp u (2 ^ 29) (if warm then (fst cr + 1, snd cr) else cr)
                 (art_repb_keys FSG rn (Kz :: rn_keys rn) _ _ _ Mr10 REPB DIz) NEq ltac:(clear - BIG; lia) (art_alloc_rep_b_ghost FSG _ _ _ _ _ REPB)).
        * intros p Hp. rewrite ELIVE in Hp. exact (LIVE p Hp).
        * intros p p' Hp Hp'. rewrite ELIVE in Hp, Hp'. exact (LIVE2 p p' Hp Hp').
        * intros p Hp. rewrite ELIVE in Hp. exact (LIVE3 p Hp).
        * intros p Hp. rewrite ELIVE in Hp. destruct (LIVE p Hp) as (L0 & L1 & L2 & L3 & _). destruct (LIVE3 p Hp) as (A1 & A2).
          eapply wr_grows; [exact GRW|]. exact (art_live_shadow_wr MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log FSG G) A M model p B0 Hp L0 L1 ltac:(clear - L2 G2; lia) L3 A1 A2).
        * clear. lia.
        * exact CREDd.
        * left. reflexivity.
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
        * intros regsF Mr' G' evs PF2 PKF RPOST. exists regsF, Mr'. split; [reflexivity|]. split; [exact PF2|]. split; [exact PKF|].
          split. { pose proof RPOST as (REP3 & _ & _ & _ & EDP3 & _). pose proof REP3 as (_ & _ & _ & _ & _ & _ & _ & DEP3 & _). unfold art_rt_depot in DEP3. rewrite EDP3 in DEP3. exact DEP3. }
          right. exists G', evs.
          split; [unfold Gfr0; cbn [art_gs_free g_log]; rewrite <- app_assoc; reflexivity|]. split; [exact (HBYd eq_refl)|]. exists Mr10. split; [|exact RPOST].
          unfold art_fpl_bundle. cbv zeta. repeat (split; [assumption|]). exact UF. }

  intros log' A' ms' model' B1 RT BH (regs' & Mr' & Est & P2 & PK & DIz & PKGS).
  destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr). set (M1 := ms_mem ms') in *. rewrite Ems. subst Mr'.
  destruct PKGS as [(d & lg & Elog & PKG & HDR)|(G' & evs & Elog & HBY3 & PKG3)].
  2: {
    pose proof (art_wfx_creditU FSG BUDGET rn G LB cr CRED CLSOK CND (proj1 (proj1 (art_items_pos_app _ _) (art_cr_items_pos FSG rn G LB _ REPr))) warm u n kb k true KBW Hin ltac:(clear - Hn; lia) (fun _ => HBY3)) as CREDd.
    cbv zeta in CREDd.
    destruct (art_wf_finish3 FSG (fun _ : art_run => FSINV rn) MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn (Kz :: rn_keys rn)) L HLlo HLhi HLst FSLAW2 FS_IN G LB FF LK (if warm then (fst cr + 1, snd cr) else cr)
                A A' M M1 model model' log' Sp u n q16 qr km kb k G' evs
                ROK OK Emu Room FS CREDd CLI KN LZ EG Hin ltac:(clear - Hn Hqr; lia) HHI HS47 LIVE Elog B1 BH PKG3) as (RI3 & AHP).
    rewrite <- HLsegs. apply (POST regs' M1 model' A').
    - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
    - rewrite HLscr. exact AHP.
    - exact RT.
    - destruct BH as (sfx & _ & INC & _). exact INC.
    - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
    - destruct RI3 as (G3 & REP3 & FS3 & REST3). exists G3. split; [exact REP3|]. split; [exact (FSKEYS rn (Kz :: rn_keys rn) _ _ _ _ FS3)|exact REST3]. }
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

  assert (LZ' : art_lazy_ok FSG rn Gfin A' (m_vm_lazy model')).
  { apply (art_lazy_ok_step FSG rn G Gfin A (m_vm_lazy model) A' (m_vm_lazy model') LZ INC).
    - intros x Hx. exact (proj1 (BH2 x Hx)).
    - intros wd Hwd. destruct (BH4 wd Hwd) as [Hi|(len & r & Hev & _)]; [exact Hi|]. exfalso. exact (NONULL _ _ Hev).
    - exact B5'.
    - intros x C. destruct (art_free_committed FSG rn G u n kb k d (U x) C) as [C0|V]; [left; exact C0|right; exact (VIS x V)]. }
  assert (EG' : art_eager_ok (lb_remove u LB) A' (m_vm_lazy model')) by exact (art_eager_ok_remove LB A (m_vm_lazy model) A' (m_vm_lazy model') u EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) B5').

  assert (SCR : forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None).
  { intros a Ha. assert (WM : wrA M (Sp - 4096) 4096) by (intros dd kk Hd Hk; rewrite <- HLsegs; apply SWR; assumption).
    pose proof (art_wr_wview ASEGS M (Sp - 4096) 4096 ltac:(lia) ltac:(lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by lia. specialize (V ltac:(lia)).
    rewrite art_wview_off in V by (rewrite art_u_lit by lia; right; lia). exact V. }
  assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
  destruct (art_wfc_client L HLlo HLhi HLst rn LB FF LK A A' M M1 FPT Sp u n qr ROK CLI INC GRF FRF NFPB NFPS NFPI NFS NSH UF Hq0 (FS_IN _ _ _ _ FS) SCR) as (CLI' & AHP).

  assert (EFS : g_fs FSG Gfin = g_fs FSG G) by (unfold Gfin; destruct d; reflexivity).
  assert (ELOG : g_log FSG Gfin = log') by (rewrite Elog; unfold Gfin; destruct d; reflexivity).
  assert (RI' : art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn (lb_remove u LB) FF LK (if warm then (fst cr + 1, snd cr) else cr) A' M1 (vml_of model')).
  { exists Gfin. cbn [vml_of fst snd].
    split; [exact REP'|]. split.
    { rewrite EFS. apply (FSLAW rn (g_fs FSG G) FF LK M M1 FS GRF). intros x Hz. apply FRF. destruct UF as (U1 & U2 & Uf). unfold apart, FS_BYTES in *.
      destruct Hz as [Z|[Z|[Z|[(Z & NS)|[Z|Z]]]]].
      - apply NFS. unfold FS_BYTES. exact Z.
      - apply NTH. exact Z.
      - apply (NSH (ar_fs (rn_ar rn)) 0xb09000 (U x)); [clear - Flo; lia|clear; lia|clear - Fhi G2; lia|clear - Afkb; lia|clear - Uf Hq0; lia|].
        pose proof (art_S_pred (ar_fs (rn_ar rn) + 0xb09000)). clear - Z H. unfold FS_BYTES in Z. lia.
      - apply NFPI; [exact Z|exact NS].
      - apply (NSH 0x10000 (0x698000 - 0x10000) (U x)); [clear; lia|clear; lia|clear; lia|left; clear - G4 Kspb; lia|left; clear - U1; lia|].
        pose proof (art_S_pred 0x698000). replace (0x10000 + (0x698000 - 0x10000) - 1) with (0x698000 - 1) by lia. clear - Z H. lia.
      - apply NDT. exact Z. }
    split. { rewrite ELOG. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
    split. { apply (art_wfx_creditU FSG BUDGET rn G LB cr CRED CLSOK); [|exact (proj1 (proj1 (art_items_pos_app _ _) (art_cr_items_pos FSG rn G LB _ REPr)))|exact KBW|exact Hin|clear - Hn; lia|exact HDR].
             destruct CLI as (_ & CNDx & _). apply NoDup_ListNoDup. exact CNDx. }
    split; [exact CLI'|]. split; [exact KN|]. split; [exact LZ'|exact EG']. }
  cbv beta zeta delta [HeapIfaceAEr.HAR.afree_postG] in POST. rewrite <- HLsegs.
  apply (POST regs' M1 model' A').
  - apply art_kept_preserved; [rewrite P2, H2; reflexivity|exact PK].
  - rewrite HLscr. exact AHP.
  - exact RT.
  - exact INC.
  - exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1).
  - apply (art_ri_inv_keys FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV FSKEYS rn (Kz :: rn_keys rn) _ _ _ _ _ _ _ RI').
    intros k1 H1. exact (art_dk_up _ _ _ _ _ _ _ H1 DIz).
Qed.

#[using="Halloc Hwx STATIC HLsegs HLfree HLscr HLtp HLlo HLhi HLst FSLAW FS_IN FSLAW2 FSKEYS FSKEYS_DN"] Theorem art_wrap_free : afree_spec L (rn_ar rn) scfg (art_iface FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn).
Proof.
  intros fx R M model LB FF LK cr A u n K RI Hhalt HMI Hin H10 H4 Hret AST K0 POST.
  pose proof RI as (G & REPr & _ & _ & _ & CLI & _ & LZ & _). cbn [vml_of fst snd] in REPr, LZ.
  pose proof REPr as (ROK & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
  set (Sp := U (getr R 2)) in *.
  pose proof AST as AST'. rewrite HLscr in AST'. destruct AST' as (S16 & SHI & SLE & STOP & SWR & SDEF).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof CLI as (_ & _ & _ & _ & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & _ & CSP & _). rewrite HIeq in CS1, CS2.
  set (Mr0 := mrestrict (mkH (m_vm_lazy model) A) M) in *.
  assert (RD0 : readable8 Mr0 Sp (ar_stack_top (rn_ar rn))). { apply (art_stack_readable FSG rn G A (m_vm_lazy model) M Sp (ar_stack_top (rn_ar rn)) ROK LZ ltac:(lia) ltac:(lia) SDEF). }
  assert (HS8 : Sp mod 8 = 0). { clear - S16. rewrite <- (Z.div_exact Sp 16) in S16 by Lia.lia. rewrite S16. replace (16 * (Sp / 16)) with ((2 * (Sp / 16)) * 8) by Lia.lia. apply Z_mod_mult. }
  destruct (ukeyG_total L (rn_ar rn) 0x7a2e0 Mr0 Sp (U (getr R 1)) (U (getr R 8)) ltac:(clear - G1 SHI; Lia.lia) ltac:(clear - SLE CSP; Lia.lia) HS8 ltac:(clear - CS4; Lia.lia) (u64_range _) (u64_range _)) as (Kz & UKz).
  { intros a Ha Ha' Ha8. destruct (RD0 a Ha Ha' Ha8) as [wq Cw]. exists (U wq). split; [apply u64_range|]. rewrite HLsegs. exact Cw. }
  apply (art_wrap_freeU fx R M model LB FF LK cr A u n K Kz false RI Hhalt HMI Hin H10 H4 Hret AST K0 ltac:(discriminate) UKz).

  intros regs' M' model' A' KEPT PRES RT INC MINV RI'.
  apply (POST regs' M' model' A' KEPT PRES RT INC MINV).
  exact (art_ri_inv_keys_dn (Kz :: rn_keys rn) _ _ _ _ _ _ _ RI' ltac:(apply incl_tl; apply incl_refl)).
Qed.
End Wrap.
