(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA PmHeapIfaceA PmShadowW As0StepLib As0Tables
     ArtMem ArtTac Pm5ArtInitCache Pm5ArtPopulate1 ArtRuns ArtRunsMem Pm5ArtCls Pm5ArtFp Pm5ArtClsRep Pm5ArtClsGfa2 Pm5ArtClsRefill Pm5ArtCellEx Pm5ArtByteCell Pm5ArtCARSpec Pm5ArtAlloc3Pure Pm5ArtDepot Pm5ArtUnwind
     Pm5ArtAllocG ArtBridge Pm5ArtAllocate3 Pm5ArtInv Pm5ArtInvMallocPure Pm5ArtInvMalloc Pm5ArtLift Pm5ArtWrapPure Pm5ArtWrapKit Pm5ArtWrapMallocH Pm5ArtWrapMallocX Pm5ArtWrapMallocC Pm5ArtWrapMalloc Pm5ArtIfaceLaws
     Pm5ArtWrapMallocLC Pm5ArtWrapMallocL Pm5ArtFxQ Pm5ArtFxBatch2 Pm5ArtFxBatch3 Pm5ArtFxDrain Pm5ArtFxImg Pm5ArtImgCell Pm5ArtFreeTop3 Pm5ArtInvFreePure Pm5ArtInvFree Pm5ArtInvRepX Pm5ArtInvDrain Pm5ArtWrapFreeA Pm5ArtWrapFreeC
     Pm5ArtRecycle1 Pm5ArtRecycle2C Pm5ArtRecycle4S Pm5ArtRecycle5A Pm5ArtInvRecycleA Pm5ArtInvRecycleD Pm5ArtInvRecycleE Pm5ArtWrapFreeR Pm5ArtFreeTop3P Pm5ArtFreeTop3Q Pm5ArtInvFreeP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac rok_openW ROK :=
  destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
                   & Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
                   & Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb & Kb0).
Ltac geo_openW GEO :=
  destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).

(* [comment removed for export] *)
Section EntryP.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte).
Hypothesis REP : art_alloc_rep FSG rn G LB M.

Lemma art_wfp_kind : forall u n, In (u, n) LB -> 2 ^ 28 < n ->
  exists idx s, nth_error (g_sec FSG G) idx = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n.
Proof.
  intros u n Hin BIG. destruct REP as (_ & _ & _ & _ & CH & _ & _ & _ & _ & BLK & _).
  destruct (BLK (u, n) Hin) as [(c & w & Hc & V & St)|(s & Hs & Hq & Eu & En)]; cbn [fst snd] in *.
  - exfalso. specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III.
    destruct III as (_ & _ & _ & (bb & _ & _ & _ & _ & Hn0) & _). clear - BIG Hn0. lia.
  - destruct (In_nth_error _ _ Hs) as (i & Hi). exists i, s. split; [exact Hi|]. split; [exact Hq|]. split; [exact Eu|exact En].
Qed.
End EntryP.

(* [comment removed for export] *)
Section FinishP.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6c4000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis FSLAW2 : forall gfs FF LK (M M' : word -> option byte), FSINV rn gfs FF LK M -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) ->
  (forall a : word, in_shadow_rw (U a) -> M' a <> None) -> FSINV rn gfs FF LK M'.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
#[local] Abbreviation BInv := (ArtBridge.BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).

Theorem art_wf_finishP : forall (G : art_gs FSG) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model)
    (log' : list aev) (Sp u n q16 qr : Z) (idx : nat) (s : art_sec) (kb : nat),
  let mb := sc_map s in let ms := sc_msize s in
  let Mr0 := mrestrict (bhid A model) M in let Mr1 := mrestrict (bhid A' model') M1 in
  art_alloc_rep FSG rn G LB Mr0 ->
  FSINV rn (g_fs FSG G) FF LK M -> art_credit_ok FSG BUDGET rn G LB cr -> art_client_ok rn LB FF LK A M -> art_kn_ok MAPS0 RESV0 rn ->
  art_lazy_ok FSG rn G A (m_vm_lazy model) -> art_eager_ok LB A (m_vm_lazy model) ->
  g_depot FSG G = Datatypes.S kb -> In (u, n) LB -> 2 ^ 28 < n < 2 ^ 39 -> u = 16 * q16 -> n <= 8 * qr <= n + 7 ->
  nth_error (g_sec FSG G) idx = Some s -> sc_quar s = false -> sc_u s = u -> sc_n s = n ->
  rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 ->
  (forall p, In p (art_live (g_log FSG G)) ->
     0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
     /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
  (forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p')) ->
  (forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0) ->
  (forall b0, In b0 (lb_remove u LB) -> In b0 LB /\ fst b0 <> u) ->
  wrA Mr0 (Sp - 4096) 4096 ->
  log' = g_log FSG G ++ art_flush_events mb ms ++ [AMunmap mb ms] ->
  BInv log' A' M1 model' ->
  bhist A M model (g_log FSG G) log' A' M1 model' ->
  art_free3P_out Mr0 Mr1 Sp (rn_t rn) u (rn_l2 rn) (rn_blk rn) (rn_parr rn) mb ms (map art_sec_b (g_sec FSG G)) idx kb ->
  art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn (lb_remove u LB) FF LK cr A' M1 (vml_of model')
  /\ aheap_pres L (rn_ar rn) (lb_remove u LB) FF Sp 4096 M M1.
Proof.
  intros G LB FF LK cr A A' M M1 model model' log' Sp u n q16 qr idx s kb mb ms Mr0 Mr1
         REP FS CRED CLI KN LZ EG Edep Hin Hn Eu Hqr Hidx Hsq Hsu Hsn HHI HS47 LIVE LIVE2 LIVE3 Hother W0 Elog B1 BH OUT.
  set (G' := art_gs_freeP G idx mb ms kb).
  pose proof (art_alloc_rep_freeP FSG rn G LB Mr0 Mr1 Sp u n mb ms idx s kb REP Hn Hidx Hsq Hsu Hsn eq_refl eq_refl HHI HS47 Edep OUT LIVE LIVE2 LIVE3 Hother) as REP'. fold G' in REP'.
  set (FPALL := art_fP_FPALL FSG rn G Sp u mb ms idx). set (FPT := fun z => ~ art_out FPALL z).
  assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
  (* [comment removed for export] *)
  assert (FR : forall x : word, ~ FPT (U x) -> Mr1 x = Mr0 x).
  { intros x N. destruct (art_out_dec FPALL (U x)) as [O|O]; [|exfalso; exact (N O)]. exact (art_fP_frame FSG rn G Mr0 Mr1 Sp u mb ms idx kb OUT x O). }
  assert (EVL : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z -> FPT z).
  { intros sfx El z Hz. rewrite Elog in El. apply app_inv_head in El. subst sfx.
    exact (art_fP_ev_range FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl Edep LIVE LIVE3 z Hz). }
  pose proof (art_lift_frame A A' M M1 model model' (g_log FSG G) log' BH FPT FR EVL) as FRF.
  pose proof BH as (sfx & Esfx & INC & BH2 & _ & BH4 & BH5).
  assert (Esfx' : sfx = art_flush_events mb ms ++ [AMunmap mb ms]). { rewrite Elog in Esfx. apply app_inv_head in Esfx. symmetry. exact Esfx. }
  assert (KINDS : forall ev, In ev sfx -> (exists a l, ev = AMadvise a l) \/ (exists a l, ev = AMunmap a l)).
  { intros ev Hev. rewrite Esfx' in Hev. apply in_app_or in Hev. destruct Hev as [Hev|[<-|[]]]; [|right; eexists; eexists; reflexivity].
    unfold art_flush_events in Hev. destruct (art_flush_beg mb <? art_flush_end mb ms); [|destruct Hev]. destruct Hev as [<-|[]]. left. eexists; eexists; reflexivity. }
  assert (NONULL : forall len r, ~ In (AMmapNull len r) sfx). { intros len r Hev. destruct (KINDS _ Hev) as [(a & l & E)|(a & l & E)]; discriminate E. }
  assert (NONR : forall a l, ~ In (AMmapFixedNR a l) sfx). { intros a l Hev. destruct (KINDS _ Hev) as [(a0 & l0 & E)|(a0 & l0 & E)]; discriminate E. }
  assert (B5' : forall x : word, page_in_ranges (page_base x) (m_vm_lazy model') = true -> page_in_ranges (page_base x) (m_vm_lazy model) = true).
  { intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. exact (NONR _ _ Hev). }
  pose proof REP as (ROK & _). pose proof ROK as ROK'. rok_openW ROK'. pose proof GEO as GEO'. geo_openW GEO'.
  (* [comment removed for export] *)
  assert (LZ' : art_lazy_ok FSG rn G' A' (m_vm_lazy model')).
  { apply (art_lazy_ok_step FSG rn G G' A (m_vm_lazy model) A' (m_vm_lazy model') LZ INC).
    - intros x Hx. exact (proj1 (BH2 x Hx)).
    - intros wd Hwd. destruct (BH4 wd Hwd) as [Hi|(len & r & Hev & _)]; [exact Hi|]. exfalso. exact (NONULL _ _ Hev).
    - exact B5'.
    - intros x C. left. unfold art_committed in C |- *. unfold G' in C. cbn [art_gs_freeP g_cls g_sec_committed] in C. exact C. }
  assert (EG' : art_eager_ok (lb_remove u LB) A' (m_vm_lazy model')) by exact (art_eager_ok_remove LB A (m_vm_lazy model) A' (m_vm_lazy model') u EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) B5').
  (* [comment removed for export] *)
  assert (NFPB : forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ FPT a).
  { intros b0 a Hb Ha X. exact (X (art_fP_out_blk FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl HHI HS47 Edep LIVE LIVE2 LIVE3 Hother b0 a Hb Ha)). }
  assert (NFPS : forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ FPT a).
  { intros a Ha Ns X. exact (X (art_fP_out_stack FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl HHI Edep LIVE LIVE3 a (proj1 Ha) Ns)). }
  assert (NFPI : forall a, 0x10000 <= a < 0x6c4000 -> ~ art_zone_statics a -> ~ FPT a).
  { intros a Ha Nz X. exact (X (art_fP_out_img FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl HHI HS47 Edep LIVE LIVE3 a Ha Nz)). }
  assert (NFS : forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ FPT a).
  { intros a Ha X. exact (X (art_fP_out_fs FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl HHI HS47 Edep LIVE LIVE3 a Ha)). }
  assert (NDT : forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> ~ FPT a).
  { intros a Ha X. exact (X (art_fP_out_dtls FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl HHI HS47 Edep LIVE LIVE3 a Ha)). }
  assert (NTH : forall a, rn_t rn + 72 <= a < rn_t rn + 80 -> ~ FPT a).
  { intros a Ha X. exact (X (art_fP_out_th72 FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl HHI HS47 Edep LIVE LIVE3 a Ha)). }
  assert (NSH : forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
            (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> (forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) lo len) ->
            HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPT a).
  { intros lo len a H0 Hl H47 Hk _ Hlv Ha X. exact (X (art_fP_out_shw FSG rn G LB Mr0 Sp u n mb ms idx s kb REP Hn Hidx Hsu Hsn eq_refl eq_refl HHI HS47 Edep LIVE LIVE3 lo len a H0 Hl H47 Hk Hlv Ha)). }
  destruct (art_fP_ufacts FSG rn G LB Mr0 u n mb ms idx s kb REP Hn Hidx Hsq Hsu Hsn eq_refl eq_refl Edep LIVE LIVE3 q16 qr Eu Hqr) as (U1 & U2 & U3 & U4 & U5 & U6 & _ & _ & Uf & _).
  assert (UF : 0x6c4000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES).
  { split; [clear - U1 U5 Hn; lia|]. split; [clear - U2 U3; lia|exact Uf]. }
  (* [comment removed for export] *)
  destruct OUT as (_ & _ & _ & FW & _).
  assert (WSCR : wrA Mr1 (Sp - 4096) 4096). { apply FW; [clear - HHI G1; lia|clear - HS47; lia|unfold apart; clear - U3 HHI; lia|exact W0]. }
  assert (SCR1 : forall a, Sp - 4096 <= a < Sp -> M1 (Z_to_bv 64 a) <> None).
  { intros a Ha. pose proof (art_wr_wview ASEGS Mr1 (Sp - 4096) 4096 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) WSCR (Z_to_bv 64 a)) as V.
    rewrite art_u_lit in V by (clear - Ha HHI G1 HS47; lia). specialize (V ltac:(clear - Ha; lia)). rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha HHI G1 HS47; lia); right; clear - Ha HHI G1; lia).
    unfold Mr1, mrestrict in V. destruct (bhid A' model' (Z_to_bv 64 a)); [exfalso; apply V; reflexivity|exact V]. }
  assert (LVF : forall p, In p (art_live (g_log FSG G)) -> 0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))).
  { intros p Hp. destruct (LIVE p Hp) as (X0 & X1 & X2 & _ & X4). split; [exact X0|]. split; [exact X1|]. split; [exact X2|exact X4]. }
  destruct (art_wfc_client_r L HLlo HLhi HLst rn LB FF LK A A' M M1 FPT (art_live (g_log FSG G)) Sp u n qr ROK CLI INC FRF NFPB NFPS NFPI NFS NSH LVF UF Hq0 (FS_IN _ _ _ _ FS) SCR1) as (CLI' & AHP).
  split; [|exact AHP].
  (* [comment removed for export] *)
  exists G'. cbn [vml_of fst snd]. fold Mr1.
  split; [exact REP'|]. split.
  { unfold G'. cbn [art_gs_freeP g_fs]. apply (FSLAW2 (g_fs FSG G) FF LK M M1 FS); [|exact (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B1)]. intros x Hz. apply FRF. destruct UF as (_ & _ & Uf'). unfold FS_BYTES in *.
    destruct Hz as [Z|[Z|[Z|[(Z & NS)|[Z|Z]]]]].
    - apply NFS. unfold FS_BYTES. exact Z.
    - apply NTH. exact Z.
    - apply (NSH (ar_fs (rn_ar rn)) 0xb09000 (U x)); [clear - Flo; lia|clear; lia|clear - Fhi G2; lia|unfold apart in Afkb; clear - Afkb; lia|unfold apart in Uf'; clear - Uf' Hq0; lia| |].
      + intros p Hp. destruct (LVF p Hp) as (_ & _ & _ & OB). pose proof (OB (ar_fs (rn_ar rn), FS_BYTES) (proj1 (art_objs_in_r rn))) as Ap. cbn [fst snd] in Ap. unfold FS_BYTES in Ap. exact Ap.
      + pose proof (art_S_pred (ar_fs (rn_ar rn) + 0xb09000)). unfold FS_BYTES in Z. clear - Z H. lia.
    - apply NFPI; assumption.
    - apply (NSH 0x10000 (0x6c4000 - 0x10000) (U x)); [clear; lia|clear; lia|clear; lia|left; clear - G4 Kspb; lia|left; clear - U1; lia| |].
      + intros p Hp. destruct (LVF p Hp) as (_ & P1 & _ & OB).
        destruct (art_objs_in_r rn) as (_ & I1 & I2 & I3 & I4).
        pose proof (OB _ I1) as A1. pose proof (OB _ I2) as A2. pose proof (OB _ I3) as A3. pose proof (OB _ I4) as A4.
        cbn [fst snd] in A1, A2, A3, A4. unfold apart in A1, A2, A3, A4 |- *. clear - A1 A2 A3 A4 P1. lia.
      + pose proof (art_S_pred 0x6c4000). replace (0x10000 + (0x6c4000 - 0x10000) - 1) with (0x6c4000 - 1) by lia. clear - Z H. lia.
    - apply NDT. exact Z. }
  split. { assert (ELOG : g_log FSG G' = log') by (rewrite Elog; unfold G'; cbn [art_gs_freeP g_log]; reflexivity). rewrite ELOG. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
  split; [exact (art_fP_credit FSG rn G LB u n mb ms idx s kb Hin Hidx Edep BUDGET cr CRED)|].
  split; [exact CLI'|]. split; [exact KN|]. split; [exact LZ'|exact EG'].
Qed.
End FinishP.
