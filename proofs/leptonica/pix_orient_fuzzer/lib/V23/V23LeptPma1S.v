(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith LeptRecs LeptSel LeptSlots GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptGrayAT O23LeptSelGP O23LeptPma1 O23LeptPma1G O23LeptSelFMT O23LeptHmtW O23LeptHmtNW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptGrayAT V23LeptPma1.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptErr V23LeptCmap2 V23LeptPixCopyST V23LeptSelGP V23LeptPixClone.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Pma1S.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Theorem pixCreateTemplate_sureT_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptGrayAT.PCT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h d cm datas) -> O23LeptPixHdr.hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm) <= bR)%Z ->
  TKs C A m md regs s w h d cm cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x6e078 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold O23LeptGrayAT.PCT_STACK, O23LeptBase.LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (pct_A al_rom regs m s pixs ret ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (O23LeptGrayAT.FR2 m s ret regs) md /\ POSTM C A s m (O23LeptGrayAT.FR2 m s ret regs)) by (unfold O23LeptGrayAT.FR2; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := O23LeptGrayAT.FR2 m s ret regs) in *.
  pose proof (cells2_FR2 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 16 <= bv_unsigned x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold O23LeptGrayAT.FR2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (O23LeptPixCopyST.hdv w h d cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplateNoInit_sureT_W C A M1 md r1 (s - 16) pixs w h d cm datas cv (Z_to_bv 64 0x6e08c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw Hh Lps HCM1 kR bR Hrm Hrk Hrb).
  intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x6e08c) with (0x6e08c : word) by (apply bv_eq; reflexivity).
  pose proof (cells2_frm C (s - 16) M1 m2 s _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  destruct OUTa as (pixd & cd & data & Hres & PT).
  apply (pct_tail_W C A A1 m md m2 vm1 regs r2 s pixd w h d cm cd data cv ret S kR bR CK HK Hrm1 Hs16 ltac:(lia) Hhi Hret HWa PMa' CE2
           ltac:(csr; reflexivity) Hres ltac:(unfold V23LeptGrayAT.ct_rest; rest_solve) H2 HOK Hw Hh PT).
Qed.

(* [comment removed for export] *)
Theorem pma1_new_sure_W : forall C A m md regs (s pixs sel pp w h cm datas sy sx cy cx sdata sname : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptPma1.PMA1_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel -> getr regs 13 = Z_to_bv 64 pp ->
  (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  RECat m sel (sel_flds sy sx cy cx sdata sname) -> live A (Z_to_bv 64 sel) = Some 32%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\
                           POSTM C A s (O23LeptPma1.clone_mem m pixs pp) m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1b7c : word) m al_rom) md) S.
Proof.
Proof.
  intros C A m md regs s pixs sel pp w h cm datas sy sx cy cx sdata sname cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13
    Hpp Hpp8 ALpp PXs HOK Hw Hh Lps L0ps HCM RC Lsel Hsy Hsx kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold O23LeptPma1.PMA1_STACK, O23LeptGrayAT.PCT_STACK, O23LeptBase.LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (RECat_range _ _ _ RC) as [Hsel0 Hsel32].
  change (Z.of_nat (flds_len (sel_flds sy sx cy cx sdata sname))) with 32%Z in Hsel32.
  destruct (blk_range C A m md (Z_to_bv 64 sel) 32 CK HW Lsel ltac:(lia)) as [Gsel TOPsel]. rewrite u_Z2bv in Gsel, TOPsel by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lsel) as (_ & ALsel & _). rewrite u_Z2bv in ALsel by lia.
  set (M1 := O23LeptPma1.MA m s ret regs pp).
  assert (OUT1 : forall x : word, (bv_unsigned x < s - 48)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold O23LeptPma1.MA, O23LeptCmap2.FR5.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia. reflexivity. }
  assert (PX1 : PIXat M1 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. apply OUT1. lia. }
  destruct (pma_A al_rom regs m s pixs sel pp (O23LeptPixCopyT.hdv w h 1 cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ALpp (al16_mod8 _ ALps) PX1 eq_refl
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A m md pp 8 CK HW ltac:(lia) ltac:(cbn; lia))
              H2 H1 H10 H11 H12 H13)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP0 : W C A (O23LeptCmap2.FR5 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FR5 m s ret regs)) by (unfold O23LeptCmap2.FR5; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (HW1 : W C A M1 md).
  { subst M1. unfold O23LeptPma1.MA. apply (W_store_win C A _ md); [exact CK | exact HW0 | rewrite u_Z2bv by lia; lia | lenb]. }
  assert (PM1 : POSTM C A s (O23LeptPma1.null_mem m pp) M1).
  { subst M1. unfold O23LeptPma1.MA, O23LeptPma1.null_mem. apply pma1_POSTM_wb2; [lenb | exact PM0]. }
  set (M2 := O23LeptSelGP.SGP2 M1 (s - 44) (s - 48) sy sx).
  assert (OUT2 : forall x : word, ~ (s - 48 <= bv_unsigned x < s - 40)%Z -> M2 x = M1 x).
  { intros x Hx. subst M2. apply O23LeptSelGP.SGP2_out; unfold O23LeptSelGP.cell_ok; lia. }
  assert (RC1 : RECat M1 sel (sel_flds sy sx cy cx sdata sname)).
  { apply (RECat_frame m); [exact RC|]. intros x Hx. change (Z.of_nat (flds_len (sel_flds sy sx cy cx sdata sname))) with 32%Z in Hx. apply OUT1. lia. }
  destruct (sgp2_run al_rom r1 M1 sel (s - 44) (s - 48) sy sx cy cx sdata sname (Z_to_bv 64 0xa1be0) RC1 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              (W_sok_win C A M1 md (s - 44) 4 CK HW1 ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A M1 md (s - 48) 4 CK HW1 ltac:(lia) ltac:(cbn; lia))
              ltac:(lia) ltac:(lia) (al16_mod8 _ ALsel) (sp_slot_al4' s 44 Hs16 eq_refl) (sp_slot_al4' s 48 Hs16 eq_refl)
              Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14)
    as (r2 & RUN2 & R10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  replace (Z_to_bv 64 0xa1be0) with (0xa1be0 : word) by (apply bv_eq; reflexivity).
  assert (INC2 : forall a : word, M2 a <> M1 a -> (s - 48 <= bv_unsigned a < s - 40)%Z).
  { intros a NE. destruct (Z_le_gt_dec (s - 48) (bv_unsigned a)); destruct (Z_lt_ge_dec (bv_unsigned a) (s - 40)); try lia;
      exfalso; apply NE; apply OUT2; lia. }
  assert (HW2 : W C A M2 md).
  { apply (W_local C A M1 md M2 s CK HW1 Hhi); [| subst M2; apply O23LeptSelGP.SGP2_grows].
    intros a NE. left. unfold scratch. pose proof (INC2 a NE). lia. }
  assert (PM2 : POSTM C A s M1 M2) by (apply (POSTM_range C A M1 md M2 (s - 48) (s - 40) s CK HW1 OUT2); lia).
  destruct (SGP2_rd M1 (s - 44) (s - 48) sy sx ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(lia) ltac:(lia)) as [Ry Rx].
  destruct (pma_C al_rom r2 M2 s pixs sy sx ltac:(lia) ltac:(lia) Hsy Hsx Ry Rx ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r3 & RUN3 & S1 & S10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN3 |].
  assert (PXs2 : PIXat M2 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite OUT2 by lia. apply OUT1. lia. }
  assert (HCM2 : cm = 0%Z \/ (CMAPat M2 cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT2 by lia. apply OUT1. lia. }
  apply (pixCreateTemplate_sureT_W C A M2 md r3 (s - 48) pixs w h 1 cm datas cv (Z_to_bv 64 0xa1d10) S CK HW2 ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold O23LeptGrayAT.PCT_STACK, O23LeptBase.LSF; lia) ltac:(lia)
           S1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) S10 PXs2 HOK Hw Hh Lps HCM2 kR bR Hrm Hrk Hrb).
  intros A1 m4 vm1 r4 HW4 CS4 PM4 OUT4 Hrm1.
  replace (Z_to_bv 64 0xa1d10) with (0xa1d10 : word) by (apply bv_eq; reflexivity).
  assert (CE4 : cells5 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { pose proof (cells5_FR5 m s ret regs ltac:(lia) ltac:(lia)) as CE0.
    assert (CE1 : cells5 M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
    { apply (cells5_out (O23LeptCmap2.FR5 m s ret regs) M1 pp (pp + 8) s); [| lia | lia | lia | exact CE0].
      intros x Hx. subst M1. unfold O23LeptPma1.MA. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
    apply (cells5_frm C (s - 48) M2 m4 s); [exact CK | exact (proj1 PM4) | lia | lia | lia |].
    apply (cells5_out M1 M2 (s - 48) (s - 40) s); [exact OUT2 | lia | lia | lia | exact CE1]. }
  destruct OUT4 as (pixd & cd & data & Resd & PT).
  pose proof PT as (Gd & TOPd & ALd & Gdat & TOPdat & ALdat & NEdd & L0d & L0dat & LC0d & LC0dat & L1d & L1dat & PXd & CMR).
  assert (NEq : forall q : Z, live A (Z_to_bv 64 q) = None -> Z_to_bv 64 pixs <> Z_to_bv 64 q).
  { intros q Lq E. rewrite E in Lps. congruence. }
  assert (L1ps : live A1 (Z_to_bv 64 pixs) = Some 64%Z).
  { destruct CMR as [(_ & EQ) | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0cd & L0ad & _ & _ & _ & _ & _ & EQ)].
    - rewrite EQ; [exact Lps | apply NEq; exact L0d | apply NEq; exact L0dat].
    - rewrite EQ; [exact Lps | apply NEq; exact L0d | apply NEq; exact L0dat | apply NEq; exact L0cd | apply NEq; exact L0ad]. }
  destruct (pma_D al_rom r4 m4 pixd pixs ltac:(lia) Resd ltac:(csr; reflexivity)) as (r5 & RUN5 & V1 & V8 & V10 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  assert (PXs4 : PIXat m4 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame M2); [exact PXs2|]. intros x Hx. apply (O23LeptCmap2.LIVK_at A M2 m4 pixs 64 x (proj2 PM4) Lps); lia. }
  replace (0x6eb08 : word) with (Z_to_bv 64 PC_pixClone) by (apply bv_eq; reflexivity).
  apply (pixClone_W fx C A1 m4 _ r5 (s - 48) pixs (O23LeptPixCopyT.hdv w h 1 cm datas) (Z_to_bv 64 0xa1d20) S CK HW4 ltac:(csr; reflexivity)
           ltac:(lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V10 PXs4 eq_refl L1ps L0ps).
  intros m5 r6 Em5 HW5 CS6 R10'.
  replace (Z_to_bv 64 0xa1d20) with (0xa1d20 : word) by (apply bv_eq; reflexivity).
  assert (DJd : (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z).
  { destruct (blk_apart C A1 m4 _ (Z_to_bv 64 pixs) (Z_to_bv 64 pixd) 64 64 CK HW4 L1ps L1d (NEq pixd L0d) ltac:(lia) ltac:(lia)) as [X|X];
      rewrite !u_Z2bv in X by lia; lia. }
  assert (OUT5 : forall x : word, ~ (pixs + 20 <= bv_unsigned x < pixs + 24)%Z -> m5 x = m4 x).
  { intros x Hx. rewrite Em5. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
  set (m6 := wbytes m5 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs))).
  assert (OUT6 : forall x : word, ~ (pp <= bv_unsigned x < pp + 8)%Z -> m6 x = m5 x).
  { intros x Hx. subst m6. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
  assert (CE6 : cells5 m6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (cells5_out m5 m6 pp (pp + 8) s); [exact OUT6 | lia | lia | lia |].
    apply (cells5_out m4 m5 (pixs + 20) (pixs + 24) s); [exact OUT5 | lia | lia | lia | exact CE4]. }
  destruct (pma_E al_rom r6 m5 s pp pixd pixs ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) Hret ltac:(lia) ltac:(lia)
              CE6 (W_sok_win C A1 m5 _ pp 8 CK HW5 ltac:(lia) ltac:(cbn; lia)) ltac:(csr; reflexivity) R10' ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & U18 & U19 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
  assert (HW6 : W C A1 m6 (with_vmmaps vm1 md)).
  { subst m6. apply (W_store_win C A1 m5 _); [exact CK | exact HW5 | rewrite u_Z2bv by lia; lia | lenb]. }
  apply (HK A1 m6 vm1 r7 HW6).
  + apply cs_kept_intro; csr; try reflexivity.
  + exists pixd, cd, data. split; [exact U10 | split].
    * apply (O23LeptPma1.pixt_new_frame C A A1 m4 m6 pixd w h 1 cd data cv PT).
      -- intros x Hx. rewrite OUT6 by lia. apply OUT5. lia.
      -- intros NZ x Hx.
         destruct CMR as [(CD0 & _) | (ad & _ & Gcd & TOPcd & _ & _ & _ & _ & _ & _ & _ & L0cd & _ & _ & _ & L1cd & _ & _ & _)]; [contradiction |].
         assert (DJc : (pixs + 64 <= cd \/ cd + 24 <= pixs)%Z).
         { destruct (blk_apart C A1 m4 _ (Z_to_bv 64 pixs) (Z_to_bv 64 cd) 64 24 CK HW4 L1ps L1cd (NEq cd L0cd) ltac:(lia) ltac:(lia)) as [X|X];
             rewrite !u_Z2bv in X by lia; lia. }
         rewrite OUT6 by lia. apply OUT5. lia.
    * apply (POSTM_trans C A s _ (wbytes (wbytes (O23LeptPma1.null_mem m pp) (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs)))).
      -- apply pma1_POSTM_ext. intros x. unfold O23LeptPma1.clone_mem, O23LeptPma1.null_mem.
         apply pma1_wb_same; [lenb |]. intros Hx. apply pma1_wb_same; [lenb |]. intros _.
         rewrite wbytes_outside; [reflexivity | lenb | revert Hx; lenb].
      -- subst m6. rewrite Em5. apply pma1_POSTM_wb2; [lenb |]. apply pma1_POSTM_wb2; [lenb |].
         eapply POSTM_trans; [exact PM1 |]. eapply POSTM_trans; [exact PM2 |]. eapply POSTM_mono; [| exact PM4]; lia.
  + exact Hrm1.
Qed.

End Pma1S.
