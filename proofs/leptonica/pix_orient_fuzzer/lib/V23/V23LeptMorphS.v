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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptDilW V23LeptHmtW V23LeptDilSegs V23LeptPma1S V23LeptHmtSegs V23LeptHmtNW.
Import ListNotations.
Open Scope bv_scope.

Section MorphS.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma dil_new_succ : forall C A m md regs (s pixs sel w h cm datas : Z) (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet)
    (kR bR : Z) (A1 : AS) (m2 : word -> option byte) (vm1 : VmMaps) (r2 : bvmap 5 word) (pixd cd data : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + DIL_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> sel_cont m sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  W C A1 m2 (with_vmmaps vm1 md) -> POSTM C A (s - 144) (O23LeptPma1.clone_mem (FRD m s ret regs) pixs (s - 128)) m2 ->
  O23LeptPixCopyT.pixt_new C A A1 m2 pixd w h 1 cd data cv ->
  getr r2 2 = Z_to_bv 64 (s - 144) -> getr r2 9 = Z_to_bv 64 sel -> getr r2 18 = Z_to_bv 64 pixs -> getr r2 10 = Z_to_bv 64 pixd ->
  (forall x, In x [3; 4; 27]%list -> getr r2 x = getr regs x) ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r2 (0xa19ac : word) m2 al_rom) (with_vmmaps vm1 md)) S.
Proof using P16 PINS.
  intros C A m md regs s pixs sel w h cm datas sv c cv ret S kR bR A1 m2 vm1 r2 pixd cd data.
  exact (dil_succ_W C A m md regs s pixs sel w h cm datas sv c cv ret S kR bR A1 m2 vm1 r2 pixd cd data).
Qed.

(* [comment removed for export] *)
Theorem pixDilate_new_sure_W : forall C A m md regs (s pixs sel w h cm datas : Z) (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + DIL_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> sel_cont m sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1968 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs sel w h cm datas sv c cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12
    PXs HOK Hw Hh Lps L0ps Ldat HCM SA SC Hcx Hcy SBD kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof Hlo as Hlo'. unfold DIL_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Ps0 & Ps64 & _).
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true)
    by (apply (W_sok_win C A m md (s - 144) 144 CK HW); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  destruct (dl_A al_rom regs m s 0 pixs sel ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q9 & Q18 & Q13 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP0 : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (SA0 : sel_at (alloc_top (c_vm C)) A (FRD m s ret regs) sel sv)
    by (apply (sel_at_keep _ A A m); [lia | exact SA | apply sub_live_refl | exact (proj2 PM0)]).
  pose proof SA0 as (Hsy & Hsx & _ & Lsel & RC0 & _).
  assert (PX0 : PIXat (FRD m s ret regs) pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. apply (O23LeptCmap2.LIVK_at A m _ pixs 64 x (proj2 PM0) Lps); lia. }
  assert (HCM0 : cm = 0%Z \/ (CMAPat (FRD m s ret regs) cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
    split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _).
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply (O23LeptCmap2.LIVK_at A m _ cm 24 x (proj2 PM0) Lcm); lia. }
  assert (PST : (c_top C - LSTK + O23LeptPma1.PMA1_STACK <= s - 144)%Z) by (change O23LeptPma1.PMA1_STACK with 3584%Z; lia).
  match type of Q1 with getr _ _ = ?rv =>
    apply (pma1_new_sure_W C A _ md r1 (s - 144) pixs sel (s - 128) w h cm datas (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv) cv rv S
             CK HW0 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) PST ltac:(lia)
             Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10 Q11 Q12 Q13 ltac:(lia) ltac:(lia) (sp_slot_al8 s 128 Hs16 eq_refl)
             PX0 HOK Hw Hh Lps L0ps HCM0 RC0 Lsel ltac:(lia) ltac:(lia) kR bR Hrm Hrk Hrb) end.
  intros A1 m2 vm1 r2 HW2 CS2 OUT2 AR2.
  destruct OUT2 as (pixd & cd & data & R10 & PT & PM2).
  pose proof (dil_new_succ C A m md regs s pixs sel w h cm datas sv c cv ret S kR bR A1 m2 vm1 r2 pixd cd data
                CK HW H2 Hs16 Hlo Hhi Hret PXs HOK Hw Hh Lps L0ps Ldat SA SC Hcx Hcy SBD HW2 PM2 PT
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R10
                ltac:(intros x Hx; cbn [In] in Hx; destruct Hx as [<- | [<- | [<- | []]]]; csr; reflexivity) AR2 HK) as D.
  match type of D with realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ => replace g with pc by (apply bv_eq; reflexivity) end end.
  exact D.
Qed.


(* [comment removed for export] *)
Theorem pixHMT_new_sure_W : forall C A m md regs (s pixs sel w h cm datas : Z) (sv : selv) (c : Z -> Z -> Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + HMT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> sel_cont m sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa2088 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs sel w h cm datas sv c cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12
    PXs HOK Hw Hh Lps L0ps Ldat HCM SA SC Hcx Hcy SBD kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof Hlo as Hlo'. unfold HMT_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Ps0 & Ps64 & _).
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true)
    by (apply (W_sok_win C A m md (s - 160) 160 CK HW); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  destruct (hm_A al_rom regs m s 0 pixs sel ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q9 & Q18 & Q13 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP0 : W C A (FRH m s ret regs) md /\ POSTM C A s m (FRH m s ret regs)) by (unfold FRH, FRD; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (SA0 : sel_at (alloc_top (c_vm C)) A (FRH m s ret regs) sel sv)
    by (apply (sel_at_keep _ A A m); [lia | exact SA | apply sub_live_refl | exact (proj2 PM0)]).
  pose proof SA0 as (Hsy & Hsx & _ & Lsel & RC0 & _).
  assert (PX0 : PIXat (FRH m s ret regs) pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. apply (O23LeptCmap2.LIVK_at A m _ pixs 64 x (proj2 PM0) Lps); lia. }
  assert (HCM0 : cm = 0%Z \/ (CMAPat (FRH m s ret regs) cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\
                                live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
    split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _).
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply (O23LeptCmap2.LIVK_at A m _ cm 24 x (proj2 PM0) Lcm); lia. }
  assert (PST : (c_top C - LSTK + O23LeptPma1.PMA1_STACK <= s - 160)%Z) by (change O23LeptPma1.PMA1_STACK with 3584%Z; lia).
  match type of Q1 with getr _ _ = ?rv =>
    apply (pma1_new_sure_W C A _ md r1 (s - 160) pixs sel (s - 152) w h cm datas (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv) cv rv S
             CK HW0 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) PST ltac:(lia)
             Q1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q10 Q11 Q12 Q13 ltac:(lia) ltac:(lia) (sp_slot_al8 s 152 Hs16 eq_refl)
             PX0 HOK Hw Hh Lps L0ps HCM0 RC0 Lsel ltac:(lia) ltac:(lia) kR bR Hrm Hrk Hrb) end.
  intros A1 m2 vm1 r2 HW2 CS2 OUT2 AR2.
  destruct OUT2 as (pixd & cd & data & R10 & PT & PM2).
  pose proof (hmt_new_succ C A m md regs s pixs sel w h cm datas sv c cv ret S kR bR A1 m2 vm1 r2 pixd cd data
                CK HW H2 Hs16 Hlo Hhi Hret PXs HOK Hw Hh Lps L0ps Ldat SA SC Hcx Hcy SBD HW2 PM2 PT
                ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R10
                ltac:(intros x Hx; cbn [In] in Hx; destruct Hx as [<- | [<- | []]]; csr; reflexivity) AR2 HK) as D.
  match type of D with realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?g _ _) _) _ => replace g with pc by (apply bv_eq; reflexivity) end end.
  exact D.
Qed.

End MorphS.
