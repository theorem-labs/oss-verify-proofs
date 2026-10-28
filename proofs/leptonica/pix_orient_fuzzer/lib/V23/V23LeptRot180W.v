(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyTR.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr V23LeptUb V23LeptRotHip_iface V23LeptRot180 V23LeptRotTBW V23_code_r90a_rot180.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptPixCopyTR V23LeptRotLRW.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_r180_pixd : str16 0x126da 13.
Proof. refine (conj _ (conj _ (conj _ _))); [vm_compute; reflexivity | lia | lia | apply Z.leb_le; vm_compute; reflexivity]. Qed.
Lemma str_r180 : str16 0x13e08 12.
Proof. refine (conj _ (conj _ (conj _ _))); [vm_compute; reflexivity | lia | lia | apply Z.leb_le; vm_compute; reflexivity]. Qed.

Section Rot180W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma cells3_frm : forall C s' m m' s ret v8 v9, Cok C -> FRM C s' m m' ->
  (s' <= s - 24)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9)]%Z -> cellsZ m' [(s - 8, ret); (s - 16, v8); (s - 24, v9)]%Z.
Proof.
  intros C s' m m' s ret v8 v9 CK F Hs' Hlo Hs64 CE. cbn [cellsZ] in CE |- *. destruct CE as (R1 & R2 & R3 & _).
  rewrite <- p16_segs in R1, R2, R3 |- *.
  rewrite !(FRM_rdn_above C s' m m' _ 8 CK F) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  repeat split; assumption.
Qed.

Section Segs.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Lemma r180_E : forall regs m (s : Z) (ret v8 v9 : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9)]%Z ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x98ac0 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = v8 /\ getr regs' 9 = v9
      /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x13e08 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s ret v8 v9 Hs Hs64 CE Rg Rs H2 H10. cbn [cellsZ] in CE. destruct CE as (R8 & R16 & R24 & _).
    eexists. split.
    - stepb_tk F_98ac0 D_98ac0 ltac:(condZ).
      sn F_98b08 D_98b08.
      stepLD F_98b0c D_98b0c (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_98b10 D_98b10 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_98b14 D_98b14. stepb_ft F_98b18 D_98b18 ltac:(condZ).
      sn F_98b1c D_98b1c. sn F_98b20 D_98b20. sn F_98b24 D_98b24. sn F_98b28 D_98b28.
      sn F_98b2c D_98b2c.
      sn F_98b54 D_98b54.
      stepLD8 F_98b58 D_98b58 ret. stepLD8 F_98b5c D_98b5c v8. stepLD8 F_98b60 D_98b60 v9.
      zv F_98b64 D_98b64 (Z_to_bv 64 s). sn F_98b68 D_98b68.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Lemma pixt_sub : forall C A A1 m pixd w h d cd data cv, pixt_new C A A1 m pixd w h d cd data cv -> sub_live A A1.
Proof.
  intros C A A1 m pixd w h d cd data cv PT.
  destruct PT as (_ & _ & _ & _ & _ & _ & _ & L0p & L0d & _ & _ & _ & _ & _ & CMR).
  intros q k Lq.
  destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LAcd & LAad & _ & _ & _ & _ & _ & LEQ)].
  - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
  - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence].
Qed.

(* [comment removed for export] *)
Lemma pixt_transfer : forall C A A1 A2 m m' pixd w h d cd data cv,
  pixt_new C A A1 m pixd w h d cd data cv -> (forall q, live A2 q = live A1 q) -> (0 <= data < 2 ^ 64)%Z ->
  PIXat m' pixd (hdv w h d cd data) ->
  (forall q k i, live A1 q = Some k -> q <> Z_to_bv 64 data -> (0 <= i < k)%Z -> m' (at_ q i) = m (at_ q i)) ->
  pixt_new C A A2 m' pixd w h d cd data cv.
Proof.
  intros C A A1 A2 m m' pixd w h d cd data cv PT LEQ Hd PX KEEP.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & _ & CMR).
  unfold pixt_new. rewrite !LEQ. do 13 (split; [assumption|]). split; [exact PX|].
  destruct CMR as [[CD0 LE] | (ad & CMOK & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L1cd & L1ad & CM & LE)].
  - left. split; [exact CD0|]. intros q N1 N2. rewrite LEQ. apply LE; assumption.
  - right. exists ad. rewrite !LEQ. do 16 (split; [assumption|]). split.
    + apply (CMAPat_frame m); [exact CM|]. intros x Hx.
      assert (EX : x = at_ (Z_to_bv 64 cd) (u x - cd)).
      { unfold at_. rewrite u_Z2bv by lia. replace (cd + (u x - cd))%Z with (u x + 0)%Z by lia. symmetry. apply at_self. }
      rewrite EX. apply (KEEP _ 24%Z); [exact L1cd | apply zbv_ne2; lia | lia].
    + intros q N1 N2 N3 N4. rewrite LEQ. apply LE; assumption.
Qed.

Lemma wpl1_facts : forall w : Z, (1 <= w)%Z -> (1 <= wpl_of w 1)%Z /\ (w <= 32 * wpl_of w 1)%Z.
Proof.
  intros w Hw. unfold wpl_of.
  pose proof (Z.div_mod (w * 1 + 31) 32 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (w * 1 + 31) 32 ltac:(lia)) as B.
  split; lia.
Qed.

Section WithHip.
Hypothesis HIP : rasteropHipLow_contract.

Definition R180_STACK : Z := 32 + 176 + 16 + LSF.

(* [comment removed for export] *)
Theorem pixRotate180_W : forall C A m md regs (s pixs rc w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + R180_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy + 3 <= kR)%Z ->
  (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm + alloc_margin 256 + 2 * alloc_margin (4 * wpl_of w 1) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy - 3) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) - alloc_margin 256 - 2 * alloc_margin (4 * wpl_of w 1)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x98a70 : word) m al_rom) md) S.
Proof using All.
  intros C A m md regs s pixs rc w h cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold R180_STACK, LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  destruct (wpl1_facts w Hw) as [Hwpl1 Hwpl32].
  pose proof (alloc_margin_ge 256 ltac:(lia)) as AM1. pose proof (alloc_margin_ge (4 * wpl_of w 1) ltac:(lia)) as AM2.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  destruct (r180_A al_rom regs m s pixs (hdvr rc w h 1 cm datas) ret ltac:(lia) Hs64 ltac:(lia) (al16_mod8 _ ALps) PXs ltac:(lia) eq_refl
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR180 m s ret regs) md /\ POSTM C A s m (FR180 m s ret regs)) by (unfold FR180; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (CE1 : cellsZ (FR180 m s ret regs) [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9)]%Z).
  { unfold FR180. cbn [cellsZ]. repeat split; rdn_solve. }
  assert (OUT1 : forall x : word, ~ (s - 32 <= u x < s)%Z -> FR180 m s ret regs x = m x).
  { intros x Hx. unfold FR180. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  set (M1 := FR180 m s ret regs) in *.
  assert (PXs1 : PIXat M1 pixs (hdvr rc w h 1 cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  apply (V23LeptPixCopyTR.pixCopy_szTR_W C A M1 md r1 (s - 32)%Z pixs rc w h 1%Z cm datas cv (Z_to_bv 64 0x98ac0) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11
           PXs1 HOK Hw Hh Lps Lds HCM1 kR bR Hrm ltac:(lia) ltac:(lia)).
  unfold V23LeptPixCopyTR.TK. intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x98ac0) with (0x98ac0 : word) by (apply bv_eq; reflexivity).
  pose proof (cells3_frm C (s - 32) M1 m2 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) Hs64 CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - destruct (r180_E al_rom r2 m2 s ret (getr regs 8) (getr regs 9) ltac:(lia) Hs64 CE2 (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V8 & V9 & V10 & V11 & V12 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 s 0x126da%Z 0x13e08%Z 13%Z 12%Z ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_r180_pixd str_r180).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + apply (aroom_mono _ _ _ _ _ _ Hrm1); lia.
  - pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR).
    pose proof (pixt_sub C A A1 m2 pixd w h 1 cd data cv PT) as SUBa.
    destruct (r180_B al_rom r2 m2 pixd ltac:(lia) Hres) as (r3 & RUN3 & X1 & X8 & X10 & X11 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (X2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (X4 : getr r3 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (NEw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    apply (V23LeptRotLRW.pixFlipLR_inplace_W HIP C A A1 m2 (with_vmmaps vm1 md) r3 (s - 32)%Z pixd (4 * (wpl_of w 1 * h))%Z (hdv w h 1 cd data) (Z_to_bv 64 0x98ad0) S
             CK HWa SUBa X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold V23LeptRotLRW.LR_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)
             X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11 PXd eq_refl L1p NEw
             ltac:(cbn [p_w hdv]; lia) ltac:(cbn [p_w p_wpl hdv]; lia) ltac:(cbn [p_wpl hdv]; lia) ltac:(cbn [p_h hdv]; lia) ltac:(cbn [p_wpl p_h hdv]; lia)
             L1d ltac:(cbn [p_wpl p_h hdv]; lia) L0d L00d
             (kR - RK_pixcopy)%Z (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm))%Z ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1) ltac:(lia) ltac:(cbn [p_wpl hdv]; lia)).
    intros A2 m3 vm2 r4 HW3 CS3 PM3 LEQ3 KEEP3 PX3 R10 Hrm2.
    rewrite with_vmmaps_twice in HW3 |- *.
    replace (Z_to_bv 64 0x98ad0) with (0x98ad0 : word) by (apply bv_eq; reflexivity).
    pose proof (cells3_frm C (s - 32) m2 m3 s _ _ _ CK (proj1 PM3) ltac:(lia) ltac:(lia) Hs64 CE2) as CE3.
    assert (SUB2 : sub_live A A2) by (exact (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LEQ3))).
    assert (L2p : live A2 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite LEQ3; exact L1p).
    assert (L2d : live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of w 1 * h))%Z) by (rewrite LEQ3; exact L1d).
    destruct (r180_C al_rom r4 m3) as (r5 & RUN5 & Y1 & Y10 & Y11 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    assert (Y8 : getr r4 8 = Z_to_bv 64 pixd) by (csr; reflexivity).
    rewrite Y8 in Y10, Y11.
    assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (Y4 : getr r5 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    apply (pixFlipTB_inplace_W C A A2 m3 (with_vmmaps vm2 md) r5 (s - 32) pixd (4 * (wpl_of w 1 * h)) (hdv w h 1 cd data) (Z_to_bv 64 0x98adc) S
             CK HW3 SUB2 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold TB_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)
             Y1 ltac:(red; apply bv_eq; reflexivity) Y4 Y10 Y11 PX3 eq_refl L2p NEw
             ltac:(cbn [p_wpl hdv]; lia) ltac:(cbn [p_h hdv]; lia) ltac:(cbn [p_wpl p_h hdv]; lia)
             L2d ltac:(cbn [p_wpl p_h hdv]; lia) L0d L00d
             (kR - RK_pixcopy - 2) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) - alloc_margin 256 - alloc_margin (4 * wpl_of w 1))
             ltac:(rewrite with_vmmaps_vmmaps; exact Hrm2) ltac:(lia) ltac:(cbn [p_wpl hdv]; lia)).
    intros A3 m4 vm3 r6 HW4 CS4 PM4 LEQ4 KEEP4 PX4 R10' Hrm3.
    rewrite with_vmmaps_twice in HW4 |- *.
    replace (Z_to_bv 64 0x98adc) with (0x98adc : word) by (apply bv_eq; reflexivity).
    pose proof (cells3_frm C (s - 32) m3 m4 s _ _ _ CK (proj1 PM4) ltac:(lia) ltac:(lia) Hs64 CE3) as CE4.
    destruct (r180_D al_rom r6 m4 s ret (getr regs 8) (getr regs 9) ltac:(lia) Hs64 Hret CE4 ltac:(csr; reflexivity))
      as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |].
    apply (HK A3 m4 vm3 r7 HW4).
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. eapply POSTM_mono; [| eapply POSTM_trans; [exact PM3 | exact PM4]]. lia.
    + right. exists pixd, cd, data. split.
      * rewrite Z10. csr; reflexivity.
      * apply (pixt_transfer C A A1 A3 m2 m4 pixd w h 1 cd data cv PT).
        -- intros q. rewrite LEQ4, LEQ3. reflexivity.
        -- lia.
        -- exact PX4.
        -- intros q k i Lq NE Hi. rewrite (KEEP4 q k i) by (first [rewrite LEQ3; exact Lq | exact NE | lia]). exact (KEEP3 q k i Lq NE Hi).
    + apply (aroom_mono _ _ _ _ _ _ Hrm3); cbn [p_wpl hdv]; lia.
Qed.

End WithHip.

End Rot180W.
