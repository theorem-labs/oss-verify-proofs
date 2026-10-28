(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSel LeptSlots LeptExecT LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptCselsSpec V23LeptCloseA V23LeptCloseP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptCselsW V23LeptBordC32B V23LeptCloseN1 V23LeptCloseR V23LeptPixCopyG.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptCloseSpec O23LeptCloseIface O23LeptCselsSpec O23LeptCloseSegs O23LeptCloseA O23LeptCloseT O23LeptCloseP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section CloseW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac rk_solve := unfold O23LeptCloseT.rkept; let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.
Ltac pc_of L := lazymatch type of L with context [@mkst _ _ ?pc _ _] => pc end.
Ltac stk_ok := match goal with |- (?a + ?X <= ?b)%Z => let v := eval vm_compute in X in change X with v; lia end.

Lemma co1_k : forall (sh : bool) (s : Z), O23LeptCloseA.co1 sh s = (s - 112 + O23LeptCselsSpec.csels_k1 (O23LeptCloseA.ssz sh))%Z.
Proof. intros sh s. destruct sh; cbn; lia. Qed.

Lemma co2_k : forall (sh : bool) (s : Z), O23LeptCloseA.co2 sh s = (s - 112 + O23LeptCselsSpec.csels_k2 (O23LeptCloseA.ssz sh))%Z.
Proof. intros sh s. destruct sh; cbn; lia. Qed.

Lemma csK_eq : forall (sh : bool), O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) = O23LeptCloseSpec.RK_csc_sels (O23LeptCloseA.vsz sh).
Proof. intros sh. destruct sh; reflexivity. Qed.

Lemma room_k : forall (sh : bool) (kR : Z), (O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) <= kR)%Z ->
  (O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) <= kR)%Z /\
  (RK_pixcopy <= kR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh))%Z /\
  (kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) + (3 * RK_pixcopy + RK_cmapcopy)
     <= kR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) - RK_pixcopy)%Z /\
  (kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) <= kR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) - RK_pixcopy)%Z /\
  (0 <= kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh))%Z.
Proof.
  intros sh kR H. rewrite csK_eq. unfold O23LeptCloseSpec.RK_csc in *. unfold RK_pixcopy, RK_pix, RK_cmapcopy in *.
  assert (0 <= O23LeptCloseSpec.RK_csc_sels (O23LeptCloseA.vsz sh))%Z by (destruct sh; cbn; lia).
  lia.
Qed.

Lemma room_b : forall (sh : bool) (w h cm bR : Z), (O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm <= bR)%Z ->
  (O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) * 2 ^ 17 <= bR)%Z /\
  (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm <= bR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) * 2 ^ 17)%Z /\
  (bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm
     + (2 * (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm) + (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) + RB_cmapT cm)
     <= bR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) * 2 ^ 17 - (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm))%Z /\
  (bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm
     <= bR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) * 2 ^ 17 - (RB_pixT (4 * (wpl_of (w + 64) 1 * (h + 64))) + RB_cmapT cm))%Z /\
  (0 <= bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm)%Z.
Proof.
  intros sh w h cm bR H. rewrite csK_eq. unfold O23LeptCloseSpec.RB_csc in *.
  pose proof (RB_pixT_nonneg (4 * (wpl_of (w + 64) 1 * (h + 64)))). pose proof (RB_pixT_nonneg (4 * (wpl_of w 1 * h))).
  pose proof (RB_cmapT_le cm).
  assert (0 <= O23LeptCloseSpec.RK_csc_sels (O23LeptCloseA.vsz sh))%Z by (destruct sh; cbn; lia).
  lia.
Qed.

Lemma livk_pix : forall A m m' (p : Z) v, LIVK A m m' -> live A (Z_to_bv 64 p) = Some 64%Z -> PIXat m p v -> PIXat m' p v.
Proof.
  intros A m m' p v L Lp PX. apply (PIXat_frame m m' p v PX). intros x Hx.
  pose proof PX as (H0 & H64 & _). apply (LIVK_byte A m m' (Z_to_bv 64 p) 64 x L Lp). rewrite u_Z2bv by lia. lia.
Qed.

Lemma frc_cz : forall m (s : Z) (ret : word) (regs : bvmap 5 word) (sh : bool), (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 (O23LeptCloseA.cz1 sh s)) 8 = Some (Z_to_le_bytes 8 0) /\
  rdn SEGS (O23LeptCloseSegs.FRC m s ret regs) (Z_to_bv 64 (O23LeptCloseA.cz2 sh s)) 8 = Some (Z_to_le_bytes 8 0).
Proof.
  intros m s ret regs sh Hs Hs64. rewrite <- (w2b_Z 8 0) by lia.
  destruct sh; cbn [O23LeptCloseA.cz1 O23LeptCloseA.cz2]; unfold O23LeptCloseSegs.FRC; split; rdn_solve.
Qed.

Lemma cz_keep : forall (sh : bool) (m m' : word -> option byte) (s z : Z), (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (forall a : word, (s - 112 <= u a < s - 112 + 48)%Z ->
     ~ (s - 112 + O23LeptCselsSpec.csels_k1 (O23LeptCloseA.ssz sh) <= u a < s - 112 + O23LeptCselsSpec.csels_k1 (O23LeptCloseA.ssz sh) + 8)%Z ->
     ~ (s - 112 + O23LeptCselsSpec.csels_k2 (O23LeptCloseA.ssz sh) <= u a < s - 112 + O23LeptCselsSpec.csels_k2 (O23LeptCloseA.ssz sh) + 8)%Z ->
     m' a = m a) ->
  (z = O23LeptCloseA.cz1 sh s \/ z = O23LeptCloseA.cz2 sh s)%Z ->
  rdn SEGS m (Z_to_bv 64 z) 8 = Some (Z_to_le_bytes 8 0) -> rdn SEGS m' (Z_to_bv 64 z) 8 = Some (Z_to_le_bytes 8 0).
Proof.
  intros sh m m' s z Hs Hs64 K Hz R. rewrite <- R.
  destruct sh; cbn in K, Hz; destruct Hz as [-> | ->]; apply rdn_ext; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
    try lia; intros x Hx; apply K; lia.
Qed.

Lemma csc_head : forall (sh : bool) (fr : bvmap 5 word) (cs : bv 32) C Ar A m md regs (s pix1 w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  (forall fx, pcg2_contract fx) ->
  Cok C -> MBC C -> W C A m md -> sub_live Ar A -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pix1 -> getr regs 11 = Z_to_bv 64 pix1 -> getr regs 12 = Z_to_bv 64 (O23LeptCloseA.hsz sh) -> getr regs 13 = Z_to_bv 64 (O23LeptCloseA.vsz sh) ->
  O23LeptCloseSpec.pix1_at C Ar A m pix1 w h cm datas cv -> pix1 <> datas -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  aroom A (m_vmmaps md) kR bR -> (O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) <= kR)%Z -> (O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm <= bR)%Z ->
  csc_K fr C Ar A m md regs s pix1 (O23LeptCloseA.vsz sh) w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xa4878 : word) m al_rom) md) S.
Proof.
  intros sh fr cs C Ar A m md regs s pix1 w h cm datas cv ret S kR bR PCG CK MB HW SUB FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13
    PX Hpd HOK Hw Hh Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  assert (Hlo' : (c_top C - LSTK + 4368 <= s)%Z) by (unfold CSC_STACK in Hlo; lia).
  pose proof (u64_range (c_sp0 C)) as USP.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs112 : (112 <= s)%Z) by lia.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  pose proof PX as (PXa & Lp & Lpr & Lp0 & Ld & Ldr & Ld0 & CCM).
  pose proof PXa as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix1) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (AL8 : (pix1 mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
  destruct (room_k sh kR Hrk) as (RKa & RKb & RKc & RKd & RKe).
  destruct (room_b sh w h cm bR Hrb) as (RBa & RBb & RBc & RBd & RBe).
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (WP1 : W C A (O23LeptCloseSegs.FRC m s ret regs) md /\ POSTM C A s m (O23LeptCloseSegs.FRC m s ret regs))
    by (unfold O23LeptCloseSegs.FRC; wp_win CK).
  destruct WP1 as [HW1 PM1]. pose proof PM1 as [FR1m LV1].
  pose proof (livk_pix A m _ pix1 _ LV1 Lp PXa) as PX1.
  pose proof (PIX_rd_d SEGS _ _ _ PX1) as RDd.
  pose proof (W_mbc C A _ md CK HW1 MB) as RDg.
  destruct (@cs_A (mkFP fr cs) al_rom sh regs m s pix1 ret Hs112 Hs64 ltac:(lia) Hp64 AL8 SOK RDd RDg H2 H1 H10 H11 H12 H13)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q10 & Q11 & Q12 & Q13 & AG1).
  rzs HW RUN1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  assert (Q12' : getr r1 12 = Z_to_bv 64 (s - 112 + O23LeptCselsSpec.csels_k1 (O23LeptCloseA.ssz sh))%Z) by (rewrite Q12, co1_k; reflexivity).
  assert (Q13' : getr r1 13 = Z_to_bv 64 (s - 112 + O23LeptCselsSpec.csels_k2 (O23LeptCloseA.ssz sh))%Z) by (rewrite Q13, co2_k; reflexivity).
  assert (M16a : ((s - 112) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  apply (selectComposableSels_lit_W fr cs C A _ md r1 (s - 112)%Z (O23LeptCloseA.ssz sh) (O23LeptCloseA.sdir sh) (Z_to_bv 64 (pcS sh)) S
           CK HW1 FZ Q2 M16a ltac:(unfold CSELS_STACK; lia) ltac:(lia) Q1 (ret_ok_pcS sh) Q4 Q10 Q11 Q12' Q13'
           ltac:(destruct sh; cbn; lia) kR bR Hrm RKa RBa).
  intros fr2 cs2 A1 m1 vm1 r2 sel1 sel2 sv1 sv2 c1 c2 FZ2 FR2 HW2 CS2 R10 SUB1 PM2 Rs1 Rs2 KEEP SA1 SA2 SC1 SC2 N1 N2 SHP FRESH DIS LE AR2.
  destruct (@cs_C (mkFP fr2 cs2) al_rom sh r2 m1 pix1 R10 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
              ltac:(csr; reflexivity)) as (r3 & RUN3 & P1 & P9 & P10 & P11 & P12 & AG3).
  rzs HW2 RUN3.
  pose proof PM2 as [FR2m LV2].
  assert (LVa : LIVK A m m1) by (intros q k i Lq Hi; rewrite (LV2 q k i Lq Hi); exact (LV1 q k i Lq Hi)).
  assert (PMa : POSTM C A s m m1).
  { apply (POSTM_trans C A s m _ m1 PM1). apply (POSTM_mono C A (s - 112 + 48) s); [lia | exact PM2]. }
  pose proof (sub_live_trans Ar A A1 SUB SUB1) as SUBr1.
  pose proof (POSTM_sub C Ar A s m m1 SUB PMa) as PMr1.
  assert (SF : forall q, O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q -> live A q = None /\ live (c_A0 C) q = None).
  { intros q [(p0 & Hb0 & ->) | (p0 & Hb0 & ->)]; apply FRESH; [left | right]; exact Hb0. }
  assert (TL : forall q, O23LeptCloseA.tblk pix1 datas cm cv q -> exists n, live A q = Some n)
    by (intros q Hq; exact (O23LeptCloseP.p1_live3 C Ar A m pix1 w h cm datas cv q PX Hq)).
  assert (ST : forall q, O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q -> ~ O23LeptCloseA.tblk pix1 datas cm cv q)
    by exact (O23LeptCloseP.apart_fresh A _ _ (fun q H => proj1 (SF q H)) TL).
  assert (NS : forall q, ~ (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) -> live A1 q = live A q).
  { intros q Hq. apply LE. intros p0 Hb0 E. apply Hq. destruct Hb0 as [Hb0 | Hb0]; [left | right]; (exists p0; split; [exact Hb0 | exact E]). }
  assert (PX1' : O23LeptCloseSpec.pix1_at C Ar A1 m1 pix1 w h cm datas cv).
  { apply (O23LeptCloseA.p1_keep3 C Ar A A1 (fun _ => True) m m1 pix1 w h cm datas cv PX).
    - intros q Hq. apply NS. intros HS. exact (ST q HS Hq).
    - exact (O23LeptCloseA.PWK_livk A m m1 LVa).
    - exact I.
    - intros _; exact I. }
  assert (FS1 : FRS m1 s ret regs).
  { apply (FRS_keep (O23LeptCloseSegs.FRC m s ret regs) m1 s ret regs Hs112 Hs64 (FRS_FRC m s ret regs Hs112 Hs64)).
    intros a Ha. apply (FRM_pw C (s - 112 + 48) _ m1 CK FR2m); lia. }
  assert (C1 : rdn SEGS m1 (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1)) by (rewrite co1_k; exact Rs1).
  assert (C2 : rdn SEGS m1 (Z_to_bv 64 (O23LeptCloseA.co2 sh s)) 8 = Some (Z_to_le_bytes 8 sel2)) by (rewrite co2_k; exact Rs2).
  destruct (frc_cz m s ret regs sh Hs112 Hs64) as [Z1 Z2].
  pose proof (cz_keep sh _ m1 s _ Hs112 Hs64 KEEP (or_introl eq_refl) Z1) as Z1'.
  pose proof (cz_keep sh _ m1 s _ Hs112 Hs64 KEEP (or_intror eq_refl) Z2) as Z2'.
  assert (RS1 : RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A1 m1)
    by exact (conj FS1 (conj C1 (conj C2 (conj Z1' (conj Z2' (conj SUBr1 (conj PMr1 (conj PX1' (conj SA1 (conj SA2 (conj SC1 SC2))))))))))).
  assert (SS : O23LeptCloseT.sels_static C A sh sel1 sel2 sv1 sv2).
  { refine (conj N1 (conj N2 (conj SHP (conj SF _)))).
    intros q (p1 & Hp1 & ->) (p2 & Hp2 & E).
    destruct (sel_blk_live _ _ _ _ _ _ SA1 Hp1) as (n1 & _ & Hn1 & G1 & B1).
    destruct (sel_blk_live _ _ _ _ _ _ SA2 Hp2) as (n2 & _ & Hn2 & G2 & B2).
    apply (DIS p1 p2 Hp1 Hp2). apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. }
  pose proof PX1' as (PXb & Lpb & _ & _ & Ldb & _ & _ & CCb).
  assert (CVX : exists cvx, (cm = 0%Z \/ (CMAPat m1 cm cvx /\ O23LeptCmapValid.cmap_ok cvx /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\
                                         live A1 (Z_to_bv 64 (c_arr cvx)) = Some (4 * c_nalloc cvx)%Z)) /\
                            (cm = 0%Z -> ~ O23LeptCmapValid.cmap_ok cvx) /\ (cm <> 0%Z -> cvx = cv)).
  { destruct CCb as [E0 | (NZ & CMa & CMo & L1 & L2 & _)].
    - exists O23LeptCloseA.cvbad. split; [left; exact E0 | split; [intros _; exact O23LeptCloseA.cvbad_not_ok | intros NZ; contradiction]].
    - exists cv. split; [right; tauto | split; [intros E; contradiction | intros _; reflexivity]]. }
  destruct CVX as (cvx & HCMx & BADx & EQx).
  assert (Y2 : getr r3 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (Y4 : getr r3 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  assert (AR2' : aroom A1 (m_vmmaps (with_vmmaps vm1 md)) (kR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh))
                   (bR - O23LeptCloseIface.csels_K (O23LeptCloseA.ssz sh) * 2 ^ 17)) by (rewrite with_vmmaps_vmmaps; exact AR2).
  let pcR := pc_of csc_refused in
  apply (@pixAddBorder32C_any_W (mkFP fr2 cs2) AL CL ASR PINS P16 C A1 m1 (with_vmmaps vm1 md) r3 (s - 112) pix1 w h cm datas cvx pcR S
           CK HW2 Y2 M16a ltac:(stk_ok) ltac:(lia) ltac:(rewrite P1; apply bv_eq; reflexivity) ltac:(red; apply bv_eq; reflexivity)
           Y4 P10 P11 P12 PXb HOK Hw Hh Lpb Ldb HCMx _ _ AR2' RKb RBb).
  intros A0 m0 vm0 r0 HW0 CS0 PM0 ALT AR0.
  rewrite with_vmmaps_twice in HW0 |- *.
  pose proof PM0 as [FR0 LV0].
  assert (R0_2 : getr r0 2 = Z_to_bv 64 (s - 112)) by (csr; reflexivity).
  assert (R0_8 : getr r0 8 = Z_to_bv 64 pix1) by (csr; reflexivity).
  assert (R0_9 : getr r0 9 = Z_to_bv 64 32) by (csr; reflexivity).
  assert (R0_18 : getr r0 18 = Z_to_bv 64 (O23LeptCloseA.hsz sh)) by (csr; reflexivity).
  assert (R0_19 : getr r0 19 = Z_to_bv 64 (O23LeptCloseA.vsz sh)) by (csr; reflexivity).
  assert (RK0 : O23LeptCloseT.rkept regs r0) by rk_solve.
  assert (FS0 : forall a : word, (s - 104 <= u a < s - 72 \/ s - 48 <= u a < s)%Z -> m0 a = m1 a)
    by (intros a Ha; apply (FRM_pw C (s - 112) m1 m0 CK FR0); lia).
  pose proof (POSTM_sub C Ar A1 s m1 m0 SUBr1 (POSTM_mono C A1 (s - 112) s m1 m0 ltac:(lia) PM0)) as PM0r.
  destruct ALT as [[N0 LS0] | (pixsb & cdb & datab & R0_10 & HOK2 & PN)].
  - assert (SUB0 : sub_live A1 A0) by (intros q k Lq; rewrite LS0; exact Lq).
    assert (RS0 : RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0)
      by exact (RST_keep C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A1 m1 A0 (fun _ => True) m0 CK Hs112 Hhi RS1
                  (fun q _ => LS0 q) (O23LeptCloseA.PWK_livk A1 m1 m0 LV0) (fun _ _ => I) FS0 (sub_live_trans Ar A1 A0 SUBr1 SUB0) PM0r).
    assert (CSLM : O23LeptCloseA.cslm (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) A A0 cm cv cm cv).
    { apply O23LeptCloseA.cslm_of_LD.
      - intros q Hq. rewrite LS0. exact (NS q Hq).
      - intros q Hq. exact (proj1 (SF q Hq)). }
    exact (csc_refused sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr2 cs2 A0 m0 vm0 r0 _ _ sel1 sel2 sv1 sv2 c1 c2
             CK Hs16 Hlo Hhi Hret H2 H4 SUB FZ2 FR2 HW0 R0_2 R0_8 R0_9 R0_18 R0_19 N0 RK0 RS0 SS ST CSLM AR0 RKd RBd RKe RBe HK).
  - destruct (O23LeptCloseA.tpx_of_pixt C A1 A0 m0 pixsb (w + 64) (h + 64) cdb datab cvx PN) as (cvb & TPX & TFR & TKP & TCM).
    assert (RL1 : forall q, O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q -> exists n, live A1 q = Some n).
    { intros q [Hq | [Hq | Hq]].
      - exact (O23LeptCloseP.p1_live3 C Ar A1 m1 pix1 w h cm datas cv q PX1' Hq).
      - exact (O23LeptCloseP.sblk_live _ A1 m1 sel1 sv1 q SA1 Hq).
      - exact (O23LeptCloseP.sblk_live _ A1 m1 sel2 sv2 q SA2 Hq). }
    pose proof (O23LeptCloseP.apart_fresh A1 _ _ TFR RL1) as TNR.
    assert (SUB0 : sub_live A1 A0).
    { intros q k Lq. destruct (O23LeptCloseA.tblk_dec pixsb datab cdb cvb q) as [Tq | Tq].
      - rewrite (TFR q Tq) in Lq. discriminate.
      - rewrite (TKP q Tq). exact Lq. }
    assert (RS0 : RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0)
      by exact (RST_keep C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A1 m1 A0 (fun _ => True) m0 CK Hs112 Hhi RS1
                  (fun q Hq => TKP q (fun T => TNR q T Hq)) (O23LeptCloseA.PWK_livk A1 m1 m0 LV0) (fun _ _ => I) FS0
                  (sub_live_trans Ar A1 A0 SUBr1 SUB0) PM0r).
    pose proof (O23LeptCloseP.fresh_sub A A1 _ SUB1 TFR) as TFA.
    assert (CZ : cm = 0%Z -> cdb = 0%Z).
    { intros E0. destruct (Z.eq_dec cdb 0) as [Z0 | NZ]; [exact Z0 |]. exfalso. exact (BADx E0 (proj1 (TCM NZ))). }
    assert (CMQ : O23LeptCloseA.cmeq cdb cvb cv).
    { intros NZ. destruct (TCM NZ) as (OK & D1 & D2 & D3).
      assert (NZc : cm <> 0%Z) by (intros E0; exact (BADx E0 OK)).
      rewrite (EQx NZc) in D1, D2, D3. tauto. }
    assert (NB0 : forall q, ~ (O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q \/ O23LeptCloseA.tblk pixsb datab cdb cvb q) ->
                            live A0 q = live A q).
    { intros q Hq. rewrite (TKP q (fun T => Hq (or_intror (or_intror T)))). apply NS. intros [HS | HS]; apply Hq; [left | right; left]; exact HS. }
    exact (csc_normal sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr2 cs2 A0 m0 vm0 r0 _ _ sel1 sel2 sv1 sv2 c1 c2 pixsb cdb datab cvb
             (PCG _) CK MB Hs16 Hlo Hhi Hret H2 H4 SUB Hpd HOK Hw Hh HOK2 FZ2 FR2 HW0 R0_2 R0_8 R0_9 R0_18 R0_19 R0_10 RK0 RS0 SS ST TL TPX TFA TNR
             CZ CMQ (sub_live_trans A A1 A0 SUB1 SUB0) NB0 AR0 RKc RBc RKe RBe HK).
Qed.

(* [comment removed for export] *)
Lemma pixCloseSafeCompBrick_inplace_over : (forall fx, pcg2_contract fx) -> pixCloseSafeCompBrick_inplace_contract.
Proof.
  intros PCG fr cs C Ar A m md regs s pix1 hs vs w h cm datas cv ret S CK MB HW SUB FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 HSV
    PX Hpd HOK Hw Hh kR bR Hrm Hrk Hrb HK.
  destruct HSV as [[-> ->] | [-> ->]].
  - exact (csc_head false fr cs C Ar A m md regs s pix1 w h cm datas cv ret S kR bR PCG CK MB HW SUB FZ H2 Hs16 Hlo Hhi H1 Hret H4
             H10 H11 H12 H13 PX Hpd HOK Hw Hh Hrm Hrk Hrb HK).
  - exact (csc_head true fr cs C Ar A m md regs s pix1 w h cm datas cv ret S kR bR PCG CK MB HW SUB FZ H2 Hs16 Hlo Hhi H1 Hret H4
             H10 H11 H12 H13 PX Hpd HOK Hw Hh Hrm Hrk Hrb HK).
Qed.

(* [comment removed for export] *)
Lemma pcg2_of : forall fx : FPState, pcg2_contract fx.
Proof.
  intros fx. exact (@pixCopy_given_W fx AL CL ASR PINS P16).
Qed.

Theorem pixCloseSafeCompBrick_inplace_W : pixCloseSafeCompBrick_inplace_contract.
Proof.
  exact (pixCloseSafeCompBrick_inplace_over pcg2_of).
Qed.

End CloseW.
