(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptSlots LeptRecs LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyT O23LeptPixCreateT2 O23LeptCloseSpec O23LeptCascW O23LeptTextSelW O23LeptMorphSeqSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptCmapValid V23LeptCmap2 V23LeptPixDestroy V23LeptPixDestroyK V23LeptPixMisc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptPixCopyT V23LeptPixCreateT2 V23LeptSelGP V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptMorphSeqSpec V23LeptSelDW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptRop_iface V23LeptDilW V23LeptHmtW V23LeptMorphS V23LeptPixOr V23LeptRb2W V23LeptCascW V23LeptCountW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUddSegs V23LeptUddLib V23LeptUddT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LiaRel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptUddLib O23LeptUddSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelGP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_rel.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition RK_blk : Z := RK_pixcopy + RK_pixcopy + RK_casc + 1.
Definition RB_blk (w h : Z) : Z := 2 * (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapcopy) + RB_casc w h + 2 ^ 17.

Section UddB.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Instance udb_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac mod16 Hs16 := rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity.
Ltac in_app := solve [repeat (first [assumption | apply in_or_app; first [left; assumption | right]])].
Ltac rk := unfold RK_blk, RK_casc, RK_pixcopy, RK_pix, RK_cmapcopy, RB_blk in *.
Ltac wsz := rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Ltac rhs H := lazymatch type of H with _ = ?x => x end.

Lemma udb_pc : forall (fx : FPState) r (p q : word) (mm : word -> option byte) md (S : TSet), bv_unsigned p = bv_unsigned q ->
  realizes SEGS (mkCfg (@mkst fx r p mm al_rom) md) S -> realizes SEGS (mkCfg (@mkst fx r q mm al_rom) md) S.
Proof. intros fx r p q mm md S E H. apply bv_eq in E. subst q. exact H. Qed.

Ltac rzp HW RUN := eapply udb_pc; [| rzs HW RUN]; [reflexivity |].

(* [comment removed for export] *)
Lemma udd_blk1_tail : forall fr5 cs5 C A A5 (m m5 : word -> option byte) md vm5 regs r5
    (s pix1 w h cd1 data1 pix2 cd2 data2 pix3 w3 h3 data3 : Z) (cv1 cv2 : cmapv) (bc : list byte) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md -> W C A5 m5 (with_vmmaps vm5 md) -> frm_zero cs5 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + UDD_STACK <= s)%Z -> (s <= c_top C)%Z ->
  cs_kept regs r5 -> getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 4 = Z_to_bv 64 0x1381d0 -> getr regs 9 = Z_to_bv 64 0 ->
  rdn SEGS m5 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pix1) ->
  rdn SEGS m5 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pix2) ->
  rdn SEGS m5 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3) ->
  rdn SEGS m5 (Z_to_bv 64 (s - 124)) 4 = Some bc -> length bc = 4%nat ->
  (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
     (b + Z.of_nat n <= s - 124 \/ s - 124 + 4 <= b)%Z -> rdn SEGS m5 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
  O23LeptUddLib.PIXC C A5 m5 pix1 w h cd1 data1 cv1 -> O23LeptUddLib.PIXC C A5 m5 pix2 w h cd2 data2 cv2 -> O23LeptUddLib.PIXO C A5 m5 pix3 w3 h3 data3 ->
  (1 <= w)%Z -> (1 <= h)%Z -> (pix3 <> 0%Z -> (1 <= w3)%Z /\ (1 <= h3)%Z) ->
  O23LeptUddLib.disj (O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2)) (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1)) ->
  O23LeptUddLib.disj (O23LeptUddLib.pixo_l pix3 data3) (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1)) -> O23LeptUddLib.disj (O23LeptUddLib.pixo_l pix3 data3) (O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2)) ->
  O23LeptUddLib.only A A5 (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1) ++ O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2) ++ O23LeptUddLib.pixo_l pix3 data3) ->
  O23LeptUddLib.offs A (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1) ++ O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2) ++ O23LeptUddLib.pixo_l pix3 data3) ->
  POSTM C A s m m5 -> aroom A5 vm5 kR bR ->
  (forall fr' cs' A' m' vm' regs' (bc' : list byte), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     (forall q, live A' q = live A q) -> POSTM C A s m m' ->
     (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
        (b + Z.of_nat n <= s - 124 \/ s - 124 + 4 <= b)%Z -> rdn SEGS m' (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
     rdn SEGS m' (Z_to_bv 64 (s - 124)) 4 = Some bc' -> length bc' = 4%nat -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (0xafc50 : word) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr5 cs5) r5 (0xafc20 : word) m5 al_rom) (with_vmmaps vm5 md)) S.
Proof.
  intros fr5 cs5 C A A5 m m5 md vm5 regs r5 s pix1 w h cd1 data1 pix2 cd2 data2 pix3 w3 h3 data3 cv1 cv2 bc S kR bR
    CK HW HW5 FZ Hs16 Hlo Hhi CS5 H2 H4 H9 R1 R2 R3 RB LB FR5 PC1 PC2 PO3 Hw Hh Hwh3 D21 D31 D32 ON OF PM5 RM5 K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold UDD_STACK, MSEQ_STACK, CSC_STACK in Hlo.
  pose proof (aroom_nonneg _ _ _ _ RM5) as [Hk0 Hb0].
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hs256 : (256 <= s)%Z) by lia.
  assert (Hsp16 : ((s - 256) mod 16 = 0)%Z) by mod16 Hs16.
  set (L1 := O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1)) in *.
  set (L2 := O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2)) in *.
  set (L3 := O23LeptUddLib.pixo_l pix3 data3) in *.
  pose proof PC1 as (PX1 & L1a & L10 & LD1 & LD10 & NE1 & _).
  pose proof PC2 as (PX2 & _ & _ & LD2 & _ & _ & _).
  pose proof PX1 as (P1a & P1b & WF1 & _). pose proof PX2 as (P2a & P2b & WF2 & _).
  assert (Hd1 : (0 <= data1 < 2 ^ 64)%Z) by exact (wf_data _ WF1).
  assert (Hd2 : (0 <= data2 < 2 ^ 64)%Z) by exact (wf_data _ WF2).
  assert (HR1 : (0 < 4 * (wpl_of w 1 * h))%Z) by (pose proof (O23LeptUddLib.wpl_pos w Hw); nia).
  destruct (blk_range C A5 m5 _ _ _ CK HW5 LD1 HR1) as [B1 _]. rewrite u_Z2bv in B1 by lia.
  destruct (blk_range C A5 m5 _ _ _ CK HW5 LD2 HR1) as [B2 _]. rewrite u_Z2bv in B2 by lia.
  assert (R1w : rdn SEGS m5 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pix1))) by (rewrite w2b_Z by lia; exact R1).
  destruct (ud_B1f al_rom (mkFP fr5 cs5) r5 m5 s (Z_to_bv 64 pix1) Hs256 Hs64 R1w ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r6 & RUN6 & F6a & F6b & AG6).
  rzp HW5 RUN6.
  let ra := rhs F6a in
  eapply udb_pc; [| apply (pixDestroy_keep_W (fx := mkFP fr5 cs5) C A5 m5 (with_vmmaps vm5 md) r6 (s - 256) (s - 144) pix1 cd1 (4 * c_nalloc cv1)
      (4 * (wpl_of w 1 * h)) _ cv1 ra S CK HW5 ltac:(csr; reflexivity) Hsp16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) F6a
      ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) F6b R1 PX1
      eq_refl eq_refl eq_refl L1a L10 LD1 LD10 HR1 NE1 (O23LeptUddLib.PIXC_dprem _ _ _ _ _ _ _ _ _ PC1))]; [reflexivity |].
  intros A6 m6 vm6 r7 HW6 CS7 PD6 PM6 Z6 LOW6 RT6.
  rewrite with_vmmaps_twice in HW6 |- *. rewrite with_vmmaps_vmmaps in RT6.
  assert (X6 : O23LeptUddLib.only A5 A6 L1 /\ O23LeptUddLib.offs A6 L1) by exact (O23LeptUddLib.pixd_post_l A5 A6 pix1 data1 cd1 (c_arr cv1) ltac:(lia) PD6).
  destruct X6 as [ON6 OF6].
  pose proof (RT6 kR bR RM5 ltac:(lia) ltac:(lia)) as RM6. rewrite !Z.sub_0_r in RM6.
  assert (ONA6 : O23LeptUddLib.only A A6 (L1 ++ L2 ++ L3)).
  { apply (O23LeptUddLib.only_trans_l A A5 A6 _ ON). apply (O23LeptUddLib.only_sub A5 A6 L1 _ ON6). intros q Hq; in_app. }
  pose proof (O23LeptUddLib.sub_of_only A A6 _ ONA6 OF) as SUB6.
  assert (PMA6 : POSTM C A s m m6).
  { eapply POSTM_trans; [exact PM5 |]. apply (POSTM_sub C A A6 s m5 m6 SUB6). eapply POSTM_mono; [| exact PM6]; lia. }
  assert (FR6 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
     (b + Z.of_nat n <= s - 124 \/ s - 124 + 4 <= b)%Z -> rdn SEGS m6 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3 Hb4.
    rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 Hb1 ltac:(lia) ltac:(lia)).
    exact (FR5 b n Hb1 Hb2 Hb3 Hb4). }
  assert (RB6 : rdn SEGS m6 (Z_to_bv 64 (s - 124)) 4 = Some bc).
  { rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) (s - 124) 4 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact RB. }
  assert (R26 : rdn SEGS m6 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pix2)).
  { rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) (s - 152) 8 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact R2. }
  assert (R36 : rdn SEGS m6 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
  { rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) (s - 160) 8 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact R3. }
  pose proof (O23LeptUddLib.PIXC_dst C A5 A6 m5 m6 pix2 w h cd2 data2 cv2 L1 PC2 ON6 D21 (proj2 PM6)) as PC26.
  pose proof (O23LeptUddLib.PIXO_dst C A5 A6 m5 m6 pix3 w3 h3 data3 L1 PO3 ON6 D31 (proj2 PM6)) as PO36.
  destruct (ud_B1g al_rom (mkFP fr5 cs5) r7 m6 s Hs256 Hs64 ltac:(csr; reflexivity)) as (r8 & RUN8 & F8a & F8b & AG8).
  rzp HW6 RUN8.
  pose proof PC26 as (PX26 & L2a & L20 & LD26 & LD20 & NE2 & _).
  let ra := rhs F8a in
  eapply udb_pc; [| apply (pixDestroy_keep_W (fx := mkFP fr5 cs5) C A6 m6 (with_vmmaps vm6 md) r8 (s - 256) (s - 152) pix2 cd2 (4 * c_nalloc cv2)
      (4 * (wpl_of w 1 * h)) _ cv2 ra S CK HW6 ltac:(csr; reflexivity) Hsp16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) F8a
      ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) F8b R26 PX26
      eq_refl eq_refl eq_refl L2a L20 LD26 LD20 HR1 NE2 (O23LeptUddLib.PIXC_dprem _ _ _ _ _ _ _ _ _ PC26))]; [reflexivity |].
  intros A7 m7 vm7 r9 HW7 CS9 PD7 PM7 Z7 LOW7 RT7.
  rewrite with_vmmaps_twice in HW7 |- *. rewrite with_vmmaps_vmmaps in RT7.
  assert (X7 : O23LeptUddLib.only A6 A7 L2 /\ O23LeptUddLib.offs A7 L2) by exact (O23LeptUddLib.pixd_post_l A6 A7 pix2 data2 cd2 (c_arr cv2) ltac:(lia) PD7).
  destruct X7 as [ON7 OF7].
  pose proof (RT7 kR bR RM6 ltac:(lia) ltac:(lia)) as RM7. rewrite !Z.sub_0_r in RM7.
  assert (ONA7 : O23LeptUddLib.only A A7 (L1 ++ L2 ++ L3)).
  { apply (O23LeptUddLib.only_trans_l A A6 A7 _ ONA6). apply (O23LeptUddLib.only_sub A6 A7 L2 _ ON7). intros q Hq; in_app. }
  pose proof (O23LeptUddLib.sub_of_only A A7 _ ONA7 OF) as SUB7.
  assert (PMA7 : POSTM C A s m m7).
  { eapply POSTM_trans; [exact PMA6 |]. apply (POSTM_sub C A A7 s m6 m7 SUB7). eapply POSTM_mono; [| exact PM7]; lia. }
  assert (FR7 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
     (b + Z.of_nat n <= s - 124 \/ s - 124 + 4 <= b)%Z -> rdn SEGS m7 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3 Hb4.
    rewrite (dst_rd C A7 m6 m7 (s - 256) (s - 152) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM7 LOW7 Hb1 ltac:(lia) ltac:(lia)).
    exact (FR6 b n Hb1 Hb2 Hb3 Hb4). }
  assert (RB7 : rdn SEGS m7 (Z_to_bv 64 (s - 124)) 4 = Some bc).
  { rewrite (dst_rd C A7 m6 m7 (s - 256) (s - 152) (s - 124) 4 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM7 LOW7 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact RB6. }
  assert (R37 : rdn SEGS m7 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
  { rewrite (dst_rd C A7 m6 m7 (s - 256) (s - 152) (s - 160) 8 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM7 LOW7 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact R36. }
  pose proof (O23LeptUddLib.PIXO_dst C A6 A7 m6 m7 pix3 w3 h3 data3 L2 PO36 ON7 D32 (proj2 PM7)) as PO37.
  destruct (ud_B1h al_rom (mkFP fr5 cs5) r9 m7 s Hs256 Hs64 ltac:(csr; reflexivity)) as (r10 & RUN10 & F10a & F10b & AG10).
  rzp HW7 RUN10.
  assert (CS10 : cs_kept regs r10) by (apply cs_kept_intro; csr; reflexivity).
  let ra := rhs F10a in
  assert (FIN : forall A8 m8 vm8 r11, W C A8 m8 (with_vmmaps vm8 md) -> cs_kept r10 r11 ->
      O23LeptUddLib.only A7 A8 L3 -> O23LeptUddLib.offs A8 L3 -> POSTM C A8 (s - 152) m7 m8 ->
      (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 152 <= b)%Z ->
         rdn SEGS m8 (Z_to_bv 64 b) n = rdn SEGS m7 (Z_to_bv 64 b) n) ->
      aroom A8 vm8 kR bR ->
      realizes SEGS (mkCfg (@mkst (mkFP fr5 cs5) r11 ra m8 al_rom) (with_vmmaps vm8 md)) S).
  { intros A8 m8 vm8 r11 HW8 CS11 ON8 OF8 PM8 FR8 RM8.
    assert (ONm : O23LeptUddLib.only A6 A8 (L2 ++ L3)) by exact (O23LeptUddLib.only_trans A6 A7 A8 L2 L3 ON7 ON8).
    assert (ONf5 : O23LeptUddLib.only A5 A8 (L1 ++ L2 ++ L3)) by exact (O23LeptUddLib.only_trans A5 A6 A8 L1 (L2 ++ L3) ON6 ONm).
    assert (ONf : O23LeptUddLib.only A A8 (L1 ++ L2 ++ L3)) by exact (O23LeptUddLib.only_trans_l A A5 A8 _ ON ONf5).
    assert (OF2 : O23LeptUddLib.offs A8 L2) by exact (O23LeptUddLib.offs_only A7 A8 L2 L3 OF7 ON8 OF8).
    assert (OF23 : O23LeptUddLib.offs A8 (L2 ++ L3)) by exact (O23LeptUddLib.offs_app A8 L2 L3 OF2 OF8).
    assert (OF1 : O23LeptUddLib.offs A8 L1) by exact (O23LeptUddLib.offs_only A6 A8 L1 (L2 ++ L3) OF6 ONm OF23).
    assert (OFf : O23LeptUddLib.offs A8 (L1 ++ L2 ++ L3)) by exact (O23LeptUddLib.offs_app A8 L1 (L2 ++ L3) OF1 OF23).
    pose proof (O23LeptUddLib.sub_of_only A A8 _ ONf OF) as SUB8.
    eapply udb_pc; [| apply (K fr5 cs5 A8 m8 vm8 r11 bc HW8 FZ)].
    1: reflexivity.
    - exact (cs_kept_trans regs r10 r11 CS10 CS11).
    - exact (O23LeptUddLib.live_eq_fin A A8 _ ONf OF OFf).
    - eapply POSTM_trans; [exact PMA7 |]. apply (POSTM_sub C A A8 s m7 m8 SUB8). eapply POSTM_mono; [| exact PM8]; lia.
    - intros b n Hb1 Hb2 Hb3 Hb4. rewrite (FR8 b n Hb1 Hb2 ltac:(lia)). exact (FR7 b n Hb1 Hb2 Hb3 Hb4).
    - rewrite (FR8 (s - 124)%Z 4%nat ltac:(lia) ltac:(lia) ltac:(lia)). exact RB7.
    - exact LB.
    - exact RM8. }
  destruct PO37 as [E3 | [NZ3 PC3]].
  - subst pix3.
    let ra := rhs F10a in
    eapply udb_pc; [| apply (pixDestroy_null_W (fx := mkFP fr5 cs5) C A7 m7 (with_vmmaps vm7 md) r10 (s - 256) (s - 160) None ra S CK HW7
        ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) F10a ltac:(red; apply bv_eq; reflexivity) F10b ltac:(split; lia)
        ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) R37)]; [reflexivity |].
    intros m8 r11 HW8 CS11 PM8 OUT8.
    apply (FIN A7 m8 vm7 r11 HW8 CS11).
    + apply O23LeptUddLib.only_refl.
    + intros q Hq. unfold L3, O23LeptUddLib.pixo_l in Hq. cbn in Hq. destruct Hq.
    + eapply POSTM_mono; [| exact PM8]; lia.
    + intros b n Hb1 Hb2 Hb3. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
      intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT8. lia.
    + exact RM7.
  - pose proof PC3 as (PX3 & L3a & L30 & LD3 & LD30 & NE3 & _).
    pose proof PX3 as (P3a & P3b & WF3 & _).
    assert (Hd3 : (0 <= data3 < 2 ^ 64)%Z) by exact (wf_data _ WF3).
    assert (HR3 : (0 < 4 * (wpl_of w3 1 * h3))%Z) by (destruct (Hwh3 NZ3); pose proof (O23LeptUddLib.wpl_pos w3 ltac:(lia)); nia).
    destruct (blk_range C A7 m7 _ _ _ CK HW7 LD3 HR3) as [B3 _]. rewrite u_Z2bv in B3 by lia.
    let ra := rhs F10a in
    eapply udb_pc; [| apply (pixDestroy_keep_W (fx := mkFP fr5 cs5) C A7 m7 (with_vmmaps vm7 md) r10 (s - 256) (s - 160) pix3 0 0
        (4 * (wpl_of w3 1 * h3)) _ cmap0 ra S CK HW7 ltac:(csr; reflexivity) Hsp16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) F10a
        ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) F10b R37 PX3
        eq_refl eq_refl eq_refl L3a L30 LD3 LD30 HR3 NE3 (or_introl eq_refl))]; [reflexivity |].
    intros A8 m8 vm8 r11 HW8 CS11 PD8 PM8 Z8 LOW8 RT8.
    rewrite with_vmmaps_twice in HW8 |- *. rewrite with_vmmaps_vmmaps in RT8.
    assert (X8 : O23LeptUddLib.only A7 A8 L3 /\ O23LeptUddLib.offs A8 L3).
    { unfold L3. rewrite (O23LeptUddLib.pixo_l_ne pix3 data3 NZ3).
      exact (O23LeptUddLib.pixd_post_l A7 A8 pix3 data3 0 (c_arr cmap0) ltac:(lia) PD8). }
    destruct X8 as [ON8 OF8].
    apply (FIN A8 m8 vm8 r11 HW8 CS11 ON8 OF8).
    + eapply POSTM_mono; [| exact PM8]; lia.
    + intros b n Hb1 Hb2 Hb3.
      exact (dst_rd C A8 m7 m8 (s - 256) (s - 160) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM8 LOW8 Hb1 ltac:(lia) ltac:(lia)).
    + pose proof (RT8 kR bR RM7 ltac:(lia) ltac:(lia)) as RM8. rewrite !Z.sub_0_r in RM8. exact RM8.
Qed.

Lemma udb_livke : forall C A (m m' : word -> option byte) md (d kd s : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 d) = Some kd ->
  (0 <= d < 2 ^ 64)%Z -> (forall a : word, ~ scratch C s a -> ~ (d <= bv_unsigned a < d + kd)%Z -> m' a = m a) -> O23LeptRb2W.LIVKe A d m m'.
Proof.
  intros C A m m' md d kd s CK HW Ld Hd FR q k i Lq NE Hi.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hk : (0 < k)%Z) by lia.
  destruct (blk_range C A m md q k CK HW Lq Hk) as [Q1 Q2].
  apply FR.
  - unfold scratch, at_. rewrite u_Z2bv by lia. lia.
  - unfold at_. rewrite u_Z2bv by lia.
    destruct (Z_le_gt_dec kd 0) as [Hkd | Hkd]; [lia |].
    destruct (live_apart C A m md (Z_to_bv 64 d) q kd k CK HW Ld Lq (not_eq_sym NE) ltac:(lia) ltac:(lia)) as [D | D];
      rewrite u_Z2bv in D by lia; lia.
Qed.

Lemma udb_sel_cont_keep : forall T (A : AS) (m m' : word -> option byte) sel sv c, (T < 2 ^ 64)%Z -> sel_at T A m sel sv -> LIVK A m m' ->
  sel_cont m sv c -> sel_cont m' sv c.
Proof.
  intros T A m m' sel sv c HT SA LK SC i j Hi Hj. destruct (SC i j Hi Hj) as [Hc R]. split; [exact Hc |]. rewrite <- R.
  destruct SA as (Hsy & Hsx & Bs & Ls & Rc & Bd & Ld & Nd & Rows & Dst). destruct (Rows i Hi) as (Br & Lr & _ & _ & _).
  unfold bok in Br. apply rdn_ext; rewrite ?u_Z2bv by lia; [cbn; lia |]. intros x Hx. cbn in Hx.
  apply (LIVK_in A m m' (v_rows sv i) (4 * v_sx sv) x LK Lr); lia.
Qed.

(* [comment removed for export] *)
Lemma udd_blk1_W : forall fr cs C A (m : word -> option byte) md regs (s pix0 w h cd data selA selB : Z) (cvx : cmapv) (svA svB : selv)
    (cA cB : Z -> Z -> Z) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md -> frm_zero cs ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + UDD_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 4 = Z_to_bv 64 0x1381d0 -> getr regs 9 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 ->
  getr regs 23 = Z_to_bv 64 pix0 -> getr regs 24 = Z_to_bv 64 selA -> getr regs 25 = Z_to_bv 64 selB ->
  O23LeptUddLib.PIXC C A m pix0 w h cd data cvx -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  sel_at (alloc_top (c_vm C)) A m selA svA -> sel_cont m svA cA -> (0 <= v_cx svA < v_sx svA)%Z -> (0 <= v_cy svA < v_sy svA)%Z -> v_sy svA = 5%Z ->
  sel_at (alloc_top (c_vm C)) A m selB svB -> sel_cont m svB cB -> (0 <= v_cx svB < v_sx svB)%Z -> (0 <= v_cy svB < v_sy svB)%Z -> v_sy svB = 5%Z ->
  O23LeptUddLib.disj (O23LeptUddLib.sel_l selA svA) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l selB svB) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) ->
  aroom A (m_vmmaps md) kR bR -> (RK_blk <= kR)%Z -> (RB_blk w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs' (bc : list byte), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     (forall q, live A' q = live A q) -> POSTM C A s m m' ->
     (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
        (b + Z.of_nat n <= s - 124 \/ s - 124 + 4 <= b)%Z -> rdn SEGS m' (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
     rdn SEGS m' (Z_to_bv 64 (s - 124)) 4 = Some bc -> length bc = 4%nat -> aroom A' vm' (kR - RK_blk) (bR - RB_blk w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (0xafc50 : word) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xafbac : word) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pix0 w h cd data selA selB cvx svA svB cA cB S kR bR
    CK HW FZ Hs16 Hlo Hhi H2 H4 H9 H20 H23 H24 H25 PC0 Hhdr Hw Hh SA ScA HcxA HcyA HsyA SB ScB HcxB HcyB HsyB DA DB RM HK HB K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 5072 <= s)%Z) by (unfold UDD_STACK, MSEQ_STACK, CSC_STACK in Hlo; lia).
  assert (EH : HMT_STACK = 3744%Z) by reflexivity.
  assert (EP : POR_STACK = 528%Z) by reflexivity.
  assert (EC1 : CASC_STACK = 3792%Z) by reflexivity.
  assert (EC2 : CNT_STACK = 4544%Z) by reflexivity.
  assert (ERK : RK_pixcopy = 4%Z) by reflexivity.
  assert (ERC : RK_casc = 5%Z) by reflexivity.
  assert (ERB : RK_blk = 14%Z) by reflexivity.
  assert (ERBB : RB_blk w h = (2 * (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapcopy) + RB_casc w h + 2 ^ 17)%Z) by reflexivity.
  pose proof (aroom_nonneg _ _ _ _ RM) as [Hk0 Hb0].
  assert (Hx : (2 ^ 17 <= RB_pixT (4 * (wpl_of w 1 * h)))%Z) by (unfold RB_pixT, RB_hdrT; lia).
  assert (Hc : (0 <= RB_cmapT cd <= RB_cmapcopy)%Z) by (unfold RB_cmapT, RB_cmapcopy; lia).
  pose proof (O23LeptUddLib.RB_casc_nonneg w h) as Hcn.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hs256 : (256 <= s)%Z) by lia.
  assert (Hsp16 : ((s - 256) mod 16 = 0)%Z) by mod16 Hs16.
  assert (HT : (alloc_top (c_vm C) < 2 ^ 64)%Z) by lia.
  assert (RS : rop_shape w h 1 (wpl_of w 1)) by (red; destruct Hhdr as (_ & X1 & X2 & X3); repeat split; first [left; reflexivity | lia]).
  pose proof PC0 as (PX0 & L0 & L00 & LD0 & _ & _ & _).
  destruct (ud_B1a al_rom (mkFP fr cs) regs m) as (r1 & RUN1 & Q1a & Q1b & Q1c & Q1d & AG1).
  rzp HW RUN1.
  let ra := rhs Q1a in
  eapply udb_pc; [| apply (pixHMT_new_sure_W (fx := mkFP fr cs) C A m md r1 (s - 256) pix0 selA w h cd data svA cA cvx ra S CK HW
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q1a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q1b
      ltac:(csr; reflexivity) ltac:(csr; reflexivity) PX0 Hhdr Hw Hh L0 L00 LD0 (O23LeptUddLib.PIXC_hprem _ _ _ _ _ _ _ _ _ PC0)
      SA ScA HcxA HcyA
      (fun p Hp => O23LeptUddLib.disj_neW _ _ _ _ DA (O23LeptUddLib.sel_l_in selA svA p HsyA Hp) (O23LeptUddLib.pix_l_pix pix0 data cd (c_arr cvx)))
      kR bR RM ltac:(lia) ltac:(lia))]; [reflexivity |].
  intros A1 m1 vm1 r2 HW1 CS2 [pixd1 [cd1 [data1 [G2a [PT1 PM1]]]]] RM1.
  destruct (O23LeptUddLib.PIXC_of_pixt_new C A A1 m1 pixd1 w h cd1 data1 cvx PT1) as (cv1 & PC1 & ON1 & OF1).
  pose proof (O23LeptUddLib.sub_of_only A A1 _ ON1 OF1) as SUB1.
  assert (PMA1 : POSTM C A s m m1) by (eapply POSTM_mono; [| exact PM1]; lia).
  assert (E1 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m1 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) m m1 b n CK (proj1 PM1) Hb1 ltac:(lia) ltac:(lia))).
  pose proof PC1 as (PX1 & L1a & L10 & LD1 & LD10 & NE1 & _).
  pose proof PX1 as (P1a & P1b & WF1 & _).
  assert (Hd1 : (0 <= data1 < 2 ^ 64)%Z) by exact (wf_data _ WF1).
  destruct (ud_B1b al_rom (mkFP fr cs) r2 m1 s Hs256 Hs64 (W_sok_win C A1 m1 _ (s - 144) 8 CK HW1 ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity))
    as (r3 & RUN3 & Q3a & Q3b & Q3c & Q3d & AG3).
  rzp HW1 RUN3.
  set (M2 := O23LeptUddSegs.wr8w m1 (s - 144) (getr r2 10)) in *.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2) by exact (WP_win C A1 A m m1 _ (Z_to_bv 64 (s - 144))
    (word_to_le_bytes 8 (getr r2 10)) s CK (conj HW1 PMA1) SUB1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi).
  destruct WP2 as [HW2 PMA2].
  assert (PL2 : POSTM C A1 s m1 M2) by exact (proj2 (WP_win C A1 A1 m1 m1 _ (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (getr r2 10)) s CK
    (conj HW1 (POSTM_refl C A1 s m1)) (sub_live_refl A1) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi)).
  assert (E2 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 144 \/ s - 136 <= b)%Z ->
     rdn SEGS M2 (Z_to_bv 64 b) n = rdn SEGS m1 (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3. unfold M2, O23LeptUddSegs.wr8w. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia. }
  assert (H2h : rdn SEGS M2 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixd1)).
  { unfold M2, O23LeptUddSegs.wr8w. rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite G2a, w2b_Z by lia. reflexivity. }
  pose proof (O23LeptUddLib.PIXC_livk C A A1 m M2 pix0 w h cd data cvx PC0 SUB1 (proj2 PMA2)) as PC0b.
  pose proof (O23LeptUddLib.PIXC_livk C A1 A1 m1 M2 pixd1 w h cd1 data1 cv1 PC1 (sub_live_refl A1) (proj2 PL2)) as PC1b.
  pose proof (sel_at_keep (alloc_top (c_vm C)) A A1 m M2 selB svB HT SB SUB1 (proj2 PMA2)) as SB2.
  pose proof (udb_sel_cont_keep (alloc_top (c_vm C)) A m M2 selB svB cB HT SB (proj2 PMA2) ScB) as ScB2.
  pose proof PC0b as (PX0b & L0b & _ & LD0b & _ & _ & _).
  let ra := rhs Q3a in
  eapply udb_pc; [| apply (pixHMT_new_sure_W (fx := mkFP fr cs) C A1 M2 (with_vmmaps vm1 md) r3 (s - 256) pix0 selB w h cd data svB cB cvx ra S CK HW2
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q3a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q3b
      ltac:(csr; reflexivity) ltac:(csr; reflexivity) PX0b Hhdr Hw Hh L0b L00 LD0b (O23LeptUddLib.PIXC_hprem _ _ _ _ _ _ _ _ _ PC0b)
      SB2 ScB2 HcxB HcyB
      (fun p Hp => O23LeptUddLib.disj_neW _ _ _ _ DB (O23LeptUddLib.sel_l_in selB svB p HsyB Hp) (O23LeptUddLib.pix_l_pix pix0 data cd (c_arr cvx)))
      (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd)) ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia))];
    [reflexivity |].
  intros A2 m3 vm2 r4 HW3 CS4 [pixd2 [cd2 [data2 [G4a [PT2 PM3]]]]] RM2.
  rewrite with_vmmaps_twice in HW3 |- *.
  destruct (O23LeptUddLib.PIXC_of_pixt_new C A1 A2 m3 pixd2 w h cd2 data2 cvx PT2) as (cv2 & PC2 & ON2 & OF2).
  pose proof (O23LeptUddLib.sub_of_only A1 A2 _ ON2 OF2) as SUB12.
  assert (SUB2 : sub_live A A2) by (intros q k Hq; exact (SUB12 q k (SUB1 q k Hq))).
  assert (PMA3 : POSTM C A s m m3)
    by (eapply POSTM_trans; [exact PMA2 | apply (POSTM_sub C A A1 s M2 m3 SUB1); eapply POSTM_mono; [| exact PM3]; lia]).
  assert (E3 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m3 (Z_to_bv 64 b) n = rdn SEGS M2 (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M2 m3 b n CK (proj1 PM3) Hb1 ltac:(lia) ltac:(lia))).
  pose proof (O23LeptUddLib.PIXC_livk C A1 A2 M2 m3 pixd1 w h cd1 data1 cv1 PC1b SUB12 (proj2 PM3)) as PC1c.
  pose proof (O23LeptUddLib.lives_of_PIXC _ _ _ _ _ _ _ _ _ PC1b) as LV1.
  pose proof (O23LeptUddLib.disj_off_live A1 _ _ LV1 OF2) as D12.
  pose proof (O23LeptUddLib.disj_sym _ _ D12) as D21.
  pose proof PC2 as (PX2 & L2a & L20 & LD2 & LD20 & NE2 & _).
  pose proof PX2 as (P2a & P2b & WF2 & _).
  assert (Hd2 : (0 <= data2 < 2 ^ 64)%Z) by exact (wf_data _ WF2).
  assert (R144c : rdn SEGS m3 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd1))).
  { rewrite (E3 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), H2h, w2b_Z by lia. reflexivity. }
  destruct (ud_B1c al_rom (mkFP fr cs) r4 m3 s (Z_to_bv 64 pixd1) Hs256 Hs64 R144c (W_sok_win C A2 m3 _ (s - 152) 8 CK HW3 ltac:(lia) ltac:(lia))
      ltac:(csr; reflexivity)) as (r5 & RUN5 & Q5a & Q5b & Q5c & Q5d & AG5).
  rzp HW3 RUN5.
  set (M4 := O23LeptUddSegs.wr8w m3 (s - 152) (getr r4 10)) in *.
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A s m M4) by exact (WP_win C A2 A m m3 _ (Z_to_bv 64 (s - 152))
    (word_to_le_bytes 8 (getr r4 10)) s CK (conj HW3 PMA3) SUB2 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi).
  destruct WP4 as [HW4 PMA4].
  assert (PL4 : POSTM C A2 s m3 M4) by exact (proj2 (WP_win C A2 A2 m3 m3 _ (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (getr r4 10)) s CK
    (conj HW3 (POSTM_refl C A2 s m3)) (sub_live_refl A2) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi)).
  assert (E4 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 152 \/ s - 144 <= b)%Z ->
     rdn SEGS M4 (Z_to_bv 64 b) n = rdn SEGS m3 (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3. unfold M4, O23LeptUddSegs.wr8w. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia. }
  assert (H4h : rdn SEGS M4 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixd2)).
  { unfold M4, O23LeptUddSegs.wr8w. rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite G4a, w2b_Z by lia. reflexivity. }
  pose proof (O23LeptUddLib.PIXC_livk C A2 A2 m3 M4 pixd1 w h cd1 data1 cv1 PC1c (sub_live_refl A2) (proj2 PL4)) as PC1d.
  pose proof (O23LeptUddLib.PIXC_livk C A2 A2 m3 M4 pixd2 w h cd2 data2 cv2 PC2 (sub_live_refl A2) (proj2 PL4)) as PC2d.
  pose proof PC1d as (PX1d & L1d & _ & LD1d & _ & _ & _).
  pose proof PC2d as (PX2d & L2d & _ & LD2d & _ & _ & _).
  pose proof (O23LeptUddLib.pix_l_pix pixd1 data1 cd1 (c_arr cv1)) as I1p.
  pose proof (O23LeptUddLib.pix_l_data pixd1 data1 cd1 (c_arr cv1)) as I1d.
  pose proof (O23LeptUddLib.pix_l_pix pixd2 data2 cd2 (c_arr cv2)) as I2p.
  pose proof (O23LeptUddLib.pix_l_data pixd2 data2 cd2 (c_arr cv2)) as I2d.
  let ra := rhs Q5a in
  eapply udb_pc; [| apply (pixOr_inplace_W (fx := mkFP fr cs) C A A2 M4 (with_vmmaps vm2 md) r5 (s - 256)%Z pixd1 pixd2 _ _ ra S CK HW4 SUB2
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q5a ltac:(red; apply bv_eq; reflexivity) Q5b Q5c ltac:(csr; reflexivity)
      PX1d PX2d eq_refl eq_refl RS RS L1d L2d (O23LeptUddLib.disj_neW _ _ _ _ D12 I1p I2p)
      (zbv_ne pixd1 data1 ltac:(lia) Hd1 (fun E => NE1 (eq_sym E))) (O23LeptUddLib.disj_neW _ _ _ _ D21 I2p I1d)
      LD1d (OF1 _ I1d) LD10 LD2d (O23LeptUddLib.disj_neW _ _ _ _ D21 I2d I1d))]; [reflexivity |].
  intros M6 r6 HW6 CS6 PM6 PX16 PX26 OUT6 G6a.
  assert (PMA6 : POSTM C A s m M6) by (eapply POSTM_trans; [exact PMA4 | eapply POSTM_mono; [| exact PM6]; lia]).
  assert (E6 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS M6 (Z_to_bv 64 b) n = rdn SEGS M4 (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M4 M6 b n CK (proj1 PM6) Hb1 ltac:(lia) ltac:(lia))).
  pose proof (udb_livke C A2 M4 M6 _ data1 _ (s - 256) CK HW4 LD1d Hd1 OUT6) as LVE6.
  assert (CD1 : cd1 <> 0%Z -> cd1 <> data1) by exact (O23LeptUddLib.PIXC_cd_data _ _ _ _ _ _ _ _ _ PC1).
  pose proof (O23LeptUddLib.PIXC_livke C A2 A2 M4 M6 pixd1 w h cd1 data1 cv1 data1 PC1d LVE6 Hd1 (fun E => NE1 (eq_sym E)) CD1 (fun p _ => eq_refl)) as PC1e.
  assert (NE21 : pixd2 <> data1) by exact (O23LeptUddLib.disj_neZ _ _ _ _ D21 I2p I1d).
  assert (CD21 : cd2 <> 0%Z -> cd2 <> data1)
    by (intros X; exact (O23LeptUddLib.disj_neZ _ _ _ _ D21 (O23LeptUddLib.pix_l_cd pixd2 data2 cd2 (c_arr cv2) X) I1d)).
  pose proof (O23LeptUddLib.PIXC_livke C A2 A2 M4 M6 pixd2 w h cd2 data2 cv2 data1 PC2d LVE6 Hd1 NE21 CD21 (fun p _ => eq_refl)) as PC2e.
  assert (R144e : rdn SEGS M6 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd1))).
  { rewrite (E6 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), (E4 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
      (E3 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), H2h, w2b_Z by lia. reflexivity. }
  destruct (ud_B1d al_rom (mkFP fr cs) r6 M6 s (Z_to_bv 64 pixd1) Hs256 Hs64 R144e ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & Q7a & Q7b & Q7c & Q7d & Q7e & Q7f & AG7).
  rzp HW6 RUN7.
  pose proof PC1e as (PX1e & L1e & _ & LD1e & _ & _ & _).
  let ra := rhs Q7a in
  eapply udb_pc; [| apply (pixReduceRankBinaryCascade_11_W fr cs C A A2 M6 (with_vmmaps vm2 md) r7 (s - 256) pixd1 1 w h cd1 data1 ra S CK HW6 FZ SUB2
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q7a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
      Q7b Q7c Q7d Q7e Q7f PX1e Hhdr Hw Hh L1e LD1e (OF1 _ I1d) LD10 (fun E => NE1 (eq_sym E))
      (kR - RK_pixcopy - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd))
      ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia))]; [reflexivity |].
  intros fr' cs' A4 m7 vm4 r8 HW7 FZ' _ CS8 PM7 LVK7 PX17 RES RM4.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (PMA7 : POSTM C A s m m7) by (eapply POSTM_trans; [exact PMA6 | eapply POSTM_mono; [| exact PM7]; lia]).
  assert (E7 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m7 (Z_to_bv 64 b) n = rdn SEGS M6 (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M6 m7 b n CK (proj1 PM7) Hb1 ltac:(lia) ltac:(lia))).
  assert (POST3 : exists pix3 w3 h3 data3, getr r8 10 = Z_to_bv 64 pix3 /\ O23LeptUddLib.PIXO C A4 m7 pix3 w3 h3 data3 /\
      O23LeptUddLib.only A2 A4 (O23LeptUddLib.pixo_l pix3 data3) /\ O23LeptUddLib.offs A2 (O23LeptUddLib.pixo_l pix3 data3) /\
      (pix3 <> 0%Z -> (1 <= w3)%Z /\ (1 <= h3)%Z /\ O23LeptPixHdrT2.hdr_ok w3 h3 1)).
  { destruct RES as [[G8 LV8] | (pix3 & data3 & G8 & Hw4 & Hh4 & Hhd3 & PR3)].
    - exists 0%Z, 0%Z, 0%Z, 0%Z. split; [exact G8 |]. split; [red; left; reflexivity |].
      split; [apply O23LeptUddLib.only_eq; exact LV8 |]. split; [intros q Hq; cbn in Hq; destruct Hq |].
      intros X; exfalso; apply X; reflexivity.
    - destruct (O23LeptUddLib.PIXC_of_pixr_new C A2 A4 m7 pix3 data3 (w / 2 / 2) (h / 2 / 2) cmap0 PR3) as (PC3 & ON3 & OF3).
      pose proof PC3 as (PX3 & L3 & _).
      pose proof PX3 as (P3a & P3b & _).
      destruct (blk_range C A4 m7 _ _ _ CK HW7 L3 ltac:(lia)) as [B3 _]. rewrite u_Z2bv in B3 by lia.
      assert (W2 : (2 <= w / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      assert (W4 : (1 <= w / 2 / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      assert (H2' : (2 <= h / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      assert (H4' : (1 <= h / 2 / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      exists pix3, (w / 2 / 2)%Z, (h / 2 / 2)%Z, data3. split; [exact G8 |]. split; [red; right; split; [lia | exact PC3] |].
      rewrite O23LeptUddLib.pixo_l_ne by lia. split; [exact ON3 |]. split; [exact OF3 |].
      intros _. split; [exact W4 | split; [exact H4' | exact Hhd3]]. }
  destruct POST3 as (pix3 & w3 & h3 & data3 & G8 & PO3 & ON3 & OF3 & HP3).
  set (LL1 := O23LeptUddLib.pix_l pixd1 data1 cd1 (c_arr cv1)) in *.
  set (LL2 := O23LeptUddLib.pix_l pixd2 data2 cd2 (c_arr cv2)) in *.
  set (LL3 := O23LeptUddLib.pixo_l pix3 data3) in *.
  assert (SUB24 : sub_live A2 A4) by exact (O23LeptUddLib.sub_of_only A2 A4 _ ON3 OF3).
  assert (SUB4 : sub_live A A4) by (intros q k Hq; exact (SUB24 q k (SUB2 q k Hq))).
  pose proof (O23LeptUddLib.lives_of_PIXC _ _ _ _ _ _ _ _ _ PC1d) as LV1d.
  pose proof (O23LeptUddLib.lives_of_PIXC _ _ _ _ _ _ _ _ _ PC2d) as LV2d.
  pose proof (O23LeptUddLib.disj_off_live A2 _ _ LV1d OF3) as D13.
  pose proof (O23LeptUddLib.disj_off_live A2 _ _ LV2d OF3) as D23.
  pose proof (O23LeptUddLib.PIXC_livke C A2 A4 M6 m7 pixd1 w h cd1 data1 cv1 data1 PC1e LVK7 Hd1 (fun E => NE1 (eq_sym E)) CD1
    (fun p Hp => ON3 p (D13 p Hp))) as PC1f.
  pose proof (O23LeptUddLib.PIXC_livke C A2 A4 M6 m7 pixd2 w h cd2 data2 cv2 data1 PC2e LVK7 Hd1 NE21 CD21
    (fun p Hp => ON3 p (D23 p Hp))) as PC2f.
  destruct (ud_B1e al_rom (mkFP fr' cs') r8 m7 s Hs256 Hs64 (W_sok_win C A4 m7 _ (s - 160) 8 CK HW7 ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity))
    as (r9 & RUN9 & Q9a & Q9b & Q9c & Q9d & AG9).
  rzp HW7 RUN9.
  set (M8 := O23LeptUddSegs.wr8w m7 (s - 160) (getr r8 10)) in *.
  assert (WP8 : W C A4 M8 (with_vmmaps vm4 md) /\ POSTM C A s m M8) by exact (WP_win C A4 A m m7 _ (Z_to_bv 64 (s - 160))
    (word_to_le_bytes 8 (getr r8 10)) s CK (conj HW7 PMA7) SUB4 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi).
  destruct WP8 as [HW8 PMA8].
  assert (PL8 : POSTM C A4 s m7 M8) by exact (proj2 (WP_win C A4 A4 m7 m7 _ (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (getr r8 10)) s CK
    (conj HW7 (POSTM_refl C A4 s m7)) (sub_live_refl A4) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi)).
  assert (E8 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 152 <= b)%Z ->
     rdn SEGS M8 (Z_to_bv 64 b) n = rdn SEGS m7 (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3. unfold M8, O23LeptUddSegs.wr8w. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia. }
  assert (Hp3 : (0 <= pix3 < 2 ^ 64)%Z).
  { destruct PO3 as [E | (_ & PCx)]; [rewrite E; lia |]. destruct PCx as ((X1 & X2 & _) & _). lia. }
  assert (H8h : rdn SEGS M8 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
  { unfold M8, O23LeptUddSegs.wr8w. rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite G8, w2b_Z by lia. reflexivity. }
  pose proof (O23LeptUddLib.PIXC_livk C A4 A4 m7 M8 pixd1 w h cd1 data1 cv1 PC1f (sub_live_refl A4) (proj2 PL8)) as PC1g.
  pose proof (O23LeptUddLib.PIXC_livk C A4 A4 m7 M8 pixd2 w h cd2 data2 cv2 PC2f (sub_live_refl A4) (proj2 PL8)) as PC2g.
  pose proof (O23LeptUddLib.PIXO_livk C A4 A4 m7 M8 pix3 w3 h3 data3 PO3 (sub_live_refl A4) (proj2 PL8)) as PO3g.
  let ra := rhs Q9a in
  assert (FIN2 : forall A5 m9 vm5 r10 (M9 : word -> option byte) (bc : list byte) (k5 b5 : Z),
      W C A5 m9 (with_vmmaps vm5 md) -> cs_kept r9 r10 -> (forall q, live A5 q = live A4 q) ->
      POSTM C A4 (s - 256) M9 m9 -> POSTM C A s m M9 -> LIVK A4 M8 M9 ->
      (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 124 \/ s - 120 <= b)%Z ->
         rdn SEGS M9 (Z_to_bv 64 b) n = rdn SEGS M8 (Z_to_bv 64 b) n) ->
      rdn SEGS M9 (Z_to_bv 64 (s - 124)) 4 = Some bc -> length bc = 4%nat -> aroom A5 vm5 k5 b5 ->
      (kR - RK_blk <= k5)%Z -> (bR - RB_blk w h <= b5)%Z ->
      realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r10 ra m9 al_rom) (with_vmmaps vm5 md)) S).
  { intros A5 m9 vm5 r10 M9 bc k5 b5 HW9 CS10 LV9 PM9 PMA9 LK9 F9 RB9 LB9 RM5 Hk5 Hb5.
    assert (SUB45 : sub_live A4 A5) by (intros q k Hq; rewrite LV9; exact Hq).
    assert (LK : LIVK A4 M8 m9) by exact (LIVK_trans A4 M8 M9 m9 LK9 (proj2 PM9)).
    assert (E9 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m9 (Z_to_bv 64 b) n = rdn SEGS M9 (Z_to_bv 64 b) n)
      by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M9 m9 b n CK (proj1 PM9) Hb1 ltac:(lia) ltac:(lia))).
    pose proof (O23LeptUddLib.PIXC_livk C A4 A5 M8 m9 pixd1 w h cd1 data1 cv1 PC1g SUB45 LK) as PC1h.
    pose proof (O23LeptUddLib.PIXC_livk C A4 A5 M8 m9 pixd2 w h cd2 data2 cv2 PC2g SUB45 LK) as PC2h.
    pose proof (O23LeptUddLib.PIXO_livk C A4 A5 M8 m9 pix3 w3 h3 data3 PO3g SUB45 LK) as PO3h.
    assert (ONa : O23LeptUddLib.only A A2 (LL1 ++ LL2 ++ LL3)).
    { apply (O23LeptUddLib.only_sub A A2 (LL1 ++ LL2) _ (O23LeptUddLib.only_trans A A1 A2 LL1 LL2 ON1 ON2)).
      intros q Hq. rewrite app_assoc. apply in_or_app. left. exact Hq. }
    assert (ONb : O23LeptUddLib.only A A4 (LL1 ++ LL2 ++ LL3)).
    { apply (O23LeptUddLib.only_trans_l A A2 A4 _ ONa). apply (O23LeptUddLib.only_sub A2 A4 LL3 _ ON3). intros q Hq; in_app. }
    assert (ONf : O23LeptUddLib.only A A5 (LL1 ++ LL2 ++ LL3))
      by exact (O23LeptUddLib.only_trans_l A A4 A5 _ ONb (O23LeptUddLib.only_eq A4 A5 _ LV9)).
    assert (OFf : O23LeptUddLib.offs A (LL1 ++ LL2 ++ LL3)) by exact (O23LeptUddLib.offs_app A LL1 _ OF1
        (O23LeptUddLib.offs_app A LL2 LL3 (O23LeptUddLib.offs_sub A A1 LL2 OF2 SUB1) (O23LeptUddLib.offs_sub A A2 LL3 OF3 SUB2))).
    assert (PMf : POSTM C A s m m9).
    { eapply POSTM_trans; [exact PMA9 |]. apply (POSTM_sub C A A4 s M9 m9 SUB4). eapply POSTM_mono; [| exact PM9]; lia. }
    assert (R144 : rdn SEGS m9 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixd1)).
    { rewrite (E9 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), (F9 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
        (E8 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)), (E7 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)),
        (E6 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), (E4 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
        (E3 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)). exact H2h. }
    assert (R152 : rdn SEGS m9 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixd2)).
    { rewrite (E9 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia)), (F9 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
        (E8 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)), (E7 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia)),
        (E6 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia)). exact H4h. }
    assert (R160 : rdn SEGS m9 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
    { rewrite (E9 (s - 160)%Z 8%nat ltac:(lia) ltac:(lia)), (F9 (s - 160)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)). exact H8h. }
    assert (RBm : rdn SEGS m9 (Z_to_bv 64 (s - 124)) 4 = Some bc).
    { rewrite (E9 (s - 124)%Z 4%nat ltac:(lia) ltac:(lia)). exact RB9. }
    assert (FRm : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
       (b + Z.of_nat n <= s - 124 \/ s - 124 + 4 <= b)%Z -> rdn SEGS m9 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n).
    { intros b n Hb1 Hb2 Hb3 Hb4.
      rewrite (E9 b n Hb1 Hb2), (F9 b n Hb1 Hb2 ltac:(lia)), (E8 b n Hb1 Hb2 ltac:(lia)), (E7 b n Hb1 Hb2), (E6 b n Hb1 Hb2),
        (E4 b n Hb1 Hb2 ltac:(lia)), (E3 b n Hb1 Hb2), (E2 b n Hb1 Hb2 ltac:(lia)), (E1 b n Hb1 Hb2). reflexivity. }
    eapply udb_pc; [| apply (udd_blk1_tail fr' cs' C A A5 m m9 md vm5 regs r10 s pixd1 w h cd1 data1 pixd2 cd2 data2 pix3 w3 h3 data3 cv1 cv2 bc S k5 b5
        CK HW HW9 FZ' Hs16 Hlo Hhi ltac:(apply cs_kept_intro; csr; reflexivity) H2 H4 H9 R144 R152 R160 RBm LB9 FRm
        PC1h PC2h PO3h Hw Hh (fun X => conj (proj1 (HP3 X)) (proj1 (proj2 (HP3 X)))) D21 (O23LeptUddLib.disj_sym _ _ D13)
        (O23LeptUddLib.disj_sym _ _ D23) ONf OFf PMf RM5)]; [reflexivity |].
    intros fr'' cs'' A' m' vm' regs' bc' HWf FZf CSf LVf PMf' FRf RBf LBf RMf.
    eapply udb_pc; [| apply (K fr'' cs'' A' m' vm' regs' bc' HWf FZf CSf LVf PMf' FRf RBf LBf)]; [reflexivity |].
    apply (aroom_mono A' vm' k5 b5 _ _ RMf); lia. }
  destruct (Z.eq_dec pix3 0) as [Z3 | NZ3].
  - subst pix3.
    let ra := rhs Q9a in
    eapply udb_pc; [| apply (pixCountPixels_null_W (fx := mkFP fr' cs') C A4 M8 (with_vmmaps vm4 md) r9 (s - 256) (s - 124) ra S CK HW8
        ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q9a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q9c ltac:(lia) ltac:(lia)
        ltac:(apply V23LeptUb.sp_slot_al4'; [exact Hs16 | reflexivity]))]; [reflexivity |].
    intros m9 r10 HW9 CS10 PM9 _.
    assert (WP9 : W C A4 (CNTM0 M8 (s - 124)) (with_vmmaps vm4 md) /\ POSTM C A s m (CNTM0 M8 (s - 124))) by (unfold CNTM0; wp_win CK).
    assert (WL9 : W C A4 (CNTM0 M8 (s - 124)) (with_vmmaps vm4 md) /\ POSTM C A4 s M8 (CNTM0 M8 (s - 124))) by (unfold CNTM0; wp_win CK).
    apply (FIN2 A4 m9 vm4 r10 (CNTM0 M8 (s - 124)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (kR - RK_pixcopy - RK_pixcopy - RK_casc)%Z
        (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - RB_casc w h)%Z
        HW9 CS10 (fun q => eq_refl) PM9 (proj2 WP9) (proj2 (proj2 WL9))).
    + intros b n Hb1 Hb2 Hb3. unfold CNTM0. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia.
    + unfold CNTM0. pose proof (SeqExec.rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 0)) M8 (Z_to_bv 64 (s - 124))
        ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia)) as X. rewrite length_N_to_le_bytes in X. exact X.
    + apply length_N_to_le_bytes.
    + exact RM4.
    + lia.
    + lia.
  - pose proof PO3g as [E3z | (_ & PC3g)]; [contradiction |].
    pose proof PC3g as (PX3g & L3g & _ & LD3g & _ & _ & _).
    destruct (HP3 NZ3) as (Hw3 & Hh3 & Hhd3).
    let ra := rhs Q9a in
    eapply udb_pc; [| apply (pixCountPixels_W (fx := mkFP fr' cs') C A4 M8 (with_vmmaps vm4 md) r9 (s - 256) pix3 (s - 124) 1 w3 h3 0 data3 ra S CK HW8
        ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q9a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
        ltac:(csr; reflexivity) Q9c Q9d ltac:(lia) ltac:(lia) ltac:(apply V23LeptUb.sp_slot_al4'; [exact Hs16 | reflexivity])
        PX3g ltac:(destruct Hhd3 as (_ & X1 & _); lia) ltac:(destruct Hhd3 as (_ & _ & X2 & _); lia) L3g LD3g
        (kR - RK_pixcopy - RK_pixcopy - RK_casc) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - RB_casc w h)
        ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia))]; [reflexivity |].
    intros A5 m9 vm5 r10 wv HW9 CS10 LV9 PM9 _ RM5.
    rewrite with_vmmaps_twice in HW9 |- *.
    assert (WP9 : W C A4 (CNTM M8 (s - 124) wv) (with_vmmaps vm4 md) /\ POSTM C A s m (CNTM M8 (s - 124) wv)) by (unfold CNTM, CNTM0; wp_win CK).
    assert (WL9 : W C A4 (CNTM M8 (s - 124) wv) (with_vmmaps vm4 md) /\ POSTM C A4 s M8 (CNTM M8 (s - 124) wv)) by (unfold CNTM, CNTM0; wp_win CK).
    apply (FIN2 A5 m9 vm5 r10 (CNTM M8 (s - 124) wv) (word_to_le_bytes 4 wv) (kR - RK_pixcopy - RK_pixcopy - RK_casc - 1)%Z
        (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - RB_casc w h - 2 ^ 17)%Z
        HW9 CS10 LV9 PM9 (proj2 WP9) (proj2 (proj2 WL9))).
    + intros b n Hb1 Hb2 Hb3. unfold CNTM, CNTM0. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; lia). reflexivity.
    + unfold CNTM. pose proof (SeqExec.rdn_wbytes_hit SEGS (word_to_le_bytes 4 wv) (CNTM0 M8 (s - 124)) (Z_to_bv 64 (s - 124))
        ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia)) as X. rewrite length_N_to_le_bytes in X. exact X.
    + apply length_N_to_le_bytes.
    + exact RM5.
    + lia.
    + lia.
Qed.

(* [comment removed for export] *)
Lemma udd_blk2_tail : forall fr5 cs5 C A A5 (m m5 : word -> option byte) md vm5 regs r5
    (s pix1 w h cd1 data1 pix2 cd2 data2 pix3 w3 h3 data3 : Z) (cv1 cv2 : cmapv) (bc : list byte) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md -> W C A5 m5 (with_vmmaps vm5 md) -> frm_zero cs5 ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + UDD_STACK <= s)%Z -> (s <= c_top C)%Z ->
  cs_kept regs r5 -> getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 4 = Z_to_bv 64 0x1381d0 -> getr regs 9 = Z_to_bv 64 0 ->
  rdn SEGS m5 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pix1) ->
  rdn SEGS m5 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pix2) ->
  rdn SEGS m5 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3) ->
  rdn SEGS m5 (Z_to_bv 64 (s - 128)) 4 = Some bc -> length bc = 4%nat ->
  (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
     (b + Z.of_nat n <= s - 128 \/ s - 128 + 4 <= b)%Z -> rdn SEGS m5 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
  O23LeptUddLib.PIXC C A5 m5 pix1 w h cd1 data1 cv1 -> O23LeptUddLib.PIXC C A5 m5 pix2 w h cd2 data2 cv2 -> O23LeptUddLib.PIXO C A5 m5 pix3 w3 h3 data3 ->
  (1 <= w)%Z -> (1 <= h)%Z -> (pix3 <> 0%Z -> (1 <= w3)%Z /\ (1 <= h3)%Z) ->
  O23LeptUddLib.disj (O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2)) (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1)) ->
  O23LeptUddLib.disj (O23LeptUddLib.pixo_l pix3 data3) (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1)) -> O23LeptUddLib.disj (O23LeptUddLib.pixo_l pix3 data3) (O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2)) ->
  O23LeptUddLib.only A A5 (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1) ++ O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2) ++ O23LeptUddLib.pixo_l pix3 data3) ->
  O23LeptUddLib.offs A (O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1) ++ O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2) ++ O23LeptUddLib.pixo_l pix3 data3) ->
  POSTM C A s m m5 -> aroom A5 vm5 kR bR ->
  (forall fr' cs' A' m' vm' regs' (bc' : list byte), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     (forall q, live A' q = live A q) -> POSTM C A s m m' ->
     (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
        (b + Z.of_nat n <= s - 128 \/ s - 128 + 4 <= b)%Z -> rdn SEGS m' (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
     rdn SEGS m' (Z_to_bv 64 (s - 128)) 4 = Some bc' -> length bc' = 4%nat -> aroom A' vm' kR bR ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (0xafcf4 : word) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr5 cs5) r5 (0xafcc4 : word) m5 al_rom) (with_vmmaps vm5 md)) S.
Proof.
  intros fr5 cs5 C A A5 m m5 md vm5 regs r5 s pix1 w h cd1 data1 pix2 cd2 data2 pix3 w3 h3 data3 cv1 cv2 bc S kR bR
    CK HW HW5 FZ Hs16 Hlo Hhi CS5 H2 H4 H9 R1 R2 R3 RB LB FR5 PC1 PC2 PO3 Hw Hh Hwh3 D21 D31 D32 ON OF PM5 RM5 K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold UDD_STACK, MSEQ_STACK, CSC_STACK in Hlo.
  pose proof (aroom_nonneg _ _ _ _ RM5) as [Hk0 Hb0].
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hs256 : (256 <= s)%Z) by lia.
  assert (Hsp16 : ((s - 256) mod 16 = 0)%Z) by mod16 Hs16.
  set (L1 := O23LeptUddLib.pix_l pix1 data1 cd1 (c_arr cv1)) in *.
  set (L2 := O23LeptUddLib.pix_l pix2 data2 cd2 (c_arr cv2)) in *.
  set (L3 := O23LeptUddLib.pixo_l pix3 data3) in *.
  pose proof PC1 as (PX1 & L1a & L10 & LD1 & LD10 & NE1 & _).
  pose proof PC2 as (PX2 & _ & _ & LD2 & _ & _ & _).
  pose proof PX1 as (P1a & P1b & WF1 & _). pose proof PX2 as (P2a & P2b & WF2 & _).
  assert (Hd1 : (0 <= data1 < 2 ^ 64)%Z) by exact (wf_data _ WF1).
  assert (Hd2 : (0 <= data2 < 2 ^ 64)%Z) by exact (wf_data _ WF2).
  assert (HR1 : (0 < 4 * (wpl_of w 1 * h))%Z) by (pose proof (O23LeptUddLib.wpl_pos w Hw); nia).
  destruct (blk_range C A5 m5 _ _ _ CK HW5 LD1 HR1) as [B1 _]. rewrite u_Z2bv in B1 by lia.
  destruct (blk_range C A5 m5 _ _ _ CK HW5 LD2 HR1) as [B2 _]. rewrite u_Z2bv in B2 by lia.
  assert (R1w : rdn SEGS m5 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pix1))) by (rewrite w2b_Z by lia; exact R1).
  destruct (ud_B2f al_rom (mkFP fr5 cs5) r5 m5 s (Z_to_bv 64 pix1) Hs256 Hs64 R1w ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r6 & RUN6 & F6a & F6b & AG6).
  rzp HW5 RUN6.
  let ra := rhs F6a in
  eapply udb_pc; [| apply (pixDestroy_keep_W (fx := mkFP fr5 cs5) C A5 m5 (with_vmmaps vm5 md) r6 (s - 256) (s - 144) pix1 cd1 (4 * c_nalloc cv1)
      (4 * (wpl_of w 1 * h)) _ cv1 ra S CK HW5 ltac:(csr; reflexivity) Hsp16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) F6a
      ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) F6b R1 PX1
      eq_refl eq_refl eq_refl L1a L10 LD1 LD10 HR1 NE1 (O23LeptUddLib.PIXC_dprem _ _ _ _ _ _ _ _ _ PC1))]; [reflexivity |].
  intros A6 m6 vm6 r7 HW6 CS7 PD6 PM6 Z6 LOW6 RT6.
  rewrite with_vmmaps_twice in HW6 |- *. rewrite with_vmmaps_vmmaps in RT6.
  assert (X6 : O23LeptUddLib.only A5 A6 L1 /\ O23LeptUddLib.offs A6 L1) by exact (O23LeptUddLib.pixd_post_l A5 A6 pix1 data1 cd1 (c_arr cv1) ltac:(lia) PD6).
  destruct X6 as [ON6 OF6].
  pose proof (RT6 kR bR RM5 ltac:(lia) ltac:(lia)) as RM6. rewrite !Z.sub_0_r in RM6.
  assert (ONA6 : O23LeptUddLib.only A A6 (L1 ++ L2 ++ L3)).
  { apply (O23LeptUddLib.only_trans_l A A5 A6 _ ON). apply (O23LeptUddLib.only_sub A5 A6 L1 _ ON6). intros q Hq; in_app. }
  pose proof (O23LeptUddLib.sub_of_only A A6 _ ONA6 OF) as SUB6.
  assert (PMA6 : POSTM C A s m m6).
  { eapply POSTM_trans; [exact PM5 |]. apply (POSTM_sub C A A6 s m5 m6 SUB6). eapply POSTM_mono; [| exact PM6]; lia. }
  assert (FR6 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
     (b + Z.of_nat n <= s - 128 \/ s - 128 + 4 <= b)%Z -> rdn SEGS m6 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3 Hb4.
    rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 Hb1 ltac:(lia) ltac:(lia)).
    exact (FR5 b n Hb1 Hb2 Hb3 Hb4). }
  assert (RB6 : rdn SEGS m6 (Z_to_bv 64 (s - 128)) 4 = Some bc).
  { rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) (s - 128) 4 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact RB. }
  assert (R26 : rdn SEGS m6 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pix2)).
  { rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) (s - 152) 8 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact R2. }
  assert (R36 : rdn SEGS m6 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
  { rewrite (dst_rd C A6 m5 m6 (s - 256) (s - 144) (s - 160) 8 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM6 LOW6 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact R3. }
  pose proof (O23LeptUddLib.PIXC_dst C A5 A6 m5 m6 pix2 w h cd2 data2 cv2 L1 PC2 ON6 D21 (proj2 PM6)) as PC26.
  pose proof (O23LeptUddLib.PIXO_dst C A5 A6 m5 m6 pix3 w3 h3 data3 L1 PO3 ON6 D31 (proj2 PM6)) as PO36.
  destruct (ud_B2g al_rom (mkFP fr5 cs5) r7 m6 s Hs256 Hs64 ltac:(csr; reflexivity)) as (r8 & RUN8 & F8a & F8b & AG8).
  rzp HW6 RUN8.
  pose proof PC26 as (PX26 & L2a & L20 & LD26 & LD20 & NE2 & _).
  let ra := rhs F8a in
  eapply udb_pc; [| apply (pixDestroy_keep_W (fx := mkFP fr5 cs5) C A6 m6 (with_vmmaps vm6 md) r8 (s - 256) (s - 152) pix2 cd2 (4 * c_nalloc cv2)
      (4 * (wpl_of w 1 * h)) _ cv2 ra S CK HW6 ltac:(csr; reflexivity) Hsp16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) F8a
      ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) F8b R26 PX26
      eq_refl eq_refl eq_refl L2a L20 LD26 LD20 HR1 NE2 (O23LeptUddLib.PIXC_dprem _ _ _ _ _ _ _ _ _ PC26))]; [reflexivity |].
  intros A7 m7 vm7 r9 HW7 CS9 PD7 PM7 Z7 LOW7 RT7.
  rewrite with_vmmaps_twice in HW7 |- *. rewrite with_vmmaps_vmmaps in RT7.
  assert (X7 : O23LeptUddLib.only A6 A7 L2 /\ O23LeptUddLib.offs A7 L2) by exact (O23LeptUddLib.pixd_post_l A6 A7 pix2 data2 cd2 (c_arr cv2) ltac:(lia) PD7).
  destruct X7 as [ON7 OF7].
  pose proof (RT7 kR bR RM6 ltac:(lia) ltac:(lia)) as RM7. rewrite !Z.sub_0_r in RM7.
  assert (ONA7 : O23LeptUddLib.only A A7 (L1 ++ L2 ++ L3)).
  { apply (O23LeptUddLib.only_trans_l A A6 A7 _ ONA6). apply (O23LeptUddLib.only_sub A6 A7 L2 _ ON7). intros q Hq; in_app. }
  pose proof (O23LeptUddLib.sub_of_only A A7 _ ONA7 OF) as SUB7.
  assert (PMA7 : POSTM C A s m m7).
  { eapply POSTM_trans; [exact PMA6 |]. apply (POSTM_sub C A A7 s m6 m7 SUB7). eapply POSTM_mono; [| exact PM7]; lia. }
  assert (FR7 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
     (b + Z.of_nat n <= s - 128 \/ s - 128 + 4 <= b)%Z -> rdn SEGS m7 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3 Hb4.
    rewrite (dst_rd C A7 m6 m7 (s - 256) (s - 152) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM7 LOW7 Hb1 ltac:(lia) ltac:(lia)).
    exact (FR6 b n Hb1 Hb2 Hb3 Hb4). }
  assert (RB7 : rdn SEGS m7 (Z_to_bv 64 (s - 128)) 4 = Some bc).
  { rewrite (dst_rd C A7 m6 m7 (s - 256) (s - 152) (s - 128) 4 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM7 LOW7 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact RB6. }
  assert (R37 : rdn SEGS m7 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
  { rewrite (dst_rd C A7 m6 m7 (s - 256) (s - 152) (s - 160) 8 CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM7 LOW7 ltac:(lia) ltac:(lia) ltac:(lia)).
    exact R36. }
  pose proof (O23LeptUddLib.PIXO_dst C A6 A7 m6 m7 pix3 w3 h3 data3 L2 PO36 ON7 D32 (proj2 PM7)) as PO37.
  destruct (ud_B2h al_rom (mkFP fr5 cs5) r9 m7 s Hs256 Hs64 ltac:(csr; reflexivity)) as (r10 & RUN10 & F10a & F10b & AG10).
  rzp HW7 RUN10.
  assert (CS10 : cs_kept regs r10) by (apply cs_kept_intro; csr; reflexivity).
  let ra := rhs F10a in
  assert (FIN : forall A8 m8 vm8 r11, W C A8 m8 (with_vmmaps vm8 md) -> cs_kept r10 r11 ->
      O23LeptUddLib.only A7 A8 L3 -> O23LeptUddLib.offs A8 L3 -> POSTM C A8 (s - 152) m7 m8 ->
      (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 152 <= b)%Z ->
         rdn SEGS m8 (Z_to_bv 64 b) n = rdn SEGS m7 (Z_to_bv 64 b) n) ->
      aroom A8 vm8 kR bR ->
      realizes SEGS (mkCfg (@mkst (mkFP fr5 cs5) r11 ra m8 al_rom) (with_vmmaps vm8 md)) S).
  { intros A8 m8 vm8 r11 HW8 CS11 ON8 OF8 PM8 FR8 RM8.
    assert (ONm : O23LeptUddLib.only A6 A8 (L2 ++ L3)) by exact (O23LeptUddLib.only_trans A6 A7 A8 L2 L3 ON7 ON8).
    assert (ONf5 : O23LeptUddLib.only A5 A8 (L1 ++ L2 ++ L3)) by exact (O23LeptUddLib.only_trans A5 A6 A8 L1 (L2 ++ L3) ON6 ONm).
    assert (ONf : O23LeptUddLib.only A A8 (L1 ++ L2 ++ L3)) by exact (O23LeptUddLib.only_trans_l A A5 A8 _ ON ONf5).
    assert (OF2 : O23LeptUddLib.offs A8 L2) by exact (O23LeptUddLib.offs_only A7 A8 L2 L3 OF7 ON8 OF8).
    assert (OF23 : O23LeptUddLib.offs A8 (L2 ++ L3)) by exact (O23LeptUddLib.offs_app A8 L2 L3 OF2 OF8).
    assert (OF1 : O23LeptUddLib.offs A8 L1) by exact (O23LeptUddLib.offs_only A6 A8 L1 (L2 ++ L3) OF6 ONm OF23).
    assert (OFf : O23LeptUddLib.offs A8 (L1 ++ L2 ++ L3)) by exact (O23LeptUddLib.offs_app A8 L1 (L2 ++ L3) OF1 OF23).
    pose proof (O23LeptUddLib.sub_of_only A A8 _ ONf OF) as SUB8.
    eapply udb_pc; [| apply (K fr5 cs5 A8 m8 vm8 r11 bc HW8 FZ)].
    1: reflexivity.
    - exact (cs_kept_trans regs r10 r11 CS10 CS11).
    - exact (O23LeptUddLib.live_eq_fin A A8 _ ONf OF OFf).
    - eapply POSTM_trans; [exact PMA7 |]. apply (POSTM_sub C A A8 s m7 m8 SUB8). eapply POSTM_mono; [| exact PM8]; lia.
    - intros b n Hb1 Hb2 Hb3 Hb4. rewrite (FR8 b n Hb1 Hb2 ltac:(lia)). exact (FR7 b n Hb1 Hb2 Hb3 Hb4).
    - rewrite (FR8 (s - 128)%Z 4%nat ltac:(lia) ltac:(lia) ltac:(lia)). exact RB7.
    - exact LB.
    - exact RM8. }
  destruct PO37 as [E3 | [NZ3 PC3]].
  - subst pix3.
    let ra := rhs F10a in
    eapply udb_pc; [| apply (pixDestroy_null_W (fx := mkFP fr5 cs5) C A7 m7 (with_vmmaps vm7 md) r10 (s - 256) (s - 160) None ra S CK HW7
        ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) F10a ltac:(red; apply bv_eq; reflexivity) F10b ltac:(split; lia)
        ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) R37)]; [reflexivity |].
    intros m8 r11 HW8 CS11 PM8 OUT8.
    apply (FIN A7 m8 vm7 r11 HW8 CS11).
    + apply O23LeptUddLib.only_refl.
    + intros q Hq. unfold L3, O23LeptUddLib.pixo_l in Hq. cbn in Hq. destruct Hq.
    + eapply POSTM_mono; [| exact PM8]; lia.
    + intros b n Hb1 Hb2 Hb3. apply rdn_ext; [rewrite u_Z2bv by lia; lia |].
      intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT8. lia.
    + exact RM7.
  - pose proof PC3 as (PX3 & L3a & L30 & LD3 & LD30 & NE3 & _).
    pose proof PX3 as (P3a & P3b & WF3 & _).
    assert (Hd3 : (0 <= data3 < 2 ^ 64)%Z) by exact (wf_data _ WF3).
    assert (HR3 : (0 < 4 * (wpl_of w3 1 * h3))%Z) by (destruct (Hwh3 NZ3); pose proof (O23LeptUddLib.wpl_pos w3 ltac:(lia)); nia).
    destruct (blk_range C A7 m7 _ _ _ CK HW7 LD3 HR3) as [B3 _]. rewrite u_Z2bv in B3 by lia.
    let ra := rhs F10a in
    eapply udb_pc; [| apply (pixDestroy_keep_W (fx := mkFP fr5 cs5) C A7 m7 (with_vmmaps vm7 md) r10 (s - 256) (s - 160) pix3 0 0
        (4 * (wpl_of w3 1 * h3)) _ cmap0 ra S CK HW7 ltac:(csr; reflexivity) Hsp16 ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) F10a
        ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(apply V23LeptUb.sp_slot_al8; [exact Hs16 | reflexivity]) F10b R37 PX3
        eq_refl eq_refl eq_refl L3a L30 LD3 LD30 HR3 NE3 (or_introl eq_refl))]; [reflexivity |].
    intros A8 m8 vm8 r11 HW8 CS11 PD8 PM8 Z8 LOW8 RT8.
    rewrite with_vmmaps_twice in HW8 |- *. rewrite with_vmmaps_vmmaps in RT8.
    assert (X8 : O23LeptUddLib.only A7 A8 L3 /\ O23LeptUddLib.offs A8 L3).
    { unfold L3. rewrite (O23LeptUddLib.pixo_l_ne pix3 data3 NZ3).
      exact (O23LeptUddLib.pixd_post_l A7 A8 pix3 data3 0 (c_arr cmap0) ltac:(lia) PD8). }
    destruct X8 as [ON8 OF8].
    apply (FIN A8 m8 vm8 r11 HW8 CS11 ON8 OF8).
    + eapply POSTM_mono; [| exact PM8]; lia.
    + intros b n Hb1 Hb2 Hb3.
      exact (dst_rd C A8 m7 m8 (s - 256) (s - 160) b n CK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PM8 LOW8 Hb1 ltac:(lia) ltac:(lia)).
    + pose proof (RT8 kR bR RM7 ltac:(lia) ltac:(lia)) as RM8. rewrite !Z.sub_0_r in RM8. exact RM8.
Qed.

(* [comment removed for export] *)
Lemma udd_blk2_W : forall fr cs C A (m : word -> option byte) md regs (s pix0 w h cd data selA selB : Z) (cvx : cmapv) (svA svB : selv)
    (cA cB : Z -> Z -> Z) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md -> frm_zero cs ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + UDD_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 256) -> getr regs 4 = Z_to_bv 64 0x1381d0 -> getr regs 9 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 0 ->
  getr regs 23 = Z_to_bv 64 pix0 -> getr regs 21 = Z_to_bv 64 selA -> getr regs 22 = Z_to_bv 64 selB ->
  O23LeptUddLib.PIXC C A m pix0 w h cd data cvx -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  sel_at (alloc_top (c_vm C)) A m selA svA -> sel_cont m svA cA -> (0 <= v_cx svA < v_sx svA)%Z -> (0 <= v_cy svA < v_sy svA)%Z -> v_sy svA = 5%Z ->
  sel_at (alloc_top (c_vm C)) A m selB svB -> sel_cont m svB cB -> (0 <= v_cx svB < v_sx svB)%Z -> (0 <= v_cy svB < v_sy svB)%Z -> v_sy svB = 5%Z ->
  O23LeptUddLib.disj (O23LeptUddLib.sel_l selA svA) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) -> O23LeptUddLib.disj (O23LeptUddLib.sel_l selB svB) (O23LeptUddLib.pix_l pix0 data cd (c_arr cvx)) ->
  aroom A (m_vmmaps md) kR bR -> (RK_blk <= kR)%Z -> (RB_blk w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs' (bc : list byte), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     (forall q, live A' q = live A q) -> POSTM C A s m m' ->
     (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
        (b + Z.of_nat n <= s - 128 \/ s - 128 + 4 <= b)%Z -> rdn SEGS m' (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n) ->
     rdn SEGS m' (Z_to_bv 64 (s - 128)) 4 = Some bc -> length bc = 4%nat -> aroom A' vm' (kR - RK_blk) (bR - RB_blk w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' (0xafcf4 : word) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xafc50 : word) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs s pix0 w h cd data selA selB cvx svA svB cA cB S kR bR
    CK HW FZ Hs16 Hlo Hhi H2 H4 H9 H20 H23 H24 H25 PC0 Hhdr Hw Hh SA ScA HcxA HcyA HsyA SB ScB HcxB HcyB HsyB DA DB RM HK HB K.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 5072 <= s)%Z) by (unfold UDD_STACK, MSEQ_STACK, CSC_STACK in Hlo; lia).
  assert (EH : HMT_STACK = 3744%Z) by reflexivity.
  assert (EP : POR_STACK = 528%Z) by reflexivity.
  assert (EC1 : CASC_STACK = 3792%Z) by reflexivity.
  assert (EC2 : CNT_STACK = 4544%Z) by reflexivity.
  assert (ERK : RK_pixcopy = 4%Z) by reflexivity.
  assert (ERC : RK_casc = 5%Z) by reflexivity.
  assert (ERB : RK_blk = 14%Z) by reflexivity.
  assert (ERBB : RB_blk w h = (2 * (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapcopy) + RB_casc w h + 2 ^ 17)%Z) by reflexivity.
  pose proof (aroom_nonneg _ _ _ _ RM) as [Hk0 Hb0].
  assert (Hx : (2 ^ 17 <= RB_pixT (4 * (wpl_of w 1 * h)))%Z) by (unfold RB_pixT, RB_hdrT; lia).
  assert (Hc : (0 <= RB_cmapT cd <= RB_cmapcopy)%Z) by (unfold RB_cmapT, RB_cmapcopy; lia).
  pose proof (O23LeptUddLib.RB_casc_nonneg w h) as Hcn.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (Hs256 : (256 <= s)%Z) by lia.
  assert (Hsp16 : ((s - 256) mod 16 = 0)%Z) by mod16 Hs16.
  assert (HT : (alloc_top (c_vm C) < 2 ^ 64)%Z) by lia.
  assert (RS : rop_shape w h 1 (wpl_of w 1)) by (red; destruct Hhdr as (_ & X1 & X2 & X3); repeat split; first [left; reflexivity | lia]).
  pose proof PC0 as (PX0 & L0 & L00 & LD0 & _ & _ & _).
  destruct (ud_B2a al_rom (mkFP fr cs) regs m) as (r1 & RUN1 & Q1a & Q1b & Q1c & Q1d & AG1).
  rzp HW RUN1.
  let ra := rhs Q1a in
  eapply udb_pc; [| apply (pixHMT_new_sure_W (fx := mkFP fr cs) C A m md r1 (s - 256) pix0 selA w h cd data svA cA cvx ra S CK HW
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q1a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q1b
      ltac:(csr; reflexivity) ltac:(csr; reflexivity) PX0 Hhdr Hw Hh L0 L00 LD0 (O23LeptUddLib.PIXC_hprem _ _ _ _ _ _ _ _ _ PC0)
      SA ScA HcxA HcyA
      (fun p Hp => O23LeptUddLib.disj_neW _ _ _ _ DA (O23LeptUddLib.sel_l_in selA svA p HsyA Hp) (O23LeptUddLib.pix_l_pix pix0 data cd (c_arr cvx)))
      kR bR RM ltac:(lia) ltac:(lia))]; [reflexivity |].
  intros A1 m1 vm1 r2 HW1 CS2 [pixd1 [cd1 [data1 [G2a [PT1 PM1]]]]] RM1.
  destruct (O23LeptUddLib.PIXC_of_pixt_new C A A1 m1 pixd1 w h cd1 data1 cvx PT1) as (cv1 & PC1 & ON1 & OF1).
  pose proof (O23LeptUddLib.sub_of_only A A1 _ ON1 OF1) as SUB1.
  assert (PMA1 : POSTM C A s m m1) by (eapply POSTM_mono; [| exact PM1]; lia).
  assert (E1 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m1 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) m m1 b n CK (proj1 PM1) Hb1 ltac:(lia) ltac:(lia))).
  pose proof PC1 as (PX1 & L1a & L10 & LD1 & LD10 & NE1 & _).
  pose proof PX1 as (P1a & P1b & WF1 & _).
  assert (Hd1 : (0 <= data1 < 2 ^ 64)%Z) by exact (wf_data _ WF1).
  destruct (ud_B2b al_rom (mkFP fr cs) r2 m1 s Hs256 Hs64 (W_sok_win C A1 m1 _ (s - 144) 8 CK HW1 ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity))
    as (r3 & RUN3 & Q3a & Q3b & Q3c & Q3d & AG3).
  rzp HW1 RUN3.
  set (M2 := O23LeptUddSegs.wr8w m1 (s - 144) (getr r2 10)) in *.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2) by exact (WP_win C A1 A m m1 _ (Z_to_bv 64 (s - 144))
    (word_to_le_bytes 8 (getr r2 10)) s CK (conj HW1 PMA1) SUB1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi).
  destruct WP2 as [HW2 PMA2].
  assert (PL2 : POSTM C A1 s m1 M2) by exact (proj2 (WP_win C A1 A1 m1 m1 _ (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (getr r2 10)) s CK
    (conj HW1 (POSTM_refl C A1 s m1)) (sub_live_refl A1) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi)).
  assert (E2 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 144 \/ s - 136 <= b)%Z ->
     rdn SEGS M2 (Z_to_bv 64 b) n = rdn SEGS m1 (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3. unfold M2, O23LeptUddSegs.wr8w. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia. }
  assert (H2h : rdn SEGS M2 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixd1)).
  { unfold M2, O23LeptUddSegs.wr8w. rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite G2a, w2b_Z by lia. reflexivity. }
  pose proof (O23LeptUddLib.PIXC_livk C A A1 m M2 pix0 w h cd data cvx PC0 SUB1 (proj2 PMA2)) as PC0b.
  pose proof (O23LeptUddLib.PIXC_livk C A1 A1 m1 M2 pixd1 w h cd1 data1 cv1 PC1 (sub_live_refl A1) (proj2 PL2)) as PC1b.
  pose proof (sel_at_keep (alloc_top (c_vm C)) A A1 m M2 selB svB HT SB SUB1 (proj2 PMA2)) as SB2.
  pose proof (udb_sel_cont_keep (alloc_top (c_vm C)) A m M2 selB svB cB HT SB (proj2 PMA2) ScB) as ScB2.
  pose proof PC0b as (PX0b & L0b & _ & LD0b & _ & _ & _).
  let ra := rhs Q3a in
  eapply udb_pc; [| apply (pixHMT_new_sure_W (fx := mkFP fr cs) C A1 M2 (with_vmmaps vm1 md) r3 (s - 256) pix0 selB w h cd data svB cB cvx ra S CK HW2
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q3a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q3b
      ltac:(csr; reflexivity) ltac:(csr; reflexivity) PX0b Hhdr Hw Hh L0b L00 LD0b (O23LeptUddLib.PIXC_hprem _ _ _ _ _ _ _ _ _ PC0b)
      SB2 ScB2 HcxB HcyB
      (fun p Hp => O23LeptUddLib.disj_neW _ _ _ _ DB (O23LeptUddLib.sel_l_in selB svB p HsyB Hp) (O23LeptUddLib.pix_l_pix pix0 data cd (c_arr cvx)))
      (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd)) ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia))];
    [reflexivity |].
  intros A2 m3 vm2 r4 HW3 CS4 [pixd2 [cd2 [data2 [G4a [PT2 PM3]]]]] RM2.
  rewrite with_vmmaps_twice in HW3 |- *.
  destruct (O23LeptUddLib.PIXC_of_pixt_new C A1 A2 m3 pixd2 w h cd2 data2 cvx PT2) as (cv2 & PC2 & ON2 & OF2).
  pose proof (O23LeptUddLib.sub_of_only A1 A2 _ ON2 OF2) as SUB12.
  assert (SUB2 : sub_live A A2) by (intros q k Hq; exact (SUB12 q k (SUB1 q k Hq))).
  assert (PMA3 : POSTM C A s m m3)
    by (eapply POSTM_trans; [exact PMA2 | apply (POSTM_sub C A A1 s M2 m3 SUB1); eapply POSTM_mono; [| exact PM3]; lia]).
  assert (E3 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m3 (Z_to_bv 64 b) n = rdn SEGS M2 (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M2 m3 b n CK (proj1 PM3) Hb1 ltac:(lia) ltac:(lia))).
  pose proof (O23LeptUddLib.PIXC_livk C A1 A2 M2 m3 pixd1 w h cd1 data1 cv1 PC1b SUB12 (proj2 PM3)) as PC1c.
  pose proof (O23LeptUddLib.lives_of_PIXC _ _ _ _ _ _ _ _ _ PC1b) as LV1.
  pose proof (O23LeptUddLib.disj_off_live A1 _ _ LV1 OF2) as D12.
  pose proof (O23LeptUddLib.disj_sym _ _ D12) as D21.
  pose proof PC2 as (PX2 & L2a & L20 & LD2 & LD20 & NE2 & _).
  pose proof PX2 as (P2a & P2b & WF2 & _).
  assert (Hd2 : (0 <= data2 < 2 ^ 64)%Z) by exact (wf_data _ WF2).
  assert (R144c : rdn SEGS m3 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd1))).
  { rewrite (E3 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), H2h, w2b_Z by lia. reflexivity. }
  destruct (ud_B2c al_rom (mkFP fr cs) r4 m3 s (Z_to_bv 64 pixd1) Hs256 Hs64 R144c (W_sok_win C A2 m3 _ (s - 152) 8 CK HW3 ltac:(lia) ltac:(lia))
      ltac:(csr; reflexivity)) as (r5 & RUN5 & Q5a & Q5b & Q5c & Q5d & AG5).
  rzp HW3 RUN5.
  set (M4 := O23LeptUddSegs.wr8w m3 (s - 152) (getr r4 10)) in *.
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A s m M4) by exact (WP_win C A2 A m m3 _ (Z_to_bv 64 (s - 152))
    (word_to_le_bytes 8 (getr r4 10)) s CK (conj HW3 PMA3) SUB2 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi).
  destruct WP4 as [HW4 PMA4].
  assert (PL4 : POSTM C A2 s m3 M4) by exact (proj2 (WP_win C A2 A2 m3 m3 _ (Z_to_bv 64 (s - 152)) (word_to_le_bytes 8 (getr r4 10)) s CK
    (conj HW3 (POSTM_refl C A2 s m3)) (sub_live_refl A2) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi)).
  assert (E4 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 152 \/ s - 144 <= b)%Z ->
     rdn SEGS M4 (Z_to_bv 64 b) n = rdn SEGS m3 (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3. unfold M4, O23LeptUddSegs.wr8w. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia. }
  assert (H4h : rdn SEGS M4 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixd2)).
  { unfold M4, O23LeptUddSegs.wr8w. rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite G4a, w2b_Z by lia. reflexivity. }
  pose proof (O23LeptUddLib.PIXC_livk C A2 A2 m3 M4 pixd1 w h cd1 data1 cv1 PC1c (sub_live_refl A2) (proj2 PL4)) as PC1d.
  pose proof (O23LeptUddLib.PIXC_livk C A2 A2 m3 M4 pixd2 w h cd2 data2 cv2 PC2 (sub_live_refl A2) (proj2 PL4)) as PC2d.
  pose proof PC1d as (PX1d & L1d & _ & LD1d & _ & _ & _).
  pose proof PC2d as (PX2d & L2d & _ & LD2d & _ & _ & _).
  pose proof (O23LeptUddLib.pix_l_pix pixd1 data1 cd1 (c_arr cv1)) as I1p.
  pose proof (O23LeptUddLib.pix_l_data pixd1 data1 cd1 (c_arr cv1)) as I1d.
  pose proof (O23LeptUddLib.pix_l_pix pixd2 data2 cd2 (c_arr cv2)) as I2p.
  pose proof (O23LeptUddLib.pix_l_data pixd2 data2 cd2 (c_arr cv2)) as I2d.
  let ra := rhs Q5a in
  eapply udb_pc; [| apply (pixOr_inplace_W (fx := mkFP fr cs) C A A2 M4 (with_vmmaps vm2 md) r5 (s - 256)%Z pixd1 pixd2 _ _ ra S CK HW4 SUB2
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q5a ltac:(red; apply bv_eq; reflexivity) Q5b Q5c ltac:(csr; reflexivity)
      PX1d PX2d eq_refl eq_refl RS RS L1d L2d (O23LeptUddLib.disj_neW _ _ _ _ D12 I1p I2p)
      (zbv_ne pixd1 data1 ltac:(lia) Hd1 (fun E => NE1 (eq_sym E))) (O23LeptUddLib.disj_neW _ _ _ _ D21 I2p I1d)
      LD1d (OF1 _ I1d) LD10 LD2d (O23LeptUddLib.disj_neW _ _ _ _ D21 I2d I1d))]; [reflexivity |].
  intros M6 r6 HW6 CS6 PM6 PX16 PX26 OUT6 G6a.
  assert (PMA6 : POSTM C A s m M6) by (eapply POSTM_trans; [exact PMA4 | eapply POSTM_mono; [| exact PM6]; lia]).
  assert (E6 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS M6 (Z_to_bv 64 b) n = rdn SEGS M4 (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M4 M6 b n CK (proj1 PM6) Hb1 ltac:(lia) ltac:(lia))).
  pose proof (udb_livke C A2 M4 M6 _ data1 _ (s - 256) CK HW4 LD1d Hd1 OUT6) as LVE6.
  assert (CD1 : cd1 <> 0%Z -> cd1 <> data1) by exact (O23LeptUddLib.PIXC_cd_data _ _ _ _ _ _ _ _ _ PC1).
  pose proof (O23LeptUddLib.PIXC_livke C A2 A2 M4 M6 pixd1 w h cd1 data1 cv1 data1 PC1d LVE6 Hd1 (fun E => NE1 (eq_sym E)) CD1 (fun p _ => eq_refl)) as PC1e.
  assert (NE21 : pixd2 <> data1) by exact (O23LeptUddLib.disj_neZ _ _ _ _ D21 I2p I1d).
  assert (CD21 : cd2 <> 0%Z -> cd2 <> data1)
    by (intros X; exact (O23LeptUddLib.disj_neZ _ _ _ _ D21 (O23LeptUddLib.pix_l_cd pixd2 data2 cd2 (c_arr cv2) X) I1d)).
  pose proof (O23LeptUddLib.PIXC_livke C A2 A2 M4 M6 pixd2 w h cd2 data2 cv2 data1 PC2d LVE6 Hd1 NE21 CD21 (fun p _ => eq_refl)) as PC2e.
  assert (R144e : rdn SEGS M6 (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd1))).
  { rewrite (E6 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), (E4 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
      (E3 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), H2h, w2b_Z by lia. reflexivity. }
  destruct (ud_B2d al_rom (mkFP fr cs) r6 M6 s (Z_to_bv 64 pixd1) Hs256 Hs64 R144e ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & Q7a & Q7b & Q7c & Q7d & Q7e & Q7f & AG7).
  rzp HW6 RUN7.
  pose proof PC1e as (PX1e & L1e & _ & LD1e & _ & _ & _).
  let ra := rhs Q7a in
  eapply udb_pc; [| apply (pixReduceRankBinaryCascade_11_W fr cs C A A2 M6 (with_vmmaps vm2 md) r7 (s - 256) pixd1 1 w h cd1 data1 ra S CK HW6 FZ SUB2
      ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q7a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
      Q7b Q7c Q7d Q7e Q7f PX1e Hhdr Hw Hh L1e LD1e (OF1 _ I1d) LD10 (fun E => NE1 (eq_sym E))
      (kR - RK_pixcopy - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd))
      ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia))]; [reflexivity |].
  intros fr' cs' A4 m7 vm4 r8 HW7 FZ' _ CS8 PM7 LVK7 PX17 RES RM4.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (PMA7 : POSTM C A s m m7) by (eapply POSTM_trans; [exact PMA6 | eapply POSTM_mono; [| exact PM7]; lia]).
  assert (E7 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m7 (Z_to_bv 64 b) n = rdn SEGS M6 (Z_to_bv 64 b) n)
    by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M6 m7 b n CK (proj1 PM7) Hb1 ltac:(lia) ltac:(lia))).
  assert (POST3 : exists pix3 w3 h3 data3, getr r8 10 = Z_to_bv 64 pix3 /\ O23LeptUddLib.PIXO C A4 m7 pix3 w3 h3 data3 /\
      O23LeptUddLib.only A2 A4 (O23LeptUddLib.pixo_l pix3 data3) /\ O23LeptUddLib.offs A2 (O23LeptUddLib.pixo_l pix3 data3) /\
      (pix3 <> 0%Z -> (1 <= w3)%Z /\ (1 <= h3)%Z /\ O23LeptPixHdrT2.hdr_ok w3 h3 1)).
  { destruct RES as [[G8 LV8] | (pix3 & data3 & G8 & Hw4 & Hh4 & Hhd3 & PR3)].
    - exists 0%Z, 0%Z, 0%Z, 0%Z. split; [exact G8 |]. split; [red; left; reflexivity |].
      split; [apply O23LeptUddLib.only_eq; exact LV8 |]. split; [intros q Hq; cbn in Hq; destruct Hq |].
      intros X; exfalso; apply X; reflexivity.
    - destruct (O23LeptUddLib.PIXC_of_pixr_new C A2 A4 m7 pix3 data3 (w / 2 / 2) (h / 2 / 2) cmap0 PR3) as (PC3 & ON3 & OF3).
      pose proof PC3 as (PX3 & L3 & _).
      pose proof PX3 as (P3a & P3b & _).
      destruct (blk_range C A4 m7 _ _ _ CK HW7 L3 ltac:(lia)) as [B3 _]. rewrite u_Z2bv in B3 by lia.
      assert (W2 : (2 <= w / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      assert (W4 : (1 <= w / 2 / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      assert (H2' : (2 <= h / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      assert (H4' : (1 <= h / 2 / 2)%Z) by (apply Z.div_le_lower_bound; lia).
      exists pix3, (w / 2 / 2)%Z, (h / 2 / 2)%Z, data3. split; [exact G8 |]. split; [red; right; split; [lia | exact PC3] |].
      rewrite O23LeptUddLib.pixo_l_ne by lia. split; [exact ON3 |]. split; [exact OF3 |].
      intros _. split; [exact W4 | split; [exact H4' | exact Hhd3]]. }
  destruct POST3 as (pix3 & w3 & h3 & data3 & G8 & PO3 & ON3 & OF3 & HP3).
  set (LL1 := O23LeptUddLib.pix_l pixd1 data1 cd1 (c_arr cv1)) in *.
  set (LL2 := O23LeptUddLib.pix_l pixd2 data2 cd2 (c_arr cv2)) in *.
  set (LL3 := O23LeptUddLib.pixo_l pix3 data3) in *.
  assert (SUB24 : sub_live A2 A4) by exact (O23LeptUddLib.sub_of_only A2 A4 _ ON3 OF3).
  assert (SUB4 : sub_live A A4) by (intros q k Hq; exact (SUB24 q k (SUB2 q k Hq))).
  pose proof (O23LeptUddLib.lives_of_PIXC _ _ _ _ _ _ _ _ _ PC1d) as LV1d.
  pose proof (O23LeptUddLib.lives_of_PIXC _ _ _ _ _ _ _ _ _ PC2d) as LV2d.
  pose proof (O23LeptUddLib.disj_off_live A2 _ _ LV1d OF3) as D13.
  pose proof (O23LeptUddLib.disj_off_live A2 _ _ LV2d OF3) as D23.
  pose proof (O23LeptUddLib.PIXC_livke C A2 A4 M6 m7 pixd1 w h cd1 data1 cv1 data1 PC1e LVK7 Hd1 (fun E => NE1 (eq_sym E)) CD1
    (fun p Hp => ON3 p (D13 p Hp))) as PC1f.
  pose proof (O23LeptUddLib.PIXC_livke C A2 A4 M6 m7 pixd2 w h cd2 data2 cv2 data1 PC2e LVK7 Hd1 NE21 CD21
    (fun p Hp => ON3 p (D23 p Hp))) as PC2f.
  destruct (ud_B2e al_rom (mkFP fr' cs') r8 m7 s Hs256 Hs64 (W_sok_win C A4 m7 _ (s - 160) 8 CK HW7 ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity))
    as (r9 & RUN9 & Q9a & Q9b & Q9c & Q9d & AG9).
  rzp HW7 RUN9.
  set (M8 := O23LeptUddSegs.wr8w m7 (s - 160) (getr r8 10)) in *.
  assert (WP8 : W C A4 M8 (with_vmmaps vm4 md) /\ POSTM C A s m M8) by exact (WP_win C A4 A m m7 _ (Z_to_bv 64 (s - 160))
    (word_to_le_bytes 8 (getr r8 10)) s CK (conj HW7 PMA7) SUB4 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi).
  destruct WP8 as [HW8 PMA8].
  assert (PL8 : POSTM C A4 s m7 M8) by exact (proj2 (WP_win C A4 A4 m7 m7 _ (Z_to_bv 64 (s - 160)) (word_to_le_bytes 8 (getr r8 10)) s CK
    (conj HW7 (POSTM_refl C A4 s m7)) (sub_live_refl A4) ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia) Hhi)).
  assert (E8 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 152 <= b)%Z ->
     rdn SEGS M8 (Z_to_bv 64 b) n = rdn SEGS m7 (Z_to_bv 64 b) n).
  { intros b n Hb1 Hb2 Hb3. unfold M8, O23LeptUddSegs.wr8w. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia. }
  assert (Hp3 : (0 <= pix3 < 2 ^ 64)%Z).
  { destruct PO3 as [E | (_ & PCx)]; [rewrite E; lia |]. destruct PCx as ((X1 & X2 & _) & _). lia. }
  assert (H8h : rdn SEGS M8 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
  { unfold M8, O23LeptUddSegs.wr8w. rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite G8, w2b_Z by lia. reflexivity. }
  pose proof (O23LeptUddLib.PIXC_livk C A4 A4 m7 M8 pixd1 w h cd1 data1 cv1 PC1f (sub_live_refl A4) (proj2 PL8)) as PC1g.
  pose proof (O23LeptUddLib.PIXC_livk C A4 A4 m7 M8 pixd2 w h cd2 data2 cv2 PC2f (sub_live_refl A4) (proj2 PL8)) as PC2g.
  pose proof (O23LeptUddLib.PIXO_livk C A4 A4 m7 M8 pix3 w3 h3 data3 PO3 (sub_live_refl A4) (proj2 PL8)) as PO3g.
  let ra := rhs Q9a in
  assert (FIN2 : forall A5 m9 vm5 r10 (M9 : word -> option byte) (bc : list byte) (k5 b5 : Z),
      W C A5 m9 (with_vmmaps vm5 md) -> cs_kept r9 r10 -> (forall q, live A5 q = live A4 q) ->
      POSTM C A4 (s - 256) M9 m9 -> POSTM C A s m M9 -> LIVK A4 M8 M9 ->
      (forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 128 \/ s - 124 <= b)%Z ->
         rdn SEGS M9 (Z_to_bv 64 b) n = rdn SEGS M8 (Z_to_bv 64 b) n) ->
      rdn SEGS M9 (Z_to_bv 64 (s - 128)) 4 = Some bc -> length bc = 4%nat -> aroom A5 vm5 k5 b5 ->
      (kR - RK_blk <= k5)%Z -> (bR - RB_blk w h <= b5)%Z ->
      realizes SEGS (mkCfg (@mkst (mkFP fr' cs') r10 ra m9 al_rom) (with_vmmaps vm5 md)) S).
  { intros A5 m9 vm5 r10 M9 bc k5 b5 HW9 CS10 LV9 PM9 PMA9 LK9 F9 RB9 LB9 RM5 Hk5 Hb5.
    assert (SUB45 : sub_live A4 A5) by (intros q k Hq; rewrite LV9; exact Hq).
    assert (LK : LIVK A4 M8 m9) by exact (LIVK_trans A4 M8 M9 m9 LK9 (proj2 PM9)).
    assert (E9 : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> rdn SEGS m9 (Z_to_bv 64 b) n = rdn SEGS M9 (Z_to_bv 64 b) n)
      by (intros b n Hb1 Hb2; exact (FRM_rdn16 C (s - 256) M9 m9 b n CK (proj1 PM9) Hb1 ltac:(lia) ltac:(lia))).
    pose proof (O23LeptUddLib.PIXC_livk C A4 A5 M8 m9 pixd1 w h cd1 data1 cv1 PC1g SUB45 LK) as PC1h.
    pose proof (O23LeptUddLib.PIXC_livk C A4 A5 M8 m9 pixd2 w h cd2 data2 cv2 PC2g SUB45 LK) as PC2h.
    pose proof (O23LeptUddLib.PIXO_livk C A4 A5 M8 m9 pix3 w3 h3 data3 PO3g SUB45 LK) as PO3h.
    assert (ONa : O23LeptUddLib.only A A2 (LL1 ++ LL2 ++ LL3)).
    { apply (O23LeptUddLib.only_sub A A2 (LL1 ++ LL2) _ (O23LeptUddLib.only_trans A A1 A2 LL1 LL2 ON1 ON2)).
      intros q Hq. rewrite app_assoc. apply in_or_app. left. exact Hq. }
    assert (ONb : O23LeptUddLib.only A A4 (LL1 ++ LL2 ++ LL3)).
    { apply (O23LeptUddLib.only_trans_l A A2 A4 _ ONa). apply (O23LeptUddLib.only_sub A2 A4 LL3 _ ON3). intros q Hq; in_app. }
    assert (ONf : O23LeptUddLib.only A A5 (LL1 ++ LL2 ++ LL3))
      by exact (O23LeptUddLib.only_trans_l A A4 A5 _ ONb (O23LeptUddLib.only_eq A4 A5 _ LV9)).
    assert (OFf : O23LeptUddLib.offs A (LL1 ++ LL2 ++ LL3)) by exact (O23LeptUddLib.offs_app A LL1 _ OF1
        (O23LeptUddLib.offs_app A LL2 LL3 (O23LeptUddLib.offs_sub A A1 LL2 OF2 SUB1) (O23LeptUddLib.offs_sub A A2 LL3 OF3 SUB2))).
    assert (PMf : POSTM C A s m m9).
    { eapply POSTM_trans; [exact PMA9 |]. apply (POSTM_sub C A A4 s M9 m9 SUB4). eapply POSTM_mono; [| exact PM9]; lia. }
    assert (R144 : rdn SEGS m9 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixd1)).
    { rewrite (E9 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), (F9 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
        (E8 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)), (E7 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)),
        (E6 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)), (E4 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
        (E3 (s - 144)%Z 8%nat ltac:(lia) ltac:(lia)). exact H2h. }
    assert (R152 : rdn SEGS m9 (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixd2)).
    { rewrite (E9 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia)), (F9 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)),
        (E8 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)), (E7 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia)),
        (E6 (s - 152)%Z 8%nat ltac:(lia) ltac:(lia)). exact H4h. }
    assert (R160 : rdn SEGS m9 (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 pix3)).
    { rewrite (E9 (s - 160)%Z 8%nat ltac:(lia) ltac:(lia)), (F9 (s - 160)%Z 8%nat ltac:(lia) ltac:(lia) ltac:(lia)). exact H8h. }
    assert (RBm : rdn SEGS m9 (Z_to_bv 64 (s - 128)) 4 = Some bc).
    { rewrite (E9 (s - 128)%Z 4%nat ltac:(lia) ltac:(lia)). exact RB9. }
    assert (FRm : forall (b : Z) (n : nat), (s - 256 <= b)%Z -> (b + Z.of_nat n <= s)%Z -> (b + Z.of_nat n <= s - 160 \/ s - 136 <= b)%Z ->
       (b + Z.of_nat n <= s - 128 \/ s - 128 + 4 <= b)%Z -> rdn SEGS m9 (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n).
    { intros b n Hb1 Hb2 Hb3 Hb4.
      rewrite (E9 b n Hb1 Hb2), (F9 b n Hb1 Hb2 ltac:(lia)), (E8 b n Hb1 Hb2 ltac:(lia)), (E7 b n Hb1 Hb2), (E6 b n Hb1 Hb2),
        (E4 b n Hb1 Hb2 ltac:(lia)), (E3 b n Hb1 Hb2), (E2 b n Hb1 Hb2 ltac:(lia)), (E1 b n Hb1 Hb2). reflexivity. }
    eapply udb_pc; [| apply (udd_blk2_tail fr' cs' C A A5 m m9 md vm5 regs r10 s pixd1 w h cd1 data1 pixd2 cd2 data2 pix3 w3 h3 data3 cv1 cv2 bc S k5 b5
        CK HW HW9 FZ' Hs16 Hlo Hhi ltac:(apply cs_kept_intro; csr; reflexivity) H2 H4 H9 R144 R152 R160 RBm LB9 FRm
        PC1h PC2h PO3h Hw Hh (fun X => conj (proj1 (HP3 X)) (proj1 (proj2 (HP3 X)))) D21 (O23LeptUddLib.disj_sym _ _ D13)
        (O23LeptUddLib.disj_sym _ _ D23) ONf OFf PMf RM5)]; [reflexivity |].
    intros fr'' cs'' A' m' vm' regs' bc' HWf FZf CSf LVf PMf' FRf RBf LBf RMf.
    eapply udb_pc; [| apply (K fr'' cs'' A' m' vm' regs' bc' HWf FZf CSf LVf PMf' FRf RBf LBf)]; [reflexivity |].
    apply (aroom_mono A' vm' k5 b5 _ _ RMf); lia. }
  destruct (Z.eq_dec pix3 0) as [Z3 | NZ3].
  - subst pix3.
    let ra := rhs Q9a in
    eapply udb_pc; [| apply (pixCountPixels_null_W (fx := mkFP fr' cs') C A4 M8 (with_vmmaps vm4 md) r9 (s - 256) (s - 128) ra S CK HW8
        ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q9a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) Q9c ltac:(lia) ltac:(lia)
        ltac:(apply V23LeptUb.sp_slot_al4'; [exact Hs16 | reflexivity]))]; [reflexivity |].
    intros m9 r10 HW9 CS10 PM9 _.
    assert (WP9 : W C A4 (CNTM0 M8 (s - 128)) (with_vmmaps vm4 md) /\ POSTM C A s m (CNTM0 M8 (s - 128))) by (unfold CNTM0; wp_win CK).
    assert (WL9 : W C A4 (CNTM0 M8 (s - 128)) (with_vmmaps vm4 md) /\ POSTM C A4 s M8 (CNTM0 M8 (s - 128))) by (unfold CNTM0; wp_win CK).
    apply (FIN2 A4 m9 vm4 r10 (CNTM0 M8 (s - 128)) (word_to_le_bytes 4 (Z_to_bv 64 0)) (kR - RK_pixcopy - RK_pixcopy - RK_casc)%Z
        (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - RB_casc w h)%Z
        HW9 CS10 (fun q => eq_refl) PM9 (proj2 WP9) (proj2 (proj2 WL9))).
    + intros b n Hb1 Hb2 Hb3. unfold CNTM0. apply rdn_wbytes_out_Z. rewrite length_N_to_le_bytes. lia.
    + unfold CNTM0. pose proof (SeqExec.rdn_wbytes_hit SEGS (word_to_le_bytes 4 (Z_to_bv 64 0)) M8 (Z_to_bv 64 (s - 128))
        ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia)) as X. rewrite length_N_to_le_bytes in X. exact X.
    + apply length_N_to_le_bytes.
    + exact RM4.
    + lia.
    + lia.
  - pose proof PO3g as [E3z | (_ & PC3g)]; [contradiction |].
    pose proof PC3g as (PX3g & L3g & _ & LD3g & _ & _ & _).
    destruct (HP3 NZ3) as (Hw3 & Hh3 & Hhd3).
    let ra := rhs Q9a in
    eapply udb_pc; [| apply (pixCountPixels_W (fx := mkFP fr' cs') C A4 M8 (with_vmmaps vm4 md) r9 (s - 256) pix3 (s - 128) 1 w3 h3 0 data3 ra S CK HW8
        ltac:(csr; reflexivity) Hsp16 ltac:(lia) ltac:(lia) Q9a ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
        ltac:(csr; reflexivity) Q9c Q9d ltac:(lia) ltac:(lia) ltac:(apply V23LeptUb.sp_slot_al4'; [exact Hs16 | reflexivity])
        PX3g ltac:(destruct Hhd3 as (_ & X1 & _); lia) ltac:(destruct Hhd3 as (_ & _ & X2 & _); lia) L3g LD3g
        (kR - RK_pixcopy - RK_pixcopy - RK_casc) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - RB_casc w h)
        ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia))]; [reflexivity |].
    intros A5 m9 vm5 r10 wv HW9 CS10 LV9 PM9 _ RM5.
    rewrite with_vmmaps_twice in HW9 |- *.
    assert (WP9 : W C A4 (CNTM M8 (s - 128) wv) (with_vmmaps vm4 md) /\ POSTM C A s m (CNTM M8 (s - 128) wv)) by (unfold CNTM, CNTM0; wp_win CK).
    assert (WL9 : W C A4 (CNTM M8 (s - 128) wv) (with_vmmaps vm4 md) /\ POSTM C A4 s M8 (CNTM M8 (s - 128) wv)) by (unfold CNTM, CNTM0; wp_win CK).
    apply (FIN2 A5 m9 vm5 r10 (CNTM M8 (s - 128) wv) (word_to_le_bytes 4 wv) (kR - RK_pixcopy - RK_pixcopy - RK_casc - 1)%Z
        (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd) - RB_casc w h - 2 ^ 17)%Z
        HW9 CS10 LV9 PM9 (proj2 WP9) (proj2 (proj2 WL9))).
    + intros b n Hb1 Hb2 Hb3. unfold CNTM, CNTM0. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; lia). reflexivity.
    + unfold CNTM. pose proof (SeqExec.rdn_wbytes_hit SEGS (word_to_le_bytes 4 wv) (CNTM0 M8 (s - 128)) (Z_to_bv 64 (s - 128))
        ltac:(rewrite length_N_to_le_bytes, u_Z2bv by lia; lia)) as X. rewrite length_N_to_le_bytes in X. exact X.
    + apply length_N_to_le_bytes.
    + exact RM5.
    + lia.
    + lia.
Qed.

End UddB.
