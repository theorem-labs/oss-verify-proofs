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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptCloseA V23LeptPixDestroyK V23LeptMorphS.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptRbordW V23LeptEroW V23LeptEroGW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptCloseSpec O23LeptCloseIface O23LeptCloseA O23LeptCloseP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CloseP.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma tpx_range : forall C A m md p w h cd data cvd, Cok C -> W C A m md -> O23LeptCloseA.tpx C A m p w h cd data cvd -> (1 <= w)%Z -> (1 <= h)%Z ->
  (4096 <= p)%Z /\ (p + 64 <= alloc_top (c_vm C))%Z /\ (4096 <= data)%Z /\ (data + 4 * (wpl_of w 1 * h) <= alloc_top (c_vm C))%Z /\ (0 < 4 * (wpl_of w 1 * h))%Z.
Proof.
  intros C A m md p w h cd data cvd CK HW (PX & Lp & L0p & Ld & L0d & NE & TC) Hw Hh.
  destruct PX as (Hp0 & Hp64 & WF & _).
  pose proof (wf_data _ WF) as Hd. cbn [p_data O23LeptPixCopyT.hdv] in Hd.
  assert (Hwp : (1 <= wpl_of w 1)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  assert (Hn : (0 < 4 * (wpl_of w 1 * h))%Z) by nia.
  destruct (blk_range C A m md (Z_to_bv 64 p) 64 CK HW Lp ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hn) as [G3 G4]. rewrite u_Z2bv in G3, G4 by lia.
  repeat split; lia.
Qed.

Lemma rblk_live : forall C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m q,
  RST C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m -> O23LeptCloseA.rblk pix1 datas cm cv sel1 sel2 sv1 sv2 q ->
  exists n, live A q = Some n.
Proof.
  intros C Ar me s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A m q R B.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & P1 & S1 & S2 & _ & _).
  destruct B as [B|[B|B]].
  - exact (O23LeptCloseP.p1_live3 C Ar A m pix1 w h cm datas cv q P1 B).
  - exact (O23LeptCloseP.sblk_live _ A m sel1 sv1 q S1 B).
  - exact (O23LeptCloseP.sblk_live _ A m sel2 sv2 q S2 B).
Qed.

Lemma tpx_self_ne : forall C A m md p w h cd data cvd, Cok C -> W C A m md -> O23LeptCloseA.tpx C A m p w h cd data cvd -> (1 <= w)%Z -> (1 <= h)%Z ->
  Z_to_bv 64 p <> Z_to_bv 64 data /\ (cd <> 0%Z -> Z_to_bv 64 cd <> Z_to_bv 64 data).
Proof.
  intros C A m md p w h cd data cvd CK HW (PX & Lp & L0p & Ld & L0d & NE & TC) Hw Hh.
  destruct PX as (Hp0 & Hp64 & WF & _).
  pose proof (wf_data _ WF) as Hd. cbn [p_data O23LeptPixCopyT.hdv] in Hd.
  split.
  - intros E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. contradiction.
  - intros Hcd E. destruct TC as [Z0|(_ & CA & _ & _ & _ & _ & _ & _ & _ & Ncd & _ & _)]; [contradiction|].
    destruct CA as (Hc0 & Hc24 & _).
    apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. contradiction.
Qed.

(* [comment removed for export] *)
Lemma pxd_hop : forall (fx : FPState) C Ar Ak mk vk md r (s pp p w h cd data : Z) (cvd : cmapv) (retpc : word) (S : TSet) (kx bx : Z),
  Cok C -> W C Ak mk (with_vmmaps vk md) -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr r 2 = Z_to_bv 64 (s - 112) -> (s - 112 <= pp)%Z -> (pp + 8 <= s)%Z -> (pp mod 8 = 0)%Z ->
  getr r 1 = retpc -> ret_ok retpc -> getr r 4 = Z_to_bv 64 0x1381d0 -> getr r 10 = Z_to_bv 64 pp ->
  rdn SEGS mk (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 p) ->
  O23LeptCloseA.tpx C Ak mk p w h cd data cvd -> (1 <= w)%Z -> (1 <= h)%Z ->
  (forall q, O23LeptCloseA.tblk p data cd cvd q -> live Ar q = None) ->
  sub_live Ar Ak -> aroom Ak vk kx bx ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> cs_kept r r' ->
     (forall q, O23LeptCloseA.tblk p data cd cvd q -> live A' q = None) -> (forall q, ~ O23LeptCloseA.tblk p data cd cvd q -> live A' q = live Ak q) ->
     O23LeptCloseA.PWK Ak (fun q => ~ O23LeptCloseA.tblk p data cd cvd q) mk m' ->
     (forall a : word, (s - 112 <= u a)%Z -> ~ (pp <= u a < pp + 8)%Z -> m' a = mk a) ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     sub_live Ar A' -> POSTM C Ar s mk m' -> aroom A' vm' kx bx ->
     realizes SEGS (mkCfg (mkst r' retpc m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0x6df98 : word) mk al_rom) (with_vmmaps vk md)) S.
Proof.
  intros fx C Ar Ak mk vk md r s pp p w h cd data cvd retpc S kx bx CK HW Hs16 Hlo Hhi R2 Hp1 Hp2 Hp8 R1 Hret R4 R10 Rpp TP Hw Hh
    LAr SUB ROOM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof (tpx_range C Ak mk _ p w h cd data cvd CK HW TP Hw Hh) as (Gp1 & Gp2 & Gd1 & Gd2 & Gn).
  pose proof TP as (PX & Lp & L0p & Ld & L0d & NE & TC).
  apply (@pixDestroy_keep_W fx AL CL ASR PINS P16 C Ak mk (with_vmmaps vk md) r (s - 112)%Z pp p cd (4 * c_nalloc cvd)%Z
           (4 * (wpl_of w 1 * h))%Z (O23LeptPixCopyT.hdv w h 1 cd data) cvd retpc S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) Hp1 ltac:(lia)
           R1 Hret R4 Hp8 R10 Rpp PX eq_refl eq_refl eq_refl Lp L0p Ld L0d Gn ltac:(cbn; lia)).
  - destruct TC as [Z0|(Nz & CA & CO & L1 & L2 & L3 & L4 & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
    destruct CO as (_ & _ & Hn & _).
    cbn [p_data O23LeptPixCopyT.hdv].
    refine (conj CA (conj L1 (conj L2 (conj L3 (conj L4 (conj N1 (conj N2 (conj N4 (conj _ (conj _ _)))))))))); lia.
  - intros A' m' vm' r' HW' CS' PP' PM' R0 BELOW RT. rewrite with_vmmaps_twice in HW'.
    rewrite with_vmmaps_vmmaps in RT. cbn [p_data O23LeptPixCopyT.hdv] in PP'.
    destruct PP' as (Dp & Dd & Dc & Keep).
    assert (LD : forall q, O23LeptCloseA.tblk p data cd cvd q -> live A' q = None).
    { intros q [->|[->|(Nz & [->| ->])]].
      - exact Dp.
      - apply Dd. lia.
      - exact (proj1 (Dc Nz)).
      - exact (proj2 (Dc Nz)). }
    assert (LE : forall q, ~ O23LeptCloseA.tblk p data cd cvd q -> live A' q = live Ak q).
    { intros q Nq. apply Keep.
      - intros E. apply Nq. left. exact E.
      - intros _ E. apply Nq. right. left. exact E.
      - intros Nz. split; intros E; apply Nq; right; right; split; [exact Nz | left; exact E | exact Nz | right; exact E]. }
    destruct PM' as [FR LV].
    assert (SUB' : sub_live Ar A').
    { apply (O23LeptCloseA.sub_live_free_X Ar Ak A' (O23LeptCloseA.tblk p data cd cvd) SUB LE LAr).
      intros q. apply O23LeptCloseA.tblk_dec. }
    apply (HK A' m' vm' r' HW' CS' LD LE).
    + exact (O23LeptCloseA.PWK_free Ak A' (O23LeptCloseA.tblk p data cd cvd) mk m' LV LE).
    + intros a Ha Hn8. destruct (Z_lt_dec (u a) pp) as [Hlt | Hge].
      * apply BELOW. lia.
      * apply (FRM_pw C (pp + 8)%Z mk m' CK FR ltac:(lia)). lia.
    + exact R0.
    + exact SUB'.
    + split; [apply (FRM_mono C (pp + 8)%Z s mk m' FR); lia | exact (LIVK_sub Ar A' mk m' SUB' LV)].
    + pose proof (aroom_nonneg Ak vk kx bx ROOM) as [Nk Nb].
      pose proof (RT kx bx ROOM ltac:(lia) ltac:(lia)) as RR. rewrite !Z.sub_0_r in RR. exact RR.
Qed.

(* [comment removed for export] *)
Lemma dil_hop : forall (fx : FPState) C Ak mk vk md r (s pixs w h cd data : Z) (cvd : cmapv) (sel : Z) (sv : selv) (c : Z -> Z -> Z) (retpc : word) (S : TSet) (kx bx : Z),
  Cok C -> W C Ak mk (with_vmmaps vk md) -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr r 2 = Z_to_bv 64 (s - 112) -> getr r 1 = retpc -> ret_ok retpc -> getr r 4 = Z_to_bv 64 0x1381d0 ->
  getr r 10 = Z_to_bv 64 0 -> getr r 11 = Z_to_bv 64 pixs -> getr r 12 = Z_to_bv 64 sel ->
  sel_at (alloc_top (c_vm C)) Ak mk sel sv -> sel_cont mk sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall q, O23LeptCloseA.sblk sel sv q -> q <> Z_to_bv 64 pixs) ->
  O23LeptCloseA.tpx C Ak mk pixs w h cd data cvd -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  aroom Ak vk kx bx -> (RK_pixcopy <= kx)%Z -> (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd <= bx)%Z ->
  (forall A' m' vm' r' (pixd cd' data' : Z) (cvd' : cmapv), W C A' m' (with_vmmaps vm' md) -> cs_kept r r' -> getr r' 10 = Z_to_bv 64 pixd ->
     O23LeptCloseA.tpx C A' m' pixd w h cd' data' cvd' -> (forall q, O23LeptCloseA.tblk pixd data' cd' cvd' q -> live Ak q = None) ->
     (forall q, ~ O23LeptCloseA.tblk pixd data' cd' cvd' q -> live A' q = live Ak q) ->
     (cd = 0%Z -> cd' = 0%Z) -> (cd' <> 0%Z -> c_d cvd' = c_d cvd /\ c_nalloc cvd' = c_nalloc cvd /\ c_n cvd' = c_n cvd) ->
     sub_live Ak A' -> POSTM C Ak (s - 112) mk m' ->
     aroom A' vm' (kx - RK_pixcopy) (bx - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd)) ->
     realizes SEGS (mkCfg (mkst r' retpc m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0xa1968 : word) mk al_rom) (with_vmmaps vk md)) S.
Proof.
  intros fx C Ak mk vk md r s pixs w h cd data cvd sel sv c retpc S kx bx CK HW Hs16 Hlo Hhi R2 R1 Hret R4 R10 R11 R12
    SA SC Hcx Hcy SB TP HD Hw Hh ROOM Hk Hb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof TP as (PX & Lp & L0p & Ld & L0d & NE & TC).
  set (cv0 := if (cd =? 0)%Z then O23LeptCloseA.cvbad else cvd).
  assert (CV0 : (cd = 0 -> ~ O23LeptCmapValid.cmap_ok cv0)%Z /\ (cd <> 0 -> cv0 = cvd)%Z).
  { unfold cv0. destruct (Z.eqb_spec cd 0) as [E|E]; split; intros X;
      [exact O23LeptCloseA.cvbad_not_ok | contradiction | contradiction | reflexivity]. }
  assert (CMX : cd = 0%Z \/ (CMAPat mk cd cv0 /\ O23LeptCmapValid.cmap_ok cv0 /\ live Ak (Z_to_bv 64 cd) = Some 24%Z /\
                                live Ak (Z_to_bv 64 (c_arr cv0)) = Some (4 * c_nalloc cv0)%Z)).
  { destruct TC as [Z0|(Nz & CA & CO & L1 & L2 & _)]; [left; exact Z0 | right].
    rewrite (proj2 CV0 Nz). exact (conj CA (conj CO (conj L1 L2))). }
  assert (SNE : forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs).
  { intros p0 Hp0. apply SB. exists p0. split; [exact Hp0 | reflexivity]. }
  rewrite <- (with_vmmaps_vmmaps vk md) in ROOM.
  apply (@pixDilate_new_sure_W fx AL CL ASR PINS P16 C Ak mk (with_vmmaps vk md) r (s - 112)%Z pixs sel w h cd data sv c cv0 retpc S
           CK HW R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold DIL_STACK; lia) ltac:(lia)
           R1 Hret R4 R10 R11 R12 PX HD Hw Hh Lp L0p Ld CMX SA SC Hcx Hcy SNE kx bx ROOM Hk Hb).
  intros A' m' vm' r' HW' CS' (pixd & cd' & data' & R10' & PN & PM) ROOM'.
  rewrite with_vmmaps_twice in HW'.
  destruct (O23LeptCloseA.tpx_of_pixt C Ak A' m' pixd w h cd' data' cv0 PN) as (cvd' & TP' & LD & LE & CDs).
  apply (HK A' m' vm' r' pixd cd' data' cvd' HW' CS' R10' TP' LD LE).
  - intros Z0. destruct (Z.eq_dec cd' 0) as [E|E]; [exact E|]. exfalso. exact (proj1 CV0 Z0 (proj1 (CDs E))).
  - intros E. destruct (CDs E) as (OK & D1 & D2 & D3).
    assert (Nz : cd <> 0%Z) by (intros Z0; exact (proj1 CV0 Z0 OK)).
    rewrite (proj2 CV0 Nz) in D1, D2, D3. auto.
  - apply (O23LeptCloseA.sub_live_free_X Ak Ak A' (O23LeptCloseA.tblk pixd data' cd' cvd') (sub_live_refl Ak) LE LD).
    intros q. apply O23LeptCloseA.tblk_dec.
  - exact PM.
  - exact ROOM'.
Qed.

(* [comment removed for export] *)
Lemma rb_hop : forall (fx : FPState) C Ak mk vk md r (s pixs w h cd data : Z) (cvd : cmapv) (retpc : word) (S : TSet) (kx bx : Z),
  Cok C -> W C Ak mk (with_vmmaps vk md) -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr r 2 = Z_to_bv 64 (s - 112) -> getr r 1 = retpc -> ret_ok retpc -> getr r 4 = Z_to_bv 64 0x1381d0 ->
  getr r 10 = Z_to_bv 64 pixs -> getr r 11 = Z_to_bv 64 32 ->
  O23LeptCloseA.tpx C Ak mk pixs (w + 64) (h + 64) cd data cvd -> O23LeptPixHdr.hdr_ok (w + 64) (h + 64) 1 -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  aroom Ak vk kx bx -> (RK_pixcopy <= kx)%Z -> (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd <= bx)%Z ->
  (forall A' m' vm' r' (pixd cd' data' : Z) (cvd' : cmapv), W C A' m' (with_vmmaps vm' md) -> cs_kept r r' -> getr r' 10 = Z_to_bv 64 pixd ->
     O23LeptCloseA.tpx C A' m' pixd w h cd' data' cvd' -> (forall q, O23LeptCloseA.tblk pixd data' cd' cvd' q -> live Ak q = None) ->
     (forall q, ~ O23LeptCloseA.tblk pixd data' cd' cvd' q -> live A' q = live Ak q) ->
     (cd = 0%Z -> cd' = 0%Z) -> (cd' <> 0%Z -> c_d cvd' = c_d cvd /\ c_nalloc cvd' = c_nalloc cvd /\ c_n cvd' = c_n cvd) ->
     sub_live Ak A' -> POSTM C Ak (s - 112) mk m' ->
     aroom A' vm' (kx - RK_pixcopy) (bx - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cd)) ->
     realizes SEGS (mkCfg (mkst r' retpc m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0x711d4 : word) mk al_rom) (with_vmmaps vk md)) S.
Proof.
  intros fx C Ak mk vk md r s pixs w h cd data cvd retpc S kx bx CK HW Hs16 Hlo Hhi R2 R1 Hret R4 R10 R11
    TP HD2 HD Hw Hh ROOM Hk Hb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof TP as (PX & Lp & L0p & Ld & L0d & NE & TC).
  set (cv0 := if (cd =? 0)%Z then O23LeptCloseA.cvbad else cvd).
  assert (CV0 : (cd = 0 -> ~ O23LeptCmapValid.cmap_ok cv0)%Z /\ (cd <> 0 -> cv0 = cvd)%Z).
  { unfold cv0. destruct (Z.eqb_spec cd 0) as [E|E]; split; intros X;
      [exact O23LeptCloseA.cvbad_not_ok | contradiction | contradiction | reflexivity]. }
  assert (CMX : cd = 0%Z \/ (CMAPat mk cd cv0 /\ O23LeptCmapValid.cmap_ok cv0 /\ live Ak (Z_to_bv 64 cd) = Some 24%Z /\
                                live Ak (Z_to_bv 64 (c_arr cv0)) = Some (4 * c_nalloc cv0)%Z)).
  { destruct TC as [Z0|(Nz & CA & CO & L1 & L2 & _)]; [left; exact Z0 | right].
    rewrite (proj2 CV0 Nz). exact (conj CA (conj CO (conj L1 L2))). }
  rewrite <- (with_vmmaps_vmmaps vk md) in ROOM.
  apply (@V23LeptRbordW.pixRemoveBorder32_W fx AL CL ASR PINS P16 C Ak mk (with_vmmaps vk md) r (s - 112)%Z pixs w h cd data cv0 retpc S
           CK HW R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold RBG32_STACK, LSF; lia) ltac:(lia)
           R1 Hret R4 R10 R11 PX HD2 HD Hw Hh Lp Ld CMX kx bx ROOM Hk Hb).
  intros A' m' vm' r' HW' CS' (pixd & cd' & data' & R10' & PN & PM) ROOM'.
  rewrite with_vmmaps_twice in HW'.
  destruct (O23LeptCloseA.tpx_of_pixt C Ak A' m' pixd w h cd' data' cv0 PN) as (cvd' & TP' & LD & LE & CDs).
  apply (HK A' m' vm' r' pixd cd' data' cvd' HW' CS' R10' TP' LD LE).
  - intros Z0. destruct (Z.eq_dec cd' 0) as [E|E]; [exact E|]. exfalso. exact (proj1 CV0 Z0 (proj1 (CDs E))).
  - intros E. destruct (CDs E) as (OK & D1 & D2 & D3).
    assert (Nz : cd <> 0%Z) by (intros Z0; exact (proj1 CV0 Z0 OK)).
    rewrite (proj2 CV0 Nz) in D1, D2, D3. auto.
  - apply (O23LeptCloseA.sub_live_free_X Ak Ak A' (O23LeptCloseA.tblk pixd data' cd' cvd') (sub_live_refl Ak) LE LD).
    intros q. apply O23LeptCloseA.tblk_dec.
  - exact PM.
  - exact ROOM'.
Qed.

(* [comment removed for export] *)
Lemma ero_hop : forall (fx : FPState) C Ar Ak mk md0 r (s pixd pixs w h cdd datad : Z) (cvdd : cmapv) (cds datas : Z) (cvds : cmapv)
    (sel : Z) (sv : selv) (c : Z -> Z -> Z) (retpc : word) (S : TSet),
  Cok C -> MBC C -> W C Ak mk md0 -> sub_live Ar Ak -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr r 2 = Z_to_bv 64 (s - 112) -> getr r 1 = retpc -> ret_ok retpc ->
  getr r 10 = Z_to_bv 64 pixd -> getr r 11 = Z_to_bv 64 pixs -> getr r 12 = Z_to_bv 64 sel ->
  O23LeptCloseA.tpx C Ak mk pixd w h cdd datad cvdd -> O23LeptCloseA.tpx C Ak mk pixs w h cds datas cvds -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  (forall q, O23LeptCloseA.tblk pixs datas cds cvds q -> ~ O23LeptCloseA.tblk pixd datad cdd cvdd q) ->
  live Ar (Z_to_bv 64 datad) = None ->
  sel_at (alloc_top (c_vm C)) Ak mk sel sv -> sel_cont mk sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall q, O23LeptCloseA.sblk sel sv q -> q <> Z_to_bv 64 pixs /\ q <> Z_to_bv 64 datad) ->
  (forall m' r', W C Ak m' md0 -> cs_kept r r' -> getr r' 10 = Z_to_bv 64 pixd ->
     O23LeptCloseA.PWK Ak (fun q => q <> Z_to_bv 64 datad) mk m' ->
     (forall a : word, (s - 112 <= u a)%Z -> m' a = mk a) -> POSTM C Ar s mk m' ->
     realizes SEGS (mkCfg (mkst r' retpc m' al_rom) md0) S) ->
  realizes SEGS (mkCfg (mkst r (0xa1d7c : word) mk al_rom) md0) S.
Proof.
  intros fx C Ar Ak mk md0 r s pixd pixs w h cdd datad cvdd cds datas cvds sel sv c retpc S CK MB HW SUB Hs16 Hlo Hhi
    R2 R1 Hret R10 R11 R12 TPd TPs HD Hw Hh DJ LAr SA SC Hcx Hcy SB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof TPs as (PXs & Lps & L0ps & Lds & L0ds & NEs & TCs).
  pose proof TPd as (PXd & Lpd & L0pd & Ldd & L0dd & NEd & TCd).
  pose proof (tpx_self_ne C Ak mk md0 pixd w h cdd datad cvdd CK HW TPd Hw Hh) as [Npd _].
  assert (Hps : pixd <> pixs).
  { intros E. subst pixd. exact (DJ (Z_to_bv 64 pixs) (or_introl eq_refl) (or_introl eq_refl)). }
  assert (Nsd : Z_to_bv 64 datas <> Z_to_bv 64 datad).
  { intros E. exact (DJ (Z_to_bv 64 datas) (or_intror (or_introl eq_refl)) (or_intror (or_introl E))). }
  assert (Nsp : Z_to_bv 64 pixs <> Z_to_bv 64 datad).
  { intros E. exact (DJ (Z_to_bv 64 pixs) (or_introl eq_refl) (or_intror (or_introl E))). }
  assert (CMd : (cdd <> 0 -> exists cv, CMAPat mk cdd cv /\ live Ak (Z_to_bv 64 cdd) = Some 24)%Z).
  { intros Nz. destruct TCd as [Z0|(_ & CA & _ & L1 & _)]; [contradiction|]. exists cvdd. exact (conj CA L1). }
  apply (@V23LeptEroGW.pixErode_given_W fx AL CL ASR PINS P16 C Ar Ak mk md0 r (s - 112)%Z pixd pixs sel w h cds datas
           (O23LeptPixCopyT.hdv w h 1 cdd datad) sv c retpc S
           CK MB HW SUB R2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold V23LeptEroW.ERO_STACK; lia) ltac:(lia)
           R1 Hret R10 R11 R12 PXs HD Hw Hh Lps L0ps Lds PXd eq_refl eq_refl eq_refl eq_refl Lpd Hps Ldd LAr L0dd
           Nsd Npd Nsp CMd SA SC Hcx Hcy).
  - intros p0 Hp0. apply (proj1 (SB (Z_to_bv 64 p0) (ex_intro _ p0 (conj Hp0 eq_refl)))).
  - intros p0 Hp0. apply (proj2 (SB (Z_to_bv 64 p0) (ex_intro _ p0 (conj Hp0 eq_refl)))).
  - intros m' r' HW' CS' FR PM PX' KEEP R10'.
    apply (HK m' r' HW' CS' R10').
    + exact KEEP.
    + intros a Ha. apply (FRM_pw C (s - 112)%Z mk m' CK FR ltac:(lia)). lia.
    + destruct PM as [F L]. split; [apply (FRM_mono C (s - 112)%Z s mk m' F); lia | exact L].
Qed.

Definition pcg2_contract (fx : FPState) : Prop :=
  forall C A m md regs (s pixd pixs w h cms datas cmd datad : Z) (cvs cvd : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs -> pixd <> pixs ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cms datas) -> PIXat m pixd (O23LeptPixCopyT.hdv w h 1 cmd datad) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 1 * h))%Z ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  O23LeptCloseIface.pcg_cm C A m cms cvs -> O23LeptCloseIface.pcg_cm C A m cmd cvd ->
  (cmd <> 0%Z -> live (c_A0 C) (Z_to_bv 64 cmd) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cvd)) = None) ->
  datas <> datad -> datad <> pixd ->
  (cmd <> 0%Z -> c_arr cvd <> pixd /\ c_arr cvd <> pixs /\ c_arr cvd <> datad /\ c_arr cvd <> datas /\ cmd <> datad /\ cmd <> datas /\
                 (cms <> 0%Z -> cmd <> cms /\ c_arr cvd <> c_arr cvs)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB_cmapT cms <= bR)%Z ->
  (forall A' m' vm' regs' (cmd' : Z) (cvd' : cmapv),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 pixd ->
     FRM C s m m' ->
     (forall (q : word) k i, live A q = Some k -> q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad ->
                             q <> Z_to_bv 64 cmd -> q <> Z_to_bv 64 (c_arr cvd) -> (0 <= i < k)%Z -> m' (at_ q i) = m (at_ q i)) ->
     (forall (q : word) k, live A q = Some k -> (cmd <> 0%Z -> q <> Z_to_bv 64 cmd /\ q <> Z_to_bv 64 (c_arr cvd)) -> live A' q = Some k) ->
     PIXat m' pixd (O23LeptPixCopyT.hdv w h 1 cmd' datad) ->
     O23LeptCloseP.pcgl C A A' m' cms cvs cmd (c_arr cvd) cmd' cvd' ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB_cmapT cms) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6eb5c : word) m al_rom) md) S.

Lemma zbv_ne : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb N E. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. contradiction. Qed.

Lemma copy_hop : forall (fx : FPState), pcg2_contract fx ->
  forall C Ar A Ak mk vk md r (s pix1 w h cm datas : Z) (cv : cmapv) (pixs cds datas2 : Z) (cvs : cmapv) (retpc : word) (S : TSet) (kx bx : Z) (T : word -> Prop),
  Cok C -> W C Ak mk (with_vmmaps vk md) -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr r 2 = Z_to_bv 64 (s - 112) -> getr r 1 = retpc -> ret_ok retpc -> getr r 4 = Z_to_bv 64 0x1381d0 ->
  getr r 10 = Z_to_bv 64 pix1 -> getr r 11 = Z_to_bv 64 pixs ->
  O23LeptCloseSpec.pix1_at C Ar Ak mk pix1 w h cm datas cv -> pix1 <> datas -> O23LeptCloseA.tpx C Ak mk pixs w h cds datas2 cvs -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  (forall q, O23LeptCloseA.tblk pixs datas2 cds cvs q -> ~ O23LeptCloseA.tblk pix1 datas cm cv q) ->
  sub_live Ar Ak ->
  (cm = 0%Z -> cds = 0%Z) -> (cds <> 0%Z -> c_d cvs = c_d cv /\ c_nalloc cvs = c_nalloc cv /\ c_n cvs = c_n cv) ->
  (forall q, ~ T q -> live Ak q = live A q) -> (forall q, T q -> live A q = None) -> (forall q, T q -> exists n, live Ak q = Some n) ->
  (forall q, T q -> ~ O23LeptCloseA.tblk pix1 datas cm cv q) ->
  (forall q, O23LeptCloseA.tblk pix1 datas cm cv q -> exists n, live A q = Some n) ->
  aroom Ak vk kx bx -> (RK_cmapcopy <= kx)%Z -> (RB_cmapT cds <= bx)%Z ->
  (forall A' m' vm' r' (cm' : Z) (cv' : cmapv), W C A' m' (with_vmmaps vm' md) -> cs_kept r r' -> getr r' 10 = Z_to_bv 64 pix1 ->
     O23LeptCloseSpec.pix1_at C Ar A' m' pix1 w h cm' datas cv' ->
     O23LeptCloseA.PWK Ak (fun q => ~ O23LeptCloseA.tblk pix1 datas cm cv q) mk m' ->
     (forall q k, live Ak q = Some k -> ~ O23LeptCloseA.tblk pix1 datas cm cv q -> live A' q = Some k) ->
     (forall a : word, (s - 112 <= u a)%Z -> m' a = mk a) ->
     O23LeptCloseA.cslm T A A' cm cv cm' cv' ->
     (forall q, T q -> ~ O23LeptCloseA.tblk pix1 datas cm' cv' q) ->
     sub_live Ar A' -> POSTM C Ar s mk m' -> aroom A' vm' (kx - RK_cmapcopy) (bx - RB_cmapT cds) ->
     realizes SEGS (mkCfg (mkst r' retpc m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0x6eb5c : word) mk al_rom) (with_vmmaps vk md)) S.
Proof.
  intros fx PCG C Ar A Ak mk vk md r s pix1 w h cm datas cv pixs cds datas2 cvs retpc S kx bx T
    CK HW Hs16 Hlo Hhi R2 R1 Hret R4 R10 R11 P1 Npd TPs HD Hw Hh DJ SUB Hcm0 Hcds TK TA TL TN P1L ROOM Hk Hb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CSC_STACK in Hlo.
  pose proof P1 as (PX1 & L1p & LR1p & L01p & L1d & LR1d & L01d & CC).
  pose proof TPs as (PXs & Lsp & L0sp & Lsd & L0sd & NEs & TCs).
  pose proof PX1 as (Hp10 & Hp164 & WF1 & _). pose proof (wf_data _ WF1) as Hd1. cbn [p_data O23LeptPixCopyT.hdv] in Hd1.
  assert (Nps : pix1 <> pixs).
  { intros E. subst pix1. exact (DJ (Z_to_bv 64 pixs) (or_introl eq_refl) (or_introl eq_refl)). }
  assert (N22 : datas2 <> datas).
  { intros E. subst datas2. exact (DJ (Z_to_bv 64 datas) (or_intror (or_introl eq_refl)) (or_intror (or_introl eq_refl))). }
  set (cv0 := if (cm =? 0)%Z then O23LeptCloseA.cvbad else cv).
  assert (CV0 : (cm = 0 -> c_arr cv0 = 0)%Z /\ (cm <> 0 -> cv0 = cv)%Z).
  { unfold cv0. destruct (Z.eqb_spec cm 0) as [E|E]; split; intros X; first [reflexivity | contradiction]. }
  assert (PGs : O23LeptCloseIface.pcg_cm C Ak mk cds cvs).
  { destruct TCs as [Z0|(Nz & CA & CO & La & Lb & _)]; [left; exact Z0 | right; exact (conj Nz (conj CA (conj CO (conj La Lb))))]. }
  assert (PGd : O23LeptCloseIface.pcg_cm C Ak mk cm cv0).
  { destruct CC as [Z0|(Nz & CA & CO & La & Lb & _)]; [left; exact Z0 | right].
    rewrite (proj2 CV0 Nz). exact (conj Nz (conj CA (conj CO (conj La Lb)))). }
  assert (A0X : cm <> 0%Z -> live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv0)) = None).
  { intros Nz. rewrite (proj2 CV0 Nz).
    destruct CC as [Z0|(_ & _ & _ & _ & _ & _ & _ & L0a & L0b & _)]; [contradiction | exact (conj L0a L0b)]. }
  assert (NEQ : cm <> 0%Z -> c_arr cv0 <> pix1 /\ c_arr cv0 <> pixs /\ c_arr cv0 <> datas /\ c_arr cv0 <> datas2 /\
                 cm <> datas /\ cm <> datas2 /\ (cds <> 0%Z -> cm <> cds /\ c_arr cv0 <> c_arr cvs)).
  { intros Nz. rewrite (proj2 CV0 Nz).
    destruct CC as [Z0|(_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5)]; [contradiction|].
    assert (TA1 : O23LeptCloseA.tblk pix1 datas cm cv (Z_to_bv 64 (c_arr cv))) by (right; right; split; [exact Nz | right; reflexivity]).
    assert (TC1 : O23LeptCloseA.tblk pix1 datas cm cv (Z_to_bv 64 cm)) by (right; right; split; [exact Nz | left; reflexivity]).
    split; [lia|]. split.
    { intros E. exact (DJ _ (or_introl (f_equal (Z_to_bv 64) E)) TA1). }
    split; [lia|]. split.
    { intros E. exact (DJ _ (or_intror (or_introl (f_equal (Z_to_bv 64) E))) TA1). }
    split; [lia|]. split.
    { intros E. exact (DJ _ (or_intror (or_introl (f_equal (Z_to_bv 64) E))) TC1). }
    intros Ns. split.
    - intros E. exact (DJ _ (or_intror (or_intror (conj Ns (or_introl (f_equal (Z_to_bv 64) E))))) TC1).
    - intros E. exact (DJ _ (or_intror (or_intror (conj Ns (or_intror (f_equal (Z_to_bv 64) E))))) TA1). }
  rewrite <- (with_vmmaps_vmmaps vk md) in ROOM.
  refine (PCG C Ak mk (with_vmmaps vk md) r (s - 112)%Z pix1 pixs w h cds datas2 cm datas cvs cv0 retpc S
           CK HW R2 _ _ _ R1 Hret R4 R10 R11 Nps PXs PX1 HD Hw Hh Lsp Lsd L1p L1d L01p L01d PGs PGd A0X _ _ NEQ
           kx bx ROOM Hk Hb _).
  { rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity. }
  { clear - Hlo. unfold PCG_STACK, LSF. lia. }
  { clear - Hhi. lia. }
  { exact N22. }
  { intros E. apply Npd. symmetry. exact E. }
  clear NEQ.
  intros A' m' vm' r' cm' cv' HW' CS' R10' FR KM KL PX' PG ROOM'.
  rewrite with_vmmaps_twice in HW'.
  assert (NZq : forall q k, live Ak q = Some k -> (0 < k)%Z -> q <> Z_to_bv 64 0).
  { intros q k Lq Hk0 E. destruct (blk_range C Ak mk _ q k CK HW Lq Hk0) as [G _]. rewrite E in G.
    assert (U0 : u (Z_to_bv 64 0) = 0%Z) by reflexivity. rewrite U0 in G. clear - G. lia. }
  assert (GNT : forall q, ~ O23LeptCloseA.tblk pix1 datas cm cv q -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv0))).
  { intros q Nt Nz. rewrite (proj2 CV0 Nz).
    split; intros E; apply Nt; right; right; split; [exact Nz | left; exact E | exact Nz | right; exact E]. }
  assert (GQ : forall q k, live Ak q = Some k -> (0 < k)%Z -> ~ O23LeptCloseA.tblk pix1 datas cm cv q ->
                 q <> Z_to_bv 64 pix1 /\ q <> Z_to_bv 64 datas /\ q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv0)).
  { intros q k Lq Hk0 Nt. split; [intros E; apply Nt; left; exact E|]. split; [intros E; apply Nt; right; left; exact E|].
    destruct (Z.eq_dec cm 0) as [Z0|Nz].
    - rewrite (proj1 CV0 Z0), Z0. pose proof (NZq q k Lq Hk0) as N0. exact (conj N0 N0).
    - exact (GNT q Nt Nz). }
  assert (NTr : forall q k, live Ar q = Some k -> ~ O23LeptCloseA.tblk pix1 datas cm cv q).
  { intros q k Lr [E|[E|(Nz & [E|E])]]; subst q; [congruence | congruence | |].
    - destruct CC as [Z0|(_ & _ & _ & _ & _ & LRa & LRb & _)]; [contradiction | congruence].
    - destruct CC as [Z0|(_ & _ & _ & _ & _ & LRa & LRb & _)]; [contradiction | congruence]. }
  assert (KLx : forall q k, live Ak q = Some k -> ~ O23LeptCloseA.tblk pix1 datas cm cv q -> live A' q = Some k).
  { intros q k Lq Nt. exact (KL q k Lq (GNT q Nt)). }
  assert (KMx : forall q k (x : word), live Ak q = Some k -> ~ O23LeptCloseA.tblk pix1 datas cm cv q ->
                  (u q <= u x < u q + k)%Z -> m' x = mk x).
  { intros q k x Lq Nt Hx. assert (Hk0 : (0 < k)%Z) by (clear - Hx; lia).
    destruct (GQ q k Lq Hk0 Nt) as (G1 & G2 & G3 & G4).
    pose proof (bv_unsigned_in_range _ x) as Rx. change (bv_modulus 64) with (2 ^ 64)%Z in Rx.
    assert (EX : at_ q (u x - u q) = x).
    { apply bv_eq. unfold at_. rewrite u_Z2bv by (clear - Rx; lia). clear - Rx; lia. }
    rewrite <- EX. exact (KM q k (u x - u q)%Z Lq G1 G2 G3 G4 ltac:(clear - Hx; lia)). }
  assert (GPD : cm <> 0%Z -> Z_to_bv 64 pix1 <> Z_to_bv 64 cm /\ Z_to_bv 64 pix1 <> Z_to_bv 64 (c_arr cv0) /\
                             Z_to_bv 64 datas <> Z_to_bv 64 cm /\ Z_to_bv 64 datas <> Z_to_bv 64 (c_arr cv0)).
  { intros Nz. rewrite (proj2 CV0 Nz).
    destruct CC as [Z0|(_ & CA & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5)]; [contradiction|].
    destruct CA as (Hc0 & Hc24 & CWF & _). pose proof (cf_arr _ CWF) as Ha.
    split; [|split; [|split]]; apply zbv_ne; clear - Hp10 Hp164 Hd1 Hc0 Hc24 Ha N1 N2 N3 N4 N5; lia. }
  assert (LP1 : live A' (Z_to_bv 64 pix1) = Some 64%Z).
  { apply (KL _ _ L1p). intros Nz. exact (conj (proj1 (GPD Nz)) (proj1 (proj2 (GPD Nz)))). }
  assert (LD1 : live A' (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z).
  { apply (KL _ _ L1d). intros Nz. exact (conj (proj1 (proj2 (proj2 (GPD Nz)))) (proj2 (proj2 (proj2 (GPD Nz))))). }
  assert (FPD : forall cd' (cvd' : cmapv), (forall (q : word) k, live Ak q = Some k ->
                   (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv0)) -> q <> Z_to_bv 64 cd' /\ q <> Z_to_bv 64 (c_arr cvd')) ->
                   cd' <> pix1 /\ cd' <> datas /\ c_arr cvd' <> pix1 /\ c_arr cvd' <> datas).
  { intros cd' cvd' FRESH.
    destruct (FRESH _ _ L1p (fun Nz => conj (proj1 (GPD Nz)) (proj1 (proj2 (GPD Nz))))) as [F1 F2].
    destruct (FRESH _ _ L1d (fun Nz => conj (proj1 (proj2 (proj2 (GPD Nz)))) (proj2 (proj2 (proj2 (GPD Nz)))))) as [F3 F4].
    split; [intros E; apply F1; rewrite E; reflexivity|]. split; [intros E; apply F3; rewrite E; reflexivity|].
    split; [intros E; apply F2; rewrite E; reflexivity | intros E; apply F4; rewrite E; reflexivity]. }
  assert (CC' : O23LeptCloseSpec.csc_cm C Ar A' m' pix1 datas cm' cv').
  { destruct PG as [(Zs & Ecm' & _)|(Ns & Nz' & CA' & CO' & Hcd & Hcn & Hcnn & La' & Lb' & L0a' & L0b' & FRESH & KEEP' & GONE)];
      [left; exact Ecm' | right].
    destruct (FPD cm' cv' FRESH) as (F1 & F2 & F3 & F4).
    assert (LRx : forall z, live Ar (Z_to_bv 64 z) = None \/ (Z_to_bv 64 z <> Z_to_bv 64 cm' /\ Z_to_bv 64 z <> Z_to_bv 64 (c_arr cv'))).
    { intros z. destruct (live Ar (Z_to_bv 64 z)) as [k|] eqn:Ez; [right | left; reflexivity].
      exact (FRESH _ k (SUB _ k Ez) (GNT _ (NTr _ k Ez))). }
    assert (NCA : cm' <> c_arr cv').
    { intros E. rewrite E in La'. rewrite La' in Lb'. injection Lb' as Lb''.
      destruct CO' as ([D|[D|[D|D]]] & Hna & _); rewrite D in Hna; cbn in Hna; clear - Lb'' Hna; lia. }
    split; [exact Nz'|]. split; [exact CA'|]. split; [exact CO'|]. split; [exact La'|]. split; [exact Lb'|].
    split; [destruct (LRx cm') as [X|[X _]]; [exact X | exfalso; exact (X eq_refl)]|].
    split; [destruct (LRx (c_arr cv')) as [X|[_ X]]; [exact X | exfalso; exact (X eq_refl)]|].
    split; [exact L0a'|]. split; [exact L0b'|].
    split; [exact NCA|]. split; [exact F1|]. split; [exact F2|]. split; [exact F3 | exact F4]. }
  assert (CSL : O23LeptCloseA.cslm T A A' cm cv cm' cv').
  { destruct (Z.eq_dec cm 0) as [Z0|Nz].
    - pose proof (Hcm0 Z0) as Zs.
      destruct PG as [(_ & Ecm' & KEEP0 & _)|(Ns & _)]; [|contradiction].
      left. split; [exact Z0|]. split; [exact Ecm'|]. intros q Nq.
      rewrite (KEEP0 q (fun X => False_ind _ (X Z0))). exact (TK q Nq).
    - destruct (Z.eq_dec cds 0) as [Zs|Ns].
      + destruct PG as [(_ & Ecm' & KEEP0 & GONE0)|(Ns & _)]; [|contradiction].
        right; right. split; [exact Nz|]. split; [exact Ecm'|].
        rewrite (proj2 CV0 Nz) in KEEP0, GONE0. split.
        * intros q Nq Q1 Q2. rewrite (KEEP0 q (fun _ => conj Q1 Q2)). exact (TK q Nq).
        * exact (GONE0 Nz).
      + destruct PG as [(Zs & _)|(_ & Nz' & CA' & CO' & Hcd & Hcn & Hcnn & La' & Lb' & L0a' & L0b' & FRESH & KEEP' & GONE)];
          [contradiction|].
        rewrite (proj2 CV0 Nz) in KEEP', GONE.
        destruct (Hcds Ns) as (E1 & E2 & E3).
        right; left. split; [exact Nz|]. split; [exact Nz'|].
        split; [congruence|]. split; [congruence|]. split; [congruence|].
        split; [intros q Nq Q1 Q2 Q3 Q4; rewrite (KEEP' q (fun _ => conj Q1 Q2) Q3 Q4); exact (TK q Nq)|].
        split; [intros q Hq Q3 Q4; exact (GONE q Nz Hq Q3 Q4)|].
        intros q k Lq Q1 Q2.
        assert (Nq : ~ T q) by (intros Tq; rewrite (TA q Tq) in Lq; discriminate).
        apply (KL q k); [rewrite (TK q Nq); exact Lq|].
        intros _. rewrite (proj2 CV0 Nz). exact (conj Q1 Q2). }
  assert (TNEW : forall q, T q -> ~ O23LeptCloseA.tblk pix1 datas cm' cv' q).
  { intros q Tq Tb. destruct (TL q Tq) as (n & Ln). pose proof (TN q Tq) as Nt.
    destruct Tb as [E|[E|(Nz' & [E|E])]].
    - apply Nt. left. exact E.
    - apply Nt. right. left. exact E.
    - destruct PG as [(_ & Ecm' & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _)]; [contradiction|].
      exact (proj1 (FRESH q n Ln (GNT q Nt)) E).
    - destruct PG as [(_ & Ecm' & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _)]; [contradiction|].
      exact (proj2 (FRESH q n Ln (GNT q Nt)) E). }
  apply (HK A' m' vm' r' cm' cv' HW' CS' R10').
  - split; [exact PX'|]. split; [exact LP1|]. split; [exact LR1p|]. split; [exact L01p|].
    split; [exact LD1|]. split; [exact LR1d|]. split; [exact L01d | exact CC'].
  - intros q k x Lq Nt Hx. exact (KMx q k x Lq Nt Hx).
  - exact KLx.
  - intros a Ha. apply (FRM_pw C (s - 112)%Z mk m' CK FR ltac:(clear - Hlo; lia)). clear - Ha; lia.
  - exact CSL.
  - exact TNEW.
  - intros q k Lr. exact (KLx q k (SUB q k Lr) (NTr q k Lr)).
  - split; [apply (FRM_mono C (s - 112)%Z s mk m' FR); clear - Hhi; lia|].
    intros q k i Lr Hi. pose proof (SUB q k Lr) as Lk.
    destruct (GQ q k Lk ltac:(clear - Hi; lia) (NTr q k Lr)) as (G1 & G2 & G3 & G4).
    exact (KM q k i Lk G1 G2 G3 G4 Hi).
  - exact ROOM'.
Qed.

End CloseP.
