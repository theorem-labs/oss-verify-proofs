(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith LeptRecs LeptSel LeptSlots LeptExecT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT O23LeptPixHdr O23LeptSelFMT O23LeptDilW O23LeptPma1 O23LeptPma1G O23LeptSelGP O23LeptCloseA.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptMbc V23LeptDilW V23LeptEroW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptSelFMT V23LeptPixMisc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23LeptEroSegs V23LeptPma1 V23LeptPma1G V23LeptSelGP V23LeptSetAll V23LeptSetAllC V23LeptMorphN V23LeptCloseA.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section EroGW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma SFRe_w4_rd_out : forall m a v (b : Z) (n : nat), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> (0 <= b)%Z -> (b + Z.of_nat n < 2 ^ 64)%Z ->
  (b + Z.of_nat n <= a \/ a + 4 <= b)%Z -> rdn SEGS (O23LeptSelFMT.wr4 m a v) (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n.
Proof.
  intros m a v b n Ha Ha4 Hb Hbn D. unfold O23LeptSelFMT.wr4. apply rdn_wbytes_out_Z.
  rewrite length_N_to_le_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Lemma SFRe_w4_hit : forall m a v, (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> (0 <= v < 2 ^ 32)%Z ->
  rdn SEGS (O23LeptSelFMT.wr4 m a v) (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 v).
Proof.
  intros m a v Ha Ha4 Hv. unfold O23LeptSelFMT.wr4. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia).
  rewrite w2b_Z by lia. reflexivity.
Qed.
Lemma SFRe_w4_out : forall m a v (x : word), (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z -> (u x < a \/ a + 4 <= u x)%Z ->
  O23LeptSelFMT.wr4 m a v x = m x.
Proof.
  intros m a v x Ha Ha4 D. unfold O23LeptSelFMT.wr4. apply MemSplit.wbytes_outside;
    rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma SFRe_rd : forall m (s y0 y1 y2 y3 : Z), (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (0 <= y0 < 2 ^ 32)%Z -> (0 <= y1 < 2 ^ 32)%Z -> (0 <= y2 < 2 ^ 32)%Z -> (0 <= y3 < 2 ^ 32)%Z ->
  rdn SEGS (O23LeptSelFMT.SFR m (s - 124) (s - 128) (s - 132) (s - 136) y0 y1 y2 y3) (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 y0) /\
  rdn SEGS (O23LeptSelFMT.SFR m (s - 124) (s - 128) (s - 132) (s - 136) y0 y1 y2 y3) (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 y1) /\
  rdn SEGS (O23LeptSelFMT.SFR m (s - 124) (s - 128) (s - 132) (s - 136) y0 y1 y2 y3) (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 y2) /\
  rdn SEGS (O23LeptSelFMT.SFR m (s - 124) (s - 128) (s - 132) (s - 136) y0 y1 y2 y3) (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 y3).
Proof.
  intros m s y0 y1 y2 y3 Hs Hs64 H0 H1 H2 H3. unfold O23LeptSelFMT.SFR.
  split; [| split; [| split]].
  - rewrite (SFRe_w4_rd_out _ (s - 136)%Z), (SFRe_w4_rd_out _ (s - 132)%Z), (SFRe_w4_rd_out _ (s - 128)%Z)
      by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply SFRe_w4_hit; lia.
  - rewrite (SFRe_w4_rd_out _ (s - 136)%Z), (SFRe_w4_rd_out _ (s - 132)%Z) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply SFRe_w4_hit; lia.
  - rewrite (SFRe_w4_rd_out _ (s - 136)%Z) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply SFRe_w4_hit; lia.
  - apply SFRe_w4_hit; lia.
Qed.

Lemma SFRe_rd_out : forall m (s y0 y1 y2 y3 b : Z) (n : nat), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= b)%Z -> (b + Z.of_nat n < 2 ^ 64)%Z ->
  (b + Z.of_nat n <= s - 136 \/ s - 120 <= b)%Z ->
  rdn SEGS (O23LeptSelFMT.SFR m (s - 124) (s - 128) (s - 132) (s - 136) y0 y1 y2 y3) (Z_to_bv 64 b) n = rdn SEGS m (Z_to_bv 64 b) n.
Proof.
  intros m s y0 y1 y2 y3 b n Hs Hs64 Hb Hbn D. unfold O23LeptSelFMT.SFR.
  rewrite (SFRe_w4_rd_out _ (s - 136)%Z), (SFRe_w4_rd_out _ (s - 132)%Z), (SFRe_w4_rd_out _ (s - 128)%Z), (SFRe_w4_rd_out _ (s - 124)%Z)
    by lia.
  reflexivity.
Qed.

Lemma SFRe_out : forall m (s y0 y1 y2 y3 : Z) (x : word), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 136 <= u x < s - 120)%Z ->
  O23LeptSelFMT.SFR m (s - 124) (s - 128) (s - 132) (s - 136) y0 y1 y2 y3 x = m x.
Proof.
  intros m s y0 y1 y2 y3 x Hs Hs64 D. unfold O23LeptSelFMT.SFR.
  rewrite (SFRe_w4_out _ (s - 136)%Z), (SFRe_w4_out _ (s - 132)%Z), (SFRe_w4_out _ (s - 128)%Z), (SFRe_w4_out _ (s - 124)%Z)
    by lia.
  reflexivity.
Qed.

Lemma egr_heap : forall C A M0 md m' (s' d nd : Z) (q : word) (k : Z) (x : word),
  Cok C -> W C A M0 md -> (s' <= c_top C)%Z -> (0 <= d < 2 ^ 64)%Z -> live A (Z_to_bv 64 d) = Some nd ->
  O23LeptDilW.dil_frame C s' d nd M0 m' -> live A q = Some k -> q <> Z_to_bv 64 d -> (u q <= u x < u q + k)%Z ->
  m' x = M0 x.
Proof.
  intros C A M0 md m' s' d nd q k x CK HW Hs Hd Ld DF Lq NE Hx. apply DF.
  - intro SC. unfold scratch in SC.
    destruct (blk_byte C A M0 md q k x CK HW Lq Hx) as (_ & _ & _ & NW & _). apply NW. unfold win. lia.
  - intro HD.
    pose proof (ai_live_disjoint A M0 (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lq Ld NE) as DJ. rewrite u_Z2bv in DJ by lia.
    pose proof (ai_live_hull A M0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lq) as (Hk0 & _).
    pose proof (ai_live_hull A M0 (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (Hn0 & _).
    pose proof (round16_ge k Hk0). pose proof (round16_ge nd Hn0). lia.
Qed.

Lemma egr_stack : forall C A M0 md m' (s' d nd : Z) (x : word),
  Cok C -> W C A M0 md -> (c_top C - LSTK <= s')%Z -> (0 <= d < 2 ^ 64)%Z -> live A (Z_to_bv 64 d) = Some nd ->
  O23LeptDilW.dil_frame C s' d nd M0 m' -> (s' <= u x < c_top C)%Z -> m' x = M0 x.
Proof.
  intros C A M0 md m' s' d nd x CK HW Hs Hd Ld DF Hx. apply DF.
  - unfold scratch. lia.
  - intro HD.
    destruct (blk_byte C A M0 md (Z_to_bv 64 d) nd x CK HW Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & _ & _ & NW & _).
    apply NW. unfold win. lia.
Qed.

Lemma eg_reads_df : forall C A M0 md m' (s sel pixd pixs : Z) (sv : selv) (c : Z -> Z -> Z) (vd vs : pixv),
  Cok C -> W C A M0 md -> (c_top C - LSTK + ERO_STACK <= s)%Z -> (s <= c_top C)%Z ->
  sel_at (alloc_top (c_vm C)) A M0 sel sv ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  live A (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z ->
  Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd) -> Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd) ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 (p_data vd)) ->
  ero_reads M0 s sel pixd pixs sv c vd vs ->
  O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m' ->
  ero_reads m' s sel pixd pixs sv c vd vs.
Proof.
  intros C A M0 md m' s sel pixd pixs sv c vd vs CK HW Hlo Hhi SA Lpd Lps Ld NEd NEs NEsel ER DF.
  pose proof CK as [T1 T2 T3 T4 T5]. unfold ERO_STACK in Hlo.
  destruct ER as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & PXd & PXs).
  pose proof PXd as (Hpd0 & Hpd64 & WFd & _). pose proof (wf_data _ WFd) as Hd.
  pose proof PXs as (Hps0 & Hps64 & _ & _).
  pose proof SA as (Hsy & Hsx & Bsel & Lsel & _ & Bdat & Ldat & _ & ROWS & _).
  unfold bok in Bsel, Bdat.
  assert (HE : forall (q : word) (k : Z) (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> (u q <= u x < u q + k)%Z ->
                 m' x = M0 x).
  { intros q k x Lq NEq Hx. exact (egr_heap C A M0 md m' (s - 144) (p_data vd) _ q k x CK HW ltac:(lia) Hd Ld DF Lq NEq Hx). }
  assert (HS : forall x : word, (s - 144 <= u x < c_top C)%Z -> m' x = M0 x).
  { intros x Hx. exact (egr_stack C A M0 md m' (s - 144) (p_data vd) _ x CK HW ltac:(lia) Hd Ld DF Hx). }
  assert (HSR : forall (b : Z) (n : nat) (v : list byte), (s - 144 <= b)%Z -> (b + Z.of_nat n <= c_top C)%Z ->
                  rdn SEGS M0 (Z_to_bv 64 b) n = Some v -> rdn SEGS m' (Z_to_bv 64 b) n = Some v).
  { intros b n v Hb Hbn Hr. rewrite (rdn_ext SEGS n m' M0); [exact Hr | rewrite u_Z2bv by lia; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply HS. lia. }
  assert (HHR : forall (q b : Z) (k : Z) (n : nat) (v : list byte), live A (Z_to_bv 64 q) = Some k ->
                  Z_to_bv 64 q <> Z_to_bv 64 (p_data vd) -> (0 <= q)%Z -> (q + k < 2 ^ 64)%Z -> (q <= b)%Z -> (b + Z.of_nat n <= q + k)%Z ->
                  rdn SEGS M0 (Z_to_bv 64 b) n = Some v -> rdn SEGS m' (Z_to_bv 64 b) n = Some v).
  { intros q b k n v Lq NEq Hq0 Hqk Hb Hbn Hr. rewrite (rdn_ext SEGS n m' M0); [exact Hr | rewrite u_Z2bv by lia; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply (HE (Z_to_bv 64 q) k); [exact Lq | exact NEq | rewrite u_Z2bv by lia; lia]. }
  unfold ero_reads. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]].
  - apply (HHR sel _ 32%Z); [exact Lsel | apply NEsel; left; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R1].
  - intros i Hi. apply (HHR (v_data sv) _ (8 * v_sy sv)%Z);
      [exact Ldat | apply NEsel; right; left; reflexivity | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact (R2 i Hi)].
  - intros i j Hi Hj. destruct (ROWS i Hi) as (Brow & Lrow & _). unfold bok in Brow.
    apply (HHR (v_rows sv i) _ (4 * v_sx sv)%Z);
      [exact Lrow | apply NEsel; right; right; exists i; split; [exact Hi | reflexivity] | lia | lia | lia
      | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact (R3 i j Hi Hj)].
  - apply HSR; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R4].
  - apply HSR; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R5].
  - apply HSR; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R6].
  - apply HSR; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R7].
  - apply HSR; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R8].
  - apply HSR; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R9].
  - apply HSR; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact R10].
  - apply (PIXat_frame M0); [exact PXd |]. intros x Hx. apply (HE (Z_to_bv 64 pixd) 64%Z); [exact Lpd | exact NEd | rewrite u_Z2bv by lia; lia].
  - apply (PIXat_frame M0); [exact PXs |]. intros x Hx. apply (HE (Z_to_bv 64 pixs) 64%Z); [exact Lps | exact NEs | rewrite u_Z2bv by lia; lia].
Qed.

Lemma ergT_pc : forall (S : TSet) (md : Model) (r : bvmap 5 word) (m rom : word -> option byte) (a b : word),
  realizes SEGS (mkCfg (mkst r b m rom) md) S -> a = b -> realizes SEGS (mkCfg (mkst r a m rom) md) S.
Proof. intros S md r m rom a b H E. subst a. exact H. Qed.

Ltac ergT_run HW RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end;
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

Lemma ergT_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

Lemma ergT_pix_same : forall m m' (p : Z) v (x : word), PIXat m p v -> PIXat m' p v -> (p <= u x < p + 64)%Z -> m' x = m x.
Proof.
  intros m m' p v x (P0 & P64 & _ & B) (_ & _ & _ & B') Hx.
  assert (L : Z.of_nat (length (pix_bytes v)) = 64%Z) by (rewrite pix_bytes_len; reflexivity).
  pose proof (u64_range x) as Ux.
  assert (E : Z_to_bv 64 (p + (u x - p)) = x) by (apply bv_eq; rewrite u_Z2bv by lia; lia).
  specialize (B (u x - p)%Z ltac:(rewrite L; lia)). specialize (B' (u x - p)%Z ltac:(rewrite L; lia)).
  rewrite E in B, B'. rewrite B, B'. reflexivity.
Qed.

Lemma ergT_selp : forall T A m sel v p, sel_at T A m sel v -> sel_blk sel v p -> (1 <= p)%Z.
Proof.
  intros T A m sel v p SA Bp. unfold sel_at, bok in SA. unfold sel_blk in Bp.
  destruct SA as (_ & _ & (B1 & _) & _ & _ & (B2 & _) & _ & _ & ROWS & _).
  destruct Bp as [-> | [-> | (i & Hi & ->)]]; [exact B1 | exact B2 |].
  destruct (ROWS i Hi) as ((B3 & _) & _). exact B3.
Qed.

Lemma ergT_al8 : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((s - k) mod 8 = 0)%Z.
Proof.
  intros s k Hs Hk.
  pose proof (Z.div_mod s 16 ltac:(lia)) as E. rewrite Hs, Z.add_0_r in E.
  pose proof (Z.div_mod k 8 ltac:(lia)) as F. rewrite Hk, Z.add_0_r in F.
  rewrite E, F. replace (16 * (s / 16) - 8 * (k / 8))%Z with ((2 * (s / 16) - k / 8) * 8)%Z by lia.
  apply Z.mod_mul. lia.
Qed.

Lemma erg_tail : forall C Ar A m md regs (s pixd pixs sel w h cm datas : Z) (vd : pixv) (sv : selv) (c : Z -> Z -> Z) (ret : word) (S : TSet)
    (M0 : word -> option byte),
  Cok C -> MBC C -> sub_live Ar A -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ERO_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  PIXat m pixd vd -> p_w vd = w -> p_h vd = h -> p_d vd = 1%Z -> p_wpl vd = wpl_of w 1 ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> pixd <> pixs ->
  live A (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z -> live Ar (Z_to_bv 64 (p_data vd)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data vd)) = None -> Z_to_bv 64 datas <> Z_to_bv 64 (p_data vd) ->
  Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd) -> Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd) ->
  (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 (p_data vd)) ->
  W C A M0 md -> FRM C s m M0 ->
  (forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> q <> Z_to_bv 64 pixs ->
     (u q <= u x < u q + k)%Z -> M0 x = m x) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixs) ->
  rdn SEGS M0 (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS M0 (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h) ->
  PIXat M0 pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) -> PIXat M0 pixd vd ->
  sel_at (alloc_top (c_vm C)) A M0 sel sv ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> FRM C s m m' -> POSTM C Ar s m m' -> PIXat m' pixd vd ->
     (forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> (u q <= u x < u q + k)%Z -> m' x = m x) ->
     getr regs' 10 = Z_to_bv 64 pixd ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  forall (m1 : word -> option byte) (r : bvmap 5 word),
  W C A m1 md -> POSTM C Ar (s - 144) M0 m1 -> O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M0 m1 ->
  getr r 2 = Z_to_bv 64 (s - 160) -> getr r 8 = Z_to_bv 64 pixd -> getr r 9 = Z_to_bv 64 sel ->
  (forall x, In x [3; 4; 27]%list -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0xa1f10 : word) m1 al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd pixs sel w h cm datas vd sv c ret S M0 CK MB SUB Hs16 Hlo Hhi Hret H2s PXs HOK Hw Hh Lps Lps0 Lds
    PXd Ew Eh Ed Ewpl Lpd NEds Ldd Ldd0 Ldd00 NEsdd NEpdd NEpsd Hcx Hcy SBs SBd HW0 FR0 LK0
    R8 R16 R24 R32 R40 R48 R56 R64 R72 R80 R88 R96 R144 R100 R104 PXs0 PXd0 SA0 HK m1 r HW1 PM1 DF1 H2 H8 H9 H3427.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof Hlo as Hlo'. unfold ERO_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs160 : (160 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w 1 ltac:(lia) DV) as Hwpl.
  assert (Hn : (0 < 4 * (p_wpl vd * p_h vd))%Z) by (rewrite Ewpl, Eh; nia).
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof PXd as (Hd0 & Hd64' & WFd & _).
  pose proof (wf_data _ WFd) as Rdd.
  destruct (blk_range C A M0 md (Z_to_bv 64 pixs) 64 CK HW0 Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (blk_range C A M0 md (Z_to_bv 64 pixd) 64 CK HW0 Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  destruct (blk_range C A M0 md (Z_to_bv 64 (p_data vd)) _ CK HW0 Ldd ltac:(lia)) as [Gdd TOPdd]. rewrite u_Z2bv in Gdd, TOPdd by lia.
  assert (SHd : V23LeptRop_iface.rop_shape (p_w vd) (p_h vd) (p_d vd) (p_wpl vd)).
  { unfold V23LeptRop_iface.rop_shape. rewrite Ew, Eh, Ed, Ewpl.
    split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|lia]. }
  assert (BLK1 : forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> (u q <= u x < u q + k)%Z -> m1 x = M0 x).
  { intros q k x Lq Nq Hx.
    destruct (blk_range C A M0 md q k CK HW0 Lq ltac:(lia)) as [Gq Tq].
    pose proof (ergT_apart C A M0 md q _ k _ CK HW0 Lq Ldd Nq ltac:(lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia.
    apply DF1; [unfold scratch; lia | lia]. }
  assert (SA1 : sel_at (alloc_top (c_vm C)) A m1 sel sv).
  { apply (sel_at_keep_pw (alloc_top (c_vm C)) A A M0 m1 sel sv ltac:(lia) SA0); [intros p _; reflexivity|].
    intros p n x Bp Lp Hx. pose proof (ergT_selp _ _ _ _ _ _ SA0 Bp) as P1.
    pose proof (u64_range x) as Ux.
    assert (Up : u (Z_to_bv 64 p) = p) by (apply u_Z2bv; lia).
    apply (BLK1 (Z_to_bv 64 p) n x Lp (SBd p Bp)). rewrite Up. exact Hx. }
  destruct (V23LeptEroSegs.er_T al_rom r m1 s sel ltac:(lia) ltac:(lia) (W_mbc C A m1 md CK HW1 MB) H2 H9)
    as (r1 & RUN1 & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & AG1).
  ergT_run HW1 RUN1.
  eapply ergT_pc;
    [ apply (V23LeptSelFMT.selFindMaxTranslations_W C A m1 md r1 (s - 160) sel (s - 124) (s - 128) (s - 132) (s - 136) sv (getr r1 1) S CK HW1
               ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold V23LeptSelFMT.SFMT_STACK; lia) ltac:(lia)
               eq_refl ltac:(rewrite Q1; red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               (sp_slot_al4 s 124 Hs16 eq_refl) (sp_slot_al4 s 128 Hs16 eq_refl) (sp_slot_al4 s 132 Hs16 eq_refl) (sp_slot_al4 s 136 Hs16 eq_refl)
               SA1 Hcx Hcy)
    | apply bv_eq; reflexivity ].
  intros M7 r2 y0 y1 y2 y3 HW2 CS2 PM2 By0 By1 By2 By3 R2_10.
  rewrite Q1.
  assert (RDS : forall mm (a : Z) (n : nat), O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 mm ->
            (s - 144 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
            rdn SEGS mm (Z_to_bv 64 a) n = rdn SEGS (O23LeptSelFMT.SFR m1 (s - 124) (s - 128) (s - 132) (s - 136) y0 y1 y2 y3) (Z_to_bv 64 a) n).
  { intros mm a n DF Ha Hna.
    rewrite (rdn_ext SEGS n mm M7 (Z_to_bv 64 a)).
    - exact (FRM_rdn16 C (s - 160) _ M7 a n CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia)).
    - rewrite u_Z2bv by lia. lia.
    - intros x Hx. rewrite u_Z2bv in Hx by lia. apply DF; [unfold scratch; lia | lia]. }
  assert (RD7 : forall mm (a : Z) (n : nat), O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 mm ->
            (s - 144 <= a)%Z -> (a + Z.of_nat n <= s - 136 \/ s - 120 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
            rdn SEGS mm (Z_to_bv 64 a) n = rdn SEGS M0 (Z_to_bv 64 a) n).
  { intros mm a n DF Ha Hb Hna. rewrite (RDS mm a n DF Ha Hna).
    rewrite (SFRe_rd_out m1 s y0 y1 y2 y3 a n) by lia.
    exact (FRM_rdn16 C (s - 144) M0 m1 a n CK (proj1 PM1) ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (BLK7 : forall mm (q : word) k (x : word), O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 mm ->
            live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> (u q <= u x < u q + k)%Z -> mm x = M0 x).
  { intros mm q k x DF Lq Nq Hx.
    destruct (blk_range C A M0 md q k CK HW0 Lq ltac:(lia)) as [Gq Tq].
    pose proof (ergT_apart C A M0 md q _ k _ CK HW0 Lq Ldd Nq ltac:(lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia.
    rewrite (DF x) by (try unfold scratch; lia).
    rewrite (LIVK_byte A _ M7 q k x (proj2 PM2) Lq Hx).
    rewrite SFRe_out by lia.
    exact (BLK1 q k x Lq Nq Hx). }
  assert (HRT : forall mm, O23LeptDilW.dil_frame C (s - 144) (p_data vd) (4 * (p_wpl vd * p_h vd)) M7 mm ->
    rdn SEGS mm (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 y0) /\ rdn SEGS mm (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 y1) /\
    rdn SEGS mm (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 y2) /\ rdn SEGS mm (Z_to_bv 64 (s - 136)) 4 = Some (Z_to_le_bytes 4 y3) /\
    rdn SEGS mm (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 (p_w vd)) /\ rdn SEGS mm (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 (p_h vd)) /\
    PIXat mm pixd vd).
  { intros mm DF.
    destruct (SFRe_rd m1 s y0 y1 y2 y3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Y0 & Y1 & Y2 & Y3).
    rewrite (RD7 mm (s - 100)%Z 4%nat DF) by (cbn; lia). rewrite (RD7 mm (s - 104)%Z 4%nat DF) by (cbn; lia).
    rewrite (RDS mm (s - 124)%Z 4%nat DF) by (cbn; lia). rewrite (RDS mm (s - 128)%Z 4%nat DF) by (cbn; lia).
    rewrite (RDS mm (s - 132)%Z 4%nat DF) by (cbn; lia). rewrite (RDS mm (s - 136)%Z 4%nat DF) by (cbn; lia).
    rewrite Ew, Eh.
    split; [exact Y0|]. split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact R100|]. split; [exact R104|].
    apply (PIXat_frame M0 mm pixd vd PXd0). intros x Hx. apply (BLK7 mm (Z_to_bv 64 pixd) 64%Z x DF Lpd NEpdd). rewrite u_Z2bv by lia. lia. }
  eapply ergT_pc;
    [ eapply ero_X1W with (C := C) (Ar := Ar) (A := A) (md := md) (M7 := M7) (s := s) (pixd := pixd) (vd := vd)
                          (y0 := y0) (y1 := y1) (y2 := y2) (y3 := y3) (r0 := regs)
    | apply bv_eq; reflexivity ].
  all: try solve [assumption | exact HRT | exact SHd].
  all: try (unfold ero_TI; solve [
    split; [exact HW2|]; split; [intros a _ _; reflexivity|]; split; [apply POSTM_refl|];
    split; [csr; reflexivity|]; split; [csr; reflexivity|];
    unfold ero_keep; intros x Hx; cbn [In] in Hx; destruct Hx as [<- | [<- | [<- | []]]]; csr; reflexivity ]).
  intros m3 r3 TI3. unfold ero_TI in TI3. destruct TI3 as (HW3 & DF3 & PM3 & G2 & G8 & KP3). unfold ero_keep in KP3.
  destruct (V23LeptEroSegs.er_F al_rom r3 m3 s ltac:(lia) ltac:(lia) G2) as (r4 & RUN4 & F1 & F10 & AG4).
  ergT_run HW3 RUN4.
  assert (PXs3 : PIXat m3 pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2)).
  { apply (PIXat_frame M0 m3 pixs _ PXs0). intros x Hx. apply (BLK7 m3 (Z_to_bv 64 pixs) 64%Z x DF3 Lps NEpsd). rewrite u_Z2bv by lia. lia. }
  assert (RP3 : rdn SEGS m3 (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 pixs)).
  { rewrite (RD7 m3 (s - 144)%Z 8%nat DF3) by (cbn; lia). exact R144. }
  eapply ergT_pc;
    [ apply (V23LeptPixMisc.pixDestroy_dec_W C A m3 md r4 (s - 160) (s - 144) pixs (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) None (getr r4 1) S
               CK HW3 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia)
               eq_refl ltac:(rewrite F1; red; apply bv_eq; reflexivity) F10 ltac:(cbn [slotok]; split; lia) (ergT_al8 s 144 Hs16 eq_refl)
               RP3 PXs3 eq_refl Lps Lps0 ltac:(intros p k E; discriminate E))
    | apply bv_eq; reflexivity ].
  intros m4 r5 HW4 CS5 PX4 RS4 OUT9 GR4.
  change (set_rc (set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2) 1) with (O23LeptPixCopyT.hdv w h 1 cm datas) in PX4.
  rewrite F1.
  assert (RD4 : forall (a : Z) (n : nat), (s - 120 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> rdn SEGS m4 (Z_to_bv 64 a) n = rdn SEGS M0 (Z_to_bv 64 a) n).
  { intros a n Ha Hna. rewrite (rdn_ext SEGS n m4 m3 (Z_to_bv 64 a)).
    - apply (RD7 m3 a n DF3); lia.
    - rewrite u_Z2bv by lia. lia.
    - intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT9; [lia | lia | unfold inslot; lia]. }
  destruct (V23LeptEroSegs.er_Z al_rom r5 m4 s pixd ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) ltac:(lia) ltac:(lia) Hret
              ltac:(rewrite RD4 by (cbn; lia); exact R8) ltac:(rewrite RD4 by (cbn; lia); exact R16) ltac:(rewrite RD4 by (cbn; lia); exact R24)
              ltac:(rewrite RD4 by (cbn; lia); exact R32) ltac:(rewrite RD4 by (cbn; lia); exact R40) ltac:(rewrite RD4 by (cbn; lia); exact R48)
              ltac:(rewrite RD4 by (cbn; lia); exact R56) ltac:(rewrite RD4 by (cbn; lia); exact R64) ltac:(rewrite RD4 by (cbn; lia); exact R72)
              ltac:(rewrite RD4 by (cbn; lia); exact R80) ltac:(rewrite RD4 by (cbn; lia); exact R88) ltac:(rewrite RD4 by (cbn; lia); exact R96)
              ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r6 & RUN6 & Z2 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & AG6).
  ergT_run HW4 RUN6.
  assert (NEsd' : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (apply O23LeptPixCopyT.zbv_ne2; lia).
  assert (BLK : forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> q <> Z_to_bv 64 pixs ->
            (u q <= u x < u q + k)%Z -> m4 x = M0 x).
  { intros q k x Lq Nq Nqs Hx.
    destruct (blk_range C A M0 md q k CK HW0 Lq ltac:(lia)) as [Gq Tq].
    pose proof (ergT_apart C A M0 md q _ k 64 CK HW0 Lq Lps Nqs ltac:(lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia.
    rewrite (OUT9 x) by (try unfold inslot; lia).
    exact (BLK7 m3 q k x DF3 Lq Nq Hx). }
  assert (PXd4 : PIXat m4 pixd vd).
  { apply (PIXat_frame M0 m4 pixd vd PXd0). intros x Hx. apply (BLK (Z_to_bv 64 pixd) 64%Z x Lpd NEpdd NEsd'). rewrite u_Z2bv by lia. lia. }
  assert (FRAME : forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> (u q <= u x < u q + k)%Z -> m4 x = m x).
  { intros q k x Lq Nq Hx.
    destruct (bv_eq_dec _ q (Z_to_bv 64 pixs)) as [->|Nqs].
    - rewrite Lps in Lq. injection Lq as Ek. subst k. rewrite u_Z2bv in Hx by lia.
      exact (ergT_pix_same m m4 pixs _ x PXs PX4 Hx).
    - destruct (bv_eq_dec _ q (Z_to_bv 64 pixd)) as [->|Nqd].
      + rewrite Lpd in Lq. injection Lq as Ek. subst k. rewrite u_Z2bv in Hx by lia.
        exact (ergT_pix_same m m4 pixd vd x PXd PXd4 Hx).
      + rewrite (BLK q k x Lq Nq Nqs Hx). exact (LK0 q k x Lq Nq Nqs Hx). }
  assert (FRM4 : FRM C s m m4).
  { intros a NH NG NE NC NS.
    destruct (Z_lt_le_dec (u a) pixs) as [Ga|Ga]; [|destruct (Z_lt_le_dec (u a) (pixs + 64)) as [Gb|Gb]].
    2: exact (ergT_pix_same m m4 pixs _ a PXs PX4 ltac:(lia)).
    all: assert (NS' : forall s' : Z, (s' <= s)%Z -> ~ scratch C s' a) by (intros s' Hs' X; apply NS; unfold scratch in *; lia).
    all: unfold scratch in NS.
    all: rewrite (OUT9 a) by (try unfold inslot; lia).
    all: rewrite (proj1 PM3 a NH NG NE NC (NS' (s - 144)%Z ltac:(lia))).
    all: rewrite (proj1 PM2 a NH NG NE NC (NS' (s - 160)%Z ltac:(lia))).
    all: rewrite SFRe_out by lia.
    all: rewrite (proj1 PM1 a NH NG NE NC (NS' (s - 144)%Z ltac:(lia))).
    all: exact (FR0 a NH NG NE NC NS). }
  assert (LIVK4 : LIVK Ar m m4).
  { intros q k i Lq Hi. pose proof (SUB q k Lq) as LqA.
    assert (Nq : q <> Z_to_bv 64 (p_data vd)) by (intros ->; rewrite Ldd0 in Lq; discriminate).
    destruct (blk_range C A M0 md q k CK HW0 LqA ltac:(lia)) as [Gq Tq].
    apply (FRAME q k (at_ q i) LqA Nq). unfold at_. rewrite u_Z2bv by lia. lia. }
  apply (HK m4 r6 HW4).
  - apply cs_kept_intro; csr; reflexivity.
  - exact FRM4.
  - exact (conj FRM4 LIVK4).
  - exact PXd4.
  - exact FRAME.
  - exact Z10.
Qed.

Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac pcfix RUN :=
  lazymatch type of RUN with msteps _ (@mkst _ _ ?p _ _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (@mkst _ _ ?q _ _) _) _ =>
      first [constr_eq p q | replace q with p by (apply bv_eq; reflexivity)]
    end
  end.
Ltac kpcs := first [exact cs2 | exact cs3 | exact cs4 | exact cs8 | exact cs9 | exact cs18 | exact cs19 | exact cs20
  | exact cs21 | exact cs22 | exact cs23 | exact cs24 | exact cs25 | exact cs26 | exact cs27].
Ltac kp := repeat match goal with
  | CS : cs_kept ?a ?b |- getr ?b ?x = _ => rewrite (cs_kept_get a b x CS) by kpcs
  | AG : regs_agree _ ?a ?b |- getr ?b ?x = _ => rewrite (AG x ltac:(notin_lit))
  end; first [assumption | reflexivity].

Lemma eg_m16 : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 16 = 0)%Z -> ((s - k) mod 16 = 0)%Z.
Proof. intros s k Hs Hk. rewrite Zminus_mod, Hs, Hk. reflexivity. Qed.

Lemma eg_nwin : forall C A m md (p : word) n (x : word), Cok C -> W C A m md -> live A p = Some n -> (u p <= u x < u p + n)%Z ->
  ~ (c_top C - LSTK <= u x < c_top C)%Z.
Proof. intros C A m md p n x CK HW L Hx. destruct (blk_byte C A m md p n x CK HW L Hx) as (_ & _ & _ & NW & _). exact NW. Qed.

Lemma eg_disj : forall C A m md (p q : word) n k (x : word), Cok C -> W C A m md -> live A p = Some n -> live A q = Some k -> p <> q ->
  (u q <= u x < u q + k)%Z -> ~ (u p <= u x < u p + n)%Z.
Proof.
  intros C A m md p q n k x CK HW Lp Lq NE Hx Hp.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (Hn & _).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lq) as (Hk & _).
  pose proof (round16_ge n Hn). pose proof (round16_ge k Hk).
  destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lq NE); lia.
Qed.

Lemma eg_m4 : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 4 = 0)%Z -> ((s - k) mod 4 = 0)%Z.
Proof.
  intros s k Hs Hk. apply Z.mod_divide in Hs; [|lia]. apply Z.mod_divide in Hk; [|lia]. apply Z.mod_divide; [lia|].
  destruct Hs as [a Ha]. destruct Hk as [b Hb]. exists (4 * a - b)%Z. lia.
Qed.

Lemma eg_bvne : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

Lemma eg_rd_keep : forall m m' (a : Z) (k : nat) bs, (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z ->
  (forall x : word, (a <= u x < a + Z.of_nat k)%Z -> m' x = m x) ->
  rdn SEGS m (Z_to_bv 64 a) k = Some bs -> rdn SEGS m' (Z_to_bv 64 a) k = Some bs.
Proof.
  intros m m' a k bs H0 H1 K R. rewrite <- R. apply rdn_ext; rewrite ?u_Z2bv by lia; [lia |]. intros x Hx. apply K. lia.
Qed.

Lemma eg_clone : forall C A m md (s pixs pp : Z), Cok C -> W C A m md -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (0 <= pixs)%Z -> (pixs + 64 < 2 ^ 64)%Z -> (c_top C - LSTK <= pp)%Z -> (pp + 8 <= s)%Z -> (s <= c_top C)%Z ->
  (forall x : word, ~ (pp <= u x < pp + 8)%Z -> ~ (pixs + 20 <= u x < pixs + 24)%Z -> O23LeptPma1.clone_mem m pixs pp x = m x) /\
  FRM C s m (O23LeptPma1.clone_mem m pixs pp) /\
  O23LeptCloseA.PWK A (fun q => q <> Z_to_bv 64 pixs) m (O23LeptPma1.clone_mem m pixs pp).
Proof.
  intros C A m md s pixs pp CK HW Lp H0 H64 Hpp1 Hpp2 Hs. pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  assert (OUT : forall x : word, ~ (pp <= u x < pp + 8)%Z -> ~ (pixs + 20 <= u x < pixs + 24)%Z -> O23LeptPma1.clone_mem m pixs pp x = m x).
  { intros x N1 N2. unfold O23LeptPma1.clone_mem.
    rewrite MemSplit.wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                      | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
    rewrite MemSplit.wbytes_outside; [reflexivity | rewrite u_Z2bv by lia; cbn; lia | rewrite u_Z2bv by lia; cbn; lia]. }
  split; [exact OUT | split].
  - intros a NG NGl NE NH NS. apply OUT.
    + intros Hc. apply NS. unfold scratch. lia.
    + intros Hc. apply NG. destruct (blk_byte C A m md (Z_to_bv 64 pixs) 64 a CK HW Lp ltac:(rewrite u_Z2bv by lia; lia)) as (HG & _). exact HG.
  - intros q k x Lq NEq Hx. apply OUT.
    + intros Hc. apply (eg_nwin C A m md q k x CK HW Lq Hx). lia.
    + intros Hc. apply (eg_disj C A m md (Z_to_bv 64 pixs) q 64 k x CK HW Lp Lq (fun E => NEq (eq_sym E)) Hx).
      rewrite u_Z2bv by lia. lia.
Qed.

Lemma eg_wb_out : forall m (a : Z) bs (x : word), (0 <= a)%Z -> (a + Z.of_nat (length bs) < 2 ^ 64)%Z ->
  (u x < a \/ a + Z.of_nat (length bs) <= u x)%Z -> wbytes m (Z_to_bv 64 a) bs x = m x.
Proof. intros m a bs x H0 H1 H2. apply MemSplit.wbytes_outside; rewrite u_Z2bv by lia; lia. Qed.

Lemma eg_pge_out : forall m (s w h : Z) (x : word), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 104 <= u x < s - 96)%Z ->
  PGE m s w h x = m x.
Proof.
  intros m s w h x Hs Hs64 Hx. unfold PGE.
  rewrite !eg_wb_out; try reflexivity; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma eg_sgp_out : forall m (s sy sx cy cx : Z) (x : word), (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 120 <= u x < s - 104)%Z ->
  O23LeptSelGP.SGP4 m (s - 112) (s - 108) (s - 120) (s - 116) sy sx cy cx x = m x.
Proof.
  intros m s sy sx cy cx x Hs Hs64 Hx. unfold O23LeptSelGP.SGP4, O23LeptSelGP.wr4.
  rewrite !eg_wb_out; try reflexivity; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma eg_rop1 : forall w h, O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z -> V23LeptRop_iface.rop_shape w h 1 (wpl_of w 1).
Proof. intros w h (DV & Hw & Hh & Hb) H1 H2. unfold V23LeptRop_iface.rop_shape. repeat split; lia. Qed.

(* [comment removed for export] *)
Theorem pixErode_given_W : forall C Ar A m md regs (s pixd pixs sel w h cm datas : Z) (vd : pixv) (sv : selv) (c : Z -> Z -> Z) (ret : word) (S : TSet),
  Cok C -> MBC C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ERO_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  PIXat m pixd vd -> p_w vd = w -> p_h vd = h -> p_d vd = 1%Z -> p_wpl vd = wpl_of w 1 ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> pixd <> pixs ->
  live A (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z -> live Ar (Z_to_bv 64 (p_data vd)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data vd)) = None -> Z_to_bv 64 datas <> Z_to_bv 64 (p_data vd) ->
  Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd) -> Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd) ->
  (p_cmap vd <> 0 -> exists cv, CMAPat m (p_cmap vd) cv /\ live A (Z_to_bv 64 (p_cmap vd)) = Some 24)%Z ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> sel_cont m sv c -> (0 <= v_cx sv < v_sx sv)%Z -> (0 <= v_cy sv < v_sy sv)%Z ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 pixs) ->
  (forall p, sel_blk sel sv p -> Z_to_bv 64 p <> Z_to_bv 64 (p_data vd)) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> FRM C s m m' -> POSTM C Ar s m m' -> PIXat m' pixd vd ->
     (forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> (u q <= u x < u q + k)%Z -> m' x = m x) ->
     getr regs' 10 = Z_to_bv 64 pixd ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1d7c : word) m al_rom) md) S.
Proof using P16 PINS.
  intros C Ar A m md regs s pixd pixs sel w h cm datas vd sv c ret S
    CK MB HW SUBA H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 PXs HO Hw Hh Lps L0ps Lds PXd Ew Eh Ed1 Ewpl Lpd NEp Ldd LAdd L0dd
    NEdd NEpdd NEpsd CMAP SA SC Hcx Hcy SNs SNd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof Hlo as Hlo'. unfold ERO_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hps0 & Hps64 & _). pose proof PXd as (Hpd0 & Hpd64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps Tps]. rewrite u_Z2bv in Gps, Tps by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lpd ltac:(lia)) as [Gpd Tpd]. rewrite u_Z2bv in Gpd, Tpd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof SA as (Hsy & Hsx & (Bs1 & Bs2 & Bs3) & Lsel & RC & (Bd1 & Bd2 & Bd3) & Ldat & NEdsel & ROWS & RDIF).
  pose proof HO as (_ & Hw1 & Hh1 & Hwh).
  set (vs := set_rc (O23LeptPixCopyT.hdv w h 1 cm datas) 2).
  assert (NEpw : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (apply eg_bvne; lia).
  assert (SNs' : forall q, O23LeptCloseA.sblk sel sv q -> q <> Z_to_bv 64 pixs)
    by (intros q (p & Hp & ->); exact (SNs p Hp)).
  assert (SNd' : forall q, O23LeptCloseA.sblk sel sv q -> q <> Z_to_bv 64 (p_data vd))
    by (intros q (p & Hp & ->); exact (SNd p Hp)).
  destruct (er_A al_rom regs m s pixd pixs sel ret ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 160) 160 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & R2_1 & R1_1 & R9_1 & R18_1 & R13_1 & R10_1 & R11_1 & R12_1 & AG1).
  pcfix RUN1. rzs HW RUN1.
  assert (WP1 : W C A (FRE m s ret regs) md /\ POSTM C A s m (FRE m s ret regs)) by (unfold FRE; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (frD_FRE m s ret regs ltac:(lia) ltac:(lia)) as FC1.
  destruct (sel_keep (alloc_top (c_vm C)) A A (fun _ => True) m (FRE m s ret regs) sel sv c ltac:(lia) SA SC
              (fun q _ => eq_refl) (O23LeptCloseA.PWK_livk A m _ (proj2 PM1)) (fun _ _ => I)) as [SA1 SC1].
  pose proof (exT_pix_livk A m _ pixs _ PXs (proj2 PM1) Lps) as PXs1.
  pose proof (exT_pix_livk A m _ pixd vd PXd (proj2 PM1) Lpd) as PXd1.
  pose proof SA1 as (_ & _ & _ & _ & RC1 & _).
  apply (pma1_given_W C A (FRE m s ret regs) md r1 (s - 160) pixd pixs sel (s - 144) w h cm datas
           (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv) (v_data sv) (v_name sv) vd _ S CK HW1 R2_1
           (eg_m16 s 160 Hs16 eq_refl) ltac:(unfold O23LeptPma1G.PMA1G_STACK; lia) ltac:(lia) R1_1
           ltac:(red; apply bv_eq; reflexivity) R10_1 R11_1 R12_1 R13_1 ltac:(lia) ltac:(lia)
           (sp_slot_al8 s 144 Hs16 eq_refl) PXs1 Lps L0ps PXd1 Ew Eh Ed1 Lpd NEp RC1 Lsel ltac:(lia) ltac:(lia)).
  intros m2 r2 HW2 CS2 PM2 V10_2.
  destruct (eg_clone C A (FRE m s ret regs) md s pixs (s - 144) CK HW1 Lps ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hhi)
    as (OUTc & FRMc & PWKc).
  set (m1 := FRE m s ret regs) in *.
  set (m1c := O23LeptPma1.clone_mem m1 pixs (s - 144)) in *.
  pose proof (O23LeptPma1.PIXat_clone_mem m1 pixs (s - 144) _ PXs1 ltac:(lia) ltac:(lia) ltac:(lia)) as PXs1c.
  pose proof (PIXat_frame m1 m1c pixd vd PXd1 (fun x Hx => PWKc (Z_to_bv 64 pixd) 64%Z x Lpd NEpw ltac:(rewrite u_Z2bv by lia; lia))) as PXd1c.
  pose proof (V23LeptPma1.rdn_clone_mem_cell m1 pixs (s - 144) ltac:(lia) ltac:(lia) ltac:(lia)) as S144_1c.
  pose proof (frD_out m1 m1c (pixs + 20) (s - 136) s ret regs
                (fun x Hx => OUTc x ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia) FC1) as FC1c.
  destruct (sel_keep (alloc_top (c_vm C)) A A (fun q => q <> Z_to_bv 64 pixs) m1 m1c sel sv c ltac:(lia) SA1 SC1
              (fun q _ => eq_refl) PWKc SNs') as [SA1c SC1c].
  pose proof (exT_pix_livk A m1c m2 pixs vs PXs1c (proj2 PM2) Lps) as PXs2.
  pose proof (exT_pix_livk A m1c m2 pixd vd PXd1c (proj2 PM2) Lpd) as PXd2.
  pose proof (frD_frm C (s - 160) m1c m2 s ret regs CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) FC1c) as FC2.
  pose proof (eg_rd_keep m1c m2 (s - 144) 8 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m1c m2 CK (proj1 PM2) ltac:(lia) x ltac:(lia)) S144_1c) as S144_2.
  destruct (sel_keep (alloc_top (c_vm C)) A A (fun _ => True) m1c m2 sel sv c ltac:(lia) SA1c SC1c
              (fun q _ => eq_refl) (O23LeptCloseA.PWK_livk A m1c m2 (proj2 PM2)) (fun _ _ => I)) as [SA2 SC2].
  assert (RW : rdn SEGS (wbytes (wbytes m2 (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                          (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w)).
  { rewrite rdn_wbytes_out_Z by (zlen; lia). rewrite rdn_wbytes_out_Z by (zlen; lia). exact (PIX_rd_w SEGS _ _ _ PXs2). }
  assert (RH : rdn SEGS (wbytes (wbytes (wbytes m2 (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                          (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                          (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w))) (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h)).
  { rewrite rdn_wbytes_out_Z by (zlen; lia). rewrite rdn_wbytes_out_Z by (zlen; lia). rewrite rdn_wbytes_out_Z by (zlen; lia).
    exact (PIX_rd_h SEGS _ _ _ PXs2). }
  destruct (er_B al_rom r2 m2 s pixd pixs sel w h ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ltac:(lia) ltac:(lia) (al16_mod8 _ ALps)
              ltac:(lia) ltac:(lia) RW RH (W_sok_win C A m2 md (s - 104) 8 CK HW2 ltac:(lia) ltac:(cbn; lia)) ltac:(kp) V10_2
              ltac:(kp) ltac:(kp))
    as (r3 & RUN3 & R2_3 & R1_3 & R8_3 & R10_3 & R11_3 & R12_3 & R13_3 & R14_3 & AG3).
  pcfix RUN3. rzs HW2 RUN3.
  assert (WP3 : W C A (PGE m2 s w h) md /\ POSTM C A s m2 (PGE m2 s w h)) by (unfold PGE; wp_win CK).
  destruct WP3 as [HW3 PM3].
  set (m3 := PGE m2 s w h) in *.
  assert (S100_3 : rdn SEGS m3 (Z_to_bv 64 (s - 100)) 4 = Some (Z_to_le_bytes 4 w)).
  { unfold m3, PGE. rewrite rdn_wbytes_out_Z by (zlen; lia). rewrite <- (w2b_Z 4 w) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv; lia. }
  assert (S104_3 : rdn SEGS m3 (Z_to_bv 64 (s - 104)) 4 = Some (Z_to_le_bytes 4 h)).
  { unfold m3, PGE. rewrite <- (w2b_Z 4 h) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv; lia. }
  pose proof (frD_out m2 m3 (s - 104) (s - 96) s ret regs (fun x Hx => eg_pge_out m2 s w h x ltac:(lia) ltac:(lia) Hx)
                ltac:(lia) ltac:(lia) ltac:(lia) FC2) as FC3.
  pose proof (eg_rd_keep m2 m3 (s - 144) 8 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => eg_pge_out m2 s w h x ltac:(lia) ltac:(lia) ltac:(cbn in Hx; lia)) S144_2) as S144_3.
  destruct (sel_keep (alloc_top (c_vm C)) A A (fun _ => True) m2 m3 sel sv c ltac:(lia) SA2 SC2
              (fun q _ => eq_refl) (O23LeptCloseA.PWK_livk A m2 m3 (proj2 PM3)) (fun _ _ => I)) as [SA3 SC3].
  pose proof SA3 as (_ & _ & _ & _ & RC3 & _).
  pose proof (exT_pix_livk A m2 m3 pixs vs PXs2 (proj2 PM3) Lps) as PXs3.
  pose proof (exT_pix_livk A m2 m3 pixd vd PXd2 (proj2 PM3) Lpd) as PXd3.
  destruct (sgp4_run al_rom r3 m3 sel (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)
              (v_data sv) (v_name sv) _ RC3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
              (W_sok_win C A m3 md (s - 112) 4 CK HW3 ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A m3 md (s - 108) 4 CK HW3 ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A m3 md (s - 120) 4 CK HW3 ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A m3 md (s - 116) 4 CK HW3 ltac:(lia) ltac:(cbn; lia))
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (al16_mod8 _ Bs3)
              (eg_m4 s 112 Hs16 eq_refl) (eg_m4 s 108 Hs16 eq_refl) (eg_m4 s 120 Hs16 eq_refl) (eg_m4 s 116 Hs16 eq_refl)
              R1_3 ltac:(red; apply bv_eq; reflexivity) R10_3 R11_3 R12_3 R13_3 R14_3)
    as (r4 & RUN4 & V10_4 & AG4).
  rzs HW3 RUN4.
  set (m4 := O23LeptSelGP.SGP4 m3 (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)) in *.
  assert (WP4 : W C A m4 md /\ POSTM C A s m3 m4) by (unfold m4, O23LeptSelGP.SGP4, O23LeptSelGP.wr4; wp_win CK).
  destruct WP4 as [HW4 PM4].
  pose proof (frD_out m3 m4 (s - 120) (s - 104) s ret regs (fun x Hx => eg_sgp_out m3 s _ _ _ _ x ltac:(lia) ltac:(lia) Hx)
                ltac:(lia) ltac:(lia) ltac:(lia) FC3) as FC4.
  pose proof (eg_rd_keep m3 m4 (s - 144) 8 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => eg_sgp_out m3 s _ _ _ _ x ltac:(lia) ltac:(lia) ltac:(cbn in Hx; lia)) S144_3) as S144_4.
  pose proof (eg_rd_keep m3 m4 (s - 100) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => eg_sgp_out m3 s _ _ _ _ x ltac:(lia) ltac:(lia) ltac:(cbn in Hx; lia)) S100_3) as S100_4.
  pose proof (eg_rd_keep m3 m4 (s - 104) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => eg_sgp_out m3 s _ _ _ _ x ltac:(lia) ltac:(lia) ltac:(cbn in Hx; lia)) S104_3) as S104_4.
  destruct (SGP4_rd m3 (s - 112) (s - 108) (s - 120) (s - 116) (v_sy sv) (v_sx sv) (v_cy sv) (v_cx sv)
              ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
              ltac:(red; lia) ltac:(red; lia) ltac:(red; lia) ltac:(red; lia) ltac:(red; lia) ltac:(red; lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (Sy4 & Sx4 & Cy4 & Cx4).
  destruct (sel_keep (alloc_top (c_vm C)) A A (fun _ => True) m3 m4 sel sv c ltac:(lia) SA3 SC3
              (fun q _ => eq_refl) (O23LeptCloseA.PWK_livk A m3 m4 (proj2 PM4)) (fun _ _ => I)) as [SA4 SC4].
  pose proof (exT_pix_livk A m3 m4 pixs vs PXs3 (proj2 PM4) Lps) as PXs4.
  pose proof (exT_pix_livk A m3 m4 pixd vd PXd3 (proj2 PM4) Lpd) as PXd4.
  destruct (er_C al_rom r4 m4 pixd ltac:(kp)) as (r5 & RUN5 & R1_5 & R10_5 & AG5).
  pcfix RUN5. rzs HW4 RUN5.
  pose proof PXd as (_ & _ & WFd & _). pose proof (wf_data _ WFd) as Bdat.
  pose proof HO as (DV1 & _).
  pose proof (wpl_of_range w 1 ltac:(lia) DV1) as WPL.
  assert (CMAP4 : (p_cmap vd <> 0 -> exists cv, CMAPat m4 (p_cmap vd) cv /\ live A (Z_to_bv 64 (p_cmap vd)) = Some 24)%Z).
  { intros Hc. destruct (CMAP Hc) as (cv & CM & Lc). exists cv. split; [| exact Lc].
    assert (NEc : Z_to_bv 64 (p_cmap vd) <> Z_to_bv 64 pixs) by (intros E; rewrite E, Lps in Lc; discriminate Lc).
    pose proof CM as (Hc0 & Hc24 & _).
    pose proof (exT_cmap_livk A m m1 _ cv CM (proj2 PM1) Lc) as CM1.
    pose proof (CMAPat_frame m1 m1c _ cv CM1 (fun x Hx => PWKc (Z_to_bv 64 (p_cmap vd)) 24%Z x Lc NEc ltac:(rewrite u_Z2bv by lia; lia))) as CM1c.
    pose proof (exT_cmap_livk A m1c m2 _ cv CM1c (proj2 PM2) Lc) as CM2.
    pose proof (exT_cmap_livk A m2 m3 _ cv CM2 (proj2 PM3) Lc) as CM3.
    exact (exT_cmap_livk A m3 m4 _ cv CM3 (proj2 PM4) Lc). }
  apply (pixSetAll_W C Ar A m4 md r5 (s - 160) pixd (4 * (p_wpl vd * p_h vd)) vd _ S CK HW4 SUBA ltac:(kp) (eg_m16 s 160 Hs16 eq_refl)
           ltac:(unfold SETALL_STACK, LSF; lia) ltac:(lia) R1_5 ltac:(red; apply bv_eq; reflexivity) R10_5 PXd4 Lpd NEpdd CMAP4
           ltac:(rewrite Ewpl, Eh; apply (Z.le_trans _ (wpl_of w 1 * 1)); [lia | apply Z.mul_le_mono_nonneg_l; lia])
           ltac:(rewrite Ewpl, Eh; lia) Ldd ltac:(lia) LAdd L0dd).
  intros m5 r6 HW5 CS6 PM5 PXd5 OUT5.
  assert (OUTh : forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> (u q <= u x < u q + k)%Z -> m5 x = m4 x).
  { intros q k x Lq NEq Hx. apply OUT5.
    - intros Hd. apply (eg_disj C A m4 md (Z_to_bv 64 (p_data vd)) q _ k x CK HW4 Ldd Lq (fun E => NEq (eq_sym E)) Hx).
      rewrite u_Z2bv by lia. exact Hd.
    - intros Hs'. apply (eg_nwin C A m4 md q k x CK HW4 Lq Hx). unfold scratch in Hs'. lia. }
  pose proof (frD_frm C (s - 160) m4 m5 s ret regs CK (proj1 PM5) ltac:(lia) ltac:(lia) ltac:(lia) FC4) as FC5.
  pose proof (eg_rd_keep m4 m5 (s - 144) 8 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m4 m5 CK (proj1 PM5) ltac:(lia) x ltac:(cbn in Hx; lia)) S144_4) as S144_5.
  pose proof (eg_rd_keep m4 m5 (s - 100) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m4 m5 CK (proj1 PM5) ltac:(lia) x ltac:(cbn in Hx; lia)) S100_4) as S100_5.
  pose proof (eg_rd_keep m4 m5 (s - 104) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m4 m5 CK (proj1 PM5) ltac:(lia) x ltac:(cbn in Hx; lia)) S104_4) as S104_5.
  pose proof (eg_rd_keep m4 m5 (s - 112) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m4 m5 CK (proj1 PM5) ltac:(lia) x ltac:(cbn in Hx; lia)) Sy4) as Sy5.
  pose proof (eg_rd_keep m4 m5 (s - 108) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m4 m5 CK (proj1 PM5) ltac:(lia) x ltac:(cbn in Hx; lia)) Sx4) as Sx5.
  pose proof (eg_rd_keep m4 m5 (s - 120) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m4 m5 CK (proj1 PM5) ltac:(lia) x ltac:(cbn in Hx; lia)) Cy4) as Cy5.
  pose proof (eg_rd_keep m4 m5 (s - 116) 4 _ ltac:(lia) ltac:(cbn; lia)
                (fun x Hx => FRM_pw C (s - 160) m4 m5 CK (proj1 PM5) ltac:(lia) x ltac:(cbn in Hx; lia)) Cx4) as Cx5.
  pose proof (PIXat_frame m4 m5 pixs vs PXs4 (fun x Hx => OUTh (Z_to_bv 64 pixs) 64%Z x Lps NEpsd ltac:(rewrite u_Z2bv by lia; lia))) as PXs5.
  destruct (sel_keep (alloc_top (c_vm C)) A A (fun q => q <> Z_to_bv 64 (p_data vd)) m4 m5 sel sv c ltac:(lia) SA4 SC4
              (fun q _ => eq_refl) OUTh SNd') as [SA5 SC5].
  assert (FRM5 : FRM C s m m5).
  { eapply FRM_trans; [exact (proj1 PM1) |]. eapply FRM_trans; [exact FRMc |].
    eapply FRM_trans; [exact (proj1 (POSTM_mono C A (s - 160) s m1c m2 ltac:(lia) PM2)) |].
    eapply FRM_trans; [exact (proj1 PM3) |]. eapply FRM_trans; [exact (proj1 PM4) |].
    exact (proj1 (POSTM_mono C Ar (s - 160) s m4 m5 ltac:(lia) PM5)). }
  assert (PWK5 : forall (q : word) k (x : word), live A q = Some k -> q <> Z_to_bv 64 (p_data vd) -> q <> Z_to_bv 64 pixs ->
                   (u q <= u x < u q + k)%Z -> m5 x = m x).
  { intros q k x Lq N1 N2 Hx.
    rewrite (OUTh q k x Lq N1 Hx), (O23LeptCloseA.PWK_livk A m3 m4 (proj2 PM4) q k x Lq I Hx),
      (O23LeptCloseA.PWK_livk A m2 m3 (proj2 PM3) q k x Lq I Hx), (O23LeptCloseA.PWK_livk A m1c m2 (proj2 PM2) q k x Lq I Hx),
      (PWKc q k x Lq N2 Hx).
    exact (O23LeptCloseA.PWK_livk A m m1 (proj2 PM1) q k x Lq I Hx). }
  pose proof FC5 as FC5'. cbn [frD cellsZ] in FC5'. destruct FC5' as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & _).
  destruct (er_E al_rom r6 m5 s (v_sy sv) (v_sx sv) sel ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (al16_mod8 _ Bs3) Sy5 Sx5 ltac:(kp) ltac:(kp))
    as (r7 & RUN7 & R18_7 & R19_7 & R20_7 & R21_7 & R22_7 & R23_7 & R24_7 & R25_7 & R26_7 & R10_7 & AG7).
  pcfix RUN7. rzs HW5 RUN7.
  assert (ER5 : ero_reads m5 s sel pixd pixs sv c vd vs).
  { pose proof SA5 as (_ & _ & _ & _ & RC5 & _ & _ & _ & ROWS5 & _).
    unfold ero_reads.
    refine (conj _ (conj _ (conj _ (conj S144_5 (conj Cy5 (conj Cx5 (conj Sy5 (conj Sx5 (conj _ (conj _ (conj PXd5 PXs5))))))))))).
    - exact (REC_rd' SEGS m5 sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data sv) RC5 ltac:(cbn; lia) eq_refl ltac:(f_equal; cbn; lia) eq_refl).
    - intros i Hi. destruct (ROWS5 i Hi) as ((Br1 & Br2 & _) & _ & _ & _ & BA).
      pose proof (bytes_at_rdn SEGS m5 (v_data sv + 8 * i) (Z_to_le_bytes 8 (v_rows sv i)) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) BA) as RD.
      rewrite length_Z_to_le_bytes in RD. exact RD.
    - intros i j Hi Hj. exact (proj2 (SC5 i j Hi Hj)).
    - rewrite Eh. exact S104_5.
    - rewrite Ew. exact S100_5. }
  assert (Brows : forall i, (0 <= i < v_sy sv)%Z -> (0 <= v_rows sv i)%Z /\ (v_rows sv i + 4 * v_sx sv < 2 ^ 64)%Z)
    by (intros i Hi; destruct (ROWS i Hi) as ((B1 & B2 & _) & _); lia).
  assert (Arows : forall i, (0 <= i < v_sy sv)%Z -> (1 <= v_rows sv i)%Z /\ (v_rows sv i mod 4 = 0)%Z).
  { intros i Hi. destruct (ROWS i Hi) as ((B1 & B2 & B3) & _). split; [lia |].
    pose proof (eg_m4 (v_rows sv i) 0 B3 eq_refl) as X. rewrite Z.sub_0_r in X. exact X. }
  assert (Bc : forall i j, (0 <= i < v_sy sv)%Z -> (0 <= j < v_sx sv)%Z -> (0 <= c i j < 2 ^ 31)%Z)
    by (intros i j Hi Hj; exact (proj1 (SC i j Hi Hj))).
  apply (ero_loop C Ar A md m5 s sel pixd pixs sv c vd vs S regs CK SUBA Hs16 Hlo Hhi Hsy Hsx Hcx Hcy
           ltac:(lia) ltac:(lia) Brows Bc (conj Bd1 (al16_mod8 _ Bd3)) Arows ltac:(lia)
           ltac:(rewrite Ed1; reflexivity) Ed1
           ltac:(rewrite Ew, Eh, Ed1, Ewpl; exact (eg_rop1 w h HO Hw Hh))
           ltac:(unfold vs; cbn [p_w p_h p_d p_wpl set_rc O23LeptPixCopyT.hdv]; exact (eg_rop1 w h HO Hw Hh))
           ltac:(unfold vs; cbn [p_w set_rc O23LeptPixCopyT.hdv]; lia)
           ltac:(unfold vs; cbn [p_h set_rc O23LeptPixCopyT.hdv]; lia)
           Lpd Lps NEpdd NEpsd Ldd LAdd L0dd Lds NEdd
           (fun m' DF => eg_reads_df C A m5 md m' s sel pixd pixs sv c vd vs CK HW5 Hlo Hhi SA5 Lpd Lps Ldd NEpdd NEpsd SNd ER5 DF)
           (fun m1' r HWx PMx DFx R2x R8x R9x KPx =>
              erg_tail C Ar A m md regs s pixd pixs sel w h cm datas vd sv c ret S m5 CK MB SUBA Hs16 Hlo Hhi Hret H2
                PXs HO Hw Hh Lps L0ps Lds PXd Ew Eh Ed1 Ewpl Lpd NEp Ldd LAdd L0dd NEdd NEpdd NEpsd Hcx Hcy SNs SNd
                HW5 FRM5 PWK5 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 S144_5 S100_5 S104_5 PXs5 PXd5 SA5 HK
                m1' r HWx PMx DFx R2x R8x R9x KPx)
           (Z.to_nat (v_sy sv * v_sx sv - 1)) 0%Z 0%Z r7 m5 HW5 (POSTM_refl C Ar (s - 144) m5) (fun _ _ _ => eq_refl)
           ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by nia; ring) ltac:(kp) ltac:(kp) ltac:(kp)
           R18_7 R19_7 R20_7 R21_7 R22_7 R23_7 R24_7 R25_7 R26_7 R10_7
           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx;
                 destruct Hx as [<-|[<-|[<-|[]]]]; kp)).
Qed.

End EroGW.
