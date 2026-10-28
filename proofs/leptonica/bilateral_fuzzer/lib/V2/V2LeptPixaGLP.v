(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB LeptBracketB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptLinePtrs V2LeptPixaLines.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

(* [comment removed for export] *)
Ltac glp_cs_absurd Cr :=
  exfalso; clear - Cr; unfold AllocIface.callee_saved in Cr;
  repeat (destruct Cr as [Cr|Cr]; [apply (f_equal bv_unsigned) in Cr; vm_compute in Cr; discriminate Cr|]);
  destruct Cr as [C1 C2]; vm_compute in C1, C2; first [apply C1; reflexivity | apply C2; reflexivity].
Ltac glp_cs := red; repeat (first [left; reflexivity | right]); vm_compute; split; discriminate.

Section GLPW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.

Definition GLP_WIN : Z := 256 + CALLOC_STACK.

(* [comment removed for export] *)
Definition pixa_mem10 (C : lctx) (Ar : AS) (m : word -> option byte) (parr w wpl h : Z) (pixes datas : Z -> Z) (vf : Z -> pixv) : Prop :=
  forall i, (0 <= i < 10)%Z ->
    (0 <= pixes i < 2 ^ 64)%Z /\ live Ar (Z_to_bv 64 (pixes i)) = Some 64%Z /\ live (c_A0 C) (Z_to_bv 64 (pixes i)) = None /\
    rdn SEGS m (Z_to_bv 64 (parr + 8 * i)) 8 = Some (Z_to_le_bytes 8 (pixes i)) /\
    PIXat m (pixes i) (vf i) /\ p_w (vf i) = w /\ p_h (vf i) = h /\ p_wpl (vf i) = wpl /\ p_d (vf i) = 8%Z /\ p_rc (vf i) = 1%Z /\ p_data (vf i) = datas i /\
    (1 <= datas i)%Z /\ (datas i + 4 * wpl * h <= 2 ^ 47)%Z.

Lemma pixa_mem10_keep : forall C Ar m m' parr w wpl h pixes datas vf, (0 <= parr)%Z -> (parr + 80 <= 2 ^ 64)%Z ->
  pixa_mem10 C Ar m parr w wpl h pixes datas vf -> live Ar (Z_to_bv 64 parr) = Some 80%Z -> LIVK Ar m m' -> pixa_mem10 C Ar m' parr w wpl h pixes datas vf.
Proof.
  intros C Ar m m' parr w wpl h pixes datas vf G0 G1 PM Lp LK i Hi.
  assert (KEEP : forall (p k : Z) (x : word), live Ar (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p <= u x < p + k)%Z -> m' x = m x).
  { intros p k x Lq Gp Hx. pose proof (u64_range x) as Rx.
    pose proof (LK (Z_to_bv 64 p) k (u x - p)%Z Lq ltac:(lia)) as E.
    replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E; [exact E|].
    unfold at_. rewrite u_Z2bv by lia. replace (p + (u x - p))%Z with (u x) by lia. rewrite zbv_self. reflexivity. }
  destruct (PM i Hi) as (Rp & Lpi & L0 & RD & PX & REST).
  split; [exact Rp|]. split; [exact Lpi|]. split; [exact L0|]. split.
  - rewrite <- RD. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
    intros x Hx. apply (KEEP parr 80%Z); [exact Lp | lia | lia].
  - split; [|exact REST]. apply (PIXat_frame m); [exact PX|].
    intros x Hx. apply (KEEP (pixes i) 64%Z); [exact Lpi | lia | lia].
Qed.

(* [comment removed for export] *)
Definition lset_upto (C : lctx) (Ar A : AS) (m : word -> option byte) (ls wpl h : Z) (linesf datas : Z -> Z) (i : Z) : Prop :=
  (forall k, (0 <= k < i)%Z ->
    (0 <= linesf k < 2 ^ 64)%Z /\ live A (Z_to_bv 64 (linesf k)) = Some (8 * h)%Z /\ live Ar (Z_to_bv 64 (linesf k)) = None /\
    live (c_A0 C) (Z_to_bv 64 (linesf k)) = None /\ linesf k <> ls /\
    rdn SEGS m (Z_to_bv 64 (ls + 8 * k)) 8 = Some (Z_to_le_bytes 8 (linesf k)) /\ lp_rows m (linesf k) (datas k) (4 * wpl) h) /\
  (forall q : word, q <> Z_to_bv 64 ls -> (forall k, (0 <= k < i)%Z -> q <> Z_to_bv 64 (linesf k)) -> live A q = live Ar q) /\
  (forall k k', (0 <= k < k')%Z -> (k' < i)%Z -> linesf k <> linesf k').

Lemma lset_sub : forall C Ar A m ls wpl h linesf datas i, lset_upto C Ar A m ls wpl h linesf datas i -> live Ar (Z_to_bv 64 ls) = None -> sub_live Ar A.
Proof.
  intros C Ar A m ls wpl h linesf datas i (LS & EQ & _) Lls q k Lq.
  rewrite EQ; [exact Lq | |].
  - intros E. subst q. rewrite Lls in Lq. discriminate.
  - intros j Hj E. subst q. destruct (LS j Hj) as (_ & _ & Lr & _). rewrite Lr in Lq. discriminate.
Qed.

Lemma LIVK_rdn : forall A (m m' : word -> option byte) (q : word) (k x : Z) (n : nat), LIVK A m m' -> live A q = Some k ->
  (u q <= x)%Z -> (x + Z.of_nat n <= u q + k)%Z -> (u q + k <= 2 ^ 64)%Z -> rdn SEGS m' (Z_to_bv 64 x) n = rdn SEGS m (Z_to_bv 64 x) n.
Proof.
  intros A m m' q k x n LK Lq H1 H2 H3.
  destruct n as [|n']; [reflexivity|].
  assert (Hn : (1 <= Z.of_nat (S n'))%Z) by (rewrite Nat2Z.inj_succ; lia).
  pose proof (u64_range q) as Rq.
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros y Hy. pose proof (u64_range y) as Ry.
  pose proof (LK q k (u y - u q)%Z Lq ltac:(lia)) as E.
  replace (at_ q (u y - u q)) with y in E; [exact E|].
  unfold at_. replace (u q + (u y - u q))%Z with (u y) by lia. rewrite zbv_self. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma glp_member : forall C Ar A m md (s pa parr w wpl h i : Z) pixes datas vf,
  Cok C -> W C A m md -> sub_live Ar A -> (c_top C - LSTK + GLP_WIN <= s)%Z -> (s <= c_top C)%Z ->
  (0 <= pa < 2 ^ 64)%Z -> (0 <= parr < 2 ^ 64)%Z -> live A (Z_to_bv 64 pa) = Some 32%Z -> live A (Z_to_bv 64 parr) = Some 80%Z ->
  pixa_mem10 C Ar m parr w wpl h pixes datas vf -> (0 <= i < 10)%Z ->
  (4096 <= pixes i)%Z /\ (pixes i + 64 <= s - 256)%Z /\ (pixes i mod 16 = 0)%Z /\
  (pixes i + 64 <= pa \/ pa + 32 <= pixes i)%Z /\ (pixes i + 64 <= parr \/ parr + 80 <= pixes i)%Z /\
  store_ok SEGS m (Z_to_bv 64 (pixes i + 20)) 4 = true /\ (forall j, (0 <= j < 4)%Z -> m (Z_to_bv 64 (pixes i + 20 + j)) <> None).
Proof.
  intros C Ar A m md s pa parr w wpl h i pixes datas vf CK HW SUB Hs1 Hs2 Hpa Hparr Lpa Lparr PM Hi.
  destruct (PM i Hi) as (Rp & Lpi & _ & _ & PX & _).
  pose proof PX as PXb. unfold PIXat in PXb. destruct PXb as (PX0 & PX1 & _).
  assert (LA : live A (Z_to_bv 64 (pixes i)) = Some 64%Z) by (apply SUB; exact Lpi).
  pose proof (blk_range C A m md _ 64 CK HW LA ltac:(lia)) as [B1 B2]. rewrite u_Z2bv in B1, B2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LA) as (_ & AL16 & _). rewrite u_Z2bv in AL16 by lia.
  pose proof CK as [T1 _ _ _ _].
  unfold GLP_WIN, CALLOC_STACK, ALLOC_STACK in Hs1.
  pose proof (round16_ge 64 ltac:(lia)) as R64.
  pose proof (round16_ge 32 ltac:(lia)) as R32.
  pose proof (round16_ge 80 ltac:(lia)) as R80.
  assert (DPA : (pixes i + 64 <= pa \/ pa + 32 <= pixes i)%Z).
  { assert (NE : Z_to_bv 64 (pixes i) <> Z_to_bv 64 pa) by (intros E; rewrite E in LA; congruence).
    destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) LA Lpa NE) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
  assert (DPR : (pixes i + 64 <= parr \/ parr + 80 <= pixes i)%Z).
  { assert (NE : Z_to_bv 64 (pixes i) <> Z_to_bv 64 parr) by (intros E; rewrite E in LA; congruence).
    destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) LA Lparr NE) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
  assert (DEF : forall j, (0 <= j < 4)%Z -> m (Z_to_bv 64 (pixes i + 20 + j)) <> None).
  { intros j Hj. apply (PIXat_defined m (pixes i) (vf i)); [exact PX|]. rewrite u_Z2bv by lia. lia. }
  split; [lia|]. split; [lia|]. split; [exact AL16|]. split; [exact DPA|]. split; [exact DPR|]. split; [|exact DEF].
  apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  exact (PIXat_defined m (pixes i) (vf i) x PX ltac:(lia) E).
Qed.

Lemma glp_rdn_same : forall (M1 M2 : word -> option byte) (a : Z) bs (x : word), (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rdn SEGS M1 (Z_to_bv 64 a) (length bs) = Some bs -> rdn SEGS M2 (Z_to_bv 64 a) (length bs) = Some bs ->
  (forall y : word, (a <= u y < a + Z.of_nat (length bs))%Z -> M1 y <> None) ->
  (forall y : word, (a <= u y < a + Z.of_nat (length bs))%Z -> M2 y <> None) ->
  (a <= u x < a + Z.of_nat (length bs))%Z -> M2 x = M1 x.
Proof.
  intros M1 M2 a bs x G0 G1 R1 R2 D1 D2 Hx. pose proof (u64_range x) as Rx.
  assert (B1 : bytes_at M1 a bs).
  { eapply rdn_bytes_at; [exact G0 | exact G1 | | exact R1]. intros j Hj. apply D1. rewrite u_Z2bv by lia. lia. }
  assert (B2 : bytes_at M2 a bs).
  { eapply rdn_bytes_at; [exact G0 | exact G1 | | exact R2]. intros j Hj. apply D2. rewrite u_Z2bv by lia. lia. }
  specialize (B1 (u x - a)%Z ltac:(lia)). specialize (B2 (u x - a)%Z ltac:(lia)).
  replace (a + (u x - a))%Z with (u x) in B1 by lia. replace (a + (u x - a))%Z with (u x) in B2 by lia.
  rewrite zbv_self in B1, B2. rewrite B1, B2. reflexivity.
Qed.

Lemma glp_keep : forall A (m MD mh ME : word -> option byte) (s c pr n0 : Z) (q x : word),
  rinv [((s - 144)%Z, 72%Z); (pr, 4%Z)] m MD -> LIVK A MD mh -> rinv [((s - 144)%Z, 72%Z); (c, 8%Z); (pr, 4%Z)] mh ME ->
  live A q = Some n0 -> (u q + n0 <= 2 ^ 64)%Z -> (u q <= u x < u q + n0)%Z ->
  (u x < s - 144)%Z -> ~ (c <= u x < c + 8)%Z -> ~ (pr <= u x < pr + 4)%Z -> ME x = m x.
Proof.
  intros A m MD mh ME s c pr n0 q x [_ R1] LK [_ R2] Lq Hq Hx Hs Hc Hp.
  pose proof (u64_range q) as Rq. pose proof (u64_range x) as Rx.
  transitivity (mh x).
  { apply R2. intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; unfold inreg; cbn [fst snd]; lia. }
  transitivity (MD x).
  { pose proof (LK q n0 (u x - u q)%Z Lq ltac:(lia)) as E.
    replace (at_ q (u x - u q)) with x in E; [exact E|].
    unfold at_. replace (u q + (u x - u q))%Z with (u x) by lia. rewrite zbv_self. reflexivity. }
  apply R1. intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; unfold inreg; cbn [fst snd]; lia.
Qed.

(* [comment removed for export] *)
Lemma glp_iter_inv : forall C Ar A A' (m MD mh ME : word -> option byte) md md' (s pa parr ls w wpl h i lines : Z) (pixes datas linesf : Z -> Z) (vf : Z -> pixv),
  Cok C -> W C A m md -> W C A' mh md' -> (c_top C - LSTK + GLP_WIN <= s)%Z -> (s <= c_top C)%Z ->
  (0 <= parr < 2 ^ 64)%Z -> live Ar (Z_to_bv 64 parr) = Some 80%Z ->
  pixa_mem10 C Ar m parr w wpl h pixes datas vf -> (0 <= i < 10)%Z -> (1 <= h)%Z ->
  (0 <= ls < 2 ^ 64)%Z -> live A (Z_to_bv 64 ls) = Some 80%Z -> live Ar (Z_to_bv 64 ls) = None -> live (c_A0 C) (Z_to_bv 64 ls) = None ->
  lset_upto C Ar A m ls wpl h linesf datas i ->
  rinv [((s - 144)%Z, 72%Z); ((pixes i + 20)%Z, 4%Z)] m MD ->
  POSTM C A (s - 80) MD mh -> lines_new C A A' mh lines (datas i) wpl h ->
  rinv [((s - 144)%Z, 72%Z); ((ls + 8 * i)%Z, 8%Z); ((pixes i + 20)%Z, 4%Z)] mh ME ->
  rdn SEGS ME (Z_to_bv 64 (ls + 8 * i)) 8 = Some (Z_to_le_bytes 8 lines) -> rdn SEGS ME (Z_to_bv 64 (pixes i + 20)) 4 = Some (Z_to_le_bytes 4 1) ->
  W C A' ME md' /\ POSTM C Ar (s - 64) m ME /\ live A' (Z_to_bv 64 ls) = Some 80%Z /\
  lset_upto C Ar A' ME ls wpl h (fun k => if (k =? i)%Z then lines else linesf k) datas (i + 1).
Proof.
  intros C Ar A A' m MD mh ME md md' s pa parr ls w wpl h i lines pixes datas linesf vf
    CK HW HW' Hs1 Hs2 Hparr Lparr PM Hi Hh Hls LAls LRls L0ls LS RI1 PM1 LN RI2 RDls RDrc.
  pose proof CK as [T1 T2 T3 T4 T5].
  pose proof (u64_range (c_sp0 C)) as RSP.
  unfold GLP_WIN, CALLOC_STACK, ALLOC_STACK in Hs1.
  pose proof (lset_sub C Ar A m ls wpl h linesf datas i LS LRls) as SUB.
  destruct LN as (Ln1 & Ln2 & Ln3 & LnA & Ln0 & LnA' & LnEQ & LnR).
  assert (SUB' : sub_live A A').
  { intros q k Lq. rewrite LnEQ; [exact Lq|]. intros E. subst q. rewrite LnA in Lq. discriminate. }
  destruct (PM i Hi) as (Rp & Lpi & L0p & RDp & PX & Pw & Ph & Pwpl & Pd & Prc & Pdata & Hd1 & Hd2).
  assert (LApi : live A (Z_to_bv 64 (pixes i)) = Some 64%Z) by (apply SUB; exact Lpi).
  assert (LA'pi : live A' (Z_to_bv 64 (pixes i)) = Some 64%Z) by (apply SUB'; exact LApi).
  assert (LA'ls : live A' (Z_to_bv 64 ls) = Some 80%Z) by (apply SUB'; exact LAls).
  pose proof (round16_ge 64 ltac:(lia)) as R64.
  pose proof (round16_ge 80 ltac:(lia)) as R80.
  pose proof (round16_ge (8 * h)%Z ltac:(lia)) as R8h.
  pose proof (blk_range C A m md _ 80 CK HW LAls ltac:(lia)) as [Bls1 Bls2]. rewrite u_Z2bv in Bls1, Bls2 by lia.
  pose proof (blk_range C A m md _ 64 CK HW LApi ltac:(lia)) as [Bp1 Bp2]. rewrite u_Z2bv in Bp1, Bp2 by lia.
  assert (Dlp : (ls + 80 <= pixes i \/ pixes i + 64 <= ls)%Z).
  { assert (NE : Z_to_bv 64 ls <> Z_to_bv 64 (pixes i)) by (intros E; rewrite E in LRls; congruence).
    destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) LAls LApi NE) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
  assert (Hln : (0 <= lines < 2 ^ 64)%Z) by lia.
  assert (NEln_ls : Z_to_bv 64 lines <> Z_to_bv 64 ls) by (intros E; rewrite E in LnA; congruence).
  assert (NEln_pi : Z_to_bv 64 lines <> Z_to_bv 64 (pixes i)) by (intros E; rewrite E in LnA; congruence).
  assert (Dnl : (lines + 8 * h <= ls \/ ls + 80 <= lines)%Z).
  { destruct (ai_live_disjoint A' mh (m_vmmaps md') _ _ _ _ (w_inv _ _ _ _ HW') LnA' LA'ls NEln_ls) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
  assert (Dnp : (lines + 8 * h <= pixes i \/ pixes i + 64 <= lines)%Z).
  { destruct (ai_live_disjoint A' mh (m_vmmaps md') _ _ _ _ (w_inv _ _ _ _ HW') LnA' LA'pi NEln_pi) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
  assert (HGls : forall y : word, (ls <= u y < ls + 80)%Z -> heap_gap C y).
  { intros y Hy. refine (proj1 (blk_byte C A m md _ 80 y CK HW LAls _)). rewrite u_Z2bv by lia. exact Hy. }
  assert (HGpi : forall y : word, (pixes i <= u y < pixes i + 64)%Z -> heap_gap C y).
  { intros y Hy. refine (proj1 (blk_byte C A m md _ 64 y CK HW LApi _)). rewrite u_Z2bv by lia. exact Hy. }
  assert (WE : W C A' ME md').
  { eapply rinv_W; [exact CK | exact HW' | exact Hs2 | exact RI2 |].
    unfold own_regions. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd].
    - left. lia.
    - right. exists (Z_to_bv 64 ls), 80%Z. rewrite u_Z2bv by lia. split; [exact LA'ls|]. split; [exact L0ls|]. lia.
    - right. exists (Z_to_bv 64 (pixes i)), 64%Z. rewrite u_Z2bv by lia. split; [exact LA'pi|]. split; [exact L0p|]. lia. }
  split; [exact WE|]. split.
  { unfold POSTM, FRM, LIVK. split.
    - intros x NG NGl NEr NH NS.
      transitivity (mh x).
      { apply (proj2 RI2). intros r Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[]]]]; unfold inreg; cbn [fst snd]; intros Hin;
          [apply NS; unfold scratch; lia | apply NG; apply HGls; lia | apply NG; apply HGpi; lia]. }
      transitivity (MD x).
      { pose proof (proj1 PM1) as F. unfold FRM in F.
        apply F; [exact NG | exact NGl | exact NEr | exact NH | intro Hsc; apply NS; unfold scratch in *; lia]. }
      apply (proj2 RI1). intros r Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[]]]; unfold inreg; cbn [fst snd]; intros Hin;
        [apply NS; unfold scratch; lia | apply NG; apply HGpi; lia].
    - intros q k j Lq Hj.
      pose proof (SUB q k Lq) as LAq.
      pose proof (blk_range C A m md q k CK HW LAq ltac:(lia)) as [Bq1 Bq2].
      assert (Ux : u (at_ q j) = (u q + j)%Z) by (unfold at_; apply u_Z2bv; lia).
      assert (Dq : (u q + k <= ls \/ ls + 80 <= u q)%Z).
      { assert (NE : q <> Z_to_bv 64 ls) by (intros E; rewrite E in Lq; congruence).
        pose proof (round16_ge k ltac:(lia)) as Rk.
        destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) LAq LAls NE) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
      assert (Hc : (pixes i + 20 <= u (at_ q j) < pixes i + 24)%Z \/ ~ (pixes i + 20 <= u (at_ q j) < pixes i + 24)%Z) by lia.
      destruct Hc as [Hc|Hc].
      + apply (glp_rdn_same m ME (pixes i + 20)%Z (Z_to_le_bytes 4 1) (at_ q j)); rewrite ?length_Z_to_le_bytes.
        * lia.
        * lia.
        * pose proof (PIX_rd_rc SEGS _ _ _ PX) as RR. rewrite Prc in RR. exact RR.
        * exact RDrc.
        * intros y Hy. apply (PIXat_defined m (pixes i) (vf i) y PX). lia.
        * intros y Hy. refine (proj1 (proj2 (blk_byte C A' ME md' _ 64 y CK WE LA'pi _))). rewrite u_Z2bv by lia. lia.
        * lia.
      + apply (glp_keep A m MD mh ME s (ls + 8 * i)%Z (pixes i + 20)%Z k q (at_ q j) RI1 (proj2 PM1) RI2 LAq); lia. }
  split; [exact LA'ls|].
  unfold lset_upto in LS |- *. destruct LS as (LSk & LSEQ & LSD). cbv beta.
  split; [|split].
  - intros k Hk. destruct (Z.eqb_spec k i) as [->|Hki]; cbv beta iota.
    + split; [exact Hln|]. split; [exact LnA'|]. split.
      { destruct (live Ar (Z_to_bv 64 lines)) eqn:E; [|reflexivity]. apply SUB in E. rewrite LnA in E. discriminate. }
      split; [exact Ln0|]. split; [intros E; apply NEln_ls; rewrite E; reflexivity|]. split; [exact RDls|].
      intros j Hj. rewrite <- (LnR j Hj). apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
      intros x Hx. apply (proj2 RI2). intros r Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[]]]]; unfold inreg; cbn [fst snd]; lia.
    + destruct (LSk k ltac:(lia)) as (Rk & LAk & LRk & L0k & NEk & RDk & LPk).
      pose proof (blk_range C A m md _ (8 * h)%Z CK HW LAk ltac:(lia)) as [Bk1 Bk2]. rewrite u_Z2bv in Bk1, Bk2 by lia.
      assert (Dkl : (linesf k + 8 * h <= ls \/ ls + 80 <= linesf k)%Z).
      { assert (NE : Z_to_bv 64 (linesf k) <> Z_to_bv 64 ls).
        { intros E. apply NEk. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. }
        destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) LAk LAls NE) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
      assert (Dkp : (linesf k + 8 * h <= pixes i \/ pixes i + 64 <= linesf k)%Z).
      { assert (NE : Z_to_bv 64 (linesf k) <> Z_to_bv 64 (pixes i)) by (intros E; rewrite E in LRk; congruence).
        destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) LAk LApi NE) as [X|X]; rewrite !u_Z2bv in X by lia; lia. }
      split; [exact Rk|]. split.
      { rewrite LnEQ; [exact LAk|]. intros E. rewrite E in LAk. congruence. }
      split; [exact LRk|]. split; [exact L0k|]. split; [exact NEk|]. split.
      { rewrite <- RDk. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
        apply (glp_keep A m MD mh ME s (ls + 8 * i)%Z (pixes i + 20)%Z 80%Z (Z_to_bv 64 ls) x RI1 (proj2 PM1) RI2 LAls); rewrite ?u_Z2bv by lia; lia. }
      intros j Hj. rewrite <- (LPk j Hj). apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
      apply (glp_keep A m MD mh ME s (ls + 8 * i)%Z (pixes i + 20)%Z (8 * h)%Z (Z_to_bv 64 (linesf k)) x RI1 (proj2 PM1) RI2 LAk); rewrite ?u_Z2bv by lia; lia.
  - intros q Hq Hk. rewrite LnEQ.
    + apply LSEQ; [exact Hq|]. intros k Hk' E. apply (Hk k ltac:(lia)). destruct (Z.eqb_spec k i); [exfalso; lia|exact E].
    + intros E. apply (Hk i ltac:(lia)). rewrite Z.eqb_refl. exact E.
  - intros k k' Hkk Hk'. destruct (Z.eqb_spec k i); [exfalso; lia|]. destruct (Z.eqb_spec k' i) as [->|Hk'i]; cbv beta iota.
    + intros E. destruct (LSk k ltac:(lia)) as (_ & LAk & _). rewrite E in LAk. rewrite LnA in LAk. discriminate.
    + apply LSD; lia.
Qed.

Lemma glp_m8 : forall p, (p mod 16 = 0)%Z -> (p mod 8 = 0)%Z.
Proof. intros p H. rewrite <- (Z.add_0_r p). apply mod16_plus_mod8; [exact H | reflexivity]. Qed.

Lemma glp_mod : forall p k d, (0 < d)%Z -> (16 mod d = 0)%Z -> (p mod 16 = 0)%Z -> (k mod d = 0)%Z -> ((p + k) mod d = 0)%Z.
Proof.
  intros p k d Hd H16 Hp Hk. apply Z.mod_divide; [lia|]. apply Z.divide_add_r.
  - apply Z.divide_trans with 16%Z; [apply Z.mod_divide; [lia | exact H16] | apply Z.mod_divide; [lia | exact Hp]].
  - apply Z.mod_divide; [lia | exact Hk].
Qed.

Lemma glp_rdD : forall (m M : word -> option byte) (s pix z : Z) (n : nat),
  rinv [((s - 144)%Z, 72%Z); ((pix + 20)%Z, 4%Z)] m M -> (0 <= z)%Z -> (z + Z.of_nat n <= 2 ^ 64)%Z ->
  (z + Z.of_nat n <= s - 144 \/ s - 72 <= z)%Z -> (z + Z.of_nat n <= pix + 20 \/ pix + 24 <= z)%Z ->
  rdn SEGS M (Z_to_bv 64 z) n = rdn SEGS m (Z_to_bv 64 z) n.
Proof.
  intros m M s pix z n RI H0 H1 H2 H3.
  apply (rinv_rdn SEGS _ m M z n RI H0 H1).
  intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
Qed.

Lemma glp_sok_blk : forall C A m md (p k a : Z) (n : nat), Cok C -> W C A m md -> live A (Z_to_bv 64 p) = Some k ->
  (0 <= p)%Z -> (p + k < 2 ^ 64)%Z -> (p <= a)%Z -> (a + Z.of_nat n <= p + k)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hp Hpk Hlo Hhi.
  apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md (Z_to_bv 64 p) k x CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E).
Qed.

Ltac glp_csc r Cr N18 N20 :=
  let CC := fresh "CC" in
  pose proof (cs_cases r Cr) as CC;
  repeat (destruct CC as [CC|CC]; [subst r; first [exfalso; apply N18; reflexivity | exfalso; apply N20; reflexivity | csr; reflexivity] |]);
  subst r; first [exfalso; apply N18; reflexivity | exfalso; apply N20; reflexivity | csr; reflexivity].

(* [comment removed for export] *)
Lemma glp_loop_W : forall (n : nat) (fx : FPState) C Ar A m md regs (s pa parr ls w wpl h i : Z) (pixes datas linesf : Z -> Z) (vf : Z -> pixv) (kR bR : Z) (S : TSet),
  Z.of_nat n = (10 - i)%Z -> (0 <= i < 10)%Z -> Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + GLP_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 4 = Z_to_bv 64 0x56270 -> getr regs 8 = Z_to_bv 64 pa -> getr regs 9 = Z_to_bv 64 ls ->
  getr regs 18 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 80 -> getr regs 20 = Z_to_bv 64 (8 * i) ->
  getr regs 21 = Z_to_bv 64 (2 ^ 64 - 1 - ls) -> getr regs 22 = Z_to_bv 64 0 ->
  (0 <= pa < 2 ^ 64)%Z -> (0 <= parr < 2 ^ 64)%Z -> live Ar (Z_to_bv 64 pa) = Some 32%Z -> live Ar (Z_to_bv 64 parr) = Some 80%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) -> rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  pixa_mem10 C Ar m parr w wpl h pixes datas vf -> (1 <= h <= 20000)%Z -> (1 <= wpl <= 20000)%Z ->
  (0 <= ls < 2 ^ 64)%Z -> live A (Z_to_bv 64 ls) = Some 80%Z -> live Ar (Z_to_bv 64 ls) = None -> live (c_A0 C) (Z_to_bv 64 ls) = None ->
  lset_upto C Ar A m ls wpl h linesf datas i ->
  aroom A (m_vmmaps md) kR bR -> (Z.of_nat n <= kR)%Z -> (Z.of_nat n * alloc_margin (8 * h) <= bR)%Z ->
  (forall A' m' vm' regs' linesf', W C A' m' (with_vmmaps vm' md) -> POSTM C Ar (s - 64) m m' ->
     getr regs' 2 = Z_to_bv 64 (s - 80) -> getr regs' 10 = Z_to_bv 64 ls ->
     (forall r, AllocIface.callee_saved r -> r <> 18%bv -> r <> 20%bv -> getr regs' r = getr regs r) ->
     lset_upto C Ar A' m' ls wpl h linesf' datas 10 -> live A' (Z_to_bv 64 ls) = Some 80%Z ->
     aroom A' vm' (kR - Z.of_nat n) (bR - Z.of_nat n * alloc_margin (8 * h)) ->
     realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 0x18ea0) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 0x18da8) m al_rom) md) S.
Proof.
  intros n. induction n as [|n IH];
    intros fx C Ar A m md regs s pa parr ls w wpl h i pixes datas linesf vf kR bR S
      Hn Hi CK HW Hs16 Hlo Hhi H2 H4 H8 H9 H18 H19 H20 H21 H22 Hpa Hparr Lpa Lparr Rpa Rpa16 PM Hh Hwpl
      Hls Lls LlsR Lls0 LS AR HkR HbR HK.
  { lia. }
  rewrite Nat2Z.inj_succ in Hn, HkR, HbR, HK.
  pose proof CK as [T1 T2 T3 T4 T5].
  assert (LS0 : (0 < LSTK)%Z) by (unfold LSTK; lia).
  pose proof Hlo as Hlo'. unfold GLP_WIN, CALLOC_STACK, ALLOC_STACK in Hlo'.
  pose proof (round16_ge 64%Z ltac:(lia)) as R64.
  pose proof (round16_ge 80%Z ltac:(lia)) as R80.
  pose proof (alloc_margin_ge (8 * h)%Z ltac:(lia)) as AM0.
  assert (NM : (0 <= Z.of_nat n * alloc_margin (8 * h))%Z) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (lset_sub C Ar A m ls wpl h linesf datas i LS LlsR) as SUB.
  pose proof (SUB _ _ Lpa) as LpaA. pose proof (SUB _ _ Lparr) as LparrA.
  pose proof (blk_range C A m md _ 32%Z CK HW LpaA ltac:(lia)) as [Bpa1 Bpa2].
  pose proof (blk_range C A m md _ 80%Z CK HW LparrA ltac:(lia)) as [Bpr1 Bpr2].
  pose proof (blk_range C A m md _ 80%Z CK HW Lls ltac:(lia)) as [Bls1 Bls2].
  rewrite u_Z2bv in Bpa1, Bpa2, Bpr1, Bpr2, Bls1, Bls2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LpaA) as (_ & ALpa & _).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LparrA) as (_ & ALparr & _).
  rewrite u_Z2bv in ALpa, ALparr by lia.
  pose proof (glp_m8 s Hs16) as Hs8.
  destruct (glp_member C Ar A m md s pa parr w wpl h i pixes datas vf CK HW SUB Hlo Hhi Hpa Hparr LpaA LparrA PM Hi)
    as (Gp0 & Gp1 & Gp16 & Dpa & Dparr & SOKrc & _).
  destruct (PM i Hi) as (Rpx & Lpx & Lpx0 & RDpx & PX & _ & Eh & Ewpl & _ & Erc & Edata & Dat1 & Dat2).
  pose proof (SUB _ _ Lpx) as LpxA.
  assert (RRC1 : rdn SEGS m (Z_to_bv 64 (pixes i + 20)) 4 = Some (Z_to_le_bytes 4 1))
    by (rewrite (PIX_rd_rc SEGS m _ _ PX), Erc; reflexivity).
  pose proof (W_sok_win C A m md (s - 144)%Z 144%nat CK HW ltac:(lia) ltac:(lia)) as SOKw.
  pose proof (gl_D al_rom fx regs m s pa parr i (pixes i) ltac:(lia) ltac:(lia) (glp_m8 pa ALpa) ltac:(lia) ltac:(lia) (glp_m8 parr ALparr) ltac:(lia) Hi ltac:(lia) ltac:(lia)
                Gp16 Dpa Dparr Rpa Rpa16 RDpx RRC1 SOKw SOKrc H2 H8 H18) as RUN1.
  apply (rz_reach SEGS _ md _ S (w_pure _ _ _ _ HW) RUN1).
  intros fin (regs1 & MD & -> & RI1 & RSP & RRC2 & R1 & R2a & R10a & R11a & AG1).
  assert (HWD : W C A MD md).
  { eapply rinv_W; [exact CK | exact HW | exact Hhi | exact RI1 |].
    unfold own_regions. constructor; [|constructor; [|constructor]]; cbn [fst snd].
    - left. lia.
    - right. exists (Z_to_bv 64 (pixes i)), 64%Z. rewrite u_Z2bv by lia. split; [exact LpxA|]. split; [exact Lpx0|]. lia. }
  assert (RDh : rdn SEGS MD (Z_to_bv 64 (pixes i + 4)) 4 = Some (Z_to_le_bytes 4 h)).
  { rewrite (glp_rdD m MD s (pixes i) (pixes i + 4)%Z 4%nat RI1) by lia. rewrite (PIX_rd_h SEGS m _ _ PX), Eh. reflexivity. }
  assert (RDw : rdn SEGS MD (Z_to_bv 64 (pixes i + 16)) 4 = Some (Z_to_le_bytes 4 wpl)).
  { rewrite (glp_rdD m MD s (pixes i) (pixes i + 16)%Z 4%nat RI1) by lia. rewrite (PIX_rd_wpl SEGS m _ _ PX), Ewpl. reflexivity. }
  assert (RDd : rdn SEGS MD (Z_to_bv 64 (pixes i + 56)) 8 = Some (Z_to_le_bytes 8 (datas i))).
  { rewrite (glp_rdD m MD s (pixes i) (pixes i + 56)%Z 8%nat RI1) by lia. rewrite (PIX_rd_data SEGS m _ _ PX), Edata. reflexivity. }
  assert (Hs80 : ((s - 80) mod 16 = 0)%Z) by (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity).
  assert (RET : ret_ok (getr regs1 1)) by (rewrite R1; red; apply bv_eq; reflexivity).
  refine (pixGetLinePtrs_W fx C A MD md regs1 (s - 80)%Z (pixes i) h wpl (datas i) (getr regs1 1) S CK HWD R2a Hs80
            ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) eq_refl RET ltac:(csr; reflexivity) R10a R11a LpxA Rpx Hh Hwpl Dat1 Dat2
            RDh RDw RDd kR bR AR ltac:(lia) ltac:(lia) _).
  intros A' mh vm' regs' lines HWh CSK PMh R10b LN ARh.
  rewrite R1.
  pose proof LN as (Ln1 & Ln2 & Ln16 & LnA & Ln0 & LnA' & LnEQ & LnR).
  assert (LlsA' : live A' (Z_to_bv 64 ls) = Some 80%Z).
  { rewrite LnEQ; [exact Lls|]. intros E. rewrite E, LnA in Lls. discriminate. }
  assert (LpxA' : live A' (Z_to_bv 64 (pixes i)) = Some 64%Z).
  { rewrite LnEQ; [exact LpxA|]. intros E. rewrite E, LnA in LpxA. discriminate. }
  assert (DPL : (pixes i + 64 <= ls \/ ls + 80 <= pixes i)%Z).
  { assert (NE : Z_to_bv 64 (pixes i) <> Z_to_bv 64 ls) by (intros E; rewrite E, LlsR in Lpx; discriminate).
    destruct (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) LpxA Lls NE) as [X|X];
      rewrite !u_Z2bv in X by lia; lia. }
  assert (RSPh : rdn SEGS mh (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 (pixes i))).
  { rewrite (FRM_rdn16 C (s - 80)%Z MD mh (s - 80)%Z 8%nat CK (proj1 PMh)) by lia. exact RSP. }
  assert (RRCh : rdn SEGS mh (Z_to_bv 64 (pixes i + 20)) 4 = Some (Z_to_le_bytes 4 2)).
  { rewrite (LIVK_rdn A MD mh (Z_to_bv 64 (pixes i)) 64%Z (pixes i + 20)%Z 4%nat (proj2 PMh) LpxA) by (rewrite u_Z2bv by lia; lia).
    exact RRC2. }
  pose proof (W_sok_win C A' mh _ (s - 144)%Z 144%nat CK HWh ltac:(lia) ltac:(lia)) as SOK1.
  pose proof (glp_sok_blk C A' mh _ (pixes i) 64%Z (pixes i + 20)%Z 4%nat CK HWh LpxA' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SOK2.
  pose proof (glp_sok_blk C A' mh _ ls 80%Z (ls + 8 * i)%Z 8%nat CK HWh LlsA' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SOK3.
  assert (Hln : (0 <= lines < 2 ^ 47)%Z) by lia.
  destruct (Z.eq_dec (i + 1)%Z 10%Z) as [E10|E10].
  - pose proof (gl_E_last al_rom fx regs' mh s (ls + 8 * i)%Z (pixes i) lines i ls ltac:(lia) Hs8 ltac:(lia) ltac:(lia) Gp0 ltac:(lia) Gp16 Hln Hi E10
                  ltac:(lia) eq_refl ltac:(lia) RSPh RRCh SOK1 SOK2 SOK3 ltac:(csr; reflexivity) R10b ltac:(csr; reflexivity) ltac:(csr; reflexivity)
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as RUN2.
    apply (rz_reach SEGS _ (with_vmmaps vm' md) _ S (w_pure _ _ _ _ HWh) RUN2).
    intros fin (regs2 & ME & -> & RI3 & RDL & RDRC & R2c & R10c & AG3).
    destruct (glp_iter_inv C Ar A A' m MD mh ME md (with_vmmaps vm' md) s pa parr ls w wpl h i lines pixes datas linesf vf
                CK HW HWh Hlo Hhi Hparr Lparr PM Hi ltac:(lia) Hls Lls LlsR Lls0 LS RI1 PMh LN RI3 RDL RDRC)
      as (HWE & PME & LlsE & LSE).
    assert (En : n = 0%nat) by lia. subst n.
    replace (i + 1)%Z with 10%Z in LSE by lia.
    refine (HK A' ME vm' regs2 _ HWE PME R2c R10c _ LSE LlsE _).
    + intros r Cr N18 N20. glp_csc r Cr N18 N20.
    + change (Z.succ (Z.of_nat 0)) with 1%Z. rewrite Z.mul_1_l. exact ARh.
  - pose proof (gl_E_more al_rom fx regs' mh s (ls + 8 * i)%Z (pixes i) lines i ls ltac:(lia) Hs8 ltac:(lia) ltac:(lia) Gp0 ltac:(lia) Gp16 Hln Hi ltac:(lia)
                  ltac:(lia) eq_refl ltac:(lia) RSPh RRCh SOK1 SOK2 SOK3 ltac:(csr; reflexivity) R10b ltac:(csr; reflexivity) ltac:(csr; reflexivity)
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as RUN2.
    apply (rz_reach SEGS _ (with_vmmaps vm' md) _ S (w_pure _ _ _ _ HWh) RUN2).
    intros fin (regs2 & ME & -> & RI3 & RDL & RDRC & R2c & R18c & R20c & AG3).
    destruct (glp_iter_inv C Ar A A' m MD mh ME md (with_vmmaps vm' md) s pa parr ls w wpl h i lines pixes datas linesf vf
                CK HW HWh Hlo Hhi Hparr Lparr PM Hi ltac:(lia) Hls Lls LlsR Lls0 LS RI1 PMh LN RI3 RDL RDRC)
      as (HWE & PME & LlsE & LSE).
    assert (RpaE : rdn SEGS ME (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10)).
    { rewrite (LIVK_rdn Ar m ME (Z_to_bv 64 pa) 32%Z pa 4%nat (proj2 PME) Lpa) by (rewrite u_Z2bv by lia; lia). exact Rpa. }
    assert (Rpa16E : rdn SEGS ME (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr)).
    { rewrite (LIVK_rdn Ar m ME (Z_to_bv 64 pa) 32%Z (pa + 16)%Z 8%nat (proj2 PME) Lpa) by (rewrite u_Z2bv by lia; lia). exact Rpa16. }
    pose proof (pixa_mem10_keep C Ar m ME parr w wpl h pixes datas vf ltac:(lia) ltac:(lia) PM Lparr (proj2 PME)) as PME10.
    refine (IH fx C Ar A' ME (with_vmmaps vm' md) regs2 s pa parr ls w wpl h (i + 1)%Z pixes datas
              (fun k => if (k =? i)%Z then lines else linesf k) vf (kR - 1)%Z (bR - alloc_margin (8 * h))%Z S
              ltac:(lia) ltac:(lia) CK HWE Hs16 Hlo Hhi R2c ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) R18c
              ltac:(csr; reflexivity) R20c ltac:(csr; reflexivity) ltac:(csr; reflexivity)
              Hpa Hparr Lpa Lparr RpaE Rpa16E PME10 Hh Hwpl Hls LlsE LlsR Lls0 LSE
              ltac:(rewrite with_vmmaps_vmmaps; exact ARh) ltac:(lia) ltac:(lia) _).
    intros A2 m2 vm2 regs3 linesf2 HW2 PM2 R2d R10d HCS3 LS2 L2 AR2.
    rewrite with_vmmaps_twice in HW2. rewrite with_vmmaps_twice.
    refine (HK A2 m2 vm2 regs3 linesf2 HW2 (POSTM_trans _ _ _ _ _ _ PME PM2) R2d R10d _ LS2 L2 _).
    + intros r Cr N18 N20. rewrite (HCS3 r Cr N18 N20). glp_csc r Cr N18 N20.
    + replace (kR - Z.succ (Z.of_nat n))%Z with (kR - 1 - Z.of_nat n)%Z by lia.
      replace (bR - Z.succ (Z.of_nat n) * alloc_margin (8 * h))%Z
        with (bR - alloc_margin (8 * h) - Z.of_nat n * alloc_margin (8 * h))%Z by lia.
      exact AR2.
Qed.

(* [comment removed for export] *)
Definition lineset_new (C : lctx) (A A' : AS) (m' : word -> option byte) (ls wpl h : Z) (linesf datas : Z -> Z) : Prop :=
  (0 <= ls < 2 ^ 64)%Z /\ live A (Z_to_bv 64 ls) = None /\ live (c_A0 C) (Z_to_bv 64 ls) = None /\ live A' (Z_to_bv 64 ls) = Some 80%Z /\
  lset_upto C A A' m' ls wpl h linesf datas 10.

Ltac glp_inl := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn [fst snd]; lia|]); destruct Hr.
Ltac glp_ne := let E := fresh "E" in intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Ltac glp_loc := unfold local_regions; repeat apply Forall_cons; try apply Forall_nil; hnf; left; cbn [fst snd]; lia.

Lemma glp_pvd_mem : forall C A m md (s pa parr w wpl h : Z) pixes datas vf,
  Cok C -> W C A m md -> (c_top C - LSTK + GLP_WIN <= s)%Z -> (s <= c_top C)%Z ->
  (0 <= pa < 2 ^ 64)%Z -> (0 <= parr < 2 ^ 64)%Z -> live A (Z_to_bv 64 pa) = Some 32%Z -> live A (Z_to_bv 64 parr) = Some 80%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) -> rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  pixa_mem10 C A m parr w wpl h pixes datas vf -> pvd_mem m (s - 80) pa parr w h pixes.
Proof.
  intros C A m md s pa parr w wpl h pixes datas vf CK HW Hs1 Hs2 Hpa Hparr Lpa Lparr Rc Ra PM.
  pose proof CK as [T1 _ _ _ _].
  pose proof Hs1 as Hs1'. unfold GLP_WIN, CALLOC_STACK, ALLOC_STACK in Hs1'.
  pose proof (blk_range C A m md _ 32 CK HW Lpa ltac:(lia)) as [Ba1 Ba2]. rewrite u_Z2bv in Ba1, Ba2 by lia.
  pose proof (blk_range C A m md _ 80 CK HW Lparr ltac:(lia)) as [Bb1 Bb2]. rewrite u_Z2bv in Bb1, Bb2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpa) as (_ & Apa & _).
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lparr) as (_ & Aparr & _).
  rewrite u_Z2bv in Apa, Aparr by lia.
  destruct (PM 0%Z ltac:(lia)) as (_ & _ & _ & _ & PX0 & Ew0 & Eh0 & _).
  destruct PX0 as (_ & _ & WF0 & _). destruct WF0 as [Rw Rh]. rewrite Ew0 in Rw. rewrite Eh0 in Rh.
  unfold pvd_mem.
  split; [lia|]. split; [lia|]. split; [exact (glp_m8 pa Apa)|]. split; [lia|]. split; [lia|]. split; [exact (glp_m8 parr Aparr)|].
  split; [lia|]. split; [lia|].
  split; [exact Rc|]. split; [exact Ra|].
  intros i Hi.
  destruct (glp_member C A A m md s pa parr w wpl h i pixes datas vf CK HW (sub_live_refl A) Hs1 Hs2 Hpa Hparr Lpa Lparr PM Hi) as (_ & _ & G3 & G4 & G5 & G6 & G7).
  destruct (PM i Hi) as (Rp & Lpi & _ & RD & PX & Ew & Eh & _ & Ed & Erc & _).
  pose proof (blk_range C A m md _ 64 CK HW Lpi ltac:(lia)) as [Bp1 Bp2]. rewrite u_Z2bv in Bp1, Bp2 by lia.
  split; [lia|]. split; [lia|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|]. split; [exact RD|].
  split; [rewrite (PIX_rd_w SEGS _ _ _ PX), Ew; reflexivity|].
  split; [rewrite (PIX_rd_h SEGS _ _ _ PX), Eh; reflexivity|].
  split; [rewrite (PIX_rd_d SEGS _ _ _ PX), Ed; reflexivity|].
  split; [rewrite (PIX_rd_rc SEGS _ _ _ PX), Erc; reflexivity|].
  split; [exact G7 | exact G6].
Qed.

Lemma pixaGetLinePtrs_W : forall (fx : FPState) C A m md regs (s pa parr w wpl h : Z) (pixes datas : Z -> Z) (vf : Z -> pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GLP_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> getr regs 10 = Z_to_bv 64 pa -> getr regs 11 = Z_to_bv 64 0 ->
  (0 <= pa < 2 ^ 64)%Z -> (0 <= parr < 2 ^ 64)%Z -> live A (Z_to_bv 64 pa) = Some 32%Z -> live A (Z_to_bv 64 parr) = Some 80%Z ->
  rdn SEGS m (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10) -> rdn SEGS m (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr) ->
  pixa_mem10 C A m parr w wpl h pixes datas vf -> (1 <= h <= 20000)%Z -> (1 <= wpl <= 20000)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (11 <= kR)%Z -> (alloc_margin 80 + 10 * alloc_margin (8 * h) <= bR)%Z ->
  (forall A' m' vm' regs' (ls : Z) (linesf : Z -> Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 ls -> lineset_new C A A' m' ls wpl h linesf datas ->
     aroom A' vm' (kR - 11) (bR - alloc_margin 80 - 10 * alloc_margin (8 * h)) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 0x18d08) m al_rom) md) S.
Proof.
  intros fx C A m md regs s pa parr w wpl h pixes datas vf ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hpa Hparr Lpa Lparr Rc Ra PM Hh Hwpl kR bR HRM HkR HbR HK.
  pose proof (glp_pvd_mem C A m md s pa parr w wpl h pixes datas vf CK HW Hlo Hhi Hpa Hparr Lpa Lparr Rc Ra PM) as PVD0.
  pose proof CK as [T1 T2 T3 T4 T5]. pose proof LSTK_val as HLS.
  pose proof Hlo as Hlo'. unfold GLP_WIN, CALLOC_STACK, ALLOC_STACK in Hlo'.
  pose proof (blk_range C A m md _ 32 CK HW Lpa ltac:(lia)) as [Ba1 Ba2]. rewrite u_Z2bv in Ba1, Ba2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpa) as (_ & ALpa & _). rewrite u_Z2bv in ALpa by lia.
  pose proof (alloc_margin_ge (8 * h) ltac:(lia)) as AMh.
  pose proof (gl_A al_rom fx regs m s pa ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 80)%Z 80 CK HW ltac:(lia) ltac:(lia)) H2 H10 H11) as R1.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW) | exact R1 |]. clear R1.
  intros fin (r1 & M1 & -> & RV1 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & Q1 & Q2 & Q10 & Q11 & Q12 & Q8 & Q9 & AG1).
  rewrite H1 in C1.
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (apply (rinv_WP2 C A A m md M1 _ s CK HW (sub_live_refl A) Hhi RV1); glp_loc).
  destruct WP1 as [HW1 PM1].
  assert (RO1 : ret_ok (getr r1 1)) by (rewrite Q1; red; apply bv_eq; reflexivity).
  pose proof (pvd_mem_keep m M1 (s - 80)%Z pa parr w h pixes _ PVD0 RV1 ltac:(lia) ltac:(glp_inl)) as PVD1.
  assert (Hs80 : ((s - 80) mod 8 = 0)%Z).
  { replace (s - 80)%Z with (s + (-80))%Z by lia. apply glp_mod; [lia | reflexivity | exact Hs16 | reflexivity]. }
  assert (Hs68 : ((s - 68) mod 4 = 0)%Z).
  { replace (s - 68)%Z with (s + (-68))%Z by lia. apply glp_mod; [lia | reflexivity | exact Hs16 | reflexivity]. }
  pose proof (pvd_run al_rom fx r1 M1 (s - 80)%Z pa parr (s - 68)%Z w h pixes (getr r1 1) ltac:(lia) Hs80 ltac:(lia) ltac:(lia) Hs68 PVD1
    (W_sok_win C A M1 md (s - 80 - 192)%Z 192 CK HW1 ltac:(lia) ltac:(lia))
    (W_sok_win C A M1 md (s - 68)%Z 4 CK HW1 ltac:(lia) ltac:(lia)) eq_refl RO1 Q2 Q10 Q11 Q12) as R2.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW1) | exact R2 |]. clear R2.
  intros fin (r2 & M2 & -> & RV2 & D68 & P10 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & AG2).
  unfold PVA in AG2. rewrite Q1.
  assert (WP2 : W C A M2 md /\ POSTM C A s M1 M2) by (apply (rinv_WP2 C A A M1 md M2 _ s CK HW1 (sub_live_refl A) Hhi RV2); glp_loc).
  destruct WP2 as [HW2 PM2].
  assert (RcM2 : rdn SEGS M2 (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10)).
  { rewrite (rinv_rdn SEGS _ _ _ pa 4 RV2) by (try lia; glp_inl). rewrite (rinv_rdn SEGS _ _ _ pa 4 RV1) by (try lia; glp_inl). exact Rc. }
  pose proof (gl_B al_rom fx r2 M2 s pa ltac:(lia) ltac:(lia) ltac:(rewrite <- (Z.add_0_r pa); apply mod16_plus_mod8; [exact ALpa | reflexivity])
    ltac:(lia) D68 RcM2 P2 ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as R3.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW2) | exact R3 |]. clear R3.
  intros fin (r3 & M3 & -> & -> & B1 & B10 & B11 & B19 & AG3).
  assert (RO3 : ret_ok (getr r3 1)) by (rewrite B1; red; apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M2 md r3 10%Z 8%Z kR bR (getr r3 1) (s - 80)%Z S CK HW2 B10 B11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM ltac:(lia) ltac:(change (10 * 8)%Z with 80%Z; lia) ltac:(unfold ROOM_NMAX; lia)
           eq_refl RO3 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r4 res HWa Hres CS4 Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMc HRM1.
  rewrite B1. change (10 * 8)%Z with 80%Z in *.
  pose proof (u64_range res) as Hru.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (ls := u res) in *. rewrite Eres in Hres, L0, L1, L00, LEQ. clearbody ls.
  pose proof (blk_range C A1 m1 _ _ 80 CK HWa L1 ltac:(lia)) as [Bl1 Bl2]. rewrite u_Z2bv in Bl1, Bl2 by lia.
  assert (PMc' : POSTM C A s m m1).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PM2|]. eapply POSTM_mono; [|exact PMc]; lia. }
  pose proof (proj2 PMc') as LK1.
  pose proof (gl_C al_rom fx r4 m1 s ls ltac:(lia) ltac:(lia) ltac:(rewrite <- (Z.add_0_r ls); apply mod16_plus_mod8; [exact AL16 | reflexivity])
    ltac:(csr; reflexivity) Hres ltac:(csr; reflexivity)) as R5.
  eapply rz_reach; [exact (w_pure _ _ _ _ HWa) | exact R5 |]. clear R5.
  intros fin (r5 & M5 & -> & -> & G9 & G18 & G19 & G20 & G21 & G22 & AG5).
  assert (LS0 : lset_upto C A A1 m1 ls wpl h (fun _ => 0%Z) datas 0).
  { split; [intros k Hk; lia|]. split; [|intros k k' Hk Hk'; lia]. intros q Hq _. apply LEQ. exact Hq. }
  assert (RD1 : rdn SEGS m1 (Z_to_bv 64 pa) 4 = Some (Z_to_le_bytes 4 10)).
  { rewrite (LIVK_rdn A m m1 (Z_to_bv 64 pa) 32 pa 4 LK1 Lpa) by (rewrite ?u_Z2bv by lia; lia). exact Rc. }
  assert (RD2 : rdn SEGS m1 (Z_to_bv 64 (pa + 16)) 8 = Some (Z_to_le_bytes 8 parr)).
  { rewrite (LIVK_rdn A m m1 (Z_to_bv 64 pa) 32 (pa + 16) 8 LK1 Lpa) by (rewrite ?u_Z2bv by lia; lia). exact Ra. }
  pose proof (blk_range C A m md _ 80 CK HW Lparr ltac:(lia)) as [Bb1 Bb2]. rewrite u_Z2bv in Bb1, Bb2 by lia.
  pose proof (pixa_mem10_keep C A m m1 parr w wpl h pixes datas vf ltac:(lia) ltac:(lia) PM Lparr LK1) as PMm1.
  apply (glp_loop_W 10%nat fx C A A1 m1 (with_vmmaps vm1 md) r5 s pa parr ls w wpl h 0%Z pixes datas (fun _ => 0%Z) vf (kR - 1)%Z (bR - alloc_margin 80)%Z S
    ltac:(reflexivity) ltac:(lia) CK HWa Hs16 Hlo Hhi ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) G9 G18 G19 G20 G21 G22
    Hpa Hparr Lpa Lparr RD1 RD2 PMm1 Hh Hwpl Hru L1 L0 L00 LS0 HRM1 ltac:(lia) ltac:(lia)).
  intros A2 m2 vm2 r6 linesf HW3 PMd Y2 Y10 YCS LS10 L2 HRM2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (KEEPS : forall k, (8 <= k <= 64)%Z -> rdn SEGS m2 (Z_to_bv 64 (s - k)) 8 = rdn SEGS M1 (Z_to_bv 64 (s - k)) 8).
  { intros k Hk.
    rewrite (FRM_rdn16 C (s - 64)%Z m1 m2 (s - k)%Z 8 CK (proj1 PMd)) by lia.
    rewrite (FRM_rdn16 C (s - 80)%Z M2 m1 (s - k)%Z 8 CK (proj1 PMc)) by lia.
    apply (rinv_rdn SEGS _ _ _ (s - k)%Z 8 RV2); [lia | lia | glp_inl]. }
  assert (F1 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (rewrite KEEPS by lia; exact C1).
  assert (F8 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (rewrite KEEPS by lia; exact C2).
  assert (F9 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (rewrite KEEPS by lia; exact C3).
  assert (F18 : rdn SEGS m2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))) by (rewrite KEEPS by lia; exact C4).
  assert (F19 : rdn SEGS m2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19))) by (rewrite KEEPS by lia; exact C5).
  assert (F20 : rdn SEGS m2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20))) by (rewrite KEEPS by lia; exact C6).
  assert (F21 : rdn SEGS m2 (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21))) by (rewrite KEEPS by lia; exact C7).
  assert (F22 : rdn SEGS m2 (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22))) by (rewrite KEEPS by lia; exact C8).
  pose proof (gl_F al_rom fx r6 m2 s ret ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
    ltac:(lia) Hret eq_refl F1 F8 F9 F18 F19 F20 F21 F22 Y2) as R7.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW3) | exact R7 |]. clear R7.
  intros fin (r7 & M7 & -> & -> & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & AG7).
  assert (RR6 : forall x, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr r6 x = getr r5 x).
  { intros x Hx. cbn [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [apply YCS; [glp_cs | glp_ne | glp_ne]|]). destruct Hx. }
  assert (PMfin : POSTM C A s m m2) by (eapply POSTM_trans; [exact PMc'|]; eapply POSTM_mono; [|exact PMd]; lia).
  apply (HK A2 m2 vm2 r7 ls linesf HW3).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PMfin.
  - csr; reflexivity.
  - unfold lineset_new. split; [exact Hru|]. split; [exact L0|]. split; [exact L00|]. split; [exact L2 | exact LS10].
  - change (Z.of_nat 10) with 10%Z in HRM2. replace (kR - 11)%Z with (kR - 1 - 10)%Z by lia. exact HRM2.
Qed.
End GLPW.
