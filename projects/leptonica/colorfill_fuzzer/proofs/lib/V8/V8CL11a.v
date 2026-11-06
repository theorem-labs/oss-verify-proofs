(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRecs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptSlots.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptStderr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptBoxa.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptPtra.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptPixa.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptRoom.
Module V8LeptCf.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRecs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptSlots.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptStderr.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBoxa.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptPtra.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptPixa.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition cf_flds (pix tw th ba naa dnaa px : Z) : list fld :=
  [(8%nat, pix); (8%nat, 0); (4%nat, 1); (4%nat, 1); (4%nat, tw); (4%nat, th); (4%nat, 0); (4%nat, 0);
   (8%nat, ba); (8%nat, 0); (8%nat, 0); (8%nat, naa); (8%nat, dnaa); (8%nat, px)].

Section Cf.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma live_apart : forall (A B : AS) (x y : word) k, sub_live A B -> live A x = Some k -> live B y = None -> x <> y.
Proof. intros A B x y k SUB Lx Ly ->. pose proof (SUB _ _ Lx). congruence. Qed.

Record cfo := CFO {
  o_cf : Z; o_pix : Z; o_tw : Z; o_th : Z;
  o_ba : Z; o_nb : Z; o_barr : Z; o_b0 : Z;
  o_naa : Z; o_narr : Z; o_dnaa : Z; o_darr : Z;
  o_px : Z; o_parr : Z; o_pba : Z; o_pbarr : Z;
  o_B1 : AS; o_B2 : AS; o_B3 : AS; o_B4 : AS; o_B5 : AS }.

Definition cf_ok (C : lctx) (A0 A : AS) (m : word -> option byte) (v : pixv) (o : cfo) : Prop :=
  RECat m (o_cf o) (cf_flds (o_pix o) (o_tw o) (o_th o) (o_ba o) (o_naa o) (o_dnaa o) (o_px o)) /\
  live A (Z_to_bv 64 (o_cf o)) = Some 88 /\ live (c_A0 C) (Z_to_bv 64 (o_cf o)) = None /\
  PIXat m (o_pix o) v /\ p_rc v = 2 /\ (o_pix o mod 16 = 0) /\
  live A (Z_to_bv 64 (o_pix o)) = Some 64 /\ live (c_A0 C) (Z_to_bv 64 (o_pix o)) = None /\
  (o_ba o = 0 \/ (boxa_at C A m (o_ba o) (o_nb o) 1 (o_barr o) (o_b0 o) /\ o_barr o <> 0 /\ (o_nb o = 0 \/ o_nb o = 1))) /\
  (o_naa o = 0 \/ (ptra_at C A m (o_naa o) 1 (o_narr o) /\ o_narr o <> 0)) /\
  (o_dnaa o = 0 \/ (ptra_at C A m (o_dnaa o) 1 (o_darr o) /\ o_darr o <> 0)) /\
  (o_px o = 0 \/ pixa_at C A m (o_px o) 20 (o_parr o) (o_pba o) 20 (o_pbarr o)) /\
  (* [comment removed for export] *)
  sub_live A0 (o_B1 o) /\ sub_live (o_B1 o) (o_B2 o) /\ sub_live (o_B2 o) (o_B3 o) /\ sub_live (o_B3 o) (o_B4 o) /\
  sub_live (o_B4 o) (o_B5 o) /\ sub_live (o_B5 o) A /\
  live A0 (Z_to_bv 64 (o_pix o)) = Some 64 /\
  (o_ba o <> 0 -> live A0 (Z_to_bv 64 (o_ba o)) = None /\ live A0 (Z_to_bv 64 (o_barr o)) = None /\
                  live (o_B1 o) (Z_to_bv 64 (o_ba o)) = Some 24 /\ live (o_B1 o) (Z_to_bv 64 (o_barr o)) = Some 8) /\
  (o_ba o <> 0 -> o_nb o = 1 -> live (o_B1 o) (Z_to_bv 64 (o_b0 o)) = None /\ live (o_B2 o) (Z_to_bv 64 (o_b0 o)) = Some 20) /\
  live (o_B2 o) (Z_to_bv 64 (o_cf o)) = None /\ live (o_B3 o) (Z_to_bv 64 (o_cf o)) = Some 88 /\
  (o_naa o <> 0 -> live (o_B3 o) (Z_to_bv 64 (o_naa o)) = None /\ live (o_B3 o) (Z_to_bv 64 (o_narr o)) = None /\
                   live (o_B4 o) (Z_to_bv 64 (o_naa o)) = Some 16 /\ live (o_B4 o) (Z_to_bv 64 (o_narr o)) = Some 8) /\
  (o_dnaa o <> 0 -> live (o_B4 o) (Z_to_bv 64 (o_dnaa o)) = None /\ live (o_B4 o) (Z_to_bv 64 (o_darr o)) = None /\
                    live (o_B5 o) (Z_to_bv 64 (o_dnaa o)) = Some 16 /\ live (o_B5 o) (Z_to_bv 64 (o_darr o)) = Some 8) /\
  (o_px o <> 0 -> live (o_B5 o) (Z_to_bv 64 (o_px o)) = None /\ live (o_B5 o) (Z_to_bv 64 (o_parr o)) = None /\
                  live (o_B5 o) (Z_to_bv 64 (o_pba o)) = None /\ live (o_B5 o) (Z_to_bv 64 (o_pbarr o)) = None).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition keeps (A A' : AS) (m m' : word -> option byte) (q : Z) : Prop :=
  forall k, live A (Z_to_bv 64 q) = Some k -> live A' (Z_to_bv 64 q) = Some k /\ (q + k <= 2 ^ 64)%Z /\ forall x : word, q <= u x < q + k -> m' x = m x.

Lemma keeps_bound : forall C A m md q k, W C A m md -> live A (Z_to_bv 64 q) = Some k -> (0 <= q < 2 ^ 64)%Z -> (q + k <= 2 ^ 64)%Z.
Proof.
  intros C A m md q k HW L Hq.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L) as (Hk0 & _ & TOP & _). pose proof (round16_ge k Hk0).
  pose proof (alloc_top_lt (m_vmmaps md)) as T. unfold two_pow_64 in T. rewrite u_Z2bv in TOP by lia. lia.
Qed.

Lemma keeps_refl : forall C A m md q, W C A m md -> (0 <= q < 2 ^ 64)%Z -> keeps A A m m q.
Proof. intros C A m md q HW Hq k L. split; [exact L|]. split; [exact (keeps_bound C A m md q k HW L Hq) | intros; reflexivity]. Qed.

Lemma keeps_trans : forall A1 A2 A3 m1 m2 m3 q, keeps A1 A2 m1 m2 q -> keeps A2 A3 m2 m3 q -> keeps A1 A3 m1 m3 q.
Proof.
  intros A1 A2 A3 m1 m2 m3 q K1 K2 k L. destruct (K1 k L) as (L2 & B & M2). destruct (K2 k L2) as (L3 & _ & M3).
  split; [exact L3|]. split; [exact B|]. intros x Hx. rewrite (M3 x Hx). exact (M2 x Hx).
Qed.

(* [comment removed for export] *)
Lemma keeps_step : forall C A A' m m' md' (s pp c q : Z) kc, Cok C -> W C A' m' md' ->
  POSTD C A' s pp m m' -> live A' (Z_to_bv 64 c) = Some kc -> (0 <= c < 2 ^ 64)%Z -> (c <= pp)%Z -> (pp + 8 <= c + kc)%Z ->
  live A' (Z_to_bv 64 q) = live A (Z_to_bv 64 q) -> (0 <= q < 2 ^ 64)%Z -> q <> c ->
  keeps A A' m m' q.
Proof.
  intros C A A' m m' md' s pp c q kc CK HW PD Lc Hc Hc1 Hc2 EQ Hq NE k L.
  rewrite <- EQ in L. split; [exact L|]. split; [exact (keeps_bound C A' m' md' q k HW L Hq)|]. intros x Hx.
  pose proof (ai_live_hull A' m' (m_vmmaps md') _ _ (w_inv _ _ _ _ HW) Lc) as (Hk0 & _ & TOPc & _). pose proof (round16_ge kc Hk0).
  pose proof (alloc_top_lt (m_vmmaps md')) as T. unfold two_pow_64 in T.
  apply (POSTD_blk_byte C A' s pp m m' (Z_to_bv 64 q) k x PD L); [rewrite u_Z2bv by lia; lia|].
  intros IN. unfold inslot in IN.
  pose proof (ai_live_disjoint A' m' (m_vmmaps md') _ _ _ _ (w_inv _ _ _ _ HW) Lc L (zneq_w c q ltac:(lia) ltac:(lia) (not_eq_sym NE))) as D.
  pose proof (ai_live_hull A' m' (m_vmmaps md') _ _ (w_inv _ _ _ _ HW) L) as (Hk1 & _ & _ & _). pose proof (round16_ge k Hk1).
  rewrite !u_Z2bv in D by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma keeps_postm : forall C A A' Ar s m m' md' q, W C A' m' md' -> POSTM C Ar s m m' ->
  live Ar (Z_to_bv 64 q) = live A (Z_to_bv 64 q) -> live A' (Z_to_bv 64 q) = live A (Z_to_bv 64 q) -> (0 <= q < 2 ^ 64)%Z ->
  keeps A A' m m' q.
Proof.
  intros C A A' Ar s m m' md' q HW PM EQr EQ Hq k L. rewrite <- EQ in L. split; [exact L|]. split; [exact (keeps_bound C A' m' md' q k HW L Hq)|].
  intros x Hx. rewrite EQ, <- EQr in L.
  exact (LIVK_byte Ar m m' (Z_to_bv 64 q) k x (proj2 PM) L ltac:(rewrite u_Z2bv by lia; lia)).
Qed.

(* [comment removed for export] *)
Lemma keeps_agree : forall C A A' m m' md' q, W C A' m' md' ->
  live A' (Z_to_bv 64 q) = live A (Z_to_bv 64 q) -> (0 <= q < 2 ^ 64)%Z ->
  (forall k (x : word), live A (Z_to_bv 64 q) = Some k -> q <= u x < q + k -> m' x = m x) ->
  keeps A A' m m' q.
Proof.
  intros C A A' m m' md' q HW EQ Hq AG k L. rewrite <- EQ in L. split; [exact L|]. split; [exact (keeps_bound C A' m' md' q k HW L Hq)|].
  intros x Hx. rewrite EQ in L. exact (AG k x L Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma boxa_at_transport : forall C A A' m m' ba n na arr b0,
  boxa_at C A m ba n na arr b0 -> keeps A A' m m' ba -> keeps A A' m m' arr -> (n = 1 -> keeps A A' m m' b0) ->
  boxa_at C A' m' ba n na arr b0.
Proof.
  intros C A A' m m' ba n na arr b0 (R & Hal & Lba & L0ba & ARR) Kba Karr Kb0.
  destruct (Kba _ Lba) as (Lba' & _ & Mba).
  split; [apply (RECat_frame m m' ba _ R); intros x Hx; apply Mba; cbn in Hx; lia|].
  split; [exact Hal|]. split; [exact Lba'|]. split; [exact L0ba|].
  destruct ARR as [[Harr0 Hn0] | (Larr & L0arr & Hna & NE & NB)]; [left; split; assumption|].
  right. destruct (Karr _ Larr) as (Larr' & Barr & Marr). pose proof (BOXA_wf m ba n na 1 arr R) as (_ & _ & Warr & _).
  split; [exact Larr'|]. split; [exact L0arr|]. split; [exact Hna|]. split; [exact NE|].
  destruct NB as [Hn0 | (Hn1 & Rb0 & (BX & Halb & Lb0 & L0b0) & NE1 & NE2)]; [left; exact Hn0|].
  right. destruct (Kb0 Hn1 _ Lb0) as (Lb0' & _ & Mb0). destruct BX as (x & y & w & h & RB). pose proof (RECat_range m b0 _ RB) as [B0 B1]. cbn in B1.
  split; [exact Hn1|]. split; [rewrite <- Rb0; apply rdn_ext; rewrite !u_Z2bv by lia; [cbn; lia|]; intros z Hz; apply Marr; cbn in Hz; lia|].
  split; [| split; [exact NE1 | exact NE2]].
  split; [exists x, y, w, h; apply (RECat_frame m m' b0 _ RB); intros z Hz; apply Mb0; cbn in Hz; lia|].
  split; [exact Halb|]. split; [exact Lb0' | exact L0b0].
Qed.

Lemma ptra_at_transport : forall C A A' m m' pa na arr,
  ptra_at C A m pa na arr -> keeps A A' m m' pa -> keeps A A' m m' arr -> ptra_at C A' m' pa na arr.
Proof.
  intros C A A' m m' pa na arr (R & Lpa & L0pa & ARR) Kpa Karr.
  destruct (Kpa _ Lpa) as (Lpa' & _ & Mpa).
  split; [apply (RECat_frame m m' pa _ R); intros x Hx; apply Mpa; cbn in Hx; lia|].
  split; [exact Lpa'|]. split; [exact L0pa|].
  destruct ARR as [Harr0 | (Larr & L0arr & Hna & NE)]; [left; exact Harr0|].
  right. destruct (Karr _ Larr) as (Larr' & _). split; [exact Larr'|]. split; [exact L0arr|]. split; [exact Hna | exact NE].
Qed.

Lemma pixa_at_transport : forall C A A' m m' px na parr ba bna barr,
  pixa_at C A m px na parr ba bna barr -> keeps A A' m m' px -> keeps A A' m m' parr -> keeps A A' m m' ba -> keeps A A' m m' barr ->
  pixa_at C A' m' px na parr ba bna barr.
Proof.
  intros C A A' m m' px na parr ba bna barr (R & Hal & Lpx & L0px & Lparr & L0parr & Hna & NE1 & BA & NE2 & NE3 & NE4 & NE5) Kpx Kparr Kba Kbarr.
  destruct (Kpx _ Lpx) as (Lpx' & _ & Mpx). destruct (Kparr _ Lparr) as (Lparr' & _).
  split; [apply (RECat_frame m m' px _ R); intros x Hx; apply Mpx; cbn in Hx; lia|].
  split; [exact Hal|]. split; [exact Lpx'|]. split; [exact L0px|]. split; [exact Lparr'|]. split; [exact L0parr|].
  split; [exact Hna|]. split; [exact NE1|]. split; [| split; [exact NE2 | split; [exact NE3 | split; [exact NE4 | exact NE5]]]].
  apply (boxa_at_transport C A A' m m' ba 0 bna barr 0 BA Kba Kbarr). intros X; discriminate X.
Qed.
End Cf.
End V8LeptCf.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8CL7a.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8CL8a.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8CL9a.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8LeptCmapValid.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require V8Kit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require LiaFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Reloc Require Reloc.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require RelocLept.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.VL Require LeptDeser.
Module V8LeptDeser.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.colorfill_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptStderr.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptBase.
Import V8CL7a.
Import V8CL8a.
Import V8CL9a.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8.V8LeptCmapValid.
Import V8Kit.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica.RelocLept.
(* [comment removed for export] *)










Import V8CL7a.V8LeptErr.

Import V8CL8a.V8LeptCmap. Import V8CL8a.V8LeptPixHdr. Import V8CL8a.V8LeptPadBitsW.

Import V8CL9a.V8LeptPixDestroy. Import V8CL9a.V8LeptPixCreate. Import V8CL9a.V8LeptCmapDeser.


Import V8Kit.V8MemcpyBase. Import V8Kit.V8Memcpy.
Import V8CL8a.V8LeptDeserA. Import V8CL8a.V8LeptDeserB.


Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].



Import V8Kit.V8Reloc. Import V8Kit.V8RelocCode. Import V8Kit.V8RelocSites. Import V8Kit.V8RelocImg. Import V8Kit.V8RelocVL.
Import V8Kit.V8RelocMusl. Import V8Kit.V8LeptEnv.
Import V8CL7a.V8LeptG.
Import ListNotations.
Open Scope bv_scope.

Section Deser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU8} {PU8 : V8Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition payload (C : lctx) (dp : Z) (pl : list byte) : Prop :=
  live (c_A0 C) (Z_to_bv 64 dp) = Some (Z.of_nat (length pl)) /\ bytes_at (c_m0 C) dp pl /\ (1 <= dp)%Z /\ (dp + Z.of_nat (length pl) < 2 ^ 64)%Z.
Definition pixobj (C : lctx) (A A' : AS) (m' : word -> option byte) (pix : Z) (v : pixv) (cv : cmapv) : Prop :=
  PIXat m' pix v /\ p_rc v = 1%Z /\ p_text v = 0%Z /\ (0 < 4 * (p_wpl v * p_h v))%Z /\
  live A' (Z_to_bv 64 pix) = Some 64%Z /\ live A (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\
  live A' (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z /\ live A (Z_to_bv 64 (p_data v)) = None /\
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ p_data v <> pix /\
  (p_cmap v = 0%Z \/
   ((1 <= p_cmap v)%Z /\ CMAPat m' (p_cmap v) cv /\ live A' (Z_to_bv 64 (p_cmap v)) = Some 24%Z /\ live A' (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
    (0 < 4 * c_nalloc cv)%Z /\ live A (Z_to_bv 64 (p_cmap v)) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
    live (c_A0 C) (Z_to_bv 64 (p_cmap v)) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
    p_cmap v <> c_arr cv /\ p_cmap v <> pix /\ c_arr cv <> pix /\ p_data v <> p_cmap v /\ p_data v <> c_arr cv)) /\
  (forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 (p_data v) -> (p_cmap v <> 0%Z -> q <> Z_to_bv 64 (p_cmap v) /\ q <> Z_to_bv 64 (c_arr cv)) ->
             live A' q = live A q).
Definition DK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s : Z) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix v cv, getr regs' 10 = Z_to_bv 64 pix /\ pixobj C A A' m' pix v cv)) ->
     aroom A' vm' (kR - RK_deser) (bR - RB_deser) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.
Lemma live_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof. rl_tail (@LeptDeser.live_apart v8_reloc v8_lept AL CL ASR). Qed.

Lemma zbv_ne : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. rl_tail (@LeptDeser.zbv_ne). Qed.

Theorem pixDeserialize_W : forall C A m md regs (s dp : Z) (pl : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x31b70 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  payload C dp pl -> (3 <= Z.of_nat (length pl) < 2 ^ 26)%Z -> (dp mod 4 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  DK C A m md regs s ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x16898 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PLD Hnb Hal4 kR bR Hrm Hrk Hrb HK.
  pose proof (@LeptDeser.pixDeserialize_W fx v8_reloc v8_code v8_sites v8_code_vl v8_sites_vl v8_lept v8_img_vl v8_data v8_img v8_rw v8_pf v8_lenv_vl AL CL ASR PINS (v8_pinsG PU8) C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret) as RLT.
  rl_to_Z_in RLT; bvlit64_to_Z_in RLT; bvlit64_to_Z.
  assert (HDP : payload C dp pl -> (1 <= dp < 2 ^ 64)%Z).
  { intros (_ & _ & Hd1 & Hd2). pose proof (Zle_0_nat (length pl)). lia. }
  apply (RLT H4 H10 H11 (HDP PLD) ltac:(lia) (fun _ => PLD) Hal4 kR bR Hrm Hrk Hrb).
  intros A' m' vm' regs' HW' CS' PM' HR' AR'. apply (HK A' m' vm' regs' HW' CS' PM'); [ | exact AR'].
  destruct HR' as [HR' | (pix & v & cv & Hp & Hobj & _)]; [left; exact HR' | right; exists pix, v, cv; split; [exact Hp | exact Hobj]].
Qed.

End Deser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
End V8LeptDeser.
