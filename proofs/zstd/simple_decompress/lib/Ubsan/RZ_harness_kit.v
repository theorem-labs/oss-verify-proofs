(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import F_malloc_free MallocHINV MallocFacts_A Malloc_iface InitMem F_malloc_top Malloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP Harness_iface RF_fse_h_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require MallocFacts_inv2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_frame_iface RZ_dframe_iface.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma RHEAP_block_low : forall s LB m b, RHEAP s LB m -> In b LB -> 4096 <= blk_addr b.
Proof.
  intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  lia.
Qed.

Lemma rheap_pres_stk_gen : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk usegs m lo hi -> (forall a, lo <= a < hi -> rclient_addr LB SP a) -> stk usegs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HC. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) (HC i Hi)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma dctx_any_rheap_pres : forall LB SP m m' A b,
  rheap_pres LB SP m m' -> dctx_any m A -> In b LB -> blk_addr b = A -> blk_size b = 95992 -> dctx_any m' A.
Proof.
  intros LB SP m m' A b HP (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                            PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]) HB EA ES.
  assert (TR : forall X cs, rw_cells usegs m X cs -> A <= X -> X + Z.of_nat (cells_size cs) <= A + 95992 -> rw_cells usegs m' X cs).
  { intros X cs RC L1 L2. eapply rheap_pres_rw_cells; [exact HP | exact RC |]. right; right. exists b. split; [exact HB| lia]. }
  assert (TS : forall x y, stk usegs m x y -> A <= x -> y <= A + 95992 -> stk usegs m' x y).
  { intros x y SK L1 L2. eapply rheap_pres_stk_gen; [exact HP | exact SK |]. intros a Ha. right; right. exists b. split; [exact HB| lia]. }
  unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
  exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
  split; [apply TR; [exact PT | lia | cbn; lia]|].
  split; [apply TR; [exact H1 | lia | cbn; lia]|].
  split; [split; [apply TR; [exact FPC | lia | rewrite FPSZ; lia]| exact FPSZ]|].
  split; [apply TR; [exact H3 | lia | cbn; lia]|].
  split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
  split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
  split; [exact H5OK|].
  split; [apply TR; [exact TX | lia | cbn; lia]|].
  split; apply TS; try assumption; lia.
Qed.

(* [comment removed for export] *)
Definition hpres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ (PDCTX <= a < PDCTX + 8) ->
    m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None).

Lemma hpres_refl : forall LB SP m, hpres LB SP m m.
Proof. intros LB SP m a _ _ _. auto. Qed.

Lemma hpres_trans : forall LB SP m1 m2 m3, hpres LB SP m1 m2 -> hpres LB SP m2 m3 -> hpres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc Hn. destruct (H1 a Ha Hc Hn) as [E1 W1]. destruct (H2 a Ha Hc Hn) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma hpres_of_rheap_pres : forall LB LB' SP SP' m m',
  rheap_pres LB' SP' m m' -> SP' <= SP -> (forall b, In b LB -> In b LB') -> hpres LB SP m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc _. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma hpres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ (PDCTX <= a < PDCTX + 8) -> outside W a) ->
  hpres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM OUT a Ha Hc Hn. split.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT; assumption.
  - intros Hv. apply WM. exact Hv.
Qed.

(* [comment removed for export] *)
Definition fh_fp_ok_d (LBX : list block) (SPC : Z) (iv : Z * Z) : Prop :=
  fh_fp_ok LBX SPC iv \/ iv = (PDCTX, PDCTX + 8).

Lemma fh_transport_d : forall s LBX LB m m' W AB SPC,
  RHEAP s (LBX ++ LB) m -> munch W m m' -> wmono usegs m m' ->
  Forall (fh_fp_ok_d LBX SPC) W -> ATOP <= SPC <= AB ->
  RHEAP s (LBX ++ LB) m'
  /\ (rauxv_ok m AB -> rauxv_ok m' AB)
  /\ hpres LB SPC m m'.
Proof.
  intros s LBX LB m m' W AB SPC HP MU WM FW HS.
  assert (BLK : forall b, In b LBX -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. eapply RMalloc_ifaceP.RHEAP_block_range_proof; [exact HP| apply in_app_iff; left; exact Hb]. }
  split; [| split].
  - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv [[[F1 F2]|(b & Hb & F1 & F2)]| ->]; [left; exact F1| |].
    + right; right. exists b. split; [apply in_app_iff; left; exact Hb| lia].
    + right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
  - intros AUX.
    eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros iv [[[F1 F2]|(b & Hb & F1 & F2)]| ->]; [unfold RAUXV_CELL in *; atop_facts; lia| |].
    + pose proof (BLK b Hb) as (B1 & B2 & B3 & B4 & B5). unfold RAUXV_CELL in *. atop_facts. lia.
    + cbn [fst snd]. unfold RAUXV_CELL. atop_facts. lia.
  - eapply hpres_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hn.
    apply outside_of_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as [[[F1 F2]|(b & Hb & F1 & F2)]| ->].
    + destruct Hc as [Hc|[Hc|(b' & Hb' & R1 & R2)]]; [lia| atop_facts; lia|].
      pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP ltac:(apply in_app_iff; right; exact Hb')) as (_ & _ & _ & R4 & _). lia.
    + pose proof (BLK b Hb) as (B1 & B2 & B3 & B4 & B5).
      destruct Hc as [Hc|[Hc|(b' & Hb' & R1 & R2)]]; [atop_facts; lia| lia|].
      pose proof (blocks_distinct_disjoint _ _ _ _ b b' HP Hb Hb'). lia.
    + cbn [fst snd]. exact Hn.
Qed.

End CANSEC1.
