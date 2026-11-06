(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA UnwindA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnCallAF AFrameComp PlaceTmodA ExpBodyKitF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma cenv_switch_plA : forall (LB : list block) PL PL' lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  frames_ok LB PL' SPv USTACK_TOP -> frames_al PL' -> frames_lb PL' LB ->
  cenvA LB PL' lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m pre used Σ ls m OW.
Proof.
  intros LB PL PL' lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW) FROK' FAL' NOFR'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & _ & _ & _).
  unfold cenvA, cenv_ok.
  split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|]. split; [exact CNT0|]. split; [exact CRED0|].
           split; [exact FROK'|]. split; [exact FAL' | exact NOFR']. }
  split; [exact HEAP|]. split; [exact ST|]. split; [exact MI|]. split; [apply ax_pres_refl|]. split; [exact CR|].
  split; [exact CNT|]. split; [exact RS|]. split; [exact FRC|]. split; [exact FSZ | exact UW].
Qed.

Lemma cenv_set_montA : forall (LB : list block) PL lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW x y,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ (set_mont x y ls) m OW.
Proof.
  intros LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW x y
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW).
  unfold cenvA. split; [exact OK|]. split; [exact HEAP|]. split; [exact ST|]. split; [exact MI|]. split; [exact AXP|]. split; [exact CR|].
  split; [exact CNT|].
  split. { eapply refs_stable_trans; [exact RS|]. intros PL1 i a H. apply ref_at_set_mont. exact H. }
  split; [exact FRC|]. split; [exact FSZ | exact UW].
Qed.

Lemma ax_pres_unplace : forall Σ OW (LB : list block) m PL a d bt bb SPv m1 m2,
  AHEAP Σ OW (bt :: bb :: LB) m -> ACEIL <= SPv ->
  blk_addr bt <= a -> a + 24 <= blk_addr bt + blk_size bt -> blk_addr bb <= d -> d + 16 <= blk_addr bb + blk_size bb ->
  ax_pres (bt :: bb :: LB) SPv (XW (pl_place_tmod PL a d)) m1 m2 ->
  ax_pres LB SPv (XW PL) m1 m2.
Proof.
  intros Σ OW LB m PL a d bt bb SPv m1 m2 HEAP CEIL T1 T2 U1 U2 AX.
  assert (IT : In bt (OW ++ bt :: bb :: LB)) by (apply in_or_app; right; left; reflexivity).
  assert (IB : In bb (OW ++ bt :: bb :: LB)) by (apply in_or_app; right; right; left; reflexivity).
  pose proof (AH_range_gen _ _ _ _ bt HEAP IT) as (_ & _ & _ & TC & _).
  pose proof (AH_range_gen _ _ _ _ bb HEAP IB) as (_ & _ & _ & BC & _).
  pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND. cbn [map] in ND.
  apply NoDup_cons_iff in ND. destruct ND as [N1 ND]. apply NoDup_cons_iff in ND. destruct ND as [N2 _].
  assert (OUT : forall x, aclient_addr LB SPv x -> ~ (blk_addr bt <= x < blk_addr bt + blk_size bt) /\ ~ (blk_addr bb <= x < blk_addr bb + blk_size bb)).
  { intros x [Hx|[Hx|(b & Hb & Hr)]].
    - unfold BnHeapA.ACEIL in *. lia.
    - split; intros HH; [exact (blk_not_static_gen Σ OW _ m bt x HEAP IT HH Hx) | exact (blk_not_static_gen Σ OW _ m bb x HEAP IB HH Hx)].
    - assert (I' : In b (OW ++ bt :: bb :: LB)) by (apply in_or_app; right; right; right; exact Hb).
      assert (NEt : blk_id b <> blk_id bt) by (intros E; apply N1; right; rewrite <- E; apply in_map; exact Hb).
      assert (NEb : blk_id b <> blk_id bb) by (intros E; apply N2; rewrite <- E; apply in_map; exact Hb).
      pose proof (AH_disjoint_gen _ _ _ _ b bt HEAP I' IT NEt) as D1. pose proof (AH_disjoint_gen _ _ _ _ b bb HEAP I' IB NEb) as D2. lia. }
  eapply agree_on_mono; [exact AX|]. intros x [Hx Hc]. split.
  - intros HX. apply xw_place_tmod in HX. destruct (OUT x Hc) as [O1 O2]. destruct HX as [HX|[HX|HX]]; [exact (Hx HX) | apply O1; lia | apply O2; lia].
  - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; exact Hc | right; left; exact Hc | right; right; exists b; split; [right; right; exact Hb | exact Hr]].
Qed.

Lemma obj_keep_inA : forall (b : block) (LB : list block) PL lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW A cs,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> In b LB ->
  rw_cells bgbsegs m0 A cs -> blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> ~ rin_ivs (pl_frames PL) x) ->
  rw_cells bgbsegs m A cs.
Proof.
  intros b LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW A cs
         (OK & HEAP & ST & MI & AXP & _) Hb CELLS B1 B2 NF.
  eapply rw_cells_agree; [exact AXP | exact CELLS |]. intros x Hx. split.
  - intros HX. unfold XW in HX. apply rin_ivs_app in HX. destruct HX as [HX|HX]; [| exact (NF x Hx HX)].
    pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & BI).
    revert HX. unfold LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. clear - BI Hx B1 B2. lia.
  - right; right. exists b. split; [exact Hb | lia].
Qed.

End WithRT.
