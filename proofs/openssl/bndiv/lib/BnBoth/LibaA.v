(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv BnCorrect.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_libiface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LIBA_BAL : Z := 1600.

Definition LIBA (RT : rt_sig) (Σ : rts RT) (LW : list (Z * Z)) (m : mem) : Prop :=
  exists (ls : lstate bptr) (OW : list block) (AD : bn_addrs) (EA : err_addrs),
    LW = map blk_an OW /\ List.NoDup (map blk_id OW) /\ Forall blk_okA OW
    /\ lib_state ls m OW AD EA /\ ls_inv ls (blocks_of ls)
    /\ cnt_bal ls OW <= LIBA_BAL.

Section Facts.
Variable RT : rt_sig.

Lemma in_block_live : forall (OW : list block) x, in_block OW x -> in_live (map blk_an OW) x.
Proof. intros OW x H. apply in_live_blocks. exact H. Qed.

Lemma libw_in_LIB_FP : forall x, rin_ivs LIBW_A x -> in_ranges LIB_FP x.
Proof.
  intros x H. unfold LIBW_A in H. cbn [rin_ivs fst snd] in H. unfold in_ranges, LIB_FP.
  destruct H as [H|[H|[H|[]]]].
  - exists 0x5e6660, 0x5e7140. split; [cbn; tauto | exact H].
  - exists 0xbd6080, 0xbda540. split; [cbn; tauto | exact H].
  - exists 0xbfc200, 0xbfc5f8. split; [cbn; tauto | exact H].
Qed.

Theorem liba_frameA : liba_frame RT (LIBA RT).
Proof.
  intros Σ Σ' LW m m' (ls & OW & AD & EA & -> & ND & OK & LS & INV & BAL) HAG.
  exists ls, OW, AD, EA. split; [reflexivity|]. split; [exact ND|]. split; [exact OK|]. split; [|split; [exact INV | exact BAL]].
  eapply lib_state_hc_agree; [exact LS|]. intros a Ha Hown. apply HAG. unfold wa. rewrite unsigned_lit by lia.
  destruct (own_fp_lib _ _ _ _ _ _ _ LS Hown) as [HL|HB]; [left; apply libw_in_LIB_FP; exact HL | right; apply in_block_live; exact HB].
Qed.

Theorem liba_exitA : liba_exit RT (LIBA RT).
Proof.
  intros Σ LW m (ls & OW & AD & EA & _ & _ & _ & LS & _). destruct LS as (_ & _ & HO & _). exact HO.
Qed.

Theorem liba_posA : liba_pos RT (LIBA RT).
Proof.
  intros Σ LW m (ls & OW & AD & EA & -> & _ & OK & _) p n Hin.
  apply in_map_iff in Hin as (b & E & Hb). unfold blk_an in E. injection E as <- <-.
  exact (proj2 (proj1 (Forall_forall _ _) OK b Hb)).
Qed.

(* [comment removed for export] *)
Theorem LIBA_init : forall (Σ : rts RT) (m : mem) (OW : list block),
  init_factsA m OW -> List.NoDup (map blk_id OW) -> Forall blk_okA OW -> Z.of_nat (length OW) <= LIBA_BAL ->
  LIBA RT Σ (map blk_an OW) m.
Proof.
  intros Σ m OW HI ND OK LEN. destruct (lib_inv_init m OW HI) as (AD & EA & LS).
  exists ls_init, OW, AD, EA. split; [reflexivity|]. split; [exact ND|]. split; [exact OK|]. split; [exact LS|].
  split; [exact ls_inv_init|]. unfold cnt_bal. lia.
Qed.

End Facts.
