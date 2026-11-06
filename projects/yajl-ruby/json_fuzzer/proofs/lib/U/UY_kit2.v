(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma buf_rep_transport : forall W m m' mb b AF,
  buf_rep usegs m mb b AF -> munch W m m' -> wmono usegs m m' ->
  disjoint_from W (mb_addr mb) 32 ->
  (yb_data b <> None -> disjoint_from W (mb_data mb) (yb_len b)) ->
  buf_rep usegs m' mb b AF.
Proof.
  intros W m m' mb b AF ((BC & BR) & BD & FB) MU WM D1 D2. split; [split; [| exact BR]|].
  - eapply (rw_cells_transport usegs); [exact BC| exact MU| exact WM|]. rewrite buf_cells_size. exact D1.
  - split; [| exact FB]. unfold buf_data in *. destruct (yb_data b); [| exact I].
    destruct BD as (HU & junk & HC). split; [exact HU|]. exists junk.
    pose proof (proj1 (proj1 HC)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (L1 & _ & L2 & _).
    eapply (rw_cells_transport usegs); [exact HC| exact MU| exact WM|].
    cbn [cells_size csize]. replace (Z.of_nat (Z.to_nat (yb_used b) + (1 + (Z.to_nat (yb_len b - yb_used b - 1) + 0)))) with (yb_len b) by lia.
    apply D2. discriminate.
Qed.

Lemma lexer_rep_transport : forall W m m' L lx mbl AF,
  lexer_rep usegs m L lx mbl AF -> munch W m m' -> wmono usegs m m' ->
  disjoint_from W L 48 -> disjoint_from W (mb_addr mbl) 32 ->
  (yb_data (lx_buf lx) <> None -> disjoint_from W (mb_data mbl) (yb_len (lx_buf lx))) ->
  lexer_rep usegs m' L lx mbl AF.
Proof.
  intros W m m' L lx mbl AF ((LC & LR) & BR) MU WM D0 D1 D2. split; [split; [| exact LR]| eapply buf_rep_transport; eauto].
  eapply (rw_cells_transport usegs); [exact LC| exact MU| exact WM|]. rewrite lexer_cells_size. exact D0.
Qed.

(* [comment removed for export] *)

Lemma buf_rep_pres : forall LB SP m m' mb b AF,
  buf_rep usegs m mb b AF -> rheap_pres LB SP m m' ->
  (exists blk, In blk LB /\ blk_addr blk <= mb_addr mb /\ mb_addr mb + 32 <= blk_addr blk + blk_size blk) ->
  (yb_data b <> None -> exists blk, In blk LB /\ blk_addr blk <= mb_data mb /\ mb_data mb + yb_len b <= blk_addr blk + blk_size blk) ->
  buf_rep usegs m' mb b AF.
Proof.
  intros LB SP m m' mb b AF ((BC & BR) & BD & FB) HP H1 H2. split; [split; [| exact BR]|].
  - eapply ypres_block; [exact HP| exact BC|]. rewrite buf_cells_size. exact H1.
  - split; [| exact FB]. unfold buf_data in *. destruct (yb_data b); [| exact I].
    destruct BD as (HU & junk & HC). split; [exact HU|]. exists junk.
    pose proof (proj1 (proj1 HC)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (L1 & _ & L2 & _).
    eapply ypres_block; [exact HP| exact HC|].
    cbn [cells_size csize]. replace (Z.of_nat (Z.to_nat (yb_used b) + (1 + (Z.to_nat (yb_len b - yb_used b - 1) + 0)))) with (yb_len b) by lia.
    apply H2. discriminate.
Qed.

Lemma lexer_rep_pres : forall LB SP m m' L lx mbl AF,
  lexer_rep usegs m L lx mbl AF -> rheap_pres LB SP m m' ->
  (exists blk, In blk LB /\ blk_addr blk <= L /\ L + 48 <= blk_addr blk + blk_size blk) ->
  (exists blk, In blk LB /\ blk_addr blk <= mb_addr mbl /\ mb_addr mbl + 32 <= blk_addr blk + blk_size blk) ->
  (yb_data (lx_buf lx) <> None -> exists blk, In blk LB /\ blk_addr blk <= mb_data mbl /\ mb_data mbl + yb_len (lx_buf lx) <= blk_addr blk + blk_size blk) ->
  lexer_rep usegs m' L lx mbl AF.
Proof.
  intros LB SP m m' L lx mbl AF ((LC & LR) & BR) HP H0 H1 H2. split; [split; [| exact LR]| eapply buf_rep_pres; eauto].
  eapply ypres_block; [exact HP| exact LC|]. rewrite lexer_cells_size. exact H0.
Qed.

(* [comment removed for export] *)
Definition sub_blocks (S LB : list block) : Prop := forall x, In x S -> In x LB.

Lemma sub_blocks_cons_l : forall x S LB, sub_blocks (x :: S) LB -> In x LB /\ sub_blocks S LB.
Proof. intros x S LB H. split; [apply H; left; reflexivity| intros y Hy; apply H; right; exact Hy]. Qed.
Lemma sub_blocks_app_l : forall S1 S2 LB, sub_blocks (S1 ++ S2) LB -> sub_blocks S1 LB /\ sub_blocks S2 LB.
Proof. intros S1 S2 LB H. split; intros y Hy; apply H; apply in_or_app; [left| right]; exact Hy. Qed.

Lemma buf_blocks_ranges : forall LB mb b, all_range LB -> sub_blocks (buf_blocks mb b) LB ->
  rblock_range (mb_addr mb) SIZEOF_BUF /\ (yb_data b <> None -> rblock_range (mb_data mb) (yb_len b)).
Proof.
  intros LB mb b RNG SB. unfold buf_blocks in SB. apply sub_blocks_cons_l in SB. destruct SB as [I1 SB]. split.
  - exact (all_range_In _ _ RNG I1).
  - intros HD. destruct (yb_data b); [| congruence]. apply sub_blocks_cons_l in SB. destruct SB as [I2 _].
    exact (all_range_In _ _ RNG I2).
Qed.

Lemma lexer_blocks_ranges : forall LB lid L mbl lx, all_range LB -> sub_blocks (lexer_blocks lid L mbl lx) LB ->
  rblock_range L SIZEOF_LEXER /\ rblock_range (mb_addr mbl) SIZEOF_BUF
  /\ (yb_data (lx_buf lx) <> None -> rblock_range (mb_data mbl) (yb_len (lx_buf lx))).
Proof.
  intros LB lid L mbl lx RNG SB. unfold lexer_blocks in SB. apply sub_blocks_cons_l in SB. destruct SB as [I1 SB].
  split; [exact (all_range_In _ _ RNG I1)| apply (buf_blocks_ranges LB); assumption].
Qed.

Lemma disjoint_from_above : forall W A n, Forall (fun iv : Z * Z => A + n <= fst iv) W -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n HF; [exact I|].
  inversion HF; subst. cbn [disjoint_from fst] in *. split; [left; assumption| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma buf_rep_transport_hi : forall LB W m m' mb b AF,
  buf_rep usegs m mb b AF -> munch W m m' -> wmono usegs m m' ->
  all_range LB -> sub_blocks (buf_blocks mb b) LB ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W ->
  buf_rep usegs m' mb b AF.
Proof.
  intros LB W m m' mb b AF BR MU WM RNG SB HW.
  destruct (buf_blocks_ranges _ _ _ RNG SB) as [R1 R2]. unfold rblock_range, SIZEOF_BUF in R1, R2.
  eapply buf_rep_transport; [exact BR| exact MU| exact WM| |].
  - apply disjoint_from_above. eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hi. lia.
  - intros HD. specialize (R2 HD). apply disjoint_from_above. eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hi. lia.
Qed.

Lemma lexer_rep_transport_hi : forall LB W m m' L lx mbl AF lid,
  lexer_rep usegs m L lx mbl AF -> munch W m m' -> wmono usegs m m' ->
  all_range LB -> sub_blocks (lexer_blocks lid L mbl lx) LB ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W ->
  lexer_rep usegs m' L lx mbl AF.
Proof.
  intros LB W m m' L lx mbl AF lid LR MU WM RNG SB HW.
  destruct (lexer_blocks_ranges _ _ _ _ _ RNG SB) as (R0 & R1 & R2). unfold rblock_range, SIZEOF_BUF, SIZEOF_LEXER in R0, R1, R2.
  eapply lexer_rep_transport; [exact LR| exact MU| exact WM| | |].
  - apply disjoint_from_above. eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hi. lia.
  - apply disjoint_from_above. eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hi. lia.
  - intros HD. specialize (R2 HD). apply disjoint_from_above. eapply Forall_impl; [| exact HW]. cbn beta. intros iv Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma buf_rep_pres_sub : forall LB SP m m' mb b AF,
  buf_rep usegs m mb b AF -> rheap_pres LB SP m m' -> sub_blocks (buf_blocks mb b) LB ->
  buf_rep usegs m' mb b AF.
Proof.
  intros LB SP m m' mb b AF BR HP SB. pose proof SB as SB'. unfold buf_blocks in SB'. apply sub_blocks_cons_l in SB'. destruct SB' as [I1 SB'].
  eapply buf_rep_pres; [exact BR| exact HP| |].
  - eexists. split; [exact I1|]. cbn. unfold SIZEOF_BUF. lia.
  - intros HD. destruct (yb_data b); [| congruence]. apply sub_blocks_cons_l in SB'. destruct SB' as [I2 _].
    eexists. split; [exact I2|]. cbn. lia.
Qed.

Lemma lexer_rep_pres_sub : forall LB SP m m' L lx mbl AF lid,
  lexer_rep usegs m L lx mbl AF -> rheap_pres LB SP m m' -> sub_blocks (lexer_blocks lid L mbl lx) LB ->
  lexer_rep usegs m' L lx mbl AF.
Proof.
  intros LB SP m m' L lx mbl AF lid ((LC & LRG) & BR) HP SB. unfold lexer_blocks in SB. apply sub_blocks_cons_l in SB. destruct SB as [I1 SB].
  split; [split; [| exact LRG]| eapply buf_rep_pres_sub; eauto].
  eapply ypres_block; [exact HP| exact LC|]. rewrite lexer_cells_size. eexists. split; [exact I1|]. cbn. unfold SIZEOF_LEXER. lia.
Qed.
End RC__1.
