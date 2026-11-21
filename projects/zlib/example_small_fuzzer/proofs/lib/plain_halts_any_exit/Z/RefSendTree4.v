(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.

Module RefBitsFwd.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma upd4_set_pending : forall s A P B V v, set_pending (upd4 s A P B V) v = upd4 s A v B V.
Proof. intros. reflexivity. Qed.
Lemma upd4_set_bi_buf : forall s A P B V v, set_bi_buf (upd4 s A P B V) v = upd4 s A P v V.
Proof. intros. reflexivity. Qed.
Lemma upd4_set_bi_valid : forall s A P B V v, set_bi_valid (upd4 s A P B V) v = upd4 s A P B v.
Proof. intros. destruct s. reflexivity. Qed.
Lemma upd4_set_pending_buf : forall s A P B V v, set_pending_buf (upd4 s A P B V) v = upd4 s v P B V.
Proof. intros. reflexivity. Qed.

Lemma set_bi_buf_upd4_self : forall s j,
  set_bi_buf s j = upd4 s (ds_pending_buf s) (ds_pending s) j (ds_bi_valid s).
Proof. intros. destruct s; reflexivity. Qed.

Lemma upd4_eq_self : forall s A P B V,
  A = ds_pending_buf s -> P = ds_pending s -> B = ds_bi_buf s -> V = ds_bi_valid s -> upd4 s A P B V = s.
Proof. intros; subst. apply upd4_self. Qed.

Lemma upd4_eq_set_bi_buf : forall s A P B V j,
  A = ds_pending_buf s -> P = ds_pending s -> B = j -> V = ds_bi_valid s -> upd4 s A P B V = set_bi_buf s j.
Proof. intros; subst. symmetry. apply set_bi_buf_upd4_self. Qed.


Section Rel4.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Local Notation PB := (p_pending_buf p).
End Rel4.

Lemma wrap16_id' : forall v x, v = x -> 0 <= x < 2 ^ 16 -> v = wrap16 x.
Proof. intros v x -> Hx. rewrite wrap16_mod'. symmetry. apply Z.mod_small. exact Hx. Qed.

Lemma mod16_congr : forall a b, a = b -> a mod 2 ^ 16 = b mod 2 ^ 16.
Proof. intros a b ->. reflexivity. Qed.

Ltac rhs_upd4 :=
  repeat first [ rewrite upd4_set_bi_buf | rewrite upd4_set_bi_valid
               | rewrite upd4_set_pending | rewrite upd4_set_pending_buf | rewrite upd4_upd4 ].

Ltac st_eq4 :=
  rhs_upd4;
  lazymatch goal with
  | |- upd4 ?s _ _ _ _ = upd4 ?s _ _ _ _ => apply upd4_congr
  | |- upd4 ?s _ _ _ _ = set_bi_buf ?s _ => apply upd4_eq_set_bi_buf
  | |- upd4 ?s _ _ _ _ = ?s => apply upd4_eq_self
  end.
End RefBitsFwd.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.

Module RefSendTree1.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable t : tree_id.
Variable mc : Z.
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation L i := (Len ds t i).
Local Notation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Notation BL c := (arr_get (ds_bl_tree_dl ds) c).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Definition PURE (s : deflate_state) : Prop :=
  BINV PBL s
  /\ (forall t', tree_fc s t' = tree_fc ds t') /\ (forall t', tree_dl s t' = tree_dl ds t')
  /\ arr_len (ds_pending_buf s) = PBL /\ tree_lens s.

Definition GI : franges := [(S, 5952); (PB, PBL)].

Lemma PURE_send : forall s v l, PURE s -> 0 <= l <= 16 -> sb_room PBL s l -> PURE (send_bits s v l).
Proof.
  intros s v l (P1 & P2 & P3 & P4 & P5) Hl Hr. unfold PURE.
  split; [apply send_bits_BINV; assumption|].
  split; [intros t'; rewrite sb_tree_fc; apply P2|]. split; [intros t'; rewrite sb_tree_dl; apply P3|].
  split; [rewrite sb_pbl; exact P4 | apply sb_lens; exact P5].
Qed.

Lemma tree_dl_set_bi_buf : forall s j t', tree_dl (set_bi_buf s j) t' = tree_dl s t'.
Proof. intros s j [| |]; reflexivity. Qed.
Lemma tree_fc_set_bi_buf : forall s j t', tree_fc (set_bi_buf s j) t' = tree_fc s t'.
Proof. intros s j [| |]; reflexivity. Qed.

Lemma PURE_Len : forall s i, PURE s -> Len s t i = L i.
Proof. intros s i (_ & _ & P3 & _). unfold Len. rewrite P3. reflexivity. Qed.
Lemma PURE_blc : forall s c, PURE s -> blc s c = (BC c, BL c).
Proof. intros s c (_ & P2 & P3 & _). unfold blc, Code, Len. rewrite P2, P3. reflexivity. Qed.


Definition stF (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb (tree_dl ds t) x | 1%nat => pb (ds_bl_tree_fc ds) x | _ => pb (ds_bl_tree_dl ds) x end.

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 17); (36%nat, 2 ^ 63); (37%nat, 600); (38%nat, 600);
   (39%nat, 19); (40%nat, 65536); (41%nat, 200); (42%nat, 65536); (43%nat, 200); (44%nat, 10); (45%nat, 2 ^ 63);
   (46%nat, 200); (47%nat, 65536); (48%nat, 2 ^ 64); (49%nat, 65536); (50%nat, 65536)].

Local Ltac nf := cbn [stF].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].

Local Ltac eregs H := destruct H as ((K10 & K15 & K30 & K29 & K5 & K6 & K8 & K7 & K31 & K9 & K2) & P11 & P17 & P28 & P12 & P18 & P19).

Local Ltac mregs H := destruct H as ((K10 & K15 & K30 & K29 & K5 & K6 & K8 & K7 & K31 & K9 & K2) & P11 & P17 & P28 & P12 & HRB & P13).

Local Ltac rregs H := destruct H as ((K10 & K15 & K30 & K29 & K5 & K6 & K8 & K7 & K31 & K9 & K2) & P11 & P17 & P28 & P12 & HRB & P14).

Local Ltac sbv_site pc_flush pc_keep rdF rdK pins pv HB HP HAG HRB vnorm :=
  idtac.


Local Ltac zsite code HB HP HAG HRB Efc Edl :=
  idtac.

End Walk.
End RefSendTree1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.

Module RefSendTree2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable t : tree_id.
Variable mc : Z.
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation L i := (Len ds t i).
Local Notation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Notation BL c := (arr_get (ds_bl_tree_dl ds) c).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Local Notation PURE := (RefSendTree1.PURE PBL ds).
Local Notation GI := (RefSendTree1.GI S p PBL).
Local Notation stF := (RefSendTree1.stF ds t).

Local Ltac nf := cbn [RefSendTree1.stF].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].


Local Ltac kregs_open K :=
  destruct K as (K10 & K15 & K30 & K29 & K5 & K6 & K8 & K7 & K31 & K9 & K2).


Local Ltac r1regs H := destruct H as (K & P28 & P17 & P13 & P14 & P16 & HRB & P12); kregs_open K.


Local Ltac qregs H := destruct H as (K & P11 & P17 & P28); kregs_open K.


Local Ltac hregs H := destruct H as (K & P11 & P17 & P18 & P19 & P16 & P20); kregs_open K.


Local Ltac pregs H := destruct H as (K & P11 & P13 & P28 & P18 & P17 & P16 & P20 & P19); kregs_open K.

End Walk.
End RefSendTree2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree2.

Module RefSendTree3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefBitsFwd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable t : tree_id.
Variable mc : Z.
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation L i := (Len ds t i).
Local Notation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Notation BL c := (arr_get (ds_bl_tree_dl ds) c).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Local Notation PURE := (RefSendTree1.PURE PBL ds).
Local Notation GI := (RefSendTree1.GI S p PBL).
Local Notation stF := (RefSendTree1.stF ds t).

Local Ltac nf := cbn [RefSendTree1.stF].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].


Local Ltac kregs_open K :=
  destruct K as (K10 & K15 & K30 & K29 & K5 & K6 & K8 & K7 & K31 & K9 & K2).

Local Ltac t1regs H := destruct H as (K & P11 & P19); kregs_open K.
Local Ltac qregs H := destruct H as (K & P11 & P17 & P28); kregs_open K.
Local Ltac xregs H := destruct H as (K & P28 & P13 & P14); kregs_open K.
Local Ltac t6regs H := destruct H as (K & P11 & P17 & P28 & P19); kregs_open K.

Definition VBX : bounds := VB ++ [(51%nat, 2 ^ 64); (52%nat, 2 ^ 64); (53%nat, 2 ^ 64); (54%nat, 2 ^ 64); (55%nat, 2 ^ 64); (56%nat, 2 ^ 64)].


Definition cnts0 : Z * Z := if L 0 =? 0 then (138, 3) else (7, 4).

End Walk.
End RefSendTree3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefSendTree3.

Module RefTrAlign_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Local Notation PB := (p_pending_buf p).
Local Notation pend := (ds_pending ds).
Local Notation bv := (ds_bi_valid ds).
Local Notation bb := (ds_bi_buf ds).
Local Notation nb := (sb_nb ds 2).
Hypothesis Hbinv : BINV PBL ds.
Hypothesis Hroom : ds_pending (tr_align ds) <= PBL.
Definition VB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 65536); (36%nat, 17)].

End Walk.
End RefTrAlign_run.

Module RefTrFlushBits_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Local Notation PB := (p_pending_buf p).
Local Notation pend := (ds_pending ds).
Local Notation bv := (ds_bi_valid ds).
Local Notation bb := (ds_bi_buf ds).
Hypothesis Hbinv : BINV PBL ds.
Hypothesis Hroom : ds_pending (tr_flush_bits ds) <= PBL.
Definition VB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 65536); (36%nat, 17)].

End Walk.
End RefTrFlushBits_run.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable t : tree_id.
Variable mc : Z.
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation L i := (Len ds t i).
Local Notation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Notation BL c := (arr_get (ds_bl_tree_dl ds) c).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.


Local Notation PURE := (RefSendTree1.PURE PBL ds).
Local Notation GI := (RefSendTree1.GI S p PBL).
Local Notation stF := (RefSendTree1.stF ds t).
Local Notation cnts0 := (RefSendTree3.cnts0 ds t).

Local Ltac nf := cbn [RefSendTree1.stF].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].


Local Ltac kregs_open K :=
  destruct K as (K10 & K15 & K30 & K29 & K5 & K6 & K8 & K7 & K31 & K9 & K2).


Definition SL (s : deflate_state) (n pl c k mx mn : Z) : deflate_state :=
  send_tree_loop (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.
Definition OK (s : deflate_state) (n pl c k mx mn : Z) : Prop :=
  send_tree_ok PBL (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.

Lemma SL_step : forall s n pl c k mx mn, 0 <= n <= mc -> 1 <= mn ->
  SL s n pl c k mx mn =
    (let nl := Len s t (n + 1) in
     if (k + 1 <? mx) && (c =? nl) then SL s (n + 1) pl nl (k + 1) mx mn
     else let '(mx', mn') := tree_counts c nl in
          SL (sbs_run s (st_calls s mn c pl (k + 1))) (n + 1) c nl 0 mx' mn').
Proof.
  intros s n pl c k mx mn Hn Hmn. unfold SL.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  rewrite send_loop_S by exact Hmn. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  destruct ((k + 1 <? mx) && (c =? Len s t (n + 1))); [reflexivity|].
  destruct (tree_counts c (Len s t (n + 1))); reflexivity.
Qed.

Lemma SL_out : forall s n pl c k mx mn, mc < n -> SL s n pl c k mx mn = s.
Proof. intros. unfold SL. apply send_loop_out. lia. Qed.

Lemma OK_step : forall s n pl c k mx mn, 0 <= n <= mc ->
  OK s n pl c k mx mn ->
    (let nl := Len s t (n + 1) in
     if (k + 1 <? mx) && (c =? nl) then OK s (n + 1) pl nl (k + 1) mx mn
     else let '(mx', mn') := tree_counts c nl in
          sbs_ok PBL s (st_calls s mn c pl (k + 1))
          /\ OK (sbs_run s (st_calls s mn c pl (k + 1))) (n + 1) c nl 0 mx' mn').
Proof.
  intros s n pl c k mx mn Hn H. unfold OK in *.
  replace (Z.to_nat (mc + 1 - n)) with (Datatypes.S (Z.to_nat (mc + 1 - (n + 1)))) in H by lia.
  cbn [send_tree_ok] in H. replace (n <=? mc) with true in H by (symmetry; apply Z.leb_le; lia).
  cbv zeta in H. exact H.
Qed.

Definition cnts (pl c : Z) : Z * Z := if c =? 0 then (138, 3) else if c =? pl then (6, 3) else (7, 4).

Lemma cnts_tree_counts : forall c nl, tree_counts c nl = cnts c nl.
Proof. intros c nl. unfold tree_counts, cnts. rewrite (Z.eqb_sym c nl). reflexivity. Qed.

Definition BND (pl c k mx mn : Z) : Prop :=
  (pl = -1 \/ 0 <= pl <= 15) /\ 0 <= c <= 15 /\ 0 <= k < mx /\ (mx, mn) = cnts pl c.

Lemma BND_facts : forall pl c k mx mn, BND pl c k mx mn ->
  (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4) /\ (c = 0 -> mn = 3) /\ (c <> 0 -> c <> pl -> mn = 4).
Proof.
  intros pl c k mx mn (_ & _ & _ & E). unfold cnts in E.
  destruct (Z.eqb_spec c 0); [injection E; intros; subst; lia|].
  destruct (Z.eqb_spec c pl); injection E; intros; subst; lia.
Qed.

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).

Lemma sbs_ok1 : forall s v l, sbs_ok PBL s [(v, l)] -> sb_room PBL s l.
Proof. intros s v l H. cbn in H. tauto. Qed.

Section Level.

Local Ltac bnd :=
  unfold BND, cnts;
  repeat match goal with |- context [?x =? ?y] =>
    first [ rewrite (proj2 (Z.eqb_neq x y)) by lia | rewrite (proj2 (Z.eqb_eq x y)) by lia ] end;
  repeat split; try lia; try reflexivity.

Local Ltac cnts_in H :=
  unfold cnts in H |- *;
  repeat match type of H with context [?x =? ?y] =>
    first [ replace (x =? y) with false in H |- * by (symmetry; apply Z.eqb_neq; lia)
          | replace (x =? y) with true in H |- * by (symmetry; apply Z.eqb_eq; lia) ] end;
  cbv beta iota in H; cbv beta iota.

Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).
End Level.


Definition send_tree_safe : Prop := OK ds 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0).

Lemma send_tree_SL : send_tree ds t mc = SL ds 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0).
Proof.
  unfold send_tree, SL, RefSendTree3.cnts0. cbv zeta. replace (mc + 1 - 0) with (mc + 1) by lia.
  destruct (L 0 =? 0); reflexivity.
Qed.

End Walk.
