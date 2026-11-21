(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBitsFwd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefTreesApi.
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
(* [comment removed for export] *)
Local Notation L i := (Len ds t i).
Local Notation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Notation BL c := (arr_get (ds_bl_tree_dl ds) c).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stF (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb (tree_dl ds t) x | 1%nat => pb (ds_bl_tree_fc ds) x | _ => pb (ds_bl_tree_dl ds) x end.

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 17); (36%nat, 2 ^ 63); (37%nat, 600); (38%nat, 600);
   (39%nat, 19); (40%nat, 65536); (41%nat, 200); (42%nat, 65536); (43%nat, 200); (44%nat, 10); (45%nat, 2 ^ 63);
   (46%nat, 200); (47%nat, 65536); (48%nat, 2 ^ 64); (49%nat, 65536); (50%nat, 65536)].

Local Ltac nf := cbn [stF].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Local Ltac sbv_site pc_flush pc_keep rdF rdK pins pv HB HP HAG HRB vnorm :=
  idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac zsite code HB HP HAG HRB Efc Edl :=
  idtac.

End Walk.
