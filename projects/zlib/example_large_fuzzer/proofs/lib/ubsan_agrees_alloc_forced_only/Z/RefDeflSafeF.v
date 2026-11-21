(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition lz_meas (s : deflate_state) : Z := ds_lookahead s + cs_avail_in (ds_strm s).

Lemma lz_fuel_meas : forall s, 0 <= lz_meas s -> lz_meas s < Z.of_nat (lz_fuel s).
Proof. intros s H. unfold lz_fuel, lz_meas in *. rewrite Z2Nat.id; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FastFrame.
  Variable ws : Z.
Variable hs : Z.
Variable flush : Z.
  (* [comment removed for export] *)
  Variable FTI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, FTI s -> 0 <= lz_meas s.
  (* [comment removed for export] *)
  Hypothesis Hstep : forall s, FTI s ->
    trip_ok ws hs s flush
    /\ match snd (st_body s flush) with
       | LCont => FTI (fst (st_body s flush)) /\ lz_meas (fst (st_body s flush)) < lz_meas s
       | LBreak => FTI (fst (st_body s flush))
       | LRet _ => True
       end.

  (* [comment removed for export] *)
  Hypothesis Htail : forall s, FTI s -> tail_ok ws s flush.

End FastFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SlowFrame.
  Variable ws : Z.
Variable hs : Z.
Variable flush : Z.
  Variable STI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, STI s -> 0 <= lz_meas s.
  Hypothesis Hstep : forall s, STI s ->
    strip_ok ws hs s flush
    /\ match snd (st_sbody s flush) with
       | LCont => STI (fst (st_sbody s flush)) /\ lz_meas (fst (st_sbody s flush)) < lz_meas s
       | LBreak => STI (fst (st_sbody s flush))
       | LRet _ => True
       end.

  Hypothesis Htail : forall s, STI s -> stail_ok ws s flush.

End SlowFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hloop_step : forall f s flush,
  deflate_huff_loop (S f) s flush
  = match snd (hf_body s flush) with
    | LCont => deflate_huff_loop f (fst (hf_body s flush)) flush
    | LBreak => (fst (hf_body s flush), None)
    | LRet bs => (fst (hf_body s flush), Some bs)
    end.
Proof. intros. cbn [deflate_huff_loop]. rewrite hf_body_eq. destruct (hf_body s flush) as [s' o]. reflexivity. Qed.

Lemma rloop_step : forall f s flush,
  deflate_rle_loop (S f) s flush
  = match snd (rl_body s flush) with
    | LCont => deflate_rle_loop f (fst (rl_body s flush)) flush
    | LBreak => (fst (rl_body s flush), None)
    | LRet bs => (fst (rl_body s flush), Some bs)
    end.
Proof. intros. cbn [deflate_rle_loop]. rewrite rl_body_eq. destruct (rl_body s flush) as [s' o]. reflexivity. Qed.

Section HuffFrame.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
  Variable flush : Z.
  Variable HTI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, HTI s -> 0 <= lz_meas s.
  Hypothesis Hstep : forall s, HTI s ->
    hf_trip_ok FB s flush
    /\ match snd (hf_body s flush) with
       | LCont => HTI (fst (hf_body s flush)) /\ lz_meas (fst (hf_body s flush)) < lz_meas s
       | LBreak => HTI (fst (hf_body s flush))
       | LRet _ => HTI (fst (hf_body s flush))
       end.

End HuffFrame.

Section RleFrame.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
  Variable flush : Z.
  Variable RTI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, RTI s -> 0 <= lz_meas s.
  Hypothesis Hstep : forall s, RTI s ->
    rl_trip_ok FB s flush
    /\ match snd (rl_body s flush) with
       | LCont => RTI (fst (rl_body s flush)) /\ lz_meas (fst (rl_body s flush)) < lz_meas s
       | LBreak => RTI (fst (rl_body s flush))
       | LRet _ => RTI (fst (rl_body s flush))
       end.

End RleFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

