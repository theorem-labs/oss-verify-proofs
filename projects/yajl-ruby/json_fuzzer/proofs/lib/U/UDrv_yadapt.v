(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajl_iface UDrv_iface UDrv_ctx UDrv_run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zbytes_unsigned : forall l : list byte, zbytes (map bv_unsigned l) = l.
Proof.
  intros l. unfold zbytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH, (definitions.Z_to_bv_bv_unsigned 8 b). reflexivity.
Qed.

Lemma Forall_unsigned_range : forall l : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned l).
Proof.
  intros l. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma YST_RYST : forall m, YST m <->
  (rw_cells usegs m RY_CALLBACKS (callbacks_cells ryc) /\ rw_cells usegs m RY_BUF_ALLOC_ERROR (buf_alloc_error_cells ryc)
   /\ rw_cells usegs m RY_NOOP_ALLOCS noop_allocs_cells).
Proof.
  intros m. unfold YST, callbacks_cells, buf_alloc_error_cells, noop_allocs_cells, ryc. cbn. unfold wz, RY_CALLBACKS, RY_BUF_ALLOC_ERROR, RY_NOOP_ALLOCS,
    RY_CB_NULL, RY_CB_BOOLEAN, RY_CB_NUMBER, RY_CB_STRING, RY_CB_START_MAP, RY_CB_MAP_KEY, RY_CB_END_MAP, RY_CB_START_ARRAY, RY_CB_END_ARRAY,
    RY_NOOP_MALLOC, RY_NOOP_REALLOC, RY_NOOP_FREE. tauto.
Qed.

Section Adapt.
  Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
  Variable HKG : HKG_T.
  Hypothesis DI : drv_iface HKG.
  Variable FS0 : Fs.Fs.
  Notation HK := (HKG (G_fs FS0)).

  Theorem yfuzz_rz_of : yfuzz_stmt HK -> yfuzz_rz_stmt HK.
  Proof.
    intros YF REST T txt lo B errv K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s
           HK0 HKx YS BY T0 T62 L26 CONT NBLK AUX SPB ST CEIL LO SPA ERR MI TP A0 A1 K1.
    assert (LE : RY_FUZZ_STACK <= YDEPTH) by (vm_compute; discriminate).
    unfold YFUZZ_PC. change (Z_to_bv 64 80288) with (wz RY_FUZZ).
    assert (ZL : zlength (map bv_unsigned txt) = Z.of_nat (length txt)) by (unfold zlength; rewrite length_map; reflexivity).
    unfold yfuzz_stmt in YF.
    apply (YF REST T (map bv_unsigned txt) lo B errv K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s); try assumption.
    - split; [exact HKx|]. apply YST_RYST. exact YS.
    - split; [rewrite zbytes_unsigned; exact BY|]. split; [apply Forall_unsigned_range|]. rewrite ZL. split; [exact T0 | exact T62].
    - rewrite ZL. exact L26.
    - rewrite ZL. destruct CONT as [C1 | C2]; [left; exact C1 | right; rewrite C2; reflexivity].
    (* [comment removed for export] *)
    - unfold yframe_pre.
      split; [exact AUX|]. split; [exact SPB|]. split; [exact ST|]. split; [exact CEIL|]. split; [lia|]. split; [exact ERR|]. split; [exact MI| exact TP].
    - rewrite ZL. exact A1.
    - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' s' F' LK ((MI' & ST' & (errv' & ERR') & AUX' & PR) & HA0 & _ & _ & HLK & (HK' & Y1 & Y2 & Y3)) FS.
      apply (K1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' s' F' LK errv'); try assumption.
      + apply ry_pres_nil. exact PR.
      + apply YST_RYST. auto.
      + rewrite (di_fs HKG DI _ _ _ _ _ HKx), (di_fs HKG DI _ _ _ _ _ HK'). reflexivity.
  Qed.
End Adapt.
