(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_kit Z_flushpend Z_defl_arms Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate FillWinModel DeflateSafe RefDeflFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Lemma fp_avail_out : forall s, 0 <= cs_avail_out (ds_strm s) ->
  0 <= cs_avail_out (ds_strm (flush_pending s)) <= cs_avail_out (ds_strm s).
Proof.
  intros s RA. rewrite flush_pending_eq. cbv zeta. pose proof (tr_flush_bits_strm' s) as ES.
  assert (EL : 0 <= fp_len (tr_flush_bits s) <= cs_avail_out (ds_strm s)).
  { unfold fp_len. rewrite ES. pose proof (wrap32_range (ds_pending (tr_flush_bits s))).
    destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (wrap32 (ds_pending (tr_flush_bits s)))); lia. }
  destruct (fp_len (tr_flush_bits s) =? 0); [rewrite ES; lia|].
  unfold fp_tail. cbv zeta.
  assert (EA : forall c l v w, cs_avail_out (cset_total_out (cset_avail_out (cs_emit c l) v) w) = v) by (intros [] l v w; reflexivity).
  destruct (_ - _ =? 0); dsred; rewrite ?EA, ?ES; lia.
Qed.

Section PEND.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

End PEND.
