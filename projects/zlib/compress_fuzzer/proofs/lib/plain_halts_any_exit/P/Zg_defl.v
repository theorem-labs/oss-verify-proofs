(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_model Z_defl_kit
  Z_defl_path Z_defl_entry Z_defl_arms Z_defl_pend Z_defl_hdr Z_defl_blocks Z_defl_fin
  Z_adler32 Zg_adler32_iface Zg_defl_iface Zg_defl_path Zg_defl_entry Zg_defl_pend Zg_defl_hdr Zg_defl_blocks Zg_defl_fin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflSlow6 RefDeflSafeS DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ASMG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HSLOW : deflate_slow_stmtg.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = 0 \/ flush = 4 \/ flush = 5.

Lemma defl_dispg : forall (Q : machine_state -> Prop) (X : deflate_state),
  (ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) -> 0 <= cs_avail_in (ds_strm X) < 2^31 ->
  (ds_status X = 42 -> DKH L flush rest0 lo r F fc me Q X) ->
  (ds_status X = 113 -> DK L flush rest0 lo r F fc me Q 0x17a00 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) = 0 -> DK L flush rest0 lo r F fc me Q 0x17a08 X) ->
  (ds_status X = 666 -> cs_avail_in (ds_strm X) <> 0 -> DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR))) ->
  DKB L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X HST RAI KH K90 K98 KERR. unfold DKB. intros until m'. intros DI.
  unfold deflR.
  destruct HST as [E|[E|E]].
  - specialize (KH E). clear K90 K98 KERR. rewrite E. zs. zstep. closed_br.
    unfold DKH, deflR in KH. eapply KH. exact DI.
  - specialize (K90 E). clear KH K98 KERR. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs. zstep. closed_br. zs.
    unfold DK, deflR in K90. eapply K90. exact DI.
  - specialize (K98 E). specialize (KERR E). clear KH K90. rewrite E. zs. zstep. closed_br.
    zs. zstep. closed_br.
    pose proof DI as DI0. destruct DI as (DR & _). destruct DR as [ZS _]. open_zs ZS.
    zs. zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
    + unfold DK, deflR in K98. eapply (K98 ltac:(lia)). exact DI0.
    + eapply (defl_buferr L inp rest0 lo r F fc me CTX Q X 0x16ef4); [right; right; reflexivity| exact DI0| apply KERR; lia].
Qed.

Variables (R : deflate_state * Z) (Q : machine_state -> Prop).
Hypothesis EXIT : forall X rc, R = (X, rc) -> DKE L rest0 lo r F fc me Q (wz rc) X.
Hypothesis ROOMR : (length (cs_out_rev (ds_strm (fst R))) <= length rest0)%nat.

End ASMG.

Section DEFLG.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HSLOW : deflate_slow_stmtg.
Hypothesis HTFB : tr_flush_bits_stmt.

End DEFLG.
