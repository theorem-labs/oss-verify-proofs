(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.

Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Lemma noseg_low : forall x : word, bv_unsigned x < AIMG_LO -> noseg asegs x.
Proof.
  intros x Hx s Hs. unfold AIMG_LO in Hx. pose proof (bv_unsigned_in_range 64 x) as RX. cbn in Hs.
  destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma noseg_out : forall a, 0 <= a < 2^64 -> (a < AIMG_LO \/ AIMG_HI <= a) -> noseg asegs (wa a).
Proof.
  intros a Ha [H|H]; [apply noseg_low| apply noseg_high]; rewrite wa_unsigned by lia; exact H.
Qed.

(* [comment removed for export] *)
Lemma oclr_noseg : forall lo hi a, oclr lo hi -> lo <= a < hi -> hi <= 2^64 -> noseg asegs (wa a).
Proof.
  intros lo hi a O Ha Hhi. destruct (oclr_lin lo hi O ltac:(lia)) as (L1 & _ & L3).
  apply noseg_out; [lia|]. destruct L3 as [L3|L3]; [left|right]; lia.
Qed.

Lemma stk_wmono_oclr : forall m m' lo hi,
  stk asegs m lo hi -> wmono asegs m m' -> oclr lo hi -> hi <= 2^64 -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) HW O Hhi. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [Hw [b Hb]]. pose proof (HW _ Hw) as Hw'. split; [exact Hw'|].
  assert (NS : noseg asegs (wa a)) by (apply (oclr_noseg lo hi); [exact O| exact Ha| exact Hhi]).
  pose proof (wview_noseg_some m' (wa a) NS Hw') as Hs. unfold mrd. destruct (m' (wa a)) as [b'|]; [eexists; reflexivity| congruence].
Qed.

Lemma stk_some_oclr : forall m lo hi a, stk asegs m lo hi -> lo <= a < hi -> oclr lo hi -> hi <= 2^64 -> m (wa a) <> None.
Proof.
  intros m lo hi a (H1 & H2 & H) Ha O Hhi. destruct (H a Ha) as [Hw _]. apply wview_noseg_some; [apply (oclr_noseg lo hi); assumption| exact Hw].
Qed.

(* [comment removed for export] *)
Lemma ceil_lt64 : alloc_ceiling < 2^64.
Proof. pose proof alloc_ceiling_range. lia. Qed.

End CeilWrap.
