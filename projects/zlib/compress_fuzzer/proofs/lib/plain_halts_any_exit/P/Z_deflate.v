(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr Frame Mem MState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZInst Stdio.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zlib_iface Z_kit Z_dview Z_drep Z_dkit Z_zrd Z_trees_iface Z_defl_iface Z_defl_path Z_defl Z_slow Z_dinit_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Deflate DeflateSafe RefDeflateRel RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI4 BoundFw BoundCall BoundPat ZApiInst ZApiOk ZTaint ZPat.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wq := (Z_to_bv 64).

Lemma upd_nat_app : forall (pre post : list Z) x b, upd_nat (pre ++ x :: post) (length pre) b = pre ++ b :: post.
Proof. induction pre as [|a pre IH]; intros post x b; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma zstore_split : forall (bs pre post : list Z), (length bs <= length post)%nat ->
  zstore (pre ++ post) (Z.of_nat (length pre)) bs = pre ++ bs ++ skipn (length bs) post.
Proof.
  induction bs as [|b bs IH]; intros pre post HL; cbn; [reflexivity|].
  destruct post as [|x post]; [cbn in HL; lia|]. cbn in HL.
  unfold zupd. replace (Z.of_nat (length pre) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Nat2Z.id, upd_nat_app.
  replace (pre ++ b :: post) with ((pre ++ [b]) ++ post) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [b]))) by (rewrite length_app; cbn; lia).
  rewrite IH by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma zstore_at : forall out o bs, 0 <= o -> (Z.to_nat o + length bs <= length out)%nat ->
  zstore out o bs = firstn (Z.to_nat o) out ++ bs ++ skipn (length bs) (skipn (Z.to_nat o) out).
Proof.
  intros out o bs Ho HL.
  pose proof (zstore_split bs (firstn (Z.to_nat o) out) (skipn (Z.to_nat o) out) ltac:(rewrite length_skipn; lia)) as E.
  rewrite firstn_skipn, length_firstn, Nat.min_l, Z2Nat.id in E by lia. exact E.
Qed.

Lemma to_bytes_app : forall l1 l2, to_bytes (l1 ++ l2) = to_bytes l1 ++ to_bytes l2.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. intros. unfold to_bytes. symmetry. apply firstn_map. Qed.
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. symmetry. apply skipn_map. Qed.
Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma nth_error_outv_tail : forall rest0 c i, (length (cs_out_rev c) <= length rest0)%nat -> (length (cs_out_rev c) <= i)%nat ->
  nth_error (outv rest0 c) i = nth_error rest0 i.
Proof.
  intros rest0 c i HL Hi. unfold outv.
  assert (L1 : length (zb8 (rev (cs_out_rev c))) = length (cs_out_rev c)) by (rewrite zb8_length, length_rev; reflexivity).
  rewrite nth_error_app2 by lia. rewrite L1, nth_error_skipn. f_equal. lia.
Qed.

Section PURE.
  Variables (sa : deflate_state) (d : list Z) (x : dstream) (ai ao flush : Z).
  Hypothesis DR : DREL sa x.
  Hypothesis PT : PAT sa.
  Hypothesis ZOK : zstrm_okP (dz_z x).
  Hypothesis HAI : 0 <= ai <= 1.
  Hypothesis HTIN : zs_total_in (dz_z x) + ai <= zlength d.
  Hypothesis HDL : zlength d < 2 ^ 63.
  Hypothesis HAO : 0 <= ao <= 1.
  Hypothesis HD : Forall (fun c => 0 <= c < 256) d.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

  Definition czc : ZCall := zd_zcall d x ai ao.
  Definition cd0 : deflate_state := set_strm sa (cstrm_of_call czc).

End PURE.

Definition dl_io (L : dlay) (ni no : Z) : dlay := Z_drep.mkDL (dl_S L) (dl_As L) (dl_Aw L) (dl_Ap L) (dl_Ah L) (dl_Ab L) ni no.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma DST_io : forall m L s ni no, DST m L s -> DST m (dl_io L ni no) s.
Proof.
  intros m L s ni no [HA HB0 HC HD Hlt Hdt Hbt Hblc Hheap Hdep Hwin Hprev Hhead Hpend Hlens Hlay]. destruct L as [LS LAs LAw LAp LAh LAb LNI LNO]. unfold dl_io. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab].
  constructor; [exact HA| exact HB0| exact HC| exact HD| exact Hlt| exact Hdt| exact Hbt| exact Hblc| exact Hheap| exact Hdep
               | exact Hwin| exact Hprev| exact Hhead| exact Hpend| exact Hlens |].
  destruct Hlay. constructor; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab] in *; assumption.
Qed.
Lemma DST_io_back : forall m L s ni no, DST m (dl_io L ni no) s -> DST m L s.
Proof.
  intros m L s ni no [HA HB0 HC HD Hlt Hdt Hbt Hblc Hheap Hdep Hwin Hprev Hhead Hpend Hlens Hlay]. destruct L as [LS LAs LAw LAp LAh LAb LNI LNO]. unfold dl_io in *. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab] in *.
  constructor; [exact HA| exact HB0| exact HC| exact HD| exact Hlt| exact Hdt| exact Hbt| exact Hblc| exact Hheap| exact Hdep
               | exact Hwin| exact Hprev| exact Hhead| exact Hpend| exact Hlens |].
  destruct Hlay. constructor; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab] in *; assumption.
Qed.

Lemma munch_shrink : forall W W' (m m' : mem), munch W m m' -> (forall x : word, outside W' (bv_unsigned x) -> outside W (bv_unsigned x) \/ m' x = m x) -> munch W' m m'.
Proof. intros W W' m m' MU H x Hx. destruct (H x Hx) as [O|E]; [exact (MU x O)| exact E]. Qed.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Transparent the_zapi.

Section CLOSE.
  Hypothesis HFW : fill_window_stmt.
  Hypothesis HTFBLK : tr_flush_block_stmt.
  Hypothesis HTFB : tr_flush_bits_stmt.

End CLOSE.
End WithCeiling0.
