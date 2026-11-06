(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import ITree.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Printf_lib F_printf_iface Printf_pieces Printf_sn.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3 Require Export LeptFormats Printf_sn2 LeptModel.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3pm Require Export LeptFormatsPm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma lept_fmts_checked : forallb fmt_check LEPT_FMT_LIST = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem lept_model_run : forall fmt kinds args,
  In (fmt, kinds) LEPT_FMT_LIST -> Forall2 lept_arg_ok kinds args ->
  pass1_ok fmt = true /\ fp_calls (Datatypes.length fmt) fmt args = [] /\
  exists r d o, printf_model OUT_sn2 OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, (d, o)))
                /\ r = zlength (d ++ o) /\ zlength (d ++ o) <= 512 /\ Forall (fun c => 0 <= c < 256) (d ++ o)
                /\ zlength o <= SN_CAP.
Proof.
  intros fmt kinds args Hin FA.
  pose proof lept_fmts_checked as CK. rewrite forallb_forall in CK. specialize (CK _ Hin).
  unfold fmt_check in CK. cbn [fst snd] in CK. apply andb_prop in CK. destruct CK as [P1 SBK].
  destruct (shape_bound (Datatypes.length fmt) fmt kinds) as [B|] eqn:SB; [|discriminate]. apply Z.leb_le in SBK.
  split; [exact P1|]. split; [exact (fp_shape _ _ _ _ _ SB FA)|].
  destruct (ppl_shape _ _ _ _ 0 _ SB FA ltac:(lia) ltac:(lia)) as (ps & r & P & Hr & Hz & Hby).
  destruct (printf_model_sn2 fmt args ps r P) as (d & o & RUN & FL & CAP).
  exists r, d, o. rewrite FL. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Theorem lept_model_run_b : forall cap fmt kinds args,
  512 <= cap -> In (fmt, kinds) LEPT_FMT_LIST -> Forall2 lept_arg_ok kinds args ->
  pass1_ok fmt = true /\ fp_calls (Datatypes.length fmt) fmt args = [] /\
  exists r d o, printf_model (OUT_sn2b cap) OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, (d, o)))
                /\ r = zlength (d ++ o) /\ zlength (d ++ o) <= 512 /\ Forall (fun c => 0 <= c < 256) (d ++ o)
                /\ zlength o <= SN_CAP.
Proof.
  intros cap fmt kinds args Hcap Hin FA.
  pose proof lept_fmts_checked as CK. rewrite forallb_forall in CK. specialize (CK _ Hin).
  unfold fmt_check in CK. cbn [fst snd] in CK. apply andb_prop in CK. destruct CK as [P1 SBK].
  destruct (shape_bound (Datatypes.length fmt) fmt kinds) as [B|] eqn:SB; [|discriminate]. apply Z.leb_le in SBK.
  split; [exact P1|]. split; [exact (fp_shape _ _ _ _ _ SB FA)|].
  destruct (ppl_shape _ _ _ _ 0 _ SB FA ltac:(lia) ltac:(lia)) as (ps & r & P & Hr & Hz & Hby).
  destruct (printf_model_sn2b cap fmt args ps r P ltac:(lia)) as (d & o & RUN & FL & CAP).
  exists r, d, o. rewrite FL. repeat split; try assumption; lia.
Qed.
