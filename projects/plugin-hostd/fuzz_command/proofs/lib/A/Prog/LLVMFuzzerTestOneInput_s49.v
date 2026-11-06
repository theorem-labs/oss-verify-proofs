(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the recorder's representation carried through the inlined words_of of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86718 .. 0x8693c), over PaCallPg.v's rec_repA_kept: the segment's writes (the three words blocks, the stack frame) lie outside g_rec, record.spill, g_quitting and the recorder's blocks, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh7.v (the facts a walk keeps across its own stores). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdPaLib CmdGlob CmdRep PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s40.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the bytes the recorder's representation reads: g_rec, record.spill, g_quitting and the recorder's blocks O *)
Definition aw_area (O : list (Z * Z)) (a : Z) : Prop :=
  A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  A_G_QUITTING <= a < A_G_QUITTING + 4 \/ inFP (ablocks_fp O) a.

(* the recorder after the send is kept by any change of memory outside that area *)
Lemma aw_rec_kept : forall cx q ly S (W : world SEGS) mem mem' extra,
  aw_rec B cx q ly S W mem extra ->
  (forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
     A_G_QUITTING <= a < A_G_QUITTING + 4 \/ inFP (ablocks_fp (q_O1 q)) a -> rdW W mem' a = rdW W mem a) ->
  aw_rec B cx q ly S W mem' extra.
Proof.
intros cx q ly S W mem mem' extra H HK. unfold aw_rec, lt_rec in *.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
split.
- apply (rec_repA_kept B ly S _ ly S _ _ _ H1).
  + intros pn Hpn. apply (Permutation_in _ (Permutation_sym H6)). apply in_or_app. left. exact Hpn.
  + intros a Ha. apply HK. tauto.
- split; [exact H2|]. split; [exact H3|]. split.
  + apply (aval_mem_kept_r (rdW W mem) (rdW W mem') _ 4 _); [|exact H4]. intros x Hx. apply HK. right. right. left. lia.
  + split; [exact H5 | exact H6].
Qed.

(* the same, for a world that changed too (the reader is the new world's) *)
Lemma aw_rec_kept_w : forall cx q ly S (W W' : world SEGS) mem mem' extra,
  aw_rec B cx q ly S W mem extra ->
  (forall a, aw_area (q_O1 q) a -> rdW W' mem' a = rdW W mem a) ->
  aw_rec B cx q ly S W' mem' extra.
Proof.
intros cx q ly S W W' mem mem' extra H HK. unfold aw_rec, lt_rec in *.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
split.
- apply (rec_repA_kept B ly S _ ly S _ _ _ H1).
  + intros pn Hpn. apply (Permutation_in _ (Permutation_sym H6)). apply in_or_app. left. exact Hpn.
  + intros a Ha. apply HK. unfold aw_area. tauto.
- split; [exact H2|]. split; [exact H3|]. split.
  + apply (aval_mem_kept_r (rdW W mem) (rdW W' mem') _ 4 _); [|exact H4]. intros x Hx. apply HK. unfold aw_area. right. right. left. lia.
  + split; [exact H5 | exact H6].
Qed.

Hypothesis LAWS : AR_laws SEGS B.

(* a byte of one of the three words blocks is outside the recorder's area *)
Lemma aw_area_words : forall cx q ly S (W : world SEGS) mem md text copy arr b n a,
  AR SEGS B ly S W mem md -> aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) ->
  In (b, n) (aw_blocks cx q text copy arr) -> b <= a < b + req_size n ->
  ~ aw_area (q_O1 q) a.
Proof.
intros cx q ly S W mem md text copy arr b n a HAR H Hbn Ha. unfold aw_rec, lt_rec in H.
destruct H as (_ & _ & _ & _ & _ & HP).
assert (Hin : In (b, n) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. right. exact Hbn. }
pose proof (blk_off_imgP B ly S W mem md b n HAR Hin) as Hoff. unfold off_img in Hoff.
unfold aw_area. intros [Hg | [Hs | [Hq | (r & Hr & Hra)]]].
- unfold A_G_REC, REC_SIZE in Hg. lia.
- unfold A_REC_SPILL, SC_SIZE in Hs. lia.
- unfold A_G_QUITTING in Hq. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p k] & <- & Hpk). cbn [fst snd] in Hra.
  destruct (in_split _ _ Hpk) as (O1 & O2 & EO). destruct (in_split _ _ Hbn) as (W1 & W2 & EW).
  assert (HP2 : Permutation (ablocks B ly S) ((p, k) :: (b, n) :: (O1 ++ O2 ++ x_bl0 B cx ++ W1 ++ W2))).
  { eapply Permutation_trans; [exact HP|]. rewrite EO, EW.
    apply Permutation_sym. rewrite <- app_assoc. cbn [app]. apply Permutation_cons_app.
    replace (O1 ++ O2 ++ x_bl0 B cx ++ W1 ++ (b, n) :: W2) with ((O1 ++ O2 ++ x_bl0 B cx ++ W1) ++ (b, n) :: W2)
      by (rewrite <- !app_assoc; reflexivity).
    apply Permutation_cons_app. rewrite <- !app_assoc. apply Permutation_refl. }
  assert (D : zdisjoint (block_rng (p, k)) (block_rng (b, n))) by (eapply sep_blocks_perm; eassumption).
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* a byte at or above the allocator's ceiling (the stack) is outside the recorder's area *)
Lemma aw_area_stack : forall cx q ly S (W : world SEGS) mem md extra a,
  AR SEGS B ly S W mem md -> aw_rec B cx q ly S W mem extra -> alloc_ceiling <= a ->
  ~ aw_area (q_O1 q) a.
Proof.
intros cx q ly S W mem md extra a HAR H Ha. unfold aw_rec, lt_rec in H.
destruct H as (_ & _ & _ & _ & _ & HP).
pose proof alloc_ceiling_value as [[Hc _] _].
unfold aw_area. intros [Hg | [Hs | [Hq | (r & Hr & Hra)]]].
- unfold A_G_REC, REC_SIZE in Hg. lia.
- unfold A_REC_SPILL, SC_SIZE in Hs. lia.
- unfold A_G_QUITTING in Hq. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p k] & <- & Hpk). cbn [fst snd] in Hra.
  assert (Hin : In (p, k) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hpk. }
  destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & _ & Hpc & _). lia.
Qed.

End e.
End f.
End d.
