(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of the walk of verbs_receive on the ASan build of plugin-hostd/fuzz_command,
   copied from the reply walk (an earlier version of lib/A/Prog/reply_s1.v, :1-291): the recorder
   representation under a memory that agrees on what it reads (rec_repA_agree). The call rule for a callee whose
   footprint holds program statics is the kit's (lib/A/Prog/PaCallPg.v cl_callS_pg). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/verbs_receive_kit.v; 51 of its 131 lines of code are new or changed and 94 lines of the source are left out. *)
(* Helpers of the walk of pin_set_words on the ASan build of plugin-hostd/fuzz_command (pin_set_words_s4.v and
   the segment files): the facts the walk reads at its calls, carried from the entry state to a state whose memory
   agrees with the entry's on the bytes they name: the recorder representation's blocks, the token array and its
   words (atoks_atA), and the read-only literals of the image (cmd_ro_ok). The call rule for the recorder callees and
   the transport of rec_repA are the kit's (lib/A/Prog/PaCallPg.v: cl_callS_pg, rec_repA_kept). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdBase CmdRo CmdRep PaArt PaCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------- the recorder representation under a reader that agrees on what it reads ---------- *)
Lemma aval_mem_agree : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.
Lemma abytes_atR_agree : forall (rd rd' : reader) p l n,
abytes_atR rd p l -> Z.of_nat (length l) <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l n H Hle Hk i Hi. rewrite Hk by lia. exact (H i Hi). Qed.
Lemma astr_atR_agree : forall (rd rd' : reader) p s n,
astr_atR rd p s -> Z.of_nat (length s) + 1 <= n -> (forall k, 0 <= k < n -> rd' (p + k) = rd (p + k)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s n [Hb Hn0] Hle Hk. split; [|exact Hn0].
apply (abytes_atR_agree rd rd' p _ n Hb); [rewrite length_app; cbn [length]; lia | exact Hk].
Qed.
Lemma in_lay_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn Hi Hp. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hi) | exact Hp].
Qed.
Lemma in_lay_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma in_lay_answer : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite H. left. reflexivity. Qed.
Lemma in_lay_reply : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite H. left. reflexivity. Qed.
Lemma lay_blocks_in_bl : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HR & _) Hin.
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  destruct HC as (C1 & C2 & _ & C4 & _).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_Some in Hi'; contradiction].
  destruct (C4 i c P Hc Hi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
  exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HC as (_ & _ & _ & _ & (_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
    exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in HA. destruct (l_answer Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R); [exact (proj1 (proj2 (proj2 HA))) | contradiction].
    * unfold areply_at in HR. destruct (l_reply Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R); [exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))) | contradiction].
Qed.

(* ---------- the token array and the read-only literals under an agreeing reader ---------- *)
Lemma atoks_atA_agree : forall (rd rd' : reader) tok ptrs tks cb ncb,
atoks_atA rd tok ptrs tks cb ncb ->
(forall k, 0 <= k < 8 * Z.of_nat (length ptrs) -> rd' (tok + k) = rd (tok + k)) ->
(forall k, 0 <= k < ncb -> rd' (cb + k) = rd (cb + k)) ->
atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb (H8 & Hlen & Hp & Hw) HT HB.
split; [exact H8|]. split; [exact Hlen|]. split.
- intros i p Hi. apply (aval_mem_agree rd rd' _ 8 _ (Hp i p Hi)).
  assert (Hi' : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  replace (tok + 8 * Z.of_nat i + k) with (tok + (8 * Z.of_nat i + k)) by lia. apply HT. lia.
- intros i p w Hi Hw'. destruct (Hw i p w Hi Hw') as (Hs & Hl & Hc1 & Hc2).
  split; [|split; [exact Hl | split; [exact Hc1 | exact Hc2]]].
  apply (astr_atR_agree rd rd' _ _ (cb + ncb - p) Hs); [lia|].
  intros k Hk. replace (p + k) with (cb + (p - cb + k)) by lia. apply HB. lia.
Qed.

Section ro.
Variable segs : list Segment.
Lemma ro_bytes_kept : forall (rd rd' : reader) lo hi p (l : list byte),
kept_out rd rd' lo hi -> abytes_atR rd p l -> 0 <= p -> p + Z.of_nat (length l) <= 0x606000 ->
0x606000 <= lo -> lo < 2 ^ 64 -> abytes_atR rd' p l.
Proof. intros rd rd' lo hi p l HK H Hp Hl Hlo H64. exact (abytes_atR_kept rd rd' lo hi p l HK H Hp ltac:(lia) ltac:(lia)). Qed.
Lemma cmd_ro_ends_low : forall e, In e cmd_ro_ends -> 0 <= e < 0xa7100.
Proof.
intros e Hin.
assert (Hall : forallb (fun x => (0 <=? x) && (x <? 0xa7100)) cmd_ro_ends = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall e Hin).
apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma cmd_ro_tails_kept : forall (rd rd' : reader) lo hi,
kept_out rd rd' lo hi -> cmd_ro_tails rd -> 0x606000 <= lo -> lo < 2 ^ 64 -> cmd_ro_tails rd'.
Proof.
intros rd rd' lo hi HK H Hlo H64 e Hin a Ha.
pose proof (cmd_ro_ends_low e Hin) as He. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (tail_below e 0xa8000 ltac:(lia) ltac:(reflexivity)).
rewrite HK by lia. exact (H e Hin a Ha).
Qed.
Ltac ro_one HK Hlo H64 :=
eapply (ro_bytes_kept _ _ _ _ _ _ HK); [eassumption | vm_compute; discriminate | vm_compute; discriminate | exact Hlo | exact H64].
Lemma cmd_ro_ok_kept : forall (rd rd' : reader) lo hi,
kept_out rd rd' lo hi -> cmd_ro_ok rd -> 0x606000 <= lo -> lo < 2 ^ 64 -> cmd_ro_ok rd'.
Proof.
intros rd rd' lo hi HK [Hb Ht] Hlo H64.
split; [|exact (cmd_ro_tails_kept rd rd' lo hi HK Ht Hlo H64)].
unfold cmd_ro_bytes in Hb |- *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat (split; [ro_one HK Hlo H64|]); ro_one HK Hlo H64.
Qed.
End ro.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
Section e.
Variable B : asyms.
Lemma rec_repA_in_blocks : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HA & HOQ) Hpn. apply (lay_blocks_in_bl _ rd _ _ R Q pn HA). apply HOQ. exact Hpn. Qed.

End e.
End f.
End d.
