(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of the walk of reply on the ASan build of plugin-hostd/fuzz_command
   (reply.v): the recorder representation under a memory that agrees on what it reads. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* the recorder representation reads only g_rec, record.spill and the recorder's own blocks *)
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
Lemma acall_at_agree : forall bl bl' rd rd' a c P,
acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < 8 + 8 * Z.of_nat (length P) -> rd' (a + k) = rd (a + k)) ->
(forall pn, In pn P -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & Hfn & Hna & Hnd & Hargs) HB HR HS.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_agree rd rd' _ 4 _ Hfn); intros k Hk; unfold CALL_OFF_FN; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 0 + k) with (a + k) by lia; apply HR; lia|].
split; [apply (aval_mem_agree rd rd' _ 4 _ Hna); intros k Hk; unfold CALL_OFF_NARGS; change (Z.of_nat 4) with 4 in Hk;
  replace (a + 4 + k) with (a + (4 + k)) by lia; apply HR; lia|].
split; [exact Hnd|].
intros k s pn Hs Hpn. destruct (Hargs k s pn Hs Hpn) as (A1 & A2 & A3 & A4 & A5).
assert (Hk : (k < length P)%nat) by (apply nth_error_Some; rewrite Hpn; discriminate).
pose proof (nth_error_In _ _ Hpn) as HinP.
split; [|split; [exact A2|split; [exact (HB pn HinP A3)|split; [exact A4|]]]].
- apply (aval_mem_agree rd rd' _ 8 _ A1). intros kk Hkk. unfold CALL_OFF_ARGS. change (Z.of_nat 8) with 8 in Hkk.
  replace (a + 8 + 8 * Z.of_nat k + kk) with (a + (8 + 8 * Z.of_nat k + kk)) by lia. apply HR. lia.
- apply (astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HS pn HinP).
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
Lemma arep_at_agree : forall bl bl' rd rd' gr sc R Q,
arep_at bl rd gr sc R Q ->
(forall pn, In pn (lay_blocks Q) -> In pn bl -> In pn bl') ->
(forall k, 0 <= k < REC_SIZE -> rd' (gr + k) = rd (gr + k)) ->
(forall k, 0 <= k < SC_SIZE -> rd' (sc + k) = rd (sc + k)) ->
(forall pn, In pn (lay_blocks Q) -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
arep_at bl' rd' gr sc R Q.
Proof.
intros bl bl' rd rd' gr sc R Q (Hg8 & Hs8 & Hap & HC & HA & HR & HSc & HOwn) HB HG HSP HO.
assert (VG : forall off n v, aval_mem rd (gr + off) n v -> 0 <= off -> off + Z.of_nat n <= REC_SIZE -> aval_mem rd' (gr + off) n v).
{ intros off n v H H0 H1. apply (aval_mem_agree rd rd' _ n _ H). intros k Hk.
  replace (gr + off + k) with (gr + (off + k)) by lia. apply HG. lia. }
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|]. split; [apply VG; [exact C3 | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, REC_SIZE; cbn; lia]|].
  split; [|split; [|exact C6]].
  - intros i c P Hc HP. destruct (C4 i c P Hc HP) as [A F]. split; [|exact F].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    pose proof A as (_ & Hn6 & HlP & _).
    apply (acall_at_agree bl bl' rd rd' _ c P A).
    + intros pn Hpn. apply HB. exact (in_lay_calls Q i P pn HP Hpn).
    + intros k Hk. replace (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i + k) with (gr + (OFF_CALLS + CALL_SIZE * Z.of_nat i + k)) by lia.
      apply HG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (in_lay_calls Q i P pn HP Hpn).
  - pose proof C5 as (_ & Hn6 & HlP & _). apply (acall_at_agree bl bl' rd rd' _ _ _ C5).
    + intros pn Hpn. apply HB. exact (in_lay_spill Q pn Hpn).
    + intros k Hk. apply HSP. unfold SC_SIZE. rewrite HlP in Hk. lia.
    + intros pn Hpn. apply HO. exact (in_lay_spill Q pn Hpn). }
split.
{ unfold aanswer_at in *. destruct (r_answer R) as [x|] eqn:Ea, (l_answer Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HA as (A1 & A2 & A3 & A4 & A5 & A6).
    split; [apply VG; [exact A1 | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]|].
    split; [exact A2|]. split; [exact (HB pn (in_lay_answer Q pn Eq) A3)|]. split; [exact A4|]. split; [|exact A6].
    apply (astr_atR_agree rd rd' _ _ (snd pn) A5); [lia|]. exact (HO pn (in_lay_answer Q pn Eq)).
  - apply VG; [exact HA | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia]. }
split.
{ unfold areply_at in *. destruct (r_reply R) as [x|] eqn:Ea, (l_reply Q) as [pn|] eqn:Eq; try contradiction.
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply VG; [exact A1 | unfold OFF_REPLY; lia | unfold OFF_REPLY, REC_SIZE; cbn; lia]|].
    split; [apply VG; [exact A2 | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, REC_SIZE; cbn; lia]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (HB pn (in_lay_reply Q pn Eq) A5)|]. split; [exact A6|]. split; [|exact A8].
    apply (abytes_atR_agree rd rd' _ _ (snd pn) A7); [lia|]. exact (HO pn (in_lay_reply Q pn Eq)).
  - destruct HR as [A1 A2].
    split; apply VG; first [exact A1 | exact A2 | unfold OFF_REPLY, OFF_REPLY_SIZE; lia | unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE; cbn; lia]. }
split; [|exact HOwn].
destruct HSc as (S1 & S2 & S3 & S4 & S5 & REST).
split; [apply VG; [exact S1 | unfold OFF_REFUSE; lia | unfold OFF_REFUSE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S2 | unfold OFF_CODE; lia | unfold OFF_CODE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S3 | unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S4 | unfold OFF_STATE; lia | unfold OFF_STATE, REC_SIZE; cbn; lia]|].
split; [apply VG; [exact S5 | unfold OFF_HOST; lia | unfold OFF_HOST, REC_SIZE; cbn; lia] | exact REST].
Qed.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Lemma rec_repA_agree : forall ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
(forall k, 0 <= k < REC_SIZE -> rd' (A_G_REC + k) = rd (A_G_REC + k)) ->
(forall k, 0 <= k < SC_SIZE -> rd' (A_REC_SPILL + k) = rd (A_REC_SPILL + k)) ->
(forall pn, In pn O -> forall k, 0 <= k < snd pn -> rd' (fst pn + k) = rd (fst pn + k)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S ly' S' rd rd' R O (Q & HA & HOQ) HB HG HS HO. exists Q. split; [|exact HOQ].
apply (arep_at_agree _ _ rd rd' _ _ R Q HA).
- intros pn Hpn Hbl. apply HB; [apply HOQ; exact Hpn | exact Hbl].
- exact HG. - exact HS.
- intros pn Hpn. apply HO. apply HOQ. exact Hpn.
Qed.
Lemma rec_repA_in_blocks : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HA & HOQ) Hpn. apply (lay_blocks_in_bl _ rd _ _ R Q pn HA). apply HOQ. exact Hpn. Qed.
End e.
End f.
End d.
