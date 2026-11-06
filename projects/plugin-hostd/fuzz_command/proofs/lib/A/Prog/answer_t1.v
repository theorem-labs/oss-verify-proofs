(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the lemmas the JOIN segment of answer's ASan walk (lib/A/Prog/answer_t.v)
   needs beside the walk itself: the bridge from CmdRep's reader-level field read (aval_mem) to the kit's
   val_mem / rdword, the transport of the recorder's representation (rec_repA) over a reader that keeps g_rec,
   record.spill and the live blocks, the blocks the recorder owns as live blocks, and the live-byte count over a
   permutation of the block list. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdBase CmdRep PaLibF.
From stdpp Require list.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
(* lia without the Euclidean-division equations: the flag value these proofs were checked with, which PaDenot.v
   gave them until an earlier commit made its redefinition Local *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

(* the live bytes of a block list are a sum, so a permutation of the list does not move them *)
Lemma at_perm_snd_sum : forall (l l' : list (Z * Z)), Permutation l l' ->
fold_right (fun pn acc => snd pn + acc) 0 l = fold_right (fun pn acc => snd pn + acc) 0 l'.
Proof. intros l l' Hp. induction Hp; cbn in *; lia. Qed.

(* `filter` of the walk's scope is stdpp's, over the boolean predicate's coercion *)
Lemma at_filter_in : forall (f : Z * Z -> bool) (l : list (Z * Z)) (x : Z * Z), In x (filter f l) -> In x l.
Proof.
intros f l x H. apply list_elem_of_In in H. apply list_basics.list.list_elem_of_filter in H.
apply list_elem_of_In. exact (proj2 H).
Qed.

(* ---- transport of a reader-level fact over a range the step keeps ---- *)
Lemma at_aval_rng : forall (rd rd' : reader) lo hi a (n : nat) v,
(forall y, lo <= y < hi -> rd' y = rd y) -> lo <= a -> a + Z.of_nat n <= hi ->
aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' lo hi a n v He Hlo Hhi H k Hk. rewrite He by lia. exact (H k Hk). Qed.

Lemma at_str_rng : forall (rd rd' : reader) lo hi p s,
(forall y, lo <= y < hi -> rd' y = rd y) -> lo <= p -> p + Z.of_nat (length s) + 1 <= hi ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' lo hi p s He Hlo Hhi [H1 H2]. split; [|exact H2]. intros i Hi.
pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
rewrite He by lia. exact (H1 i Hi).
Qed.

Lemma at_bytes_rng : forall (rd rd' : reader) lo hi p l,
(forall y, lo <= y < hi -> rd' y = rd y) -> lo <= p -> p + Z.of_nat (length l) <= hi ->
abytes_atR rd p l -> abytes_atR rd' p l.
Proof. intros rd rd' lo hi p l He Hlo Hhi H i Hi. rewrite He by lia. exact (H i Hi). Qed.

Lemma at_range_addressable_le : forall (rd : reader) (Bs a n m : Z), 0 <= m <= n ->
range_addressable rd Bs a n -> range_addressable rd Bs a m.
Proof. intros rd Bs a n m Hm H y Hy. apply H. lia. Qed.

Lemma at_ra_kept : forall (rd rd' : reader) (Bs a n : Z),
range_addressable rd Bs a n ->
(forall y, a <= y < a + n -> rd' (shadow_of_addr Bs y) = rd (shadow_of_addr Bs y)) ->
range_addressable rd' Bs a n.
Proof.
intros rd rd' Bs a n H He y Hy. destruct (H y Hy) as (s & Hs & Hok).
exists s. rewrite (He y Hy). split; [exact Hs | exact Hok].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).

(* CmdRep's field read through the ASan reader is the kit's val_mem of the restricted memory *)
Lemma at_val_mem_of_aval : forall (H : word -> bool) (mem : word -> option byte) (a : Z) (n : nat) (v : Z),
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; cbn [option_map] in Hv; [|discriminate].
injection Hv as Hv.
assert (Hb : b = Z_to_bv 8 (bv_unsigned b)) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
rewrite Hb, Hv. reflexivity.
Qed.

Lemma at_rdword_of_aval : forall (H : word -> bool) (mem : word -> option byte) (a v : Z),
aval_mem (aview SEGS H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr. apply (rdword_of_val_mem SEGS H mem a v); [apply at_val_mem_of_aval; exact Hv | exact Hr].
Qed.

Section e.
Variable B : asyms.

(* ---- the live bytes over a permutation of the block list ---- *)
Lemma at_blocks_bytes_fold : forall ly S,
blocks_bytes S = fold_right (fun pn acc => snd pn + acc) 0 (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks.
induction (st_chunks S) as [|k l IH]; [reflexivity|].
cbn [List.filter fold_right].
destruct (is_alloc k); cbn [map fold_right snd]; [rewrite IH; reflexivity | exact IH].
Qed.

Lemma at_blocks_bytes_perm : forall ly S ly' S',
Permutation (ablocks B ly' S') (ablocks B ly S) -> blocks_bytes S' = blocks_bytes S.
Proof.
intros ly S ly' S' Hp.
rewrite (at_blocks_bytes_fold ly' S'), (at_blocks_bytes_fold ly S). apply at_perm_snd_sum. exact Hp.
Qed.

(* ---- the recorder's representation over a reader that keeps what it reads ---- *)
Lemma at_call_rng : forall bl bl' (rd rd' : reader) lo hi a c P,
(forall y, lo <= y < hi -> rd' y = rd y) -> lo <= a -> a + CALL_SIZE <= hi ->
(forall p n y, In (p, n) bl -> p <= y < p + req_size n -> rd' y = rd y) ->
(forall pn, In pn bl -> In pn bl') ->
acall_at bl rd a c P -> acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' lo hi a c P He Hlo Hhi Hb Hsub (H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold CALL_SIZE in Hhi.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [eapply (at_aval_rng rd rd' lo hi); [exact He | unfold CALL_OFF_FN; lia | unfold CALL_OFF_FN; cbn; lia | exact H4]|].
split; [eapply (at_aval_rng rd rd' lo hi); [exact He | unfold CALL_OFF_NARGS; lia | unfold CALL_OFF_NARGS; cbn; lia | exact H5]|].
split; [exact H6|].
intros k s pn Hs Hp.
assert (Hk6 : (k < 6)%nat).
{ assert (Hlt : (k < length (snd c))%nat) by (apply (proj1 (nth_error_Some (snd c) k)); rewrite Hs; discriminate). lia. }
destruct (H7 k s pn Hs Hp) as (A1 & A2 & A3 & A4 & A5).
split; [eapply (at_aval_rng rd rd' lo hi); [exact He | unfold CALL_OFF_ARGS; lia | unfold CALL_OFF_ARGS; cbn; lia | exact A1]|].
split; [exact A2|]. split; [exact (Hsub pn A3)|]. split; [exact A4|].
destruct pn as [q m]. cbn [fst snd] in A2, A3, A4, A5 |- *.
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
eapply (at_str_rng rd rd' q (q + req_size m)); [intros y Hy; exact (Hb q m y A3 Hy) | lia | lia | exact A5].
Qed.

Lemma at_rep_kept : forall bl bl' (rd rd' : reader) R Q,
(forall y, A_G_REC <= y < A_G_REC + REC_SIZE -> rd' y = rd y) ->
(forall y, A_REC_SPILL <= y < A_REC_SPILL + SC_SIZE -> rd' y = rd y) ->
(forall p n y, In (p, n) bl -> p <= y < p + req_size n -> rd' y = rd y) ->
(forall pn, In pn bl -> In pn bl') ->
arep_at bl rd A_G_REC A_REC_SPILL R Q -> arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q Hg Hs Hb Hsub (E1 & E2 & E3 & HC & HA & HR & HSC & HO).
split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
split.
{ destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact C1|]. split; [exact C2|].
  split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
    [exact Hg | unfold OFF_NCALLS; lia | unfold OFF_NCALLS, REC_SIZE; cbn; lia | exact C3]|].
  split.
  - intros i cc P Hi HP. destruct (C4 i cc P Hi HP) as [Hc Hf]. split; [|exact Hf].
    assert (Hi16 : (i < 16)%nat).
    { assert (Hlt : (i < length (r_calls R))%nat)
        by (apply (proj1 (nth_error_Some (r_calls R) i)); rewrite Hi; discriminate). lia. }
    eapply (at_call_rng bl bl' rd rd' A_G_REC (A_G_REC + REC_SIZE));
      [exact Hg | unfold OFF_CALLS, CALL_SIZE; lia | unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia
       | exact Hb | exact Hsub | exact Hc].
  - split; [|exact C6].
    eapply (at_call_rng bl bl' rd rd' A_REC_SPILL (A_REC_SPILL + SC_SIZE));
      [exact Hs | lia | unfold SC_SIZE, CALL_SIZE; lia | exact Hb | exact Hsub | exact C5]. }
split.
{ unfold aanswer_at in HA |- *.
  destruct (r_answer R) as [xa|]; destruct (l_answer Q) as [[q m]|]; [| destruct HA | destruct HA |].
  - destruct HA as (A1 & A2 & A3 & A4 & A5 & A6). cbn [fst snd] in A2, A3, A4, A5 |- *.
    split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
      [exact Hg | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia | exact A1]|].
    split; [exact A2|]. split; [exact (Hsub _ A3)|]. split; [exact A4|]. split; [|exact A6].
    pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
    eapply (at_str_rng rd rd' q (q + req_size m)); [intros y Hy; exact (Hb q m y A3 Hy) | lia | lia | exact A5].
  - eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
      [exact Hg | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia | exact HA]. }
split.
{ unfold areply_at in HR |- *.
  destruct (r_reply R) as [xr|]; destruct (l_reply Q) as [[q m]|]; [| destruct HR | destruct HR |].
  - destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). cbn [fst snd] in A3, A5, A6, A7 |- *.
    split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
      [exact Hg | unfold OFF_REPLY; lia | unfold OFF_REPLY, REC_SIZE; cbn; lia | exact A1]|].
    split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
      [exact Hg | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, REC_SIZE; cbn; lia | exact A2]|].
    split; [exact A3|]. split; [exact A4|]. split; [exact (Hsub _ A5)|]. split; [exact A6|]. split; [|exact A8].
    pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
    assert (Hx1 : (1 <= length xr)%nat) by (destruct xr; [exfalso; exact (A4 eq_refl) | cbn; lia]).
    eapply (at_bytes_rng rd rd' q (q + req_size m)); [intros y Hy; exact (Hb q m y A5 Hy) | lia | lia | exact A7].
  - destruct HR as (A1 & A2).
    split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
      [exact Hg | unfold OFF_REPLY; lia | unfold OFF_REPLY, REC_SIZE; cbn; lia | exact A1]|].
    eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
      [exact Hg | unfold OFF_REPLY_SIZE; lia | unfold OFF_REPLY_SIZE, REC_SIZE; cbn; lia | exact A2]. }
split; [|exact HO].
destruct HSC as (S1 & S2 & S3 & S4 & S5 & S6).
split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
  [exact Hg | unfold OFF_REFUSE; lia | unfold OFF_REFUSE, REC_SIZE; cbn; lia | exact S1]|].
split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
  [exact Hg | unfold OFF_CODE; lia | unfold OFF_CODE, REC_SIZE; cbn; lia | exact S2]|].
split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
  [exact Hg | unfold OFF_NREPLIES; lia | unfold OFF_NREPLIES, REC_SIZE; cbn; lia | exact S3]|].
split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
  [exact Hg | unfold OFF_STATE; lia | unfold OFF_STATE, REC_SIZE; cbn; lia | exact S4]|].
split; [eapply (at_aval_rng rd rd' A_G_REC (A_G_REC + REC_SIZE));
  [exact Hg | unfold OFF_HOST; lia | unfold OFF_HOST, REC_SIZE; cbn; lia | exact S5]|].
exact S6.
Qed.

Lemma at_rec_repA_kept : forall ly S ly' S' (rd rd' : reader) R O,
rec_repA B ly S rd R O ->
(forall y, A_G_REC <= y < A_G_REC + REC_SIZE -> rd' y = rd y) ->
(forall y, A_REC_SPILL <= y < A_REC_SPILL + SC_SIZE -> rd' y = rd y) ->
(forall p n y, In (p, n) (ablocks B ly S) -> p <= y < p + req_size n -> rd' y = rd y) ->
(forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S ly' S' rd rd' R O (Q & HA & HO) Hg Hs Hb Hsub.
exists Q. split; [|exact HO]. eapply at_rep_kept; eassumption.
Qed.

(* the recorder's own blocks are live blocks of the state *)
Lemma at_call_at_P_in : forall bl (rd : reader) a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl.
Proof.
intros bl rd a c P pn (_ & _ & Hlen & _ & _ & _ & HK) Hin.
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Es.
- exact (proj1 (proj2 (proj2 (HK k s pn Es Hk)))).
- exfalso. apply nth_error_None in Es.
  assert (Hlt : (k < length P)%nat) by (apply (proj1 (nth_error_Some P k)); rewrite Hk; discriminate). lia.
Qed.

Lemma at_rec_repA_O_blocks : forall ly S (rd : reader) R O pn,
rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O pn (Q & HA & HO) Hin. apply HO in Hin. unfold lay_blocks in Hin.
pose proof HA as (_ & _ & _ & HC & HAns & HRep & _ & _).
apply in_app_iff in Hin as [Hc | Hin].
- apply in_concat in Hc as (l & Hl & Hpn). apply In_nth_error in Hl as (i & Hi).
  destruct HC as (C1 & C2 & _ & C4 & _ & _).
  destruct (nth_error (r_calls R) i) as [cc|] eqn:Ec.
  + exact (at_call_at_P_in _ _ _ _ _ _ (proj1 (C4 i cc l Ec Hi)) Hpn).
  + exfalso. apply nth_error_None in Ec.
    assert (Hlt : (i < length (l_calls Q))%nat)
      by (apply (proj1 (nth_error_Some (l_calls Q) i)); rewrite Hi; discriminate). lia.
- apply in_app_iff in Hin as [Hsp | Hin].
  + destruct HC as (_ & _ & _ & _ & C5 & _). exact (at_call_at_P_in _ _ _ _ _ _ C5 Hsp).
  + apply in_app_iff in Hin as [Ha | Hr].
    * unfold aanswer_at in HAns. destruct (l_answer Q) as [q|]; cbn [oblk In] in Ha; [|destruct Ha].
      destruct Ha as [<-|[]]. destruct (r_answer R) as [xa|]; [|destruct HAns].
      exact (proj1 (proj2 (proj2 HAns))).
    * unfold areply_at in HRep. destruct (l_reply Q) as [q|]; cbn [oblk In] in Hr; [|destruct Hr].
      destruct Hr as [<-|[]]. destruct (r_reply R) as [xr|]; [|destruct HRep].
      exact (proj1 (proj2 (proj2 (proj2 (proj2 HRep))))).
Qed.

(* the recorder's code field is a 32-bit signed number (ag1_scalars), which bounds the refusal text *)
Lemma at_rep_code : forall ly S (rd : reader) R O, rec_repA B ly S rd R O -> -2 ^ 31 <= r_code R < 2 ^ 31.
Proof.
intros ly S rd R O (Q & (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & H & _) & _) & _). exact H.
Qed.

End e.
End f.
End d.
