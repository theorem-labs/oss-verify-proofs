(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v; 658 of its 782 lines of code are new or changed and 4929 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_copy_s1.v, with its module paths and module names changed; 261 of its 354 lines of code are new or changed and 689 lines of the source are left out. *)
(* Reader-level facts for the recorder conjuncts of rec_calls_free's contract on fuzz_command.asan-ubsan
   (lib/B/Prog/rec_calls_free_c.v:123-136); copied from lib/A/Prog/rec_calls_free_rep.v, module paths changed.

   The walk of rec_calls_free (lib/B/Prog/rec_calls_free.v) reduces each of the three recorder conjuncts of the post
   to one of the lemmas below, stated over plain readers and block lists: the table rec_calls_free cleared (g_rec's
   call table, record.spill, or a table apart from the recorder), the blocks it freed, and the bytes it kept. The
   representation is lib/B/Prog/CmdRep.v (arep_at, rec_repA), the model lib/Prog/RecModel.v (set_calls, set_spill). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the recorder's own storage: g_rec and record.spill *)
Definition rcf_inrec (a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).

(* ---------- list facts ---------- *)

(* `NoDup` here (as in CmdRep's ag1_own) is stdpp's, which LinuxProcessSem exports; the proofs go through
   Stdlib's List.NoDup by stdpp's NoDup_ListNoDup *)
Lemma rcfr_nodup_disj : forall (A : Type) (l1 l2 : list A) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1 l2 x H. apply NoDup_ListNoDup in H. revert l2 x H.
induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
cbn [app] in H. apply List.NoDup_cons_iff in H. destruct H as [Hn Hd]. destruct H1 as [<-|H1].
- apply Hn. apply in_or_app. right. exact H2.
- exact (IH l2 x Hd H1 H2).
Qed.

Lemma rcfr_nodup_r : forall (A : Type) (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
intros A l1 l2 H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. revert l2 H.
induction l1 as [|y l1 IH]; intros l2 H; [exact H|].
cbn [app] in H. apply List.NoDup_cons_iff in H. exact (IH l2 (proj2 H)).
Qed.

Lemma rcfr_nodup_mid : forall (A : Type) (l1 l2 l3 : list A), NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof.
intros A l1 l2 l3 H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. revert l2 l3 H.
induction l1 as [|y l1 IH]; intros l2 l3 H.
- apply NoDup_ListNoDup. apply NoDup_ListNoDup in H. exact (rcfr_nodup_r _ l2 l3 H).
- cbn [app] in *. apply List.NoDup_cons_iff in H. destruct H as [Hn Hd]. apply List.NoDup_cons.
  + intros Hi. apply Hn. apply in_app_or in Hi. destruct Hi as [Hi|Hi]; apply in_or_app;
    [left; exact Hi | right; apply in_or_app; right; exact Hi].
  + exact (IH l2 l3 Hd).
Qed.

Lemma rcfr_fst_disj : forall (l1 l2 : list (Z * Z)) x, NoDup (map fst (l1 ++ l2)) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x ND H1 H2. rewrite map_app in ND.
exact (rcfr_nodup_disj _ (map fst l1) (map fst l2) (fst x) ND (in_map fst l1 x H1) (in_map fst l2 x H2)).
Qed.

Lemma rcfr_concat_nils : forall (l : list (list (Z * Z))), concat (map (fun _ : list (Z * Z) => @nil (Z * Z)) l) = [].
Proof. induction l as [|x l IH]; [reflexivity|]. simpl. exact IH. Qed.

Lemma rcfr_nth_map : forall (A B : Type) (f : A -> B) (l : list A) i y,
nth_error (map f l) i = Some y -> exists x, nth_error l i = Some x /\ f x = y.
Proof.
intros A B f l; induction l as [|a l IH]; intros [|i] y H; cbn in H; try discriminate H.
- injection H as <-. exists a. split; reflexivity.
- exact (IH i y H).
Qed.

(* a block of bl that is not among the freed F is still live, and its bytes are kept *)
Lemma rcfr_blk_keep : forall (bl bl' F : list (Z * Z)) (rd rd' : reader) pn,
Permutation bl (bl' ++ F) -> ~ In pn F ->
(forall p n i, In (p, n) bl' -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i).
Proof.
intros bl bl' F rd rd' [p n] HP HF HK Hin.
assert (Hin' : In (p, n) bl').
{ eapply Permutation_in in Hin; [|exact HP]. apply in_app_or in Hin. destruct Hin as [H|H]; [exact H|contradiction]. }
split; [exact Hin'|]. intros i Hi. exact (HK p n i Hin' Hi).
Qed.

(* ---------- reader facts ---------- *)

Lemma rcfr_aval_keep : forall (rd rd' : reader) a n v,
aval_mem rd a n v -> (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite (K k Hk). exact (H k Hk). Qed.

Lemma rcfr_bytes_keep : forall (rd rd' : reader) p l, abytes_atR rd p l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (p + i) = rd (p + i)) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H K i Hi. rewrite (K (Z.of_nat i)) by lia. exact (H i Hi). Qed.

Lemma rcfr_str_keep : forall (rd rd' : reader) p s, astr_atR rd p s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (p + i) = rd (p + i)) -> astr_atR rd' p s.
Proof.
intros rd rd' p s [H Hn] K. split; [|exact Hn].
apply (rcfr_bytes_keep rd _ _ _ H). intros i Hi. apply K. rewrite length_app in Hi. cbn [length] in Hi. lia.
Qed.

(* ---------- the parts of arep_at ---------- *)

Lemma rcfr_call_keep : forall bl bl' (rd rd' : reader) a c P,
acall_at bl rd a c P ->
(forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
(forall pn, In pn P -> In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & Hb1 & Hnd & Hargs) K KP.
unfold acall_at. unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
split; [exact Hfn|]. split; [exact Hn|]. split; [exact Hl|].
split; [apply (rcfr_aval_keep rd _ _ _ _ Hb0); intros k Hk; apply K; lia|].
split; [apply (rcfr_aval_keep rd _ _ _ _ Hb1); intros k Hk; apply K; lia|].
split; [exact Hnd|].
intros k s pn Es Ep. destruct (Hargs k s pn Es Ep) as (Hs & Hp0 & Hin & Hsz & Hstr).
assert (Hkl : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
destruct (KP pn (nth_error_In P k Ep) Hin) as [Hin' Kp].
split; [apply (rcfr_aval_keep rd _ _ _ _ Hs); intros j Hj; apply K; lia|].
split; [exact Hp0|]. split; [exact Hin'|]. split; [exact Hsz|].
apply (rcfr_str_keep rd _ _ _ Hstr). intros i Hi. apply Kp. lia.
Qed.

(* a cleared call: the same function, no arguments; only its fn field and its nargs field (now 0) are read *)
Lemma rcfr_call_clear : forall bl bl' (rd rd' : reader) a c P,
acall_at bl rd a c P ->
(forall x, a <= x < a + 4 -> rd' x = rd x) ->
aval_mem rd' (a + CALL_OFF_NARGS) 4 0 ->
acall_at bl' rd' a (fst c, @nil (list byte)) (@nil (Z * Z)).
Proof.
intros bl bl' rd rd' a c P (Hfn & Hn & Hl & Hb0 & _) K HN.
unfold acall_at. cbn [fst snd length].
split; [exact Hfn|]. split; [lia|]. split; [reflexivity|].
split; [apply (rcfr_aval_keep rd _ _ _ _ Hb0); intros k Hk; apply K; unfold CALL_OFF_FN; lia|].
split; [exact HN|]. split; [constructor|].
intros k s pn Es _. destruct k; cbn in Es; discriminate.
Qed.

Lemma rcfr_answer_keep : forall bl bl' (rd rd' : reader) gr t q,
aanswer_at bl rd gr t q ->
(forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
(forall pn, In pn (oblk q) -> In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H K KB.
destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
- destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (KB pn (or_introl eq_refl) N3) as [Kin Kp].
  split; [apply (rcfr_aval_keep rd _ _ _ _ N1); intros k Hk; apply K; lia|].
  split; [exact N2|]. split; [exact Kin|]. split; [exact N4|]. split; [|exact N6].
  apply (rcfr_str_keep rd _ _ _ N5). intros i Hi. apply Kp. lia.
- apply (rcfr_aval_keep rd _ _ _ _ H). intros k Hk. apply K. lia.
Qed.

Lemma rcfr_reply_keep : forall bl bl' (rd rd' : reader) gr y q,
areply_at bl rd gr y q ->
(forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY_SIZE + 8 -> rd' x = rd x) ->
(forall pn, In pn (oblk q) -> In pn bl -> In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H K KB.
destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
unfold OFF_REPLY, OFF_REPLY_SIZE in *.
- destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct (KB pn (or_introl eq_refl) P5) as [Kin Kp].
  split; [apply (rcfr_aval_keep rd _ _ _ _ P1); intros k Hk; apply K; lia|].
  split; [apply (rcfr_aval_keep rd _ _ _ _ P2); intros k Hk; apply K; lia|].
  split; [exact P3|]. split; [exact P4|]. split; [exact Kin|]. split; [exact P6|]. split; [|exact P8].
  apply (rcfr_bytes_keep rd _ _ _ P7). intros i Hi. apply Kp. lia.
- destruct H as [P1 P2].
  split; [apply (rcfr_aval_keep rd _ _ _ _ P1); intros k Hk; apply K; lia|].
  apply (rcfr_aval_keep rd _ _ _ _ P2). intros k Hk. apply K. lia.
Qed.

Lemma rcfr_scalars_keep : forall (rd rd' : reader) gr R, ag1_scalars rd gr R ->
(forall x, gr <= x < gr + 16 \/ gr + 912 <= x < gr + 960 -> rd' x = rd x) -> ag1_scalars rd' gr R.
Proof.
intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
unfold ag1_scalars. unfold OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
split; [apply (rcfr_aval_keep rd _ _ _ _ X1); intros k Hk; apply K; lia|].
split; [apply (rcfr_aval_keep rd _ _ _ _ X2); intros k Hk; apply K; lia|].
split; [apply (rcfr_aval_keep rd _ _ _ _ X3); intros k Hk; apply K; lia|].
split; [apply (rcfr_aval_keep rd _ _ _ _ X4); intros k Hk; apply K; lia|].
split; [apply (rcfr_aval_keep rd _ _ _ _ X5); intros k Hk; apply K; lia|].
exact X6.
Qed.

Lemma rcfr_own_sub : forall gr sc Q Q', ag1_own gr sc Q -> NoDup (map fst (lay_blocks Q')) ->
(forall pn, In pn (lay_blocks Q') -> In pn (lay_blocks Q)) -> ag1_own gr sc Q'.
Proof. intros gr sc Q Q' [_ HW] ND HS. split; [exact ND|]. intros pn Hpn. exact (HW pn (HS pn Hpn)). Qed.

(* the layouts after the call: g_rec's table cleared (each call with no argument blocks), or the spill cleared *)
Definition rcfr_lay_calls (Q : rlay) : rlay :=
RLay (map (fun _ : list (Z * Z) => @nil (Z * Z)) (l_calls Q)) (l_spill Q) (l_answer Q) (l_reply Q).
Definition rcfr_lay_spill (Q : rlay) : rlay := RLay (l_calls Q) [] (l_answer Q) (l_reply Q).

Lemma rcfr_lay_calls_blocks : forall Q,
lay_blocks (rcfr_lay_calls Q) = l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q).
Proof. intros Q. unfold lay_blocks, rcfr_lay_calls. cbn [l_calls l_spill l_answer l_reply]. rewrite rcfr_concat_nils. reflexivity. Qed.

Lemma rcfr_lay_spill_blocks : forall Q,
lay_blocks (rcfr_lay_spill Q) = concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q).
Proof. intros Q. reflexivity. Qed.

(* ---------- the three recorder conjuncts ---------- *)

(* rec_clear's call: g_rec's table cleared, its argument blocks freed *)
Lemma rcf_rep_grec : forall (bl bl' : list (Z*Z)) (rd rd' : reader) R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, rcf_inrec a -> ~ PRcf.nargs_field (A_G_REC + OFF_CALLS) (length (l_calls Q)) a -> rd' a = rd a) ->
  (forall i, (i < length (l_calls Q))%nat -> aval_mem rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0) ->
  Permutation bl (bl' ++ concat (l_calls Q)) ->
  (forall p n i, In (p, n) bl' -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (set_calls R (rcf_cleared (r_calls R))) Q' /\
    (forall pn, In pn (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) <-> In pn (lay_blocks Q')).
Proof.
intros bl bl' rd rd' R Q HA K HN HP HK.
destruct HA as (H1 & H2 & H3 & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (proj1 HW) as ND.
assert (Hn : (length (l_calls Q) <= 16)%nat) by lia.
assert (KL : forall x, A_G_REC <= x < A_G_REC + 16 \/ A_G_REC + 912 <= x < A_G_REC + 960 -> rd' x = rd x).
{ intros x Hx. apply K; [unfold rcf_inrec; left; unfold REC_SIZE; lia|].
  intros (j & Hj & Hx'). unfold OFF_CALLS in Hx'. lia. }
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x).
{ intros x Hx. apply K; [unfold rcf_inrec; right; exact Hx|].
  intros (j & Hj & Hx'). unfold OFF_CALLS, SC_SIZE, A_G_REC, A_REC_SPILL in *. lia. }
assert (KF : forall i x, (i < 16)%nat ->
  A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i <= x < A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + 4 -> rd' x = rd x).
{ intros i x Hi Hx. apply K; [unfold rcf_inrec; left; unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
  intros (j & Hj & Hx'). unfold OFF_CALLS, CALL_SIZE in *. lia. }
assert (KB : forall pn, In pn (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl ->
  In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hr Hb. apply (rcfr_blk_keep bl bl' (concat (l_calls Q)) rd rd' pn HP); [|exact HK|exact Hb].
  intros Hc. unfold lay_blocks in ND. exact (rcfr_fst_disj _ _ pn ND Hc Hr). }
assert (E1 : (length (rcf_cleared (r_calls R)) <= 16)%nat) by (unfold rcf_cleared; rewrite length_map; exact C1).
assert (E2 : length (map (fun _ : list (Z * Z) => @nil (Z * Z)) (l_calls Q)) = length (rcf_cleared (r_calls R)))
  by (unfold rcf_cleared; rewrite !length_map; exact C2).
assert (E3 : aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (rcf_cleared (r_calls R))))).
{ unfold rcf_cleared. rewrite length_map. apply (rcfr_aval_keep rd _ _ _ _ C3).
  intros k Hk. apply KL. left. unfold OFF_NCALLS. lia. }
assert (HT : forall i c P, nth_error (rcf_cleared (r_calls R)) i = Some c ->
  nth_error (map (fun _ : list (Z * Z) => @nil (Z * Z)) (l_calls Q)) i = Some P ->
  acall_at bl' rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\
  Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
{ intros i c P Ec EP. unfold rcf_cleared in Ec.
  destruct (rcfr_nth_map _ _ _ _ _ _ Ec) as (c0 & E0 & <-).
  destruct (rcfr_nth_map _ _ _ _ _ _ EP) as (P0 & EP0 & <-).
  cbv beta.
  assert (Hi : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite EP0; discriminate).
  destruct (C4 i c0 P0 E0 EP0) as [Hc _]. split; [|cbn [snd]; constructor].
  apply (rcfr_call_clear bl bl' rd rd' _ c0 P0 Hc); [|exact (HN i Hi)].
  intros x Hx. apply (KF i x); [lia|exact Hx]. }
assert (HS : acall_at bl' rd' A_REC_SPILL (r_spill R) (l_spill Q)).
{ apply (rcfr_call_keep bl bl' rd rd' _ _ _ C5).
  - intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
  - intros pn Hpn Hb. apply KB; [apply in_or_app; left; exact Hpn | exact Hb]. }
assert (HAn' : aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q)).
{ apply (rcfr_answer_keep bl bl' rd rd' _ _ _ HAn).
  - intros x Hx. apply KL. right. unfold OFF_ANSWER in Hx. lia.
  - intros pn Hpn Hb. apply KB; [|exact Hb]. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
assert (HRp' : areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q)).
{ apply (rcfr_reply_keep bl bl' rd rd' _ _ _ HRp).
  - intros x Hx. apply KL. right. unfold OFF_REPLY, OFF_REPLY_SIZE in Hx. lia.
  - intros pn Hpn Hb. apply KB; [|exact Hb]. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
assert (HX' : ag1_scalars rd' A_G_REC R) by exact (rcfr_scalars_keep rd _ _ _ HX KL).
assert (HW' : ag1_own A_G_REC A_REC_SPILL (rcfr_lay_calls Q)).
{ apply (rcfr_own_sub _ _ Q _ HW).
  - rewrite rcfr_lay_calls_blocks. unfold lay_blocks in ND. rewrite map_app in ND. exact (rcfr_nodup_r _ _ _ ND).
  - intros pn Hpn. rewrite rcfr_lay_calls_blocks in Hpn. unfold lay_blocks. apply in_or_app. right. exact Hpn. }
exists (rcfr_lay_calls Q). split.
- unfold arep_at, ag1_calls.
  exact (conj H1 (conj H2 (conj H3 (conj (conj E1 (conj E2 (conj E3 (conj HT (conj HS C6)))))
    (conj HAn' (conj HRp' (conj HX' HW'))))))).
- intros pn. rewrite rcfr_lay_calls_blocks. apply iff_refl.
Qed.

(* record()'s call: the spill cleared, its argument blocks freed *)
Lemma rcf_rep_spill : forall bl bl' rd rd' R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, rcf_inrec a -> ~ PRcf.nargs_field A_REC_SPILL 1 a -> rd' a = rd a) ->
  aval_mem rd' (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) 4 0 ->
  Permutation bl (bl' ++ concat [l_spill Q]) ->
  (forall p n i, In (p, n) bl' -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  exists Q', arep_at bl' rd' A_G_REC A_REC_SPILL (set_spill R (fst (r_spill R), [])) Q' /\
    (forall pn, In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) <-> In pn (lay_blocks Q')).
Proof.
intros bl bl' rd rd' R Q HA K HN HP HK.
destruct HA as (H1 & H2 & H3 & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (proj1 HW) as ND.
assert (EF : concat [l_spill Q] = l_spill Q) by (simpl; apply app_nil_r).
rewrite EF in HP.
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x).
{ intros x Hx. apply K; [unfold rcf_inrec; left; exact Hx|].
  intros (j & Hj & Hx'). unfold A_G_REC, A_REC_SPILL, REC_SIZE in *. lia. }
assert (KF : forall x, A_REC_SPILL <= x < A_REC_SPILL + 4 -> rd' x = rd x).
{ intros x Hx. apply K; [unfold rcf_inrec; right; unfold SC_SIZE; lia|].
  intros (j & Hj & Hx'). lia. }
assert (KB : forall pn, In pn (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl ->
  In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hr Hb. apply (rcfr_blk_keep bl bl' (l_spill Q) rd rd' pn HP); [|exact HK|exact Hb].
  intros Hs. unfold lay_blocks in ND. apply in_app_or in Hr. destruct Hr as [Hc|Hr].
  - apply (rcfr_fst_disj _ _ pn ND Hc). apply in_or_app. left. exact Hs.
  - rewrite (app_assoc (concat (l_calls Q)) (l_spill Q)) in ND.
    apply (rcfr_fst_disj _ _ pn ND); [apply in_or_app; right; exact Hs | exact Hr]. }
assert (E3 : aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)))).
{ apply (rcfr_aval_keep rd _ _ _ _ C3). intros k Hk. apply KG. unfold OFF_NCALLS, REC_SIZE. lia. }
assert (HT : forall i c P, nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
  acall_at bl' rd' (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\
  Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
{ intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  apply (rcfr_call_keep bl bl' rd rd' _ c P Hc).
  - intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
  - intros pn Hpn Hb. apply KB; [|exact Hb]. apply in_or_app. left.
    apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn]. }
assert (HS : acall_at bl' rd' A_REC_SPILL (fst (r_spill R), @nil (list byte)) (@nil (Z * Z))).
{ apply (rcfr_call_clear bl bl' rd rd' _ _ _ C5 KF).
  replace (A_REC_SPILL + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) by lia.
  exact HN. }
assert (HS6 : Forall (fun s => Z.of_nat (length s) <= LMAX) (@nil (list byte))) by constructor.
assert (HAn' : aanswer_at bl' rd' A_G_REC (r_answer R) (l_answer Q)).
{ apply (rcfr_answer_keep bl bl' rd rd' _ _ _ HAn).
  - intros x Hx. apply KG. unfold OFF_ANSWER, REC_SIZE in *. lia.
  - intros pn Hpn Hb. apply KB; [|exact Hb]. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
assert (HRp' : areply_at bl' rd' A_G_REC (r_reply R) (l_reply Q)).
{ apply (rcfr_reply_keep bl bl' rd rd' _ _ _ HRp).
  - intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
  - intros pn Hpn Hb. apply KB; [|exact Hb]. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
assert (HX' : ag1_scalars rd' A_G_REC R).
{ apply (rcfr_scalars_keep rd _ _ _ HX). intros x Hx. apply KG. unfold REC_SIZE. lia. }
assert (HW' : ag1_own A_G_REC A_REC_SPILL (rcfr_lay_spill Q)).
{ apply (rcfr_own_sub _ _ Q _ HW).
  - rewrite rcfr_lay_spill_blocks. unfold lay_blocks in ND. rewrite !map_app in ND. rewrite !map_app.
    exact (rcfr_nodup_mid _ _ _ _ ND).
  - intros pn Hpn. rewrite rcfr_lay_spill_blocks in Hpn. unfold lay_blocks.
    apply in_app_or in Hpn. destruct Hpn as [Hpn|Hpn]; apply in_or_app; [left; exact Hpn|].
    right. apply in_or_app. right. exact Hpn. }
exists (rcfr_lay_spill Q). split.
- unfold arep_at, ag1_calls.
  exact (conj H1 (conj H2 (conj H3 (conj (conj C1 (conj C2 (conj E3 (conj HT (conj HS HS6)))))
    (conj HAn' (conj HRp' (conj HX' HW'))))))).
- intros pn. rewrite rcfr_lay_spill_blocks. apply iff_refl.
Qed.

(* a table apart from the recorder (check_round_trip's copy): the recorder's bytes kept, none of its blocks freed *)
Lemma rcf_rep_apart : forall bl bl' rd rd' R Q (F : list (Z*Z)),
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  (forall a, rcf_inrec a -> rd' a = rd a) ->
  Permutation bl (bl' ++ F) ->
  (forall pn, In pn F -> ~ In pn (lay_blocks Q)) ->
  (forall p n i, In (p, n) bl' -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q F HA K HP HF HK.
destruct HA as (H1 & H2 & H3 & HC & HAn & HRp & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x).
{ intros x Hx. apply K. unfold rcf_inrec. left. exact Hx. }
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE -> rd' x = rd x).
{ intros x Hx. apply K. unfold rcf_inrec. right. exact Hx. }
assert (KB : forall pn, In pn (lay_blocks Q) -> In pn bl ->
  In pn bl' /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hq Hb. apply (rcfr_blk_keep bl bl' F rd rd' pn HP); [|exact HK|exact Hb].
  intros Hf. exact (HF pn Hf Hq). }
unfold arep_at. refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj _ (conj _ HW))))))).
- unfold ag1_calls. refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
  + apply (rcfr_aval_keep rd _ _ _ _ C3). intros k Hk. apply KG. unfold OFF_NCALLS, REC_SIZE. lia.
  + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
    apply (rcfr_call_keep bl bl' rd rd' _ c P Hc).
    * intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
    * intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. left.
      apply in_concat. exists P. split; [exact (nth_error_In _ _ EP) | exact Hpn].
  + apply (rcfr_call_keep bl bl' rd rd' _ _ _ C5).
    * intros x Hx. apply KS. unfold CALL_SIZE, SC_SIZE in *. lia.
    * intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
      apply in_or_app. left. exact Hpn.
- apply (rcfr_answer_keep bl bl' rd rd' _ _ _ HAn).
  + intros x Hx. apply KG. unfold OFF_ANSWER, REC_SIZE in *. lia.
  + intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. left. exact Hpn.
- apply (rcfr_reply_keep bl bl' rd rd' _ _ _ HRp).
  + intros x Hx. apply KG. unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
  + intros pn Hpn Hb. apply KB; [|exact Hb]. unfold lay_blocks. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right. exact Hpn.
- apply (rcfr_scalars_keep rd _ _ _ HX). intros x Hx. apply KG. unfold REC_SIZE. lia.
Qed.

(* rec_repA form of rcf_rep_apart *)
Lemma rcf_rep_repA : forall B ly S ly' S' rd rd' R O F, rec_repA B ly S rd R O -> (forall a, rcf_inrec a -> rd' a = rd a) -> Permutation (ablocks B ly S) (ablocks B ly' S' ++ F) -> (forall pn, In pn F -> ~ In pn O) -> (forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < n -> rd' (p + i) = rd (p + i)) -> rec_repA B ly' S' rd' R O.
Proof.
intros B ly S ly' S' rd rd' R O F (Q & HA & HO) K HP HF HK.
exists Q. split; [|exact HO].
apply (rcf_rep_apart (ablocks B ly S) (ablocks B ly' S') rd rd' R Q F HA K HP); [|exact HK].
intros pn Hf Hq. exact (HF pn Hf (proj2 (HO pn) Hq)).
Qed.
