(* proves no function (kind: invariant lemma): the image-B port of the model facts on the drain and relay_remove
   request traces and on fr_RINV's pairs that the B proofs of LS_rm_rr_pre and GN_LS_rig read *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Ported from A at a working branch 9f4cbd12a19 (A below), names and statements kept, over lib/B's
   records (lib/B/W_rep.v, lib/B/W_contract.v, lib/B/W_LLVMFuzzerTestOneInput_cut.v of
   a working branch 61e610e6176), fr_RINV from lib/B/ReplyRINVB.v, and the plain model files
   lib/Prog/drain_b_c.v, send_line_b_c.v, gestures_end_b_c.v, RelayModel.v, RelayKeys.v, RelayCap.v, SlotReads.v,
   SlotInv.v, ListTr.v, RelayRunT.v, HarnessRep.v (byte-identical in both trees).
     A lib/A/ReplyRINV.v :232 RI_fds_obl, :597 fr_Forall2_comb, :605 fr_comb_inj, :619 fr_pair_of_open, :715
       RI_fds_holds, :1144 fr_F2_nth, :1166 fr_sum_perm, :1169 fr_keys_total_nonneg, :1171 fr_pair_cost_nonneg
       (lib/B/ReplyRINVB.v does not have them);
     A lib/A/ReplyLS.v :106 zsum_app (lib/B/ReplyLSB.v did not port it);
     A lib/A/ReplyLSDrainPre.v :84-411 (the drain's request bound: dpre_rq .. dpre_dr_tr_max), :425 dpre_keys_le;
     A lib/A/ReplyLSRemove3.v :69-75, :108-109 (pure helpers), :112-209 (the relay's lines, drain's g_nout), :237
       rm3_kw, :284-291 rm3_kt_kw, :357-369 (the model's blocks), :413-436 rm3_pair, rm3_kt_len;
     A lib/A/ReplyLSRrPre.v :95-228 (relay_remove's find, the held keys drain leaves, the gesture ends' requests).
   Not ported (A duplicates of what is here or in lib/B/ReplyLSBTrPeak.v): A ReplyLSRemove3.v rm3_gesture_len (=
   dpre_gesture_len), A ReplyLSDrainPre.v dpre_sum_in (= rm3_in_le_sum), A ReplyLSRrPre.v rrp_tr_max_nonneg /
   rrp_tr_max_app (= ReplyLSBTrPeak.v tr_max_nonneg' / tr_max_app'); A ReplyLS.v zsum_map_nonneg is
   lib/B/ReplyLSBArms.v bt_zsum_map_nonneg.
   A -> B SWAPS: as lib/B/ReplyLSBArms.v (lib/A AB1v -> lib/B YB1v; Reusable YE01 + lib/A AE2k -> lib/B YE01 YE2k;
   lib/A ACfn -> lib/B YCfn, Required; lib/A W_* -> lib/B W_*; then ReplyGuardB, ReplyLSB, ReplyRINVB, ReplyLSBArms);
   A's lib/A W_op_add, _drain, _write, _event, ReplyLS, ReplyLSArms are not loaded: their names here come from
   lib/B/ReplyLSB.v (the bsum lemmas), lib/B/W_LLVMFuzzerTestOneInput_remove.v (rm_ent, rm_at, pinned by Local
   Notations), lib/B/ReplyLSBArms.v (bt_zsum_map_nonneg for A's zsum_map_nonneg) and lib/B/ReplyRINVB.v (fr_RINV and
   its parts).  A's sections over (B : asyms) that do not read
   B (rm3_pair, the model's blocks) take only {fx rc} here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation zsum l := (fold_right Z.add 0 l).
(* the remove arm's notions are lib/B/W_LLVMFuzzerTestOneInput_remove.v's (:124, :130) *)
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.

(* ================================================================== fr_RINV's pairs (A ReplyRINV.v) *)
(* A :597 *)
Lemma fr_Forall2_comb : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In (x, y) (combine l1 l2) /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
(* A :605: two entries of the table with the same fd are one row, so their sources are one *)
Lemma fr_comb_inj : forall (Y : Type) (es : list rentry) (hj : list Y), List.NoDup (map re_fd es) ->
  forall e1 p1 e2 p2, In (e1, p1) (combine es hj) -> In (e2, p2) (combine es hj) -> re_fd e1 = re_fd e2 ->
  p1 = p2.
Proof.
  intros Y es. induction es as [|x es IH]; intros hj Hnd e1 p1 e2 p2 H1 H2 Hf; [destruct H1|].
  destruct hj as [|y hj]; [destruct H1|]. cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Hx Hnd].
  cbn [combine In] in H1, H2.
  destruct H1 as [E1 | H1]; destruct H2 as [E2 | H2].
  - injection E1 as <- <-. injection E2 as <- <-. reflexivity.
  - injection E1 as <- <-. exfalso. apply Hx. rewrite Hf. apply in_map. eapply in_combine_l. exact H2.
  - injection E2 as <- <-. exfalso. apply Hx. rewrite <- Hf. apply in_map. eapply in_combine_l. exact H1.
  - exact (IH hj Hnd e1 p1 e2 p2 H1 H2 Hf).
Qed.
(* A :1144 *)
Lemma fr_F2_nth : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2, Forall2 R l1 l2 ->
  forall i d1 d2, (i < length l1)%nat -> R (nth i l1 d1) (nth i l2 d2).
Proof.
  intros T1 T2 R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros [|i] d1 d2 Hi; cbn [length] in Hi;
    try lia; cbn [nth]; [exact Hxy | apply IH; lia].
Qed.
(* A :1166 *)
Lemma fr_sum_perm : forall (T : Type) (f : T -> Z) l l', Permutation l l' ->
  fold_right Z.add 0 (map f l) = fold_right Z.add 0 (map f l').
Proof. intros T f l l' H. induction H; cbn [map fold_right]; lia. Qed.
(* A :1169 *)
Lemma fr_keys_total_nonneg : forall ks, 0 <= gestures_end_b_c.keys_total ks.
Proof. unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.
(* A :1171 *)
Lemma fr_pair_cost_nonneg : forall e p, 0 <= fr_pair_cost e p.
Proof.
  intros e p. unfold fr_pair_cost. pose proof (fr_keys_total_nonneg (re_keys e)).
  destruct (re_skip e =? 0); lia.
Qed.

Section rinv_pairs.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* A :619: an open slot is some entry's source *)
Lemma fr_pair_of_open : forall m t hj i h, Forall2 (fr_pair_ok m t) (lm_es m) hj ->
  (forall i, (i < 4)%nat -> SlotInv.slot_open hj i = false -> nth i (lm_hs m) None = None) ->
  (i < 4)%nat -> nth i (lm_hs m) None = Some h ->
  exists e p, In (e, p) (combine (lm_es m) hj) /\ fr_pair_ok m t e p /\ snd p = i /\ fst p = h.
Proof.
  intros m t hj i h HF Hcl Hi Hh.
  destruct (SlotInv.slot_open hj i) eqn:Ho; [|rewrite (Hcl i Hi Ho) in Hh; discriminate Hh].
  unfold SlotInv.slot_open in Ho. apply existsb_exists in Ho as (x & Hx & Hxi).
  apply Nat.eqb_eq in Hxi. subst x. apply in_map_iff in Hx as (p & Hpi & Hp).
  destruct (fr_Forall2_comb _ _ _ _ _ HF p Hp) as (e & Hin & HR).
  exists e, p. split; [exact Hin|]. split; [exact HR|]. split; [exact Hpi|].
  destruct HR as (_ & Hn & _). rewrite Hpi, Hh in Hn. injection Hn as Ef. exact (eq_sym Ef).
Qed.
(* A :232 (_drain.v:638 RI_fds) *)
Definition RI_fds_obl : Prop := forall cx t m i1 i2 h1 h2,
  fr_RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* A :715 *)
Lemma RI_fds_holds : RI_fds_obl.
Proof.
  intros cx t m i1 i2 h1 h2 (_ & HR & _) Hi1 Hi2 Hne Hh1 Hh2 Hf.
  destruct HR as (_ & Hnd & _ & _ & hj & HF & _ & Hcl & _). apply NoDup_ListNoDup in Hnd.
  destruct (fr_pair_of_open m t hj i1 h1 HF Hcl Hi1 Hh1) as (e1 & p1 & Hin1 & HR1 & Hs1 & Hf1).
  destruct (fr_pair_of_open m t hj i2 h2 HF Hcl Hi2 Hh2) as (e2 & p2 & Hin2 & HR2 & Hs2 & Hf2).
  apply Hne. rewrite <- Hs1, <- Hs2. f_equal.
  apply (fr_comb_inj _ (lm_es m) hj Hnd e1 p1 e2 p2 Hin1 Hin2).
  destruct HR1 as (_ & _ & E1 & _). destruct HR2 as (_ & _ & E2 & _).
  rewrite <- E1, <- E2, Hf1, Hf2. exact Hf.
Qed.
End rinv_pairs.

(* ================================================================== pure helpers (A ReplyLS.v, ReplyLSRemove3.v) *)
(* A ReplyLS.v :106 *)
Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [|a l1 IH]; intros l2; cbn; [lia | rewrite IH; lia]. Qed.
(* A ReplyLSRemove3.v :69 *)
Lemma rm3_in_le_sum : forall (X : Type) (g : X -> Z) l x, (forall y, 0 <= g y) -> In x l -> g x <= zsum (map g l).
Proof.
  intros X g l x Hg. induction l as [|y l IH]; intros Hx; [destruct Hx|].
  cbn [map fold_right]. pose proof (bt_zsum_map_nonneg g l Hg). destruct Hx as [<- | Hx]; [lia|].
  specialize (IH Hx). specialize (Hg y). lia.
Qed.
(* A ReplyLSRemove3.v :75 *)
Lemma rm3_nodup_inj : forall (X Y : Type) (f : X -> Y) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y ->
  x = y.
Proof.
  intros X Y f l. induction l as [|a l IH]; intros x y Hnd Hx Hy E; [destruct Hx|].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd as [Ha Hnd].
  destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy]; [reflexivity | | | exact (IH x y Hnd Hx Hy E)].
  - exfalso. apply Ha. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Ha. rewrite <- E. apply in_map. exact Hx.
Qed.
(* A ReplyLSRemove3.v :108 *)
Lemma rm3_skip_if : forall s (X : Z), (s = 0 \/ s = 1) -> (if s =? 1 then 0 else X) = (if s =? 0 then X else 0).
Proof. intros s X [-> | ->]; reflexivity. Qed.

(* ================================================================== the drain's request bound (A ReplyLSDrainPre.v) *)
(* A :84: a request asks at most M bytes (a free asks none) *)
Definition dpre_rq {P : Type} (M : Z) (ev : RelayRunT.rev P) : Prop :=
  match ev with
  | RelayRunT.RMalloc n => n <= M
  | RelayRunT.RFree _ _ => True
  | RelayRunT.RRealloc _ n _ => n <= M
  end.

Lemma dpre_tr_max : forall {P : Type} (tr : list (RelayRunT.rev P)) M, 0 <= M -> Forall (dpre_rq M) tr ->
  tr_max tr <= M.
Proof.
  intros P tr M HM HF. induction HF as [|ev tr Hev _ IH]; [unfold tr_max; cbn [fold_right]; lia|].
  unfold tr_max in *. cbn [fold_right]. destruct ev; cbn [dpre_rq] in Hev |- *; lia.
Qed.

(* A :99: drain's buffer growth: 8192, or 2 cap with cap < used + 4096 *)
Lemma dpre_grow : forall cap used j b M, used <= 6000 -> 20192 <= M ->
  Forall (dpre_rq M) (fst (drain_b_c.grow_tr cap used j b)).
Proof.
  intros cap used j b M Hu HM. unfold drain_b_c.grow_tr.
  destruct (Z.ltb_spec (cap - used) 4096) as [Hlt|Hge]; cbn [fst]; [|constructor].
  destruct (Z.eqb_spec cap 0) as [E|E]; cbn [fst]; (apply Forall_cons; [cbn [dpre_rq]; lia | constructor]).
Qed.

(* A :108: send_line's rounds: a growth asks (no + n) * 2 with n <= rem, and no + rem is kept *)
Lemma dpre_sl_run : forall f mx no cap rem j o M, 2 * (no + rem) <= M ->
  Forall (dpre_rq M) (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o M HM; cbn [send_line_b_c.sl_run]; [constructor|].
  destruct (Z.leb_spec rem 0) as [Hr|Hr]; [constructor|].
  match goal with |- context [if ?b then mx else rem] =>
    assert (Hn : (if b then mx else rem) <= rem)
      by (destruct b eqn:E; [apply andb_true_iff in E as [_ E]; apply Z.ltb_lt in E; lia | lia]);
    revert Hn; generalize (if b then mx else rem); intros n Hn end.
  destruct (Z.ltb_spec cap (no + n)) as [Hc|Hc].
  - cbn [fst]. apply Forall_cons; [destruct (cap =? 0); cbn [dpre_rq]; lia | apply IH; lia].
  - apply IH. lia.
Qed.

(* A :122 *)
Lemma dpre_send_line : forall live mx no cap len j o M, 2 * (no + len) <= M ->
  Forall (dpre_rq M) (send_line_b_c.send_line_tr live mx no cap len j o).
Proof.
  intros live mx no cap len j o M HM. unfold send_line_b_c.send_line_tr.
  destruct live; [apply dpre_sl_run; exact HM | constructor].
Qed.

(* A :130: a gesture's key is a prefix of its line *)
Lemma dpre_gesture_len : forall l k x, RelayModel.gesture l = Some (k, x) -> (length x <= length l)%nat.
Proof.
  intros l k x H. unfold RelayModel.gesture in H. cbv zeta in H.
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b
  | context [match ?o with Some _ => _ | None => _ end] => destruct o
  end; try discriminate H.
  all: injection H as _ Hx; subst x; rewrite length_firstn; lia.
Qed.

(* A :141: gesture_seen: (|H| + 1) * 8 and |key| + 1, or a free *)
Lemma dpre_seen : forall H ka l j ha ks M, Z.of_nat (length l) <= 6000 ->
  8 * (Z.of_nat (length H) + 1) <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
  intros H ka l j ha ks M Hl HH HM. unfold drain_b_c.seen_tr.
  destruct (RelayModel.gesture l) as [[kd x]|] eqn:G; [|constructor].
  pose proof (dpre_gesture_len l kd x G) as Hx.
  destruct kd; destruct (RelayKeys.index_of x H); cbn [fst].
  - constructor.
  - apply Forall_cons; [destruct (ka =? 0); cbn [dpre_rq]; lia|].
    apply Forall_cons; [cbn [dpre_rq]; lia | constructor].
  - apply Forall_cons; [exact I | constructor].
  - constructor.
Qed.

(* A :156 *)
Lemma dpre_seen_arr_len : forall H l, (length (RelayKeys.seen_arr H l) <= S (length H))%nat.
Proof.
  intros H l. unfold RelayKeys.seen_arr.
  destruct (RelayModel.gesture l) as [[[|] x]|]; [destruct (RelayKeys.index_of x H) .. | lia].
  - lia.
  - rewrite length_app. cbn [length]. lia.
  - unfold RelayKeys.swap_remove. rewrite length_firstn. lia.
  - lia.
Qed.

(* A :166 *)
Lemma dpre_with_nul_cons : forall l ls,
  length (RelayModel.with_nul (l :: ls)) = (length l + 1 + length (RelayModel.with_nul ls))%nat.
Proof.
  intros l ls. unfold RelayModel.with_nul. cbn [map concat]. rewrite !length_app. cbn [length]. lia.
Qed.

(* A :174: the relayed lines (each <= 6000 bytes): the sends ask at most 2 * A, the held array at most 8 * (Hk + A),
   where g_nout plus the lines' bytes is at most A and the held keys at most Hk plus g_nout *)
Lemma dpre_lines_run : forall ls live mx no cap H ka j o ha ks M Hk A,
  Forall (fun l => Z.of_nat (length l) <= 6000) ls ->
  Z.of_nat (length H) <= Hk + no -> no + Z.of_nat (length (RelayModel.with_nul ls)) <= A ->
  2 * A <= M -> 8 * (Hk + A) <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) /\
  Z.of_nat (length (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))))) <=
    Hk + no + Z.of_nat (length (RelayModel.with_nul ls)).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks M Hk A HF HH HA H2 H8 H6;
    cbn [drain_b_c.lines_run].
  - cbn [fst snd]. split; [constructor|]. lia.
  - apply Forall_cons_iff in HF as [Hl HF].
    rewrite dpre_with_nul_cons in HA |- *.
    pose proof (dpre_seen_arr_len H l) as HS.
    match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 r ?a5 ?a6 ?a7 ?a8] =>
      destruct (IH live mx a1 a2 a3 a4 a5 a6 a7 a8 M Hk A HF ltac:(lia) ltac:(lia) H2 H8 H6) as [I1 I2] end.
    cbn [fst snd]. split; [|lia].
    apply Forall_app. split; [apply dpre_send_line; lia|].
    apply Forall_app. split; [apply dpre_seen; [exact Hl | lia | exact H6] | exact I1].
Qed.

(* A :196: reference_feed's pushes: the grown array (128, or 32 cap at n = cap < En) and the text (|l| + 1) *)
Lemma dpre_pushes_run : forall ls n cap j v rs M En,
  Forall (fun l => Z.of_nat (length l) <= 6000) ls -> n + Z.of_nat (length ls) <= En ->
  32 * (En - 1) <= M -> 128 <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs M En HF Hn H32 H128 H6; cbn [drain_b_c.pushes_run];
    [constructor|].
  apply Forall_cons_iff in HF as [Hl HF]. cbn [length] in Hn.
  cbn [fst]. apply Forall_app. split.
  - unfold ListTr.list_push_tra. apply Forall_app. split.
    + destruct (Z.eqb_spec n cap) as [E|E]; [|constructor].
      destruct (cap =? 0); (apply Forall_cons; [cbn [dpre_rq]; lia | constructor]).
    + apply Forall_cons; [cbn [dpre_rq]; lia | constructor].
  - apply (IH _ _ _ _ _ M En HF); lia.
Qed.

(* A :213: LINE_LIMIT, a nat numeral above the abstraction threshold, read as a Z *)
Lemma dpre_LL : Z.of_nat RelayModel.LINE_LIMIT = 6000.
Proof. vm_compute. reflexivity. Qed.

(* A :218: the reference splitter (RelayModel.step): while it is not skipping, its line is at most LINE_LIMIT bytes *)
Definition dpre_jref (st : RelayModel.lstate) : Prop :=
  RelayModel.ls_k st = true \/ Z.of_nat (length (RelayModel.ls_w st)) <= 6000.

(* A :221 *)
Lemma dpre_step : forall st b, dpre_jref st ->
  dpre_jref (fst (RelayModel.step st b)) /\
  (forall l, snd (RelayModel.step st b) = Some l -> Z.of_nat (length l) <= 6000).
Proof.
  intros st b Hj. pose proof dpre_LL as LL. unfold RelayModel.step.
  destruct (Z.eqb b 0).
  - cbn [fst snd]. split; [right; cbn [RelayModel.ls_w length]; lia|].
    intros l Hl. destruct (RelayModel.ls_k st) eqn:Ek; [discriminate Hl|]. injection Hl as <-.
    destruct Hj as [Hj|Hj]; [congruence | exact Hj].
  - destruct (RelayModel.ls_k st) eqn:Ek; cbn [fst snd].
    + split; [left; exact Ek | intros l Hl; discriminate Hl].
    + destruct (Nat.eqb_spec (length (RelayModel.ls_w st)) RelayModel.LINE_LIMIT) as [El|El]; cbn [fst snd].
      * split; [left; reflexivity | intros l Hl; discriminate Hl].
      * split; [|intros l Hl; discriminate Hl]. right. cbn [RelayModel.ls_w]. rewrite length_app. cbn [length].
        destruct Hj as [Hj|Hj]; [congruence|]. lia.
Qed.

(* A :238 *)
Lemma dpre_ref_lines : forall d st, dpre_jref st ->
  Forall (fun l => Z.of_nat (length l) <= 6000) (RelayModel.lines st d) /\
  (length (RelayModel.lines st d) <= length d)%nat /\ dpre_jref (RelayModel.feed st d).
Proof.
  induction d as [|b d IH]; intros st Hj.
  - rewrite RelayModel.lines_nil, RelayModel.feed_nil. split; [constructor|]. split; [cbn [length]; lia | exact Hj].
  - rewrite RelayModel.lines_cons, RelayModel.feed_cons.
    destruct (dpre_step st b Hj) as [S1 S2].
    destruct (IH (fst (RelayModel.step st b)) S1) as (I1 & I2 & I3).
    destruct (snd (RelayModel.step st b)) as [l|] eqn:Eo.
    + split; [apply Forall_cons; [exact (S2 l eq_refl) | exact I1]|]. split; [cbn [length]; lia | exact I3].
    + split; [exact I1|]. split; [cbn [length]; lia | exact I3].
Qed.

(* A :254: the relay's splitter (RelayModel.scan / chunk): a line it relays is at most LINE_LIMIT bytes, the lines'
   bytes with their NULs and the unfinished line are at most the old unfinished line and the new bytes *)
Lemma dpre_scan : forall d sk0 acc sk r ls, RelayModel.scan sk0 acc d = (sk, r, ls) ->
  Forall (fun l => Z.of_nat (length l) <= 6000) ls /\
  (length (RelayModel.with_nul ls) + length r <= length acc + length d)%nat.
Proof.
  pose proof dpre_LL as LL. induction d as [|b d IH]; intros sk0 acc sk r ls E.
  - cbn [RelayModel.scan] in E. injection E as E1 E2 E3. subst. split; [constructor|].
    unfold RelayModel.with_nul. cbn [map concat length]. lia.
  - destruct (Z.eq_dec b 0) as [Eb|Eb].
    + subst b. rewrite RelayModel.scan_zero in E.
      destruct (RelayModel.scan false [] d) as [[sk1 r1] ls1] eqn:E1. cbv beta iota in E.
      destruct (IH false [] sk1 r1 ls1 E1) as [I1 I2]. cbn [length] in I2.
      destruct (sk0 || Nat.ltb RelayModel.LINE_LIMIT (length acc)) eqn:Es; cbv beta iota in E;
        injection E as E2 E3 E4; subst.
      * split; [exact I1|]. cbn [length]. lia.
      * apply orb_false_iff in Es as [_ Es]. apply Nat.ltb_ge in Es.
        split; [apply Forall_cons; [lia | exact I1]|]. rewrite dpre_with_nul_cons. cbn [length]. lia.
    + rewrite (RelayModel.scan_nz sk0 acc b d Eb) in E. destruct (IH sk0 (acc ++ [b]) sk r ls E) as [I1 I2].
      rewrite length_app in I2. cbn [length] in I2 |- *. split; [exact I1 | lia].
Qed.

(* A :274 *)
Lemma dpre_chunk : forall u sk0 d u' sk' rl, RelayModel.chunk u sk0 d = (u', sk', rl) ->
  Forall (fun l => Z.of_nat (length l) <= 6000) rl /\
  (length (RelayModel.with_nul rl) + length u' <= length u + length d)%nat /\ Z.of_nat (length u') <= 6000.
Proof.
  intros u sk0 d u' sk' rl E. pose proof dpre_LL as LL. unfold RelayModel.chunk in E.
  destruct (RelayModel.scan sk0 u d) as [[sk r] ls] eqn:E1. cbv beta iota in E.
  destruct (dpre_scan d sk0 u sk r ls E1) as [I1 I2].
  destruct (Nat.ltb_spec RelayModel.LINE_LIMIT (length r)) as [Hl|Hl]; cbv beta iota in E;
    injection E as E2 E3 E4; subst.
  - split; [exact I1|]. cbn [length]. lia.
  - split; [exact I1|]. lia.
Qed.

(* A :289: the bytes still pending in a round state *)
Definition dpre_rem (s : drain_b_c.dstate) : Z :=
  Z.of_nat (length (concat (drain_b_c.ds_pend s))) - drain_b_c.ds_off s.

(* A :294: the round invariant: Hk bounds the held keys against g_nout, A bounds g_nout + the unfinished line + the
   pending bytes, En bounds the expected list's length + the pending bytes *)
Definition dpre_inv (Hk A En : Z) (s : drain_b_c.dstate) : Prop :=
  Z.of_nat (length (drain_b_c.ds_u s)) <= 6000 /\ 0 <= drain_b_c.ds_off s /\ dpre_jref (drain_b_c.ds_ref s) /\
  drain_b_c.ds_no s + Z.of_nat (length (drain_b_c.ds_u s)) + dpre_rem s <= A /\
  Z.of_nat (length (drain_b_c.ds_H s)) <= Hk + drain_b_c.ds_no s /\
  drain_b_c.ds_en s + dpre_rem s <= En.

(* A :300 *)
Lemma dpre_drain_run : forall f live mx s j a M Hk A En, dpre_inv Hk A En s ->
  20192 <= M -> 2 * A <= M -> 8 * (Hk + A) <= M -> 32 * (En - 1) <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx s j a M Hk A En HI Hg H2 H8 H32 H6; [constructor|].
  pose proof HI as (Iu & Io & Ir & Ia & Ih & Ie).
  cbn [drain_b_c.drain_run].
  pose proof (dpre_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) M
                ltac:(lia) Hg) as G1.
  destruct (drain_b_c.ds_eintr s).
  - (* EINTR: the growth only, then the same state *)
    cbn [fst]. apply Forall_app. split; [exact G1|].
    apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
    unfold dpre_inv, dpre_rem in HI |- *.
    cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
         drain_b_c.ds_pend].
    exact HI.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP; [exact G1|].
    assert (Hrem : dpre_rem s = Z.of_nat (length r0) + Z.of_nat (length (concat rs)) - drain_b_c.ds_off s).
    { unfold dpre_rem. rewrite EP. cbn [concat]. rewrite length_app. lia. }
    match goal with |- context [Z.leb ?x 0] => destruct (Z.leb_spec x 0) as [Hn0|Hn0] end; [exact G1|].
    match type of Hn0 with 0 < ?x =>
      assert (Hn1 : x <= Z.of_nat (length r0) - drain_b_c.ds_off s) by lia;
      set (n := x) in * end.
    assert (Hd : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0))) = n)
      by (rewrite length_firstn, length_skipn; lia).
    set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
    destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
    destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & C2 & C3).
    cbv beta iota.
    destruct (dpre_ref_lines d (drain_b_c.ds_ref s) Ir) as (R1 & R2 & R3).
    match goal with |- context [drain_b_c.pushes_run ?n0 ?c ?ls ?jj ?v ?rs0] =>
      assert (P1 : Forall (dpre_rq M) (fst (fst (drain_b_c.pushes_run n0 c ls jj v rs0))))
        by (apply (dpre_pushes_run ls n0 c jj v rs0 M En R1); lia) end.
    match goal with |- context [drain_b_c.lines_run ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?l8 ?l9 ?l10 ?l11] =>
      pose proof (dpre_lines_run l7 l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 M Hk A C1 ltac:(lia) ltac:(lia) H2 H8 H6)
        as [L1 L2];
      revert L1 L2;
      destruct (drain_b_c.lines_run l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11) as [[tl [[oc' H'] ka']] [[o' ha'] ks']];
      intros L1 L2 end.
    cbn [fst snd] in L1, L2 |- *.
    apply Forall_app. split; [exact G1|].
    apply Forall_app. split; [exact P1|].
    destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [Ew|Ew].
    + (* the head text is read to its end: list_drop frees it *)
      apply Forall_app. split; [unfold ListTr.list_drop_tra; apply Forall_cons; [exact I | constructor]|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend].
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
    + apply Forall_app. split; [constructor|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend concat].
      rewrite length_app.
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
Qed.

(* A :363: the pending texts' bytes from the read offset are the pending stream *)
Lemma dpre_concat_bzs : forall rs : list (Z * list byte),
  length (concat (map (fun r => bzs (snd r)) rs)) = length (concat (map snd rs)).
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite !length_app, IH.
  unfold bzs. rewrite length_map. reflexivity.
Qed.

(* A :370 *)
Lemma dpre_rem_init : forall NO CAP e h, 0 <= hs_off h ->
  dpre_rem (drain_b_c.drain_init NO CAP e h) <= Z.of_nat (length (pending_stream h)).
Proof.
  intros NO CAP e h Ho. unfold dpre_rem, pending_stream.
  cbn [drain_b_c.drain_init drain_b_c.ds_pend drain_b_c.ds_off].
  destruct (hl_recs (hs_pending h)) as [|r rs]; cbn [map concat length]; [lia|].
  rewrite !length_app, length_skipn, dpre_concat_bzs. unfold bzs. rewrite length_map. lia.
Qed.

(* A :381: drain's requests from g_nout = 0, for an entry whose unfinished line is at most APARTIAL bytes and the
   source the relay reads it from (pair_ok's clauses), with at most 65535 * 511 bytes pending (t < OPS_MAX); A's
   WR_MMAX is fr_MMAX (lib/B/ReplyLSBArms.v fr_MMAX_val) *)
Lemma dpre_dr_tr_max : forall c mx cap e h,
  Z.of_nat (length (re_U e)) <= APARTIAL ->
  hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h) ->
  0 <= hs_off h -> hl_recs (hs_expected h) = [] ->
  Z.of_nat (length (re_keys e)) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 ->
  Z.of_nat (length (pending_stream h)) <= 65535 * 511 ->
  tr_max (dr_tr c mx 0 cap e h) < fr_MMAX.
Proof.
  intros c mx cap e h HU HJ Ho He Hk Hp.
  pose proof fr_MMAX_val as EM.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold APARTIAL in HU.
  assert (HM : tr_max (dr_tr c mx 0 cap e h) <= fr_MMAX - 1).
  { unfold dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go.
    apply dpre_tr_max; [lia|].
    apply (dpre_drain_run _ _ _ _ _ _ (fr_MMAX - 1) (Z.of_nat (length (re_keys e)))
             (6000 + Z.of_nat (length (pending_stream h))) (Z.of_nat (length (pending_stream h))));
      [|lia ..].
    pose proof (dpre_rem_init 0 cap e h Ho) as Hr.
    unfold dpre_inv.
    cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H
         drain_b_c.ds_en] in Hr |- *.
    assert (Hu : length (bzs (re_U e)) = length (re_U e)) by (unfold bzs; apply length_map).
    split; [lia|]. split; [exact Ho|]. split.
    { unfold dpre_jref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
      destruct HJ as [E|E]; [left; rewrite E; reflexivity | right; rewrite <- E; lia]. }
    split; [lia|]. split.
    { unfold drain_b_c.keys_texts. rewrite length_map. lia. }
    unfold hl_n. rewrite He. cbn [length]. lia. }
  lia.
Qed.

(* A :425 *)
Lemma dpre_keys_le : forall ks, Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof.
  induction ks as [|k ks IH]; [cbn; lia|].
  unfold gestures_end_b_c.keys_total in *. cbn [fold_right length]. lia.
Qed.

(* ================================================================== the relay's lines, drain's g_nout (A ReplyLSRemove3.v) *)
(* A :112 *)
Lemma rm3_scan_mass : forall d skip acc,
  Z.of_nat (length (RelayModel.with_nul (snd (RelayModel.scan skip acc d)))) +
  (if fst (fst (RelayModel.scan skip acc d)) then 0 else Z.of_nat (length (snd (fst (RelayModel.scan skip acc d))))) <=
  (if skip then 0 else Z.of_nat (length acc)) + Z.of_nat (length d).
Proof.
  induction d as [|b d IH]; intros skip acc.
  - cbn [RelayModel.scan fst snd]. rewrite RelayCap.with_nul_nil_len. cbn [length]. destruct skip; lia.
  - destruct (Z.eq_dec b 0) as [-> | Hb].
    + rewrite RelayModel.scan_zero. pose proof (IH false []) as I. cbn [length] in I |- *.
      destruct (RelayModel.scan false [] d) as [[sk r] ls]. cbv beta iota in I |- *. cbn [fst snd] in I |- *.
      destruct (skip || Nat.ltb RelayModel.LINE_LIMIT (length acc))%bool eqn:C.
      * destruct skip, sk; lia.
      * apply orb_false_iff in C as [C _]. subst skip. rewrite RelayCap.with_nul_cons_len. destruct sk; lia.
    + rewrite (RelayModel.scan_nz skip acc b d Hb). pose proof (IH skip (acc ++ [b])) as I.
      rewrite length_app in I. cbn [length] in I |- *.
      destruct (fst (fst (RelayModel.scan skip (acc ++ [b]) d))), skip; lia.
Qed.
(* A :129 *)
Lemma rm3_chunk_mass : forall u skip d u' sk' rl, RelayModel.chunk u skip d = (u', sk', rl) ->
  Z.of_nat (length (RelayModel.with_nul rl)) + (if sk' then 0 else Z.of_nat (length u')) <=
  (if skip then 0 else Z.of_nat (length u)) + Z.of_nat (length d).
Proof.
  intros u skip d u' sk' rl E. unfold RelayModel.chunk in E. pose proof (rm3_scan_mass d skip u) as M.
  destruct (RelayModel.scan skip u d) as [[sk r] ls]. cbv beta iota in E. cbn [fst snd] in M.
  destruct (Nat.ltb RelayModel.LINE_LIMIT (length r)); injection E as <- <- <-; cbn [length];
    [destruct sk; lia | exact M].
Qed.

(* A :139: drain's g_nout: at most the relay's unfinished line (when it keeps it) and the pending stream *)
Definition rm3_dstr (s : drain_b_c.dstate) : list Z :=
  match drain_b_c.ds_pend s with [] => [] | r :: rs => skipn (Z.to_nat (drain_b_c.ds_off s)) r ++ concat rs end.
Definition rm3_dm (s : drain_b_c.dstate) : Z :=
  drain_b_c.ds_no s + (if drain_b_c.ds_skip s then 0 else Z.of_nat (length (drain_b_c.ds_u s))) +
  Z.of_nat (length (rm3_dstr s)).
(* A :144 *)
Lemma rm3_dstr0 : forall rs : list (list Z),
  length (match rs with [] => [] | r :: rs' => skipn (Z.to_nat 0) r ++ concat rs' end) = length (concat rs).
Proof. intros [|r rs]; reflexivity. Qed.
(* A :147 *)
Lemma rm3_dm_run : forall f lv mx s j a, 0 <= drain_b_c.ds_off s ->
  rm3_dm (fst (snd (drain_b_c.drain_run f lv mx s j a))) <= rm3_dm s.
Proof.
  intros f lv mx. induction f as [|f IH]; intros s j a Ho; [cbn [drain_b_c.drain_run fst snd]; lia|].
  cbn [drain_b_c.drain_run]. cbv zeta.
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst snd].
    match goal with |- rm3_dm (fst (snd (drain_b_c.drain_run f lv mx ?s1 ?j1 ?a1))) <= _ =>
      eapply Z.le_trans; [apply (IH s1 j1 a1); exact Ho|] end.
    unfold rm3_dm, rm3_dstr.
    cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off]. lia.
  - unfold rm3_dm at 2. unfold rm3_dstr.
    destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:Ep.
    + cbn [fst snd]. unfold rm3_dm, rm3_dstr.
      cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off]. lia.
    + match goal with |- context [Z.min ?x ?y <=? 0] => set (n := Z.min x y) in * end.
      assert (Hnr : n <= Z.of_nat (length r0) - drain_b_c.ds_off s) by (unfold n; apply Z.le_min_l).
      destruct (Z.leb_spec n 0) as [Hn | Hn].
      * cbn [fst snd]. unfold rm3_dm, rm3_dstr.
        cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off]. lia.
      * match goal with |- context [RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) ?d] =>
          set (dd := d) in *;
          destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) dd) as [[u' sk'] rl] eqn:EC end.
        pose proof (rm3_chunk_mass _ _ _ _ _ _ EC) as CM.
        assert (Ld : Z.of_nat (length dd) = n) by (unfold dd; rewrite length_firstn, length_skipn; lia).
        try (cbv beta iota).
        match goal with |- context [drain_b_c.lines_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)
                                      (drain_b_c.ds_H s) (drain_b_c.ds_ka s) rl ?j3 ?o ?ha ?ks] =>
          destruct (drain_b_c.lines_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                      (drain_b_c.ds_ka s) rl j3 o ha ks) as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
        cbn [fst snd].
        match goal with |- rm3_dm (fst (snd (drain_b_c.drain_run f lv mx ?s2 ?j4 ?a2))) <= _ =>
          eapply Z.le_trans; [apply (IH s2 j4 a2)|] end.
        { cbn [drain_b_c.ds_off]. destruct (_ =? _); lia. }
        unfold rm3_dm, rm3_dstr.
        cbn [drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_pend drain_b_c.ds_off].
        rewrite length_app, length_skipn.
        destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [W|W].
        -- rewrite rm3_dstr0. lia.
        -- rewrite length_app, length_skipn. lia.
Qed.
(* A :188 *)
Lemma rm3_skipn_map : forall (X Y : Type) (f : X -> Y) n l, skipn n (map f l) = map f (skipn n l).
Proof. intros X Y f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
(* A :190 *)
Lemma rm3_dstr_init : forall NO CAP e h, rm3_dstr (drain_b_c.drain_init NO CAP e h) = bzs (pending_stream h).
Proof.
  intros NO CAP e h. unfold rm3_dstr, drain_b_c.drain_init, pending_stream. cbn [drain_b_c.ds_pend drain_b_c.ds_off].
  destruct (hl_recs (hs_pending h)) as [|r rs]; [reflexivity|]. cbn [map].
  unfold bzs. rewrite map_app, rm3_skipn_map, concat_map, map_map. reflexivity.
Qed.
(* A :196 *)
Lemma rm3_no_fin : forall live mx CAP e h, 0 <= hs_off h ->
  drain_b_c.ds_no (drain_b_c.drain_fin live mx 0 CAP e h) <=
  (if re_skip e =? 1 then 0 else Z.of_nat (length (re_U e))) + Z.of_nat (length (pending_stream h)).
Proof.
  intros live mx CAP e h Ho. unfold drain_b_c.drain_fin, drain_b_c.drain_go.
  pose proof (rm3_dm_run (S (S (length (pending_stream h)))) live mx (drain_b_c.drain_init 0 CAP e h) 0%nat
    drain_b_c.dadr0 Ho) as D.
  unfold rm3_dm at 2 in D. rewrite rm3_dstr_init in D.
  cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u] in D.
  rewrite !RelayCap.rc_length_bzs in D.
  revert D. generalize (fst (snd (drain_b_c.drain_run (S (S (length (pending_stream h)))) live mx
    (drain_b_c.drain_init 0 CAP e h) 0 drain_b_c.dadr0))). intros s D.
  unfold rm3_dm in D. destruct (drain_b_c.ds_skip s); lia.
Qed.

(* A :237: the held keys' bytes, 5 each for the gesture end *)
Definition rm3_kw (T : list (list Z)) : Z := zsum (map (fun x => Z.of_nat (length x) + 5) T).
(* A :284 *)
Lemma rm3_kt_kw : forall ks, gestures_end_b_c.keys_total ks = rm3_kw (drain_b_c.keys_texts ks).
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  change (gestures_end_b_c.keys_total (k :: ks)) with
    (Z.of_nat (length (gestures_end_b_c.key_text k)) + 5 + gestures_end_b_c.keys_total ks).
  change (drain_b_c.keys_texts (k :: ks)) with (bzs (gestures_end_b_c.key_text k) :: drain_b_c.keys_texts ks).
  unfold rm3_kw in *. cbn [map fold_right]. rewrite IH, RelayCap.rc_length_bzs. lia.
Qed.
(* A :435 *)
Lemma rm3_kt_len : forall ks, 5 * Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof. unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right length]; lia. Qed.

(* ================================================================== relay_remove's trace (A ReplyLSRrPre.v) *)
(* A :95: the entry of fd that find returns is the first one with that fd *)
Lemma rrp_find : forall (es : list rentry) (j0 : nat) (fd : Z),
  (j0 < length es)%nat -> re_fd (nth j0 es relay_remove_b_c.no_entry) = fd ->
  (forall q, (q < j0)%nat -> re_fd (nth q es relay_remove_b_c.no_entry) <> fd) ->
  find (fun e => re_fd e =? fd) es = Some (nth j0 es relay_remove_b_c.no_entry).
Proof.
  induction es as [|e es IH]; intros j0 fd Hj Hf Hq; [cbn [length] in Hj; lia|].
  destruct j0 as [|j0].
  - cbn [nth] in Hf |- *. cbn [find]. rewrite Hf, Z.eqb_refl. reflexivity.
  - pose proof (Hq 0%nat ltac:(lia)) as E. cbn [nth] in E. cbn [find nth].
    rewrite (proj2 (Z.eqb_neq _ _) E).
    apply IH; [cbn [length] in Hj; lia | exact Hf |].
    intros q Hq'. exact (Hq (S q) ltac:(lia)).
Qed.

(* A :112: a begin line's key and its 5 end bytes are at most the line and its NUL *)
Lemma rrp_gesture_begin : forall l x, RelayModel.gesture l = Some (GBegin, x) ->
  Z.of_nat (length x) + 5 <= Z.of_nat (length l) + 1.
Proof.
  intros l x G. unfold RelayModel.gesture in G.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|]; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:EB.
  - injection G as EX. subst x. unfold list_eqb in EB.
    destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [Es|]; [|discriminate].
    pose proof (f_equal (@length Z) Es) as LE. rewrite length_skipn in LE. cbn [W_BEGIN length] in LE.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.

(* A :129: gesture_seen's held array: its keys' bytes with 5 each grow by at most the line and its NUL *)
Lemma rrp_seen_kw : forall H l, rm3_kw (RelayKeys.seen_arr H l) <= rm3_kw H + Z.of_nat (length l) + 1.
Proof.
  intros H l. unfold RelayKeys.seen_arr. destruct (RelayModel.gesture l) as [[k x]|] eqn:EG; [destruct k|].
  - destruct (RelayKeys.index_of x H); [lia|]. unfold rm3_kw. rewrite map_app, zsum_app. cbn [map fold_right].
    pose proof (rrp_gesture_begin l x EG). lia.
  - destruct (RelayKeys.index_of x H) as [n|] eqn:EI; [|lia].
    destruct (RelayKeys.index_of_some x H n EI) as (a & b & -> & <-).
    pose proof (fr_sum_perm _ (fun y => Z.of_nat (length y) + 5) _ _ (RelayKeys.swap_remove_perm [] a x b)) as E.
    unfold rm3_kw. rewrite E. cbn [map fold_right]. lia.
  - lia.
Qed.

(* A :141 *)
Lemma rrp_lines_kw : forall live mx ls no cap H ka j o ha ks,
  rm3_kw (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))))) <=
  rm3_kw H + Z.of_nat (length (RelayModel.with_nul ls)).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks.
  - cbn [drain_b_c.lines_run snd fst]. rewrite RelayCap.with_nul_nil_len. lia.
  - cbn [drain_b_c.lines_run]. cbv zeta. cbn [snd fst]. rewrite RelayCap.with_nul_cons_len.
    match goal with |- context [drain_b_c.lines_run live mx ?n ?c (RelayKeys.seen_arr H l) ?k ls ?j1 ?o1 ?h1 ?s1] =>
      pose proof (IH n c (RelayKeys.seen_arr H l) k j1 o1 h1 s1) as IHr end.
    pose proof (rrp_seen_kw H l). lia.
Qed.

(* A :154: over drain's rounds the held keys' bytes grow by at most what g_nout grows by *)
Lemma rrp_drain_kw : forall f live mx s j a,
  rm3_kw (drain_b_c.ds_H (fst (snd (drain_b_c.drain_run f live mx s j a)))) -
    drain_b_c.ds_no (fst (snd (drain_b_c.drain_run f live mx s j a))) <=
  rm3_kw (drain_b_c.ds_H s) - drain_b_c.ds_no s.
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a.
  - cbn [drain_b_c.drain_run snd fst]. lia.
  - cbn [drain_b_c.drain_run]. cbv zeta. destruct (drain_b_c.ds_eintr s).
    + cbn [snd fst].
      match goal with |- context [drain_b_c.drain_run f live mx ?s1 ?j1 ?a1] => pose proof (IH s1 j1 a1) as I1 end.
      cbn [drain_b_c.ds_H drain_b_c.ds_no] in I1. lia.
    + destruct (drain_b_c.ds_pend s) as [|r0 rs].
      { cbn [snd fst drain_b_c.ds_H drain_b_c.ds_no]. lia. }
      match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end.
      { cbn [snd fst drain_b_c.ds_H drain_b_c.ds_no]. lia. }
      match goal with |- context [RelayModel.chunk ?u ?k ?d] =>
        destruct (RelayModel.chunk u k d) as [[u' sk'] rl] end.
      match goal with |- context [drain_b_c.lines_run live mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)
                                    (drain_b_c.ds_H s) (drain_b_c.ds_ka s) rl ?j3 ?o ?ha ?ks] =>
        pose proof (rrp_lines_kw live mx rl (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                      (drain_b_c.ds_ka s) j3 o ha ks) as LW;
        destruct (drain_b_c.lines_run live mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                    (drain_b_c.ds_ka s) rl j3 o ha ks) as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
      cbn [snd fst] in LW |- *.
      match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] => pose proof (IH s2 j4 a2) as I1 end.
      cbn [drain_b_c.ds_H drain_b_c.ds_no] in I1. lia.
Qed.

(* A :183: from g_nout = 0, the keys drain leaves are at most the entry's keys_total and drain's final g_nout *)
Lemma rrp_fin_kw : forall lv mx CAP e h,
  rm3_kw (drain_b_c.ds_H (drain_b_c.drain_fin lv mx 0 CAP e h)) <=
  gestures_end_b_c.keys_total (re_keys e) + drain_b_c.ds_no (drain_b_c.drain_fin lv mx 0 CAP e h).
Proof.
  intros lv mx CAP e h. unfold drain_b_c.drain_fin, drain_b_c.drain_go.
  pose proof (rrp_drain_kw (S (S (length (pending_stream h)))) lv mx (drain_b_c.drain_init 0 CAP e h) 0%nat
                drain_b_c.dadr0) as W.
  change (drain_b_c.ds_H (drain_b_c.drain_init 0 CAP e h)) with (drain_b_c.keys_texts (re_keys e)) in W.
  change (drain_b_c.ds_no (drain_b_c.drain_init 0 CAP e h)) with 0 in W.
  rewrite <- rm3_kt_kw in W. lia.
Qed.

(* A :199: gestures_end_b_c.keys_end_run: each key's two send_lines from g_nout no, which then grows by |key| + 5;
   each send_line round asks at most 2 * (no + len) (dpre_send_line); the key's free asks nothing *)
Lemma rrp_ker : forall live mx (xks : list (Z * RelayRunT.addr YO0i.sptr)) no cap j o M,
  Forall (fun x => 0 <= fst x) xks ->
  2 * (no + fold_right (fun x acc => fst x + 5 + acc) 0 xks) <= M ->
  Forall (dpre_rq M) (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o M HF HM;
    cbn [gestures_end_b_c.keys_end_run fst]; [constructor|].
  apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx. cbn [fold_right fst] in HM.
  assert (Hr : 0 <= fold_right (fun x acc => fst x + 5 + acc) 0 r).
  { clear -HF. revert HF. induction r as [|[x k] r IHr]; intros HF; cbn [fold_right fst]; [lia|].
    apply Forall_cons_iff in HF as [H1 H2]. cbn [fst] in H1. specialize (IHr H2). lia. }
  apply Forall_app. split.
  - unfold gesture_end_b_c.gesture_end_tr. apply Forall_app. split; apply dpre_send_line; lia.
  - apply Forall_cons; [exact I|]. apply IH; [exact HF | lia].
Qed.

(* A :215 *)
Lemma rrp_ker_w : forall (A : Type) (a0 : A) (H : list (list Z)),
  fold_right (fun x acc => fst x + 5 + acc) 0 (map (fun x => (Z.of_nat (length x), a0)) H) = rm3_kw H.
Proof. intros A a0 H. unfold rm3_kw. induction H as [|x H IH]; cbn [map fold_right fst]; lia. Qed.

(* A :220: rr_tr's key run: the held texts' lengths, from g_nout no *)
Lemma rrp_ker_lens : forall live mx (H : list (list Z)) (a0 : RelayRunT.addr YO0i.sptr) no cap j o M,
  2 * (no + rm3_kw H) <= M ->
  Forall (dpre_rq M)
    (fst (gestures_end_b_c.keys_end_run live mx no cap (map (fun x => (Z.of_nat (length x), a0)) H) j o)).
Proof.
  intros live mx H a0 no cap j o M HM. apply rrp_ker.
  - apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (x & <- & _). cbn [fst]. lia.
  - rewrite rrp_ker_w. exact HM.
Qed.

(* ================================================================== the model's blocks, fr_RINV at the source *)
Section rm3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* A ReplyLSRemove3.v :357 *)
Lemma rm3_in_model_entry : forall m j0 b, (j0 < length (lm_es m))%nat -> In b (aentry_blks (rm_ent m j0)) ->
  In b (model_blks m).
Proof.
  intros m j0 b Hj Hb. unfold model_blks. right. apply in_or_app. left. apply in_concat.
  exists (aentry_blks (rm_ent m j0)). split; [apply in_map; unfold rm_ent; apply nth_In; exact Hj | exact Hb].
Qed.
(* A ReplyLSRemove3.v :101 *)
Lemma rm3_nth_lt : forall (hs : list (option hsrc)) i h, nth i hs None = Some h -> (i < length hs)%nat.
Proof.
  intros hs i h H. destruct (Nat.lt_ge_cases i (length hs)) as [L|L]; [exact L|].
  rewrite nth_overflow in H by exact L. discriminate H.
Qed.
(* A ReplyLSRemove3.v :363 *)
Lemma rm3_in_model_slot : forall m si h b, nth si (lm_hs m) None = Some h -> In b (asrc_blks h) -> In b (model_blks m).
Proof.
  intros m si h b Hh Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. apply in_concat.
  exists (slot_blks (Some h)). split; [|exact Hb]. apply in_map. rewrite <- Hh. apply nth_In. exact (rm3_nth_lt _ _ _ Hh).
Qed.
(* A ReplyLSRemove3.v :368 *)
Lemma rm3_in_model_out : forall m b, In b (aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m).
Proof. intros m b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. right. exact Hb. Qed.

(* A ReplyLSRemove3.v :413: the relay entry j0 and slot si's source h are one pair of fr_relay; its cost is under the
   input *)
Lemma rm3_pair : forall cx t m si h j0, fr_RINV cx t m -> rm_at cx m si h j0 ->
  fr_pair_ok m t (rm_ent m j0) (h, si) /\ fr_entry_ok (rm_ent m j0) /\
  fr_pair_cost (rm_ent m j0) (h, si) <= c_n cx /\ c_n cx < 2 ^ 26.
Proof.
  intros cx t m si h j0 HRI Hat.
  pose proof HRI as (_ & HR & Hn & _).
  destruct Hat as (_ & _ & _ & _ & Hsi & Hh & Hj0 & Hfd & _).
  destruct HR as (Hlen & Hnd & _ & Hent & hj & HF & _ & Hcl & _ & Hcn).
  destruct (fr_pair_of_open m t hj si h HF Hcl Hsi Hh) as (e & p & Hin & HRp & Hs & Hf).
  destruct p as [p1 p2]. cbn [fst snd] in Hs, Hf. subst p1 p2.
  assert (He : In e (lm_es m)) by (eapply in_combine_l; exact Hin).
  assert (He0 : In (rm_ent m j0) (lm_es m)) by (unfold rm_ent; apply nth_In; exact Hj0).
  assert (Ee : e = rm_ent m j0).
  { apply (rm3_nodup_inj _ _ re_fd (lm_es m)); [apply NoDup_ListNoDup; exact Hnd | exact He | exact He0 |].
    destruct HRp as (_ & _ & Hf' & _). cbn [fst] in Hf'. rewrite <- Hf'. symmetry. exact Hfd. }
  subst e.
  split; [exact HRp|]. split; [rewrite Forall_forall in Hent; exact (Hent _ He0)|].
  split; [|lia].
  eapply Z.le_trans; [|exact Hcn]. unfold fr_cost.
  exact (rm3_in_le_sum _ (fun q => fr_pair_cost (fst q) (snd q)) _ (rm_ent m j0, (h, si))
    (fun q => fr_pair_cost_nonneg _ _) Hin).
Qed.
End rm3.
