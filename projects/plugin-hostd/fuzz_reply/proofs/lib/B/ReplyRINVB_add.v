(* proves no function (rule 24; kind: model rules): ARM_add's three RINV rules of B top_x against ReplyRINVB.fr_RINV *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B (fuzz_reply.asan-ubsan) twin of ARM_add's part of lib/A/ReplyRINV.v
   and lib/A/ReplyTopXRI.v at 8da615a239d (a working branch; file sha256 f3e0c442419d and
   cd0b3c4e0107).  FREE-PIECES.md (sha256 0f44f6fd1403; internal record) row G-BRI-add [STABLE]: B-TOPX-OWNERS.md (sha256 705727227472; internal record) rows 67-69.

   What is here, each with its source in A's ReplyRINV.v (A) and the B top_x hypothesis it closes
   (lib/B/W_LLVMFuzzerTestOneInput_top_x.v at e43cf0c7bef, file sha256 44f0396075f3):
     fr_Forall2_r, fr_in4, fr_nopen_set, fr_nodup_snoc, fr_cost_snoc   A :605-611, :691-692, :966-990, the same text;
     RI_add_pre_B   = top_x :403-406 RI_add_pre   with RINV := ReplyRINVB.fr_RINV   (proof: A :693-725 RI_add_pre_fix_holds);
     RI_add_open_B  = top_x :407-411 RI_add_open  with RINV := ReplyRINVB.fr_RINV   (proof: A :992-1061 RI_add_open_fix_holds);
     RI_add_none_B  = top_x :412-415 RI_add_none  with RINV := ReplyRINVB.fr_RINV   (proof: A :829-834 RI_add_none_holds).
   Each lemma is stated in top_x's premise order (RINV, then 0 <= t < OPS_MAX), so it IS the hypothesis's text and no
   premise-reorder adapter (A's ReplyTopXRI.v :162-176 topx_RI_add_pre / _open) is needed; the proofs are A's with
   their intros reordered to match.  fr_step_k and fr_Forall2_impl are ReplyRINVB.v's (:290, :286; A :805, :798).
   No numeral of an image address: the model functions (ad_at_op / ad_os / ad_open / ad_none, lib/B/
   W_LLVMFuzzerTestOneInput_add.v :823-834 and :168-187; oa_first / oa_new_src, lib/B/W_op_add.v :140-149; ra_new,
   lib/B/W_contract.v :1131) have A's text, and fr_RINV is A's (ReplyRINVB.v header :10). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c gestures_end_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
(* ARM_add's model: the AR file and W_op_add (oa_first, oa_new_src), as top_x names them qualified *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_op_add W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRINVB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".

Local Notation ad_at_op := W_LLVMFuzzerTestOneInput_add.ad_at_op.
Local Notation ad_os := W_LLVMFuzzerTestOneInput_add.ad_os.
Local Notation ad_os_nth := W_LLVMFuzzerTestOneInput_add.ad_os_nth.
Local Notation ad_open := W_LLVMFuzzerTestOneInput_add.ad_open.
Local Notation ad_none := W_LLVMFuzzerTestOneInput_add.ad_none.
Local Notation ad_set_ev := W_LLVMFuzzerTestOneInput_add.ad_set_ev.
Local Notation ad_set_nth := W_LLVMFuzzerTestOneInput_add.ad_set_nth.
Local Notation oa_first := W_op_add.oa_first.
Local Notation oa_new_src := W_op_add.oa_new_src.

Section add.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation fr_RINV := ReplyRINVB.fr_RINV.

(* ---- helpers, A :605-611, :691-692, :966-990 *)
Lemma fr_Forall2_r : forall (X Y : Type) (R : X -> Y -> Prop) l1 l2,
  Forall2 R l1 l2 -> forall y, In y l2 -> exists x, In x l1 /\ R x y.
Proof.
  intros X Y R l1 l2 H. induction H as [|x y l1 l2 Hxy _ IH]; intros z Hz; [destruct Hz|].
  destruct Hz as [<- | Hz]; [exists x; split; [left; reflexivity | exact Hxy]|].
  destruct (IH z Hz) as (x' & Hx' & HR). exists x'. split; [right; exact Hx' | exact HR].
Qed.
Lemma fr_in4 : forall s, (s < 4)%nat -> In s [0; 1; 2; 3]%nat.
Proof. intros s Hs. destruct s as [|[|[|[|s]]]]; cbn; first [tauto | lia]. Qed.
Lemma fr_nopen_set : forall hs i x, nth i hs None = None -> (i < length hs)%nat ->
  nopen (ad_set_nth i (Some x) hs) = nopen hs + 1.
Proof.
  intros hs i x. unfold nopen. revert i. induction hs as [|o hs IH]; intros [|i] Hn Hi;
    cbn [length] in Hi; try lia.
  - cbn [nth] in Hn. subst o. cbn [W_LLVMFuzzerTestOneInput_add.ad_set_nth List.filter length]. lia.
  - cbn [nth] in Hn. pose proof (IH i Hn ltac:(lia)) as Hih.
    destruct o; cbn [W_LLVMFuzzerTestOneInput_add.ad_set_nth List.filter length]; lia.
Qed.
Lemma fr_nodup_snoc : forall (T : Type) (l : list T) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros T l x. induction l as [|a l IH]; intros Hnd Hx; cbn [app].
  - constructor; [intros [] | constructor].
  - apply NoDup_cons_iff in Hnd as [Ha Hnd]. constructor.
    + intros Hin. apply in_app_or in Hin as [Hin | [Hin | []]]; [exact (Ha Hin)|].
      subst a. apply Hx. left. reflexivity.
    + apply IH; [exact Hnd|]. intros Hin. apply Hx. right. exact Hin.
Qed.
Lemma fr_cost_snoc : forall es hj e p, length es = length hj ->
  ReplyRINVB.fr_cost (es ++ [e]) (hj ++ [p]) = ReplyRINVB.fr_cost es hj + ReplyRINVB.fr_pair_cost e p.
Proof.
  unfold ReplyRINVB.fr_cost. induction es as [|e0 es IH]; intros [|p0 hj] e p Hl; cbn [length] in Hl;
    try discriminate Hl.
  - cbn [app combine map fold_right fst snd]. lia.
  - cbn [app combine map fold_right fst snd]. rewrite IH by lia. lia.
Qed.

(* ---- top_x :403-406 RI_add_pre at RINV := fr_RINV (A :693-725, intros in top_x's order) *)
Lemma RI_add_pre_B : forall cx t m,
  fr_RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m ->
  oa_first (ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Proof.
  intros cx t m ((HC & Hnfd) & HR & _ & _) Ht _ Hfree.
  destruct HR as (Hlen & _ & Hrng & _ & hj & HF & HNDs & _ & _ & _).
  assert (Hi : exists i, (i < 4)%nat /\ nth i (lm_hs m) None = None).
  { unfold W_op_add.oa_first in Hfree. rewrite !ad_os_nth in Hfree.
    destruct (nth 0 (lm_hs m) None) eqn:E0; [|exists 0%nat; split; [lia | exact E0]].
    destruct (nth 1 (lm_hs m) None) eqn:E1; [|exists 1%nat; split; [lia | exact E1]].
    destruct (nth 2 (lm_hs m) None) eqn:E2; [|exists 2%nat; split; [lia | exact E2]].
    destruct (nth 3 (lm_hs m) None) eqn:E3; [|exists 3%nat; split; [lia | exact E3]].
    exfalso. apply Hfree. reflexivity. }
  destruct Hi as (i & Hi4 & Hin).
  (* the free slot leaves at most three open *)
  assert (Hop : nopen (lm_hs m) <= 3).
  { clear - Hlen Hi4 Hin. unfold nopen.
    destruct (lm_hs m) as [|o0 [|o1 [|o2 [|o3 [|o4 hs']]]]]; cbn in Hlen; try discriminate Hlen.
    destruct o0, o1, o2, o3; destruct i as [|[|[|[|i]]]]; cbn in Hin |- *; try discriminate Hin; lia. }
  split; [|split].
  - (* the entries' sources are distinct open slots, none of them the free one *)
    rewrite (Forall2_length HF).
    assert (Hinc : incl (map snd hj) (List.filter (fun y => negb (Nat.eqb y i)) [0; 1; 2; 3]%nat)).
    { intros y Hy. apply in_map_iff in Hy as (p & <- & Hp).
      destruct (fr_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & HRp).
      destruct HRp as (Hs4 & Hsn & _).
      apply filter_In. split; [exact (fr_in4 _ Hs4)|].
      apply negb_true_iff, Nat.eqb_neq. intros E. rewrite E, Hin in Hsn. discriminate Hsn. }
    apply NoDup_ListNoDup in HNDs.
    pose proof (NoDup_incl_length HNDs Hinc) as Hle. rewrite length_map in Hle.
    destruct i as [|[|[|[|i]]]]; cbn in Hle; lia.
  - intros Hx. apply in_map_iff in Hx as (e & Hfd & He).
    rewrite Forall_forall in Hrng. specialize (Hrng e He). lia.
  - unfold OPS_MAX in *. lia.
Qed.

(* ---- top_x :407-411 RI_add_open at RINV := fr_RINV (A :992-1061, intros in top_x's order) *)
Lemma RI_add_open_B : forall cx t m i q pj ev,
  fr_RINV cx t m -> 0 <= t < OPS_MAX -> ad_at_op cx m ->
  oa_first (ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  fr_RINV cx (t + 1) (ad_open m i q pj ev).
Proof.
  intros cx t m i q pj ev HRI Ht Hop Hfirst _ _.
  pose proof (RI_add_pre_B cx t m HRI Ht Hop ltac:(rewrite Hfirst; discriminate)) as (_ & _ & Hlt).
  destruct HRI as ((HC & Hnfd) & HR & Hn & HG).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  pose proof (W_LLVMFuzzerTestOneInput_add.ad_first_lt _ _ Hfirst) as Hi4.
  assert (Hfree : nth i (lm_hs m) None = None).
  { pose proof (W_LLVMFuzzerTestOneInput_add.ad_first_zero _ _ Hfirst) as Hz. rewrite ad_os_nth in Hz.
    destruct (nth i (lm_hs m) None); [discriminate Hz | reflexivity]. }
  assert (Hil : (i < length (lm_hs m))%nat) by (rewrite Hlen; exact Hi4).
  (* no entry of the table follows slot i *)
  assert (Hnot : forall p, In p hj -> snd p <> i).
  { intros p Hp E. destruct (fr_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & HRp).
    destruct HRp as (_ & Hsn & _). rewrite E, Hfree in Hsn. discriminate Hsn. }
  split; [|split; [|split; [exact Hn|]]].
  - unfold ReplyRINVB.fr_count, W_LLVMFuzzerTestOneInput_add.ad_open. cbn [lm_nfd lm_hs].
    rewrite (fr_nopen_set _ _ _ Hfree Hil). unfold OPS_MAX in *. lia.
  - unfold ReplyRINVB.fr_relay, W_LLVMFuzzerTestOneInput_add.ad_open. cbn [lm_hs lm_es lm_nfd lm_k].
    split; [rewrite W_LLVMFuzzerTestOneInput_add.ad_set_nth_length; exact Hlen|].
    split.
    { apply NoDup_ListNoDup. rewrite List.map_app. cbn [map]. apply fr_nodup_snoc.
      - exact (proj1 (NoDup_ListNoDup _) Hnd).
      - intros Hx. apply in_map_iff in Hx as (e & Hfd & He). rewrite Forall_forall in Hrng.
        specialize (Hrng e He). cbn [re_fd ra_new] in Hfd. lia. }
    split.
    { apply Forall_app. split.
      - eapply Forall_impl; [|exact Hrng]. intros e He. cbv beta in *. lia.
      - constructor; [cbn [re_fd ra_new]; lia | constructor]. }
    split.
    { apply Forall_app. split; [exact Hent|].
      constructor; [|constructor]. unfold ReplyRINVB.fr_entry_ok. cbn [re_eof re_pad1 re_pad2 re_keys re_skip ra_new].
      split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
    exists (hj ++ [(oa_new_src (100 + lm_nfd m) q pj, i)]).
    split.
    { apply Forall2_app.
      - eapply ReplyRINVB.fr_Forall2_impl; [|exact HF]. intros e p Hp.
        assert (Hne : i <> snd p).
        { intros E. destruct Hp as (_ & Hsn & _). rewrite <- E, Hfree in Hsn. discriminate Hsn. }
        destruct Hp as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        unfold ReplyRINVB.fr_pair_ok. cbn [lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_add.ad_set_nth_other _ i (snd p) _ _ _ Hne).
        unfold SlotInv.WRITE_MAX in *.
        refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
          (conj _ H11)))))))))). lia.
      - constructor; [|constructor].
        unfold ReplyRINVB.fr_pair_ok. cbn [fst snd lm_hs].
        rewrite (W_LLVMFuzzerTestOneInput_add.ad_set_nth_same _ i _ _ _ Hil).
        split; [exact Hi4|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; reflexivity]|].
        split; [intros y; split; intros []|].
        split; [apply NoDup_ListNoDup; constructor|].
        split; [reflexivity|]. split; [left; reflexivity|].
        split; [change (0 < 2 ^ 24); lia|].
        split; [change (0 <= SlotInv.WRITE_MAX * (t + 1)); unfold SlotInv.WRITE_MAX; lia | change (0 <= 0); lia]. }
    split.
    { apply NoDup_ListNoDup. rewrite List.map_app. cbn [map snd]. apply fr_nodup_snoc.
      - exact (proj1 (NoDup_ListNoDup _) HNDs).
      - intros Hin. apply in_map_iff in Hin as (p & Hpi & Hp). exact (Hnot p Hp Hpi). }
    split.
    { intros j Hj Ho. unfold SlotInv.slot_open in Ho. rewrite List.map_app, existsb_app in Ho.
      cbn [map snd existsb] in Ho. apply orb_false_iff in Ho as [Ho1 Ho2].
      rewrite orb_false_r in Ho2. apply Nat.eqb_neq in Ho2.
      rewrite (W_LLVMFuzzerTestOneInput_add.ad_set_nth_other _ i j _ _ _ (not_eq_sym Ho2)).
      exact (Hcl j Hj Ho1). }
    rewrite fr_cost_snoc by exact (Forall2_length HF).
    assert (H0 : ReplyRINVB.fr_pair_cost (ra_new (100 + lm_nfd m)) (oa_new_src (100 + lm_nfd m) q pj, i) = 0)
      by reflexivity.
    rewrite H0. split; lia.
  - unfold ReplyRINVB.fr_gone, W_LLVMFuzzerTestOneInput_add.ad_open, W_LLVMFuzzerTestOneInput_add.ad_set_ev.
    cbn [lm_gn lm_c ct_cl ct_br ct_dd]. exact HG.
Qed.

(* ---- top_x :412-415 RI_add_none at RINV := fr_RINV (A :829-834) *)
Lemma RI_add_none_B : forall cx t m,
  fr_RINV cx t m -> ad_at_op cx m ->
  oa_first (ad_os (lm_hs m)) = None ->
  fr_RINV cx (t + 1) (ad_none m).
Proof.
  intros cx t m H _ _. apply (ReplyRINVB.fr_step_k cx t m _ H); try reflexivity.
  - unfold W_LLVMFuzzerTestOneInput_add.ad_none. cbn [lm_k]. lia.
  - destruct H as (_ & _ & _ & HG). exact HG.
Qed.
End add.
