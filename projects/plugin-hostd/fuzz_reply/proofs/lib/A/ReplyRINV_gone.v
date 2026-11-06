(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: group RI-gone of the image-A top (W_LLVMFuzzerTestOneInput_top_x.v, the rows
   RI_gone_pairs / RI_gone_read / RI_gone_step / RI_gone_end) at RINV := fr_RINV (ReplyRINV.v).  Proves no function
   walk (model-rule obligations only).
   Part 1 (over ReplyRINV.v's copies of the gone model, verbatim the same text as gone_base.v's):
   - RI_gone_pairs_holds: fr_RINV's pairing hj of the table with the open sources is a gn_pairs witness.  The size
     bounds gn_pair_ok asks come from fr_RINV's cost bound (fr_cost <= c_n < 2 ^ 26: a pending stream and a key count
     are parts of one entry's cost) and from fr_pair_ok's ecap_ok.
   - RI_gone_read_holds: a slot k that reads (gn_reads m k = 1) holds the source of an open entry j; that entry's
     gn_pair_ok source is at slot k (fr_RINV's distinct fds, RI_fds_holds), so after relay_instance_gone slot k holds
     rig_post's source for entry j, which rig_rel's dr_rel leaves drained (pending list empty, offset 0).
   - RI_gone_read_sat: one state meets all of RI_gone_read's premises (and RI_gone_pairs's).
   - Section collapse / collapse2: the records of rounds 1 and 2 of the gone rules' texts (bb9dae5d905, a1a3591c77c),
     which were false at the instance; machine-checked counter-instances, not proofs of the rows.
   Part 2 (over W_LLVMFuzzerTestOneInput_gone_base.v's own model): RI_gone_pairs_plug / RI_gone_read_plug restate
   part 1 at gone_base's GN_RI_pairs / GN_RI_read; then the step and end rows.
   - The table-order loop (gn_run) as an invariant (rg_inv): every entry's slot, once processed, holds what
     check_no_loss and check_shape_ends left of what relay_instance_gone left there; when gone = 0, `at` is the
     entry's position in the stream relay_instance_gone sent (rg_acc_pos), which is the entries' drained lines and
     then their ended keys' end lines (rg_rel_dec, rg_strm).
   - RI_gone_step_holds(_c): GN_RI_step of a working branch a39b599f92e (copied verbatim as
     GN_RI_step_d) at MT := ameter_triv, RINV := fr_RINV, MMAX := WR_MMAX, LS := fr_LS3 B / fr_LS3c B.  The LS-side
     conjunct cnl_room is a Theorem Labs lane's gx6_step_room(_c) (ReplyLS3cTopxGoneF.v at b25d82fcf04); mo_ok is True at
     ameter_triv; the rest is RINV-side (rg_step_rinv_side).
   - RI_gone_end_holds_q5(_c): GN_RI_end of a39b599f92e (copied as GN_RI_end_q5) with REQ5 (no held list's capacity
     shrinks from m to mc) as one more, last, premise: s5-r1d's gx6_end_LS3(_c) needs it, and a39b599f92e's gn_cnl_ok
     does not carry `hl_cap (hs_held h) <= hl_cap H'` from which ReplyLS3cTopxGoneH.v's gxh_req5 derives it.
   - GN_RI_step_r3 (Section rg3): the record of round 3 (aa34c06e82c): without re_U NUL-free the step row is false.
   Local helpers rg_lines_nz / rg_upds_in / rg_W_read_lines_nz state what a Theorem Labs lane's ReplyRINV_a12.v
   (lines_nul_free / upds_nul_free) states; they stay local. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
RelayRunT drain_b_c gestures_end_b_c relay_remove_b_c relay_instance_gone_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section rg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== list facts *)
(* a sum of non-negative terms is non-negative, and each summand is at most the sum *)
Lemma rg_sum_nonneg : forall (T : Type) (f : T -> Z) l, (forall y, In y l -> 0 <= f y) ->
  0 <= fold_right Z.add 0 (map f l).
Proof.
  intros T f l. induction l as [|y l IH]; intros Hnn; cbn [map fold_right]; [lia|].
  pose proof (Hnn y (or_introl eq_refl)). pose proof (IH (fun w Hw => Hnn w (or_intror Hw))). lia.
Qed.
Lemma rg_sum_le : forall (T : Type) (f : T -> Z) l x, (forall y, In y l -> 0 <= f y) -> In x l ->
  f x <= fold_right Z.add 0 (map f l).
Proof.
  intros T f l. induction l as [|y l IH]; intros x Hnn Hx; [destruct Hx|].
  cbn [map fold_right].
  pose proof (rg_sum_nonneg T f l (fun w Hw => Hnn w (or_intror Hw))) as Hl.
  pose proof (Hnn y (or_introl eq_refl)) as Hy.
  destruct Hx as [<- | Hx]; [lia|].
  pose proof (IH x (fun w Hw => Hnn w (or_intror Hw)) Hx). lia.
Qed.
(* a key costs its text and five bytes, so the key count is at most keys_total *)
Lemma rg_nheld_le : forall ks, Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof.
  unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [fold_right length]; lia.
Qed.
(* the slots relay_instance_gone drains are some of the pairing's slots *)
Lemma rg_rig_slots_nodup : forall (es : list rentry) (hj : list (hsrc * nat)), List.NoDup (map snd hj) ->
  List.NoDup (rig_slots (combine es hj)) /\ (forall s, In s (rig_slots (combine es hj)) -> In s (map snd hj)).
Proof.
  unfold rig_slots. induction es as [|e es IH]; intros [|p hj] Hnd; cbn [combine map concat];
    try (split; [constructor | intros s []]).
  cbn [map] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hp Hnd].
  destruct (IH hj Hnd) as (ND & Inc). cbn [fst snd].
  destruct (re_eof e =? 0); cbn [app].
  - split.
    + constructor; [|exact ND]. intros Hin. exact (Hp (Inc _ Hin)).
    + intros s [<- | Hs]; [left; reflexivity | right; exact (Inc s Hs)].
  - split; [exact ND|]. intros s Hs. right. exact (Inc s Hs).
Qed.
(* relay_source's scan: the index it returns is an entry of fd *)
Lemma rg_find_spec : forall es fd i j, gn_find es fd i = Some j ->
  (i <= j)%nat /\ (j - i < length es)%nat /\ re_fd (nth (j - i) es gn_e0) = fd.
Proof.
  induction es as [|e es IH]; intros fd i j H; cbn [gn_find] in H; [discriminate H|].
  destruct (re_fd e =? fd) eqn:E.
  - injection H as <-. rewrite Nat.sub_diag. cbn [nth length].
    split; [lia|]. split; [lia | apply Z.eqb_eq; exact E].
  - destruct (IH fd (S i) j H) as (H1 & H2 & H3).
    replace (j - i)%nat with (S (j - S i)) by lia. cbn [nth length].
    split; [lia|]. split; [lia | exact H3].
Qed.
(* rig_rel leaves every open entry's source drained: dr_rel's empty pending list and zero offset *)
Lemma rg_rel_drained : forall pre mx ps qs c O cap c2 O2 cap2,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  forall i, (i < length ps)%nat -> re_eof (fst (nth i ps (gn_e0, gn_hj0))) = 0 ->
  hl_recs (hs_pending (snd (nth i qs gn_q0))) = [] /\ hs_off (snd (nth i qs gn_q0)) = 0.
Proof.
  intros pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs c O cap c2 O2 cap2 HR i Hi Heof;
    [cbn in Hi; lia|].
  destruct qs as [|[e' h'] q]; [cbn in HR; contradiction|].
  cbn [rig_rel] in HR. destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & _ & Hrest).
  destruct i as [|i].
  - cbn [nth fst snd] in Heof |- *. revert Hd. destruct (re_eof e =? 0) eqn:Ee; intros Hd.
    + unfold dr_rel in Hd. cbv zeta in Hd.
      destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Ho & _).
      split; [exact Hp | exact Ho].
    + rewrite Heof in Ee. discriminate Ee.
  - cbn [nth length] in *.
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] end.
    exact (IH q c3 O3 cap3 c2 O2 cap2 Hrest i ltac:(lia) Heof).
Qed.

(* ================================================================== RI_gone_pairs *)
Lemma RI_gone_pairs_holds : GN_RI_pairs_obl.
Proof.
  intros cx t m (_ & HR & Hn & _).
  destruct HR as (_ & _ & _ & _ & hj & HF & HNDs & _ & _ & Hcn).
  exists hj.
  assert (Hlen : length hj = length (lm_es m)) by exact (eq_sym (Forall2_length HF)).
  split; [exact Hlen|]. split.
  - rewrite Forall_forall. intros q Hq Heof.
    pose proof (fr_combine_of_F2 _ _ _ _ _ HF q Hq) as HRq.
    pose proof (rg_sum_le _ (fun q => fr_pair_cost (fst q) (snd q)) (combine (lm_es m) hj) q
      (fun y _ => fr_pair_cost_nonneg (fst y) (snd y)) Hq) as Hle.
    change (fold_right Z.add 0 (map (fun q => fr_pair_cost (fst q) (snd q)) (combine (lm_es m) hj)))
      with (fr_cost (lm_es m) hj) in Hle.
    destruct q as [e [h s]]. cbn [fst snd] in *.
    unfold fr_pair_ok in HRq. cbv zeta in HRq. cbn [fst snd] in HRq.
    destruct HRq as (Hs4 & Hsn & Hfd & Hrd & _ & _ & _ & Hecap & _ & _ & _).
    destruct (Hrd Heof) as (Hsk & HU).
    pose proof (SlotInv.ecap_ok_lt _ Hecap) as Hec.
    pose proof (rg_nheld_le (re_keys e)) as Hkn.
    unfold fr_pair_cost in Hle. cbn [fst] in Hle.
    assert (Hu : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
      by (destruct (re_skip e =? 0); lia).
    unfold gn_pair_ok, re_nheld. cbn [fst snd].
    split; [exact Hs4|]. split; [exact Hsn|]. split; [exact Hfd|]. split; [exact Hsk|]. split; [exact HU|].
    split; [lia|]. split; [lia | lia].
  - apply NoDup_ListNoDup. apply rg_rig_slots_nodup. apply NoDup_ListNoDup. exact HNDs.
Qed.

(* ================================================================== RI_gone_read *)
(* integ bb9dae5d905 W_LLVMFuzzerTestOneInput_gone_base.v:444-453 gn_entry_model / gn_rig_ok, copied verbatim *)
Definition gn_entry_model (e : rentry) : Prop :=
  (re_eof e = 0 \/ re_eof e = 1) /\ (re_skip e = 0 \/ re_skip e = 1) /\
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
  re_nheld e < 2 ^ 26 /\ NoDup (map gestures_end_b_c.key_text (re_keys e)).
Definition gn_rig_ok (cx : lfcx) (m : lmod) (hs : list (hsrc * nat)) (qs : list (rentry * hsrc))
    (c2 : ctl) (O2 : list byte) (cap2 : Z) : Prop :=
  rig_rel (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) (lm_mx m) (lm_c m) (lm_O m) (lm_cap m)
    (combine (lm_es m) hs) qs c2 O2 cap2 /\
  length qs = length (lm_es m) /\
  Forall gn_entry_model (map fst qs) /\ NoDup (map re_fd (map fst qs)).
(* integ bb9dae5d905 W_LLVMFuzzerTestOneInput_gone_base.v:573-577 GN_RI_read, copied verbatim at RINV := fr_RINV *)
Definition GN_RI_read_d : Prop := forall cx t m hs qs c2 O2 cap2 out2 m1 k h,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  (k < 4)%nat -> gn_reads m k = 1 -> nth k (lm_hs m1) None = Some h ->
  hl_recs (hs_pending h) = [] /\ hs_off h = 0.

Lemma RI_gone_read_holds : GN_RI_read_d.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 k h HRI HP HA HO Hk Hrd Hh.
  unfold gn_reads in Hrd. destruct (nth k (lm_hs m) None) as [h0|] eqn:Eh0; [|discriminate Hrd].
  unfold gn_src in Hrd. destruct (gn_find (lm_es m) (hs_fd h0) 0) as [j|] eqn:Ej; [|discriminate Hrd].
  destruct (re_eof (nth j (lm_es m) gn_e0) =? 0) eqn:Eeof; [|discriminate Hrd]. apply Z.eqb_eq in Eeof.
  destruct (rg_find_spec _ _ _ _ Ej) as (_ & Hj & Hfd). rewrite Nat.sub_0_r in Hj, Hfd.
  destruct HP as (Hlen & HF & _).
  assert (Hjl : (j < length (combine (lm_es m) hs))%nat)
    by (rewrite length_combine, Hlen, Nat.min_id; exact Hj).
  assert (Hjc : In (nth j (lm_es m) gn_e0, nth j hs gn_hj0) (combine (lm_es m) hs)).
  { rewrite <- (combine_nth (lm_es m) hs j gn_e0 gn_hj0 (eq_sym Hlen)). apply nth_In. exact Hjl. }
  rewrite Forall_forall in HF. pose proof (HF _ Hjc) as HPj. cbv beta in HPj. cbn [fst snd] in HPj.
  destruct (HPj Eeof) as (Hs4 & Hsn & Hsfd & _).
  (* the entry's source sits at slot k: two open slots have distinct fds *)
  assert (Hsk : snd (nth j hs gn_hj0) = k).
  { destruct (Nat.eq_dec (snd (nth j hs gn_hj0)) k) as [E | Ne]; [exact E|]. exfalso.
    exact (RI_fds_holds cx t m _ _ _ _ HRI Hs4 Hk Ne Hsn Eh0 (eq_trans Hsfd Hfd)). }
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdr).
  specialize (Hdr j Hj Eeof). rewrite Hsk, Hh in Hdr. injection Hdr as ->.
  destruct HO as (Hrig & _).
  apply (rg_rel_drained _ _ _ _ _ _ _ _ _ _ Hrig j Hjl).
  rewrite (combine_nth (lm_es m) hs j gn_e0 gn_hj0 (eq_sym Hlen)). exact Eeof.
Qed.

(* ================================================================== satisfiability (VERIFY rule 10)
   One state meets every premise of RI_gone_read (and so the premise of RI_gone_pairs): the first head's model
   (ReplyRINV.v pro_m, where RI_pro_holds proves fr_RINV from the entry contract) with the controller connected,
   slot 0 open with nothing pending and its entry open; relay_instance_gone drains slot 0 (drain grows the fresh
   entry's buffer to 8192 and reads nothing), so the table becomes [rg_e1] and slot 0 keeps its source.  Any input
   with 0 <= c_n < 2 ^ 26 (the contract's 0 < n < 2 ^ 26) will do. *)
Definition rg_c0 : ctl := CTL 3 0 0 0 0.
Definition rg_h0 : hsrc := oa_new_src 100 0 [].
Definition rg_m0 : lmod := pro_m 0 0 [] rg_c0 [] 0 0.
Definition rg_e1 : rentry :=
  RE 100 0 0 (repeat (Z_to_bv 8 0) 4) 0 0 8192 0 0 (repeat (Z_to_bv 8 0) 4) [] [] [].
Definition rg_c2 : ctl := dr_ctl rg_c0 rg_h0 0.
Definition rg_m1 (cx : lfcx) : lmod :=
  LM (gn_kq cx rg_m0) (lm_hs rg_m0) (lm_G rg_m0) [rg_e1] rg_c2 [] (lm_mx rg_m0) 0 0 (lm_gn rg_m0) (lm_nfd rg_m0).

(* drain of the fresh entry with nothing pending *)
Lemma rg_dr_rel0 : dr_rel rg_c0 0 0 0 (ra_new 100) rg_h0 rg_e1 rg_h0 [].
Proof.
  unfold dr_rel. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor)
          | (intros y; split; intros []) | (intros _; reflexivity) ].
Qed.

Lemma RI_gone_read_sat : forall cx, 0 <= c_n cx < 2 ^ 26 ->
  fr_RINV cx 0 rg_m0 /\ gn_pairs rg_m0 [(rg_h0, 0%nat)] /\
  gn_after_rig cx rg_m0 [(rg_h0, 0%nat)] [(rg_e1, rg_h0)] rg_c2 [] 0 0 (rg_m1 cx) /\
  gn_rig_ok cx rg_m0 [(rg_h0, 0%nat)] [(rg_e1, rg_h0)] rg_c2 [] 0 /\
  (0 < 4)%nat /\ gn_reads rg_m0 0 = 1 /\ nth 0 (lm_hs (rg_m1 cx)) None = Some rg_h0.
Proof.
  intros cx Hn.
  split; [|split; [|split; [|split; [|split; [lia | split; reflexivity]]]]].
  - (* fr_RINV at the first head, as in RI_pro_holds *)
    split; [|split; [|split]].
    + unfold fr_count, rg_m0, pro_m, nopen, OPS_MAX. cbn. lia.
    + unfold fr_relay, rg_m0, pro_m. cbn [lm_hs lm_es lm_nfd lm_k].
      split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [constructor; [cbn; lia | constructor]|].
      split.
      { constructor; [|constructor]. unfold fr_entry_ok. cbn.
        split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
      exists [(rg_h0, 0%nat)].
      split.
      { constructor; [|constructor]. unfold fr_pair_ok, rg_h0. cbn.
        split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; reflexivity]|].
        split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
        split; [left; reflexivity|]. split; [lia|]. split; [unfold SlotInv.WRITE_MAX; lia | lia]. }
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split.
      { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
          first [discriminate Ho | reflexivity | lia]. }
      unfold fr_cost, fr_pair_cost. cbn. lia.
    + exact (proj2 Hn).
    + unfold fr_gone, rg_m0, pro_m, rg_c0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros H; [auto | discriminate H].
  - (* gn_pairs: the one open entry with slot 0's source *)
    unfold gn_pairs, rg_m0, pro_m. cbn [lm_es]. split; [reflexivity|]. split.
    + constructor; [|constructor]. intros _. unfold gn_pair_ok, rg_h0, oa_new_src. cbn [fst snd lm_hs nth].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; reflexivity|].
      unfold pending_stream, re_nheld. vm_compute. repeat match goal with |- _ /\ _ => split end; reflexivity.
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
  - (* gn_after_rig: the table is [rg_e1], slot 0 keeps its source *)
    unfold gn_after_rig, rg_m1.
    do 11 (split; [reflexivity|]). split.
    + intros j _ _. reflexivity.
    + intros [|i] Hi _; [reflexivity | cbn in Hi; lia].
  - (* gn_rig_ok: rig_rel is one drain (rg_dr_rel0) and no key ended *)
    unfold gn_rig_ok. split; [|split; [reflexivity | split]].
    + generalize (relay_instance_gone_b_c.instance_prefix (gn_id cx rg_m0)). intros pre.
      unfold rg_m0, pro_m. cbn [rig_rel combine lm_es lm_mx lm_c lm_O lm_cap].
      exists rg_e1, 0, []. cbv zeta. cbn [re_eof ra_new Z.eqb Pos.eqb].
      split; [exact rg_dr_rel0|]. split; [reflexivity|].
      vm_compute. split; [reflexivity | split; reflexivity].
    + constructor; [|constructor]. unfold gn_entry_model, rg_e1, re_nheld. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ (left; reflexivity) | reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
Qed.

(* ================================================================== FINDING: the OLD RI_gone_step and RI_gone_end
   (integ bb9dae5d905 gone_base.v:579-613) are false at the instance.  Machine-checked evidence, kept as the record;
   not proofs of the rows (a Theorem Labs lane restated both on a working branch a1a3591c77c with the callee
   posts' block relation as a premise).  Both old rows tie their post-state Sx to the pre-state S by
   `mo_le MT S Sx cst` alone (gone_base.v:583, :612), and the instance's meter is MT := ameter_triv, whose mo_le is
   True (Reusable/YCbp.v:17-18).  So Sx may be rg_big S (W8Add's big_state, its LS-FINDING.v
   ls_rules_collapse_at_triv), with blocks_bytes = LIVE_MAX + 1:
   - GN_RI_step concludes `cnl_room MMAX (blocks_bytes Sx) ...` (:597), whose first record asks
     blocks_bytes Sx + ... + len + 1 <= LIVE_MAX (W_contract.v cnl_room): false at every step whose slot holds an
     expected record (relay_instance_gone's dr_rel appends the drained lines to the expected list);
   - GN_RI_end concludes `LS cx (t + 1) mc lyx Sx` (:613): false for every LS that bounds the live bytes, as
     fr_LS3 does (ReplyLS3.v:143 fr_LS3_room on a working branch 793a73ec89e: blocks_bytes S + 2 ^ 31
     <= LIVE_MAX).  (lyx is free as well, for any MT: fr_LS3's Permutation (ablocks B lyx Sx) ..., ReplyLS3.v:125,
     reads lyx.)
   GN_RI_step_old / GN_RI_end_old are the old texts (bb9dae5d905 gone_base.v:579-605, :608-613), copied verbatim
   with their Section parameters (MT, LS, RINV, MMAX) as arguments.  gn_run here is ReplyRINV.v's copy, an inductive
   distinct from gone_base's, which the two proofs only pass through. *)
Section collapse.

Definition GN_RI_step_old (MT : ameter_ops) (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (RINV : lfcx -> Z -> lmod -> Prop) (MMAX : Z) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (Sx : astate) cst,
  RINV cx t m -> LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) /\
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)) /\
  (forall h' E' H' (Sy : astate) cst', gn_cnl_ok h h' E' H' -> mo_le MT Sx Sy cst' ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None) /\
     mo_ok MT Sy (hl_n (hs_held h') * mo_free MT)).
Definition GN_RI_end_old (MT : ameter_ops) (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (RINV : lfcx -> Z -> lmod -> Prop) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  RINV cx t m -> LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  A = Z.of_nat (length (lm_O mc)) /\ RINV cx (t + 1) mc /\ LS cx (t + 1) mc lyx Sx.

(* a state with more live bytes than LIVE_MAX (LS-FINDING.v's big_state) *)
Definition rg_big (S : astate) : astate :=
  YG00.set_chunks [YG00.mkChunk YG00.PNull (LIVE_MAX + 1) YG00.CAllocated] S.
Lemma rg_big_bytes : forall S, blocks_bytes (rg_big S) = LIVE_MAX + 1.
Proof. intros S. unfold blocks_bytes, rg_big, YG00.set_chunks. cbn. lia. Qed.

(* RI_gone_step at MT := ameter_triv (any LS, any MMAX): its premises at a slot with an expected record imply False *)
Lemma GN_RI_step_collapse_triv : forall LS MMAX, GN_RI_step_old ameter_triv LS fr_RINV MMAX ->
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h,
  fr_RINV cx t m -> LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A i k ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  hl_recs (hs_expected h) <> [] -> False.
Proof.
  intros LS MMAX HST cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hne.
  destruct (HST cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (rg_big S) 0 H1 H2 H3 H4 H5 H6 I H7 H8 H9 H10)
    as (_ & _ & _ & _ & _ & _ & _ & Hroom & _).
  destruct (hl_recs (hs_expected h)) as [|r rs]; [exact (Hne eq_refl)|].
  cbn [cnl_room] in Hroom. destruct Hroom as (_ & Hb & _). rewrite rg_big_bytes in Hb.
  revert Hb. unfold grow_cap.
  destruct (Z.eqb_spec (Z.of_nat (length (texts (hs_held h)))) (hl_cap (hs_held h))) as [Ec | Ec]; intros Hb.
  - destruct (hl_cap (hs_held h) =? 0); unfold AREC in Hb; lia.
  - lia.
Qed.

(* RI_gone_end at MT := ameter_triv, for any LS whose states have at most LIVE_MAX live bytes (fr_LS3 by
   fr_LS3_room): its premises imply False *)
Lemma GN_RI_end_collapse_triv : forall LS,
  (forall cx t m ly S, LS cx t m ly S -> blocks_bytes S <= LIVE_MAX) ->
  GN_RI_end_old ameter_triv LS fr_RINV ->
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> False.
Proof.
  intros LS Hroom HE cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A H1 H2 H3 H4 H5 H6.
  destruct (HE cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A ly (rg_big S) 0 H1 H2 H3 H4 H5 H6 I) as (_ & _ & HL).
  pose proof (Hroom _ _ _ _ _ HL) as Hb. rewrite rg_big_bytes in Hb. lia.
Qed.
End collapse.

(* ================================================================== FINDING, round 2: the restated rows of
   a working branch a1a3591c77c (the callee posts' block relation added after mo_le; GN_RI_step also
   takes lyx) are still false at RINV := fr_RINV: nothing in them pins the stream lm_O m, which fr_RINV does not read
   (ReplyRINV.v:219-226) and fr_LS3 does not read either.  The counter-instance below is concrete: the first head's
   kind of state with one byte x already in the stream, and slot 0's source holding the line "a" (bytes 97, 0).
   relay_instance_gone drains it, so the stream is x, 97, 0 and slot 0's expected list is ["a"]:
   - GN_RI_step at the first call (gn_run0, A = 0) asks skipn 0 [x; 97; 0] = [97; 0] ++ rest (x = 120 here; any x
     fails, as 97 <> 0);
   - GN_RI_end after the loop (check_no_loss reads the 2 bytes of "a", check_shape_ends none) asks A = 2 = 3.
   The two lemmas leave as hypotheses only LS at rg2_m0 and the block-relation premise at some lyx / Sx (fr_LS3 does
   not read lm_O, so it holds at rg2_m0 where it holds at the same state with an empty stream).  The fix, the arm's
   gn_op (op 5, lm_O m = [], t < OPS_MAX) as a premise, is in the rows proved below. *)
Section collapse2.

(* the round-2 texts (a1a3591c77c gone_base.v:583-622), verbatim, with their Section parameters as arguments *)
Definition GN_RI_step_r2 (B : asyms) (MT : ameter_ops) (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (RINV : lfcx -> Z -> lmod -> Prop) (MMAX : Z) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
  RINV cx t m -> LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) /\
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)) /\
  (forall h' E' H' (Sy : astate) cst', gn_cnl_ok h h' E' H' -> mo_le MT Sx Sy cst' ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None) /\
     mo_ok MT Sy (hl_n (hs_held h') * mo_free MT)).
Definition GN_RI_end_r2 (B : asyms) (MT : ameter_ops) (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (RINV : lfcx -> Z -> lmod -> Prop) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  RINV cx t m -> LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  A = Z.of_nat (length (lm_O mc)) /\ RINV cx (t + 1) mc /\ LS cx (t + 1) mc lyx Sx.

(* the counter-instance *)
Definition rg2_a : byte := Z_to_bv 8 97.
Definition rg2_x : byte := Z_to_bv 8 120.
Definition rg2_z : byte := Z_to_bv 8 0.
Definition rg2_h0 : hsrc := HS 100 1 0 0 (HL 0 8 [(0, [rg2_a; rg2_z])] []) 0 0 [] 0 0 [] empty_list empty_list.
Definition rg2_h1 : hsrc := HS 100 1 0 0 (HL 0 8 [] []) 0 0 [] 0 0 [] (HL 0 8 [(0, [rg2_a])] []) empty_list.
Definition rg2_m0 : lmod := LM 2 [Some rg2_h0; None; None; None] 0 [ra_new 100] rg_c0 [rg2_x] 0 0 0 0 1.
Definition rg2_c2 : ctl := dr_ctl rg_c0 rg2_h0 0.
Definition rg2_O2 : list byte := [rg2_x; rg2_a; rg2_z].
Definition rg2_cap2 : Z := drain_b_c.ds_ocap (dr_fin rg_c0 0 1 0 (ra_new 100) rg2_h0).
Definition rg2_m1 (cx : lfcx) : lmod :=
  LM (gn_kq cx rg2_m0) [Some rg2_h1; None; None; None] 0 [rg_e1] rg2_c2 rg2_O2 0 rg2_cap2 0 0 1.
Definition rg2_E : hlist := HL 0 8 [] [].
Definition rg2_h1' : hsrc := set_exp_held rg2_h1 rg2_E empty_list.
Definition rg2_h1'' : hsrc := set_held rg2_h1' empty_list.
Definition rg2_mc (cx : lfcx) : lmod := gn_set (rg2_m1 cx) 0 rg2_h1''.

(* drain of the entry with the line "a" pending *)
Lemma rg2_dr_rel : dr_rel rg_c0 0 1 0 (ra_new 100) rg2_h0 rg_e1 rg2_h1 [rg2_a; rg2_z].
Proof.
  unfold dr_rel. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor)
          | (intros y; split; intros []) | (intros _; reflexivity) ].
Qed.

(* the premises the two rows share, at the counter-instance *)
Lemma rg2_premises : forall cx, 2 <= c_n cx < 2 ^ 26 ->
  fr_RINV cx 1 rg2_m0 /\ gn_pairs rg2_m0 [(rg2_h0, 0%nat)] /\
  gn_after_rig cx rg2_m0 [(rg2_h0, 0%nat)] [(rg_e1, rg2_h1)] rg2_c2 rg2_O2 rg2_cap2 0 (rg2_m1 cx) /\
  gn_rig_ok cx rg2_m0 [(rg2_h0, 0%nat)] [(rg_e1, rg2_h1)] rg2_c2 rg2_O2 rg2_cap2.
Proof.
  intros cx Hn. split; [|split; [|split]].
  - split; [|split; [|split]].
    + unfold fr_count, rg2_m0, nopen, OPS_MAX. cbn. lia.
    + unfold fr_relay, rg2_m0. cbn [lm_hs lm_es lm_nfd lm_k].
      split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [constructor; [cbn; lia | constructor]|].
      split.
      { constructor; [|constructor]. unfold fr_entry_ok. cbn.
        split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
      exists [(rg2_h0, 0%nat)].
      split.
      { constructor; [|constructor]. unfold fr_pair_ok, rg2_h0. cbn.
        split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; reflexivity]|].
        split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
        split; [left; reflexivity|]. split; [lia|].
        split; [vm_compute; intros Hx; discriminate Hx | vm_compute; intros Hx; discriminate Hx]. }
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split.
      { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
          first [discriminate Ho | reflexivity | lia]. }
      assert (Ec : fr_cost [ra_new 100] [(rg2_h0, 0%nat)] = 2) by (vm_compute; reflexivity).
      rewrite Ec. lia.
    + exact (proj2 Hn).
    + unfold fr_gone, rg2_m0, rg_c0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros H; [auto | discriminate H].
  - unfold gn_pairs, rg2_m0. cbn [lm_es]. split; [reflexivity|]. split.
    + constructor; [|constructor]. intros _. unfold gn_pair_ok, rg2_h0. cbn [fst snd lm_hs nth].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; reflexivity|].
      unfold pending_stream, re_nheld. vm_compute. repeat match goal with |- _ /\ _ => split end; reflexivity.
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
  - unfold gn_after_rig, rg2_m1.
    do 11 (split; [reflexivity|]). split.
    + intros j _ Hj. destruct j as [|j]; [exfalso; apply Hj; cbn; left; reflexivity | reflexivity].
    + intros [|i] Hi _; [reflexivity | cbn [lm_es rg2_m0 length] in Hi; lia].
  - unfold gn_rig_ok. split; [|split; [reflexivity | split]].
    + generalize (relay_instance_gone_b_c.instance_prefix (gn_id cx rg2_m0)). intros pre.
      unfold rg2_m0. cbn [rig_rel combine lm_es lm_mx lm_c lm_O lm_cap].
      exists rg_e1, 0, [rg2_a; rg2_z]. cbv zeta. cbn [re_eof ra_new Z.eqb Pos.eqb].
      split; [exact rg2_dr_rel|]. split; [reflexivity|].
      vm_compute. split; [reflexivity | split; reflexivity].
    + constructor; [|constructor]. unfold gn_entry_model, rg_e1, re_nheld. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ (left; reflexivity) | reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
Qed.

(* the loop over the one entry: check_no_loss reads "a" (2 bytes), check_shape_ends ends nothing, three slots
   passed *)
Lemma rg2_run : forall cx, gn_run (gn_pre cx rg2_m0) (rg2_m1 cx) (rg2_mc cx) 2 (length (lm_es (rg2_m1 cx))) 0%nat.
Proof.
  intros cx. change (length (lm_es (rg2_m1 cx))) with 1%nat. apply gn_run_next.
  apply gn_run_skip; [|lia | left; reflexivity].
  apply gn_run_skip; [|lia | left; reflexivity].
  apply gn_run_skip; [|lia | left; reflexivity].
  unfold rg2_mc.
  refine (gn_run_call _ _ (rg2_m1 cx) 0 0%nat 0%nat rg2_h1 rg2_h1' rg2_h1'' rg2_E empty_list [] 0
    (gn_run0 _ _) ltac:(lia) (Nat.lt_0_succ 0) eq_refl eq_refl _ _).
  - unfold gn_cnl_ok. vm_compute.
    repeat match goal with |- _ /\ _ => split end;
      first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
  - unfold gn_cshe_ok. exists empty_list.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply NoDup_ListNoDup; constructor|]. split; [lia|].
    right. split; reflexivity.
Qed.

Lemma GN_RI_step_r2_counter : forall B MT LS MMAX cx ly S lyx Sx cst,
  2 <= c_n cx < 2 ^ 26 -> LS cx 1 rg2_m0 ly S -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks rg2_m0 ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks (rg2_m1 cx) ++ rest)) ->
  GN_RI_step_r2 B MT LS fr_RINV MMAX -> False.
Proof.
  intros B MT LS MMAX cx ly S lyx Sx cst Hn HLS Hle HP HST.
  destruct (rg2_premises cx Hn) as (HRI & HPR & HAR & HOK).
  destruct (HST cx 1 rg2_m0 ly S [(rg2_h0, 0%nat)] [(rg_e1, rg2_h1)] rg2_c2 rg2_O2 rg2_cap2 0 (rg2_m1 cx)
    (rg2_m1 cx) 0 0%nat 0%nat rg2_h1 lyx Sx cst HRI HLS HPR HAR HOK (gn_run0 _ _) Hle HP (Nat.lt_0_succ 0)
    ltac:(lia) eq_refl eq_refl) as (_ & _ & _ & _ & _ & Hf & _).
  destruct (Hf eq_refl) as (rest & E).
  apply (f_equal (fun l => bv_unsigned (nth 0 l (Z_to_bv 8 0)))) in E. vm_compute in E. discriminate E.
Qed.

Lemma GN_RI_end_r2_counter : forall B MT LS cx ly S lyx Sx cst,
  2 <= c_n cx < 2 ^ 26 -> LS cx 1 rg2_m0 ly S -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks rg2_m0 ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks (rg2_mc cx) ++ rest)) ->
  GN_RI_end_r2 B MT LS fr_RINV -> False.
Proof.
  intros B MT LS cx ly S lyx Sx cst Hn HLS Hle HP HE.
  destruct (rg2_premises cx Hn) as (HRI & HPR & HAR & HOK).
  destruct (HE cx 1 rg2_m0 ly S [(rg2_h0, 0%nat)] [(rg_e1, rg2_h1)] rg2_c2 rg2_O2 rg2_cap2 0 (rg2_m1 cx)
    (rg2_mc cx) 2 lyx Sx cst HRI HLS HPR HAR HOK (rg2_run cx) Hle HP) as (HA & _ & _).
  vm_compute in HA. discriminate HA.
Qed.
End collapse2.
End rg.

(* ================================================================== the OLD RI_gone_end (bb9dae5d905) is vacuous
   at the top's instance: a concrete state meets all its premises (the first head of a Theorem Labs lane's fr_LS3_sat,
   ReplyLS3.v:464-505: one relay entry, slot 0 open, nothing pending, nothing read), so GN_RI_end_collapse_triv's
   general statement (ANY LS whose states have at most LIVE_MAX live bytes, at MT := ameter_triv) closes it at
   LS := fr_LS3 B, RINV := fr_RINV. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLS ReplyLS3.
Section close.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Notation cq := (ReplyLS3.ls3_q B).
Local Notation cG := (ReplyLS3.ls3_G B).
Definition rgc_h0 : hsrc := oa_new_src 100 cq [].
Definition rgc_m0 : lmod := pro_m cq cG [] rg_c0 [] 0 0.
Definition rgc_c2 : ctl := dr_ctl rg_c0 rgc_h0 0.
Definition rgc_m1 (cx : lfcx) : lmod :=
  LM (gn_kq cx rgc_m0) (lm_hs rgc_m0) (lm_G rgc_m0) [rg_e1] rgc_c2 [] (lm_mx rgc_m0) 0 0 (lm_gn rgc_m0) (lm_nfd rgc_m0).
Definition rgc_h0' : hsrc := set_exp_held rgc_h0 (hs_expected rgc_h0) (hs_held rgc_h0).
Definition rgc_h0'' : hsrc := set_held rgc_h0' (hs_held rgc_h0').
Definition rgc_mc (cx : lfcx) : lmod := gn_set (rgc_m1 cx) 0 rgc_h0''.

Lemma rgc_dr_rel : dr_rel rg_c0 0 0 0 (ra_new 100) rgc_h0 rg_e1 rgc_h0 [].
Proof.
  unfold dr_rel. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor)
          | (intros y; split; intros []) | (intros _; reflexivity) ].
Qed.

Lemma rgc_premises : forall cx, 0 <= c_n cx < 2 ^ 26 ->
  fr_RINV cx 0 rgc_m0 /\ gn_pairs rgc_m0 [(rgc_h0, 0%nat)] /\
  gn_after_rig cx rgc_m0 [(rgc_h0, 0%nat)] [(rg_e1, rgc_h0)] rgc_c2 [] 0 0 (rgc_m1 cx) /\
  gn_rig_ok cx rgc_m0 [(rgc_h0, 0%nat)] [(rg_e1, rgc_h0)] rgc_c2 [] 0 /\
  gn_run (gn_pre cx rgc_m0) (rgc_m1 cx) (rgc_mc cx) 0 (length (lm_es (rgc_m1 cx))) 0%nat.
Proof.
  intros cx Hn.
  split; [|split; [|split; [|split]]].
  - split; [|split; [|split]].
    + unfold fr_count, rgc_m0, pro_m, nopen, OPS_MAX. cbn. lia.
    + unfold fr_relay, rgc_m0, pro_m. cbn [lm_hs lm_es lm_nfd lm_k].
      split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [constructor; [cbn; lia | constructor]|].
      split.
      { constructor; [|constructor]. unfold fr_entry_ok. cbn.
        split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
      exists [(rgc_h0, 0%nat)].
      split.
      { constructor; [|constructor]. unfold fr_pair_ok, rgc_h0. cbn.
        split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; reflexivity]|].
        split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
        split; [left; reflexivity|]. split; [lia|]. split; [unfold SlotInv.WRITE_MAX; lia | lia]. }
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split.
      { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
          first [discriminate Ho | reflexivity | lia]. }
      unfold fr_cost, fr_pair_cost. cbn. lia.
    + exact (proj2 Hn).
    + unfold fr_gone, rgc_m0, pro_m, rg_c0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros H; [auto | discriminate H].
  - unfold gn_pairs, rgc_m0, pro_m. cbn [lm_es]. split; [reflexivity|]. split.
    + constructor; [|constructor]. intros _. unfold gn_pair_ok, rgc_h0, oa_new_src. cbn [fst snd lm_hs nth].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; reflexivity|].
      unfold pending_stream, re_nheld. vm_compute. repeat match goal with |- _ /\ _ => split end; reflexivity.
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
  - unfold gn_after_rig, rgc_m1.
    do 11 (split; [reflexivity|]). split.
    + intros j _ _. reflexivity.
    + intros [|i] Hi _; [reflexivity | cbn in Hi; lia].
  - unfold gn_rig_ok. split; [|split; [reflexivity | split]].
    + generalize (relay_instance_gone_b_c.instance_prefix (gn_id cx rgc_m0)). intros pre.
      unfold rgc_m0, pro_m. cbn [rig_rel combine lm_es lm_mx lm_c lm_O lm_cap].
      exists rg_e1, 0, []. cbv zeta. cbn [re_eof ra_new Z.eqb Pos.eqb].
      split; [exact rgc_dr_rel|]. split; [reflexivity|].
      vm_compute. split; [reflexivity | split; reflexivity].
    + constructor; [|constructor]. unfold gn_entry_model, rg_e1, re_nheld. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ (left; reflexivity) | reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
  - change (length (lm_es (rgc_m1 cx))) with 1%nat. apply gn_run_next.
    apply gn_run_skip; [|lia | left; reflexivity].
    apply gn_run_skip; [|lia | left; reflexivity].
    apply gn_run_skip; [|lia | left; reflexivity].
    unfold rgc_mc.
    refine (gn_run_call _ _ (rgc_m1 cx) 0 0%nat 0%nat rgc_h0 rgc_h0' rgc_h0'' (hs_expected rgc_h0) (hs_held rgc_h0)
      [] 0 (gn_run0 _ _) ltac:(lia) (Nat.lt_0_succ 0) eq_refl eq_refl _ _).
    + unfold gn_cnl_ok. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    + unfold gn_cshe_ok. exists (hs_held rgc_h0').
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; constructor|]. split; [lia|].
      right. split; reflexivity.
Qed.

(* fr_LS3 at the same state: ReplyLS3.v's fr_LS3_sat witness (its proof, at its named state) *)
Lemma rgc_LS3 : ReplyLS3.fr_LS3 B (ReplyLS3.ls3_cx B) 0 rgc_m0 ReplyLS3.ls3_ly ReplyLS3.ls3_S.
Proof.
  exists [], 0.
  assert (EA : ablocks B ReplyLS3.ls3_ly ReplyLS3.ls3_S =
    input_blks (ReplyLS3.ls3_cx B) ++ model_blks rgc_m0 ++ []) by reflexivity.
  assert (Hbb : blocks_bytes ReplyLS3.ls3_S = 1 + ATABLE + APARTIAL) by (vm_compute; reflexivity).
  assert (Hin : bsum (input_blks (ReplyLS3.ls3_cx B)) = 1) by reflexivity.
  assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
  assert (HS : c_S (ReplyLS3.ls3_cx B) = ReplyLS3.ls3_S) by reflexivity.
  assert (Hn : c_n (ReplyLS3.ls3_cx B) = 1) by reflexivity.
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  assert (En : ReplyLS.npend rgc_m0 = 0) by reflexivity.
  assert (Ek : ReplyLS.kk (ReplyLS3.ls3_cx B) rgc_m0 = 0) by reflexivity.
  assert (Eo : nopen (lm_hs rgc_m0) = 1) by reflexivity.
  assert (Ep : ReplyLS3.PHI3 rgc_m0 = ATABLE + APARTIAL + ReplyLS3.E_ENT + ReplyLS3.K0) by reflexivity.
  rewrite EA, HS, Hbb, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
  split; [apply Permutation_refl|].
  unfold ReplyLS3.W_OPEN, ReplyLS.MB_K, ReplyLS.MB_C, ATABLE, APARTIAL, ReplyLS3.E_ENT, ReplyLS3.K0.
  refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
Qed.

(* the corollary at the top's instance: the OLD GN_RI_end at MT := ameter_triv, LS := fr_LS3 B, RINV := fr_RINV is
   false (not merely unusable) *)
Lemma GN_RI_end_old_false : ~ GN_RI_end_old ameter_triv (ReplyLS3.fr_LS3 B) fr_RINV.
Proof.
  intros HE.
  assert (Room : forall cx t m ly S, ReplyLS3.fr_LS3 B cx t m ly S -> blocks_bytes S <= LIVE_MAX).
  { intros cx t m ly S HL. pose proof (ReplyLS3.fr_LS3_room B cx t m ly S HL). unfold ReplyLS.ROOM_SPARE in *. lia. }
  destruct (rgc_premises (ReplyLS3.ls3_cx B) ltac:(cbn; lia)) as (H1 & H2 & H3 & H4 & H5).
  exact (GN_RI_end_collapse_triv (ReplyLS3.fr_LS3 B) Room HE (ReplyLS3.ls3_cx B) 0 rgc_m0 ReplyLS3.ls3_ly
    ReplyLS3.ls3_S _ _ _ _ _ _ _ _ _ H1 rgc_LS3 H2 H3 H4 H5).
Qed.
End close.

(* ================================================================== part 2: over lib/A/W_LLVMFuzzerTestOneInput_gone_base.v's model *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotReads SlotPass5Check.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotReads SlotPass4C.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotReads SlotDrain3 SlotPass2Aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotReads SlotPass2Aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
  ReplyLS3 ReplyLS3c ReplyLS3cTopxGoneF ReplyLS3cTopxGone8 W_LLVMFuzzerTestOneInput_write CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.

(* part 1's rows at gone_base's own texts (its gn_* are part 1's copies, verbatim) *)
Section plug1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma RI_gone_pairs_plug : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_pairs fr_RINV.
Proof. exact RI_gone_pairs_holds. Qed.
Lemma RI_gone_read_plug : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_read fr_RINV.
Proof. exact RI_gone_read_holds. Qed.
End plug1.

(* ---------------------------------------------------------------- (from scratch D1) *)

(* Removing the record at index i from rs, put back in front, is a permutation of rs. *)
Lemma rg_perm_drop : forall (rs : list (Z * list byte)) i, (i < length rs)%nat ->
  Permutation rs (nth i rs (0, []) :: drop_nth i rs).
Proof.
  intros rs i Hi. unfold drop_nth.
  pose proof (SlotReads.split_at rs i (0, []) Hi) as E.
  apply Permutation_sym. eapply Permutation_trans; [apply Permutation_middle|].
  rewrite <- E. apply Permutation_refl.
Qed.

(* ends_run on a stream of end lines for exactly the prefixed records: its count, the records it drops,
   and the records it keeps. *)
Lemma rg_ends_res : forall (P : list byte) (E : list (list Z)) (rs : list (Z * list byte)) (d : list byte) (z : list Z)
    rs' ds c,
  NoDup E -> NoDup (SlotReads.rtexts rs) ->
  (forall y, In y E <-> In y (SlotReads.rtexts rs) /\ has_prefix (bzs P) y = true) ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs ->
  bzs d = concat (map (fun x => x ++ relay_instance_gone_b_c.END5Z) E) ++ z ->
  ends_run P rs d (want_of P rs) = Some (rs', ds, c) ->
  c = Z.of_nat (length (concat (map (fun x => x ++ relay_instance_gone_b_c.END5Z) E))) /\
  Permutation rs (ds ++ rs') /\
  (forall y, In y (SlotReads.rtexts rs') <-> In y (SlotReads.rtexts rs) /\ has_prefix (bzs P) y = false) /\
  NoDup (SlotReads.rtexts rs') /\ Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs'.
Proof.
  intros P E. induction E as [|x E IH]; intros rs d z rs' ds c NE NR HS NZ HD ER.
  - assert (W : want_of P rs = 0%nat).
    { apply SlotPass5Check.g5_want_zero. intros r Hr. destruct (prefixb P (snd r)) eqn:Pr; [|reflexivity]. exfalso.
      apply (proj2 (HS (bzs (snd r)))). split; [|rewrite <- SlotPass5Check.g5_prefixb; exact Pr].
      unfold SlotReads.rtexts. apply (in_map (fun r => bzs (snd r))). exact Hr. }
    rewrite W in ER. cbn [ends_run] in ER. injection ER as <- <- <-.
    split; [reflexivity|]. split; [apply Permutation_refl|]. split; [|split; assumption].
    intros y. split; [|intros [Hy _]; exact Hy].
    intros Hy. split; [exact Hy|]. destruct (has_prefix (bzs P) y) eqn:Hp; [|reflexivity].
    exfalso. exact (proj2 (HS y) (conj Hy Hp)).
  - apply NoDup_ListNoDup in NE. inversion NE as [|? ? NX NE']; subst. apply NoDup_ListNoDup in NE'.
    destruct (proj1 (HS x) (or_introl eq_refl)) as [Ix Px].
    destruct (In_nth (SlotReads.rtexts rs) x [] Ix) as (i0 & Li0 & Ni0).
    assert (Li0' : (i0 < length rs)%nat)
      by (unfold SlotReads.rtexts in Li0; rewrite length_map in Li0; exact Li0).
    rewrite (SlotReads.nth_rtexts rs i0 Li0') in Ni0.
    set (xb := snd (nth i0 rs (0, []))) in *.
    assert (Ixb : In (bzs xb) (SlotReads.rtexts rs)) by (rewrite Ni0; exact Ix).
    destruct (SlotReads.find_text_some xb rs Ixb) as (i & F & Li & Ni).
    assert (NZx : ~ In (Z_to_bv 8 0) xb).
    { rewrite Forall_forall in NZ. apply NZ. apply nth_In. exact Li0'. }
    assert (Pxb : prefixb P xb = true) by (rewrite SlotPass5Check.g5_prefixb, Ni0; exact Px).
    assert (Pi : prefixb P (snd (nth i rs (0, []))) = true)
      by (rewrite SlotPass5Check.g5_prefixb, Ni; rewrite <- SlotPass5Check.g5_prefixb; exact Pxb).
    assert (HD' : bzs d = bzs ((xb ++ END4) ++ [Z_to_bv 8 0]) ++
                            (concat (map (fun x => x ++ relay_instance_gone_b_c.END5Z) E) ++ z)).
    { rewrite HD. cbn [map concat].
      rewrite !SlotReads.bzs_app, SlotPass5Check.g5_end4_bzs, SlotReads.bzs_zero, Ni0.
      unfold relay_instance_gone_b_c.END5Z. rewrite <- !app_assoc. reflexivity. }
    destruct (SlotPass5Check.g5_bzs_split _ _ _ HD') as (d' & -> & HD2).
    rewrite <- (app_assoc (xb ++ END4) [Z_to_bv 8 0] d') in ER. cbn [app] in ER.
    rewrite (SlotPass5Check.g5_want_drop P rs i Li), Pi in ER. cbn [Nat.add ends_run] in ER.
    assert (NZX : ~ In (Z_to_bv 8 0) (xb ++ END4)).
    { rewrite in_app_iff. intros [X | X]; [exact (NZx X) | exact (SlotPass5Check.g5_end4_nz X)]. }
    rewrite (SlotReads.split_nul_app _ _ NZX) in ER. cbv beta iota zeta in ER.
    destruct (SlotPass5Check.g5_end_ok P xb Pxb) as [C1 C2]. rewrite C1, C2, F in ER. cbv beta iota zeta in ER.
    destruct (ends_run P (drop_nth i rs) d' (want_of P (drop_nth i rs))) as [[[rs1 ds1] c1]|] eqn:ER1;
      [|discriminate].
    injection ER as <- <- <-.
    assert (LRi : (i < length (SlotReads.rtexts rs))%nat)
      by (unfold SlotReads.rtexts; rewrite length_map; exact Li).
    assert (NT : nth i (SlotReads.rtexts rs) [] = x) by (rewrite (SlotReads.nth_rtexts rs i Li), Ni; exact Ni0).
    assert (NR' : NoDup (SlotReads.rtexts (drop_nth i rs))).
    { apply NoDup_ListNoDup. rewrite SlotReads.rtexts_drop. pose proof (proj1 (NoDup_ListNoDup _) NR) as NR0.
      rewrite (SlotReads.split_at (SlotReads.rtexts rs) i [] LRi) in NR0. apply NoDup_remove_1 in NR0. exact NR0. }
    assert (HS' : forall y, In y E <-> In y (SlotReads.rtexts (drop_nth i rs)) /\ has_prefix (bzs P) y = true).
    { intros y. rewrite SlotReads.rtexts_drop, (SlotReads.in_drop_split (SlotReads.rtexts rs) i [] y NR LRi), NT.
      split.
      - intros HY. destruct (proj1 (HS y) (or_intror HY)) as [H1 H2].
        split; [split; [exact H1|] | exact H2]. intros ->. exact (NX HY).
      - intros [[H1 H2] H3]. destruct (proj2 (HS y) (conj H1 H3)) as [HY | HY]; [congruence | exact HY]. }
    assert (NZ' : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (drop_nth i rs)).
    { rewrite (SlotReads.split_at rs i (0, []) Li) in NZ. apply Forall_app in NZ. destruct NZ as [N1 N2].
      inversion N2 as [|? ? _ N3]; subst. unfold drop_nth. apply Forall_app. split; assumption. }
    destruct (IH (drop_nth i rs) d' z rs1 ds1 c1 NE' NR' HS' NZ' HD2 ER1) as (Hc & Hp & Hy & Hn & Hf).
    split; [|split; [|split; [|split]]].
    + rewrite Hc. cbn [map concat]. rewrite !length_app. unfold relay_instance_gone_b_c.END5Z.
      change (length END4) with 4%nat.
      assert (LX : length xb = length x) by (rewrite <- Ni0, SlotReads.bzs_length; reflexivity).
      cbn [length]. rewrite LX. lia.
    + apply (Permutation_trans (rg_perm_drop rs i Li)). cbn [app]. apply perm_skip. exact Hp.
    + intros y. rewrite Hy, SlotReads.rtexts_drop, (SlotReads.in_drop_split (SlotReads.rtexts rs) i [] y NR LRi), NT.
      split.
      * intros [[H1 _] H3]. split; assumption.
      * intros [H1 H3]. split; [split; [exact H1|] | exact H3]. intros ->. rewrite Px in H3. discriminate.
    + exact Hn.
    + exact Hf.
Qed.

(* ---------------------------------------------------------------- (from scratch D2) *)

(* a pair of the zipped lists stays a pair after mapping the first list *)
Lemma rg_in_combine_map : forall (A B C : Type) (f : A -> C) (l : list A) (l' : list B) a b,
  In (a, b) (combine l l') -> In (f a, b) (combine (map f l) l').
Proof.
  intros A B C f l. induction l as [|x l IH]; intros [|y l'] a b H; cbn [combine map In] in *; try contradiction.
  destruct H as [E | H]; [injection E as <- <-; left; reflexivity | right; exact (IH l' a b H)].
Qed.

(* fr_cost is SlotInv's slot_cost of the entries with re_used := length re_U *)
Lemma rg_cost_ru : forall es hj, fr_cost es hj = SlotInv.slot_cost (map fr_ru es) hj.
Proof.
  induction es as [|e es IH]; intros [|p hj]; try reflexivity.
  unfold fr_cost, SlotInv.slot_cost in *. cbn [combine map fold_right fst snd]. rewrite IH. reflexivity.
Qed.

Lemma rg_counts : forall (es : list rentry) (hj : list (hsrc * nat)) (e : rentry) (h : hsrc) (s : nat)
    (L : list (list Z)) k,
  In (e, (h, s)) (combine es hj) -> fr_cost es hj <= k -> k < 2 ^ 26 ->
  Forall (fun x => 14 <= Z.of_nat (length (gestures_end_b_c.key_text x))) (re_keys e) ->
  same_set (drain_b_c.keys_texts (re_keys e)) (texts (hs_held h)) -> NoDup (texts (hs_held h)) ->
  NoDup (drain_b_c.keys_texts (re_keys e)) ->
  Z.of_nat (length (with_nul L)) <=
    (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0) + Z.of_nat (length (pending_stream h)) ->
  hl_n (hs_held h) + Z.of_nat (count_begin L) < 2 ^ 22 /\ Z.of_nat (length L) < 2 ^ 26.
Proof.
  intros es hj e h s L k Hin Hc Hk KL SS ND _ WB.
  apply (SlotPass4C.p4_cnl_bound (fr_ru e) h s (hs_held h) L (map fr_ru es) hj k).
  - exact (rg_in_combine_map _ _ _ fr_ru es hj e (h, s) Hin).
  - apply Forall_map, Forall_forall. intros x _. unfold fr_ru. cbn [re_used]. lia.
  - rewrite <- rg_cost_ru. exact Hc.
  - exact Hk.
  - exact KL.
  - exact (SlotPass4C.p4_held_len (re_keys e) (hs_held h) ND SS).
  - exact WB.
Qed.

Lemma rg_counts_drain : forall (es : list rentry) (hj : list (hsrc * nat)) (e : rentry) (h : hsrc) (s : nat) k,
  In (e, (h, s)) (combine es hj) -> fr_cost es hj <= k -> k < 2 ^ 26 ->
  Forall (fun x => 14 <= Z.of_nat (length (gestures_end_b_c.key_text x))) (re_keys e) ->
  same_set (drain_b_c.keys_texts (re_keys e)) (texts (hs_held h)) -> NoDup (texts (hs_held h)) ->
  NoDup (drain_b_c.keys_texts (re_keys e)) ->
  re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (hs_overlong h = 0 \/ hs_overlong h = 1) ->
  hl_n (hs_held h) + Z.of_nat (count_begin (dr_lines h)) < 2 ^ 22 /\ Z.of_nat (length (dr_lines h)) < 2 ^ 26.
Proof.
  intros es hj e h s k Hin Hc Hk KL SS ND NDk E1 E2 Ho.
  apply (rg_counts es hj e h s (dr_lines h) k Hin Hc Hk KL SS ND NDk).
  unfold dr_lines.
  exact (SlotReads.reads_bound (fr_ru e) h E1 E2 Ho eq_refl).
Qed.

(* ---------------------------------------------------------------- (from scratch D3) *)

Definition rg_kok (k : Z * list byte * list byte) : Prop :=
  ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\ 14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL.

(* ---------------------------------------------------------------- 1. the reference splitter keeps 0 bytes out *)

Lemma rg_step_nz : forall st b, RelayModel.nozero (RelayModel.ls_w st) ->
  RelayModel.nozero (RelayModel.ls_w (fst (RelayModel.step st b))) /\
  (forall l, snd (RelayModel.step st b) = Some l -> RelayModel.nozero l).
Proof.
  intros st b Hw. unfold RelayModel.step. destruct (Z.eqb_spec b 0) as [Hb|Hb].
  - cbn [fst snd RelayModel.ls_w]. split; [apply Forall_nil|]. intros l E.
    destruct (RelayModel.ls_k st); [discriminate E|]. injection E as <-. exact Hw.
  - destruct (RelayModel.ls_k st).
    + cbn [fst snd]. split; [exact Hw|]. intros l E; discriminate E.
    + destruct (Nat.eqb (length (RelayModel.ls_w st)) RelayModel.LINE_LIMIT).
      * cbn [fst snd RelayModel.ls_w]. split; [exact Hw|]. intros l E; discriminate E.
      * cbn [fst snd RelayModel.ls_w]. split; [|intros l E; discriminate E].
        unfold RelayModel.nozero in *. apply Forall_app. split; [exact Hw|].
        apply Forall_cons; [exact Hb|apply Forall_nil].
Qed.

(* 1. the reference splitter's lines and partial line carry no 0 byte when its start state's partial line has none *)
Lemma rg_lines_nz : forall d st, RelayModel.nozero (RelayModel.ls_w st) ->
  Forall RelayModel.nozero (RelayModel.lines st d) /\ RelayModel.nozero (RelayModel.ls_w (RelayModel.feed st d)).
Proof.
  induction d as [|b d IH]; intros st Hw.
  - rewrite RelayModel.lines_nil, RelayModel.feed_nil. split; [apply Forall_nil|exact Hw].
  - rewrite RelayModel.lines_cons, RelayModel.feed_cons.
    destruct (rg_step_nz st b Hw) as [S1 S2].
    destruct (IH (fst (RelayModel.step st b)) S1) as [I1 I2]. split; [|exact I2].
    revert S2. destruct (snd (RelayModel.step st b)) as [l|]; intros S2.
    + apply Forall_cons; [exact (S2 l eq_refl)|exact I1].
    + exact I1.
Qed.

(* ---------------------------------------------------------------- 2. drain keeps the key clause *)

(* the length clause of a held key's text *)
Definition rg_pc (y : list Z) : Prop := (14 <= length y <= RelayModel.LINE_LIMIT)%nat.

Lemma rg_lsf : forall l i j, RelayModel.last_space_from i l = Some j -> (i <= j < i + length l)%nat.
Proof.
  induction l as [|b l IH]; intros i j E; cbn [RelayModel.last_space_from] in E; [discriminate E|].
  destruct (RelayModel.last_space_from (S i) l) as [j'|] eqn:E'.
  - injection E as <-. apply IH in E'. cbn [length]. lia.
  - destruct (b =? RelayModel.SPACE); [injection E as <-; cbn [length]; lia|discriminate E].
Qed.

(* a gesture line's key is a prefix of the line, of 14 bytes or more, shorter than the line *)
Lemma rg_gesture : forall l k x, RelayModel.gesture l = Some (k, x) ->
  x = firstn (length x) l /\ (14 <= length x)%nat /\ (length x < length l)%nat.
Proof.
  intros l k x G. unfold RelayModel.gesture in G.
  destruct (RelayModel.list_eqb (firstn 13 l) RelayModel.K_GESTURE && Z.eqb (nth 13 l 0) RelayModel.SPACE &&
            Nat.ltb 13 (length l)); [|discriminate G].
  destruct (RelayModel.last_space_from 0 l) as [j|] eqn:EL; [|discriminate G].
  destruct (Nat.ltb 13 j) eqn:Ej; [|discriminate G]. apply Nat.ltb_lt in Ej.
  pose proof (rg_lsf l 0 j EL) as Hj.
  assert (Lx : length (firstn j l) = j) by (rewrite length_firstn; lia).
  destruct (RelayModel.list_eqb (skipn (S j) l) RelayModel.W_BEGIN).
  - injection G as Hk Hx. subst x. rewrite Lx. split; [reflexivity|]. lia.
  - destruct (RelayModel.list_eqb (skipn (S j) l) RelayModel.W_END); [|discriminate G].
    injection G as Hk Hx. subst x. rewrite Lx. split; [reflexivity|]. lia.
Qed.

Lemma rg_seen : forall H l, Forall rg_pc H -> (length l <= RelayModel.LINE_LIMIT)%nat ->
  Forall rg_pc (RelayKeys.seen_arr H l).
Proof.
  intros H l HP Hl. unfold RelayKeys.seen_arr.
  destruct (RelayModel.gesture l) as [[[|] x]|] eqn:EG.
  - destruct (RelayKeys.index_of x H); [exact HP|].
    apply Forall_app. split; [exact HP|]. apply Forall_cons; [|apply Forall_nil].
    destruct (rg_gesture l RelayModel.GBegin x EG) as (_ & L1 & L2). unfold rg_pc. lia.
  - destruct (RelayKeys.index_of x H) as [n|] eqn:E; [|exact HP].
    destruct (RelayKeys.index_of_some x H n E) as (a & b & -> & <-).
    rewrite Forall_forall in HP |- *. intros z Hz. apply HP.
    apply (Permutation_in _ (Permutation_sym (RelayKeys.swap_remove_perm [] a x b))). right. exact Hz.
  - exact HP.
Qed.

Lemma rg_scan6 : forall d skip acc,
  Forall (fun l => (length l <= RelayModel.LINE_LIMIT)%nat) (snd (RelayModel.scan skip acc d)).
Proof.
  induction d as [|b d IH]; intros skip acc; [apply Forall_nil|].
  cbn [RelayModel.scan]. destruct (b =? 0).
  - pose proof (IH false []) as I. destruct (RelayModel.scan false [] d) as [[sk r] ls]. cbn [snd] in I |- *.
    match goal with |- context [if ?c then _ else _] => destruct c eqn:E end; [exact I|].
    apply Forall_cons; [|exact I]. apply orb_false_iff in E. destruct E as [_ E]. apply Nat.ltb_ge in E. exact E.
  - apply IH.
Qed.

Lemma rg_chunk6 : forall u skip d,
  Forall (fun l => (length l <= RelayModel.LINE_LIMIT)%nat) (snd (RelayModel.chunk u skip d)).
Proof.
  intros u skip d. unfold RelayModel.chunk. pose proof (rg_scan6 d skip u) as I.
  destruct (RelayModel.scan skip u d) as [[sk r] ls]. cbn [snd] in I.
  cbv beta iota zeta. destruct (Nat.ltb RelayModel.LINE_LIMIT (length r)); exact I.
Qed.

Lemma rg_lines_run : forall live mx ls no cap H ka j o ha ks, Forall rg_pc H ->
  Forall (fun l => (length l <= RelayModel.LINE_LIMIT)%nat) ls ->
  Forall rg_pc (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))))).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks HP HL.
  - cbn [drain_b_c.lines_run snd fst]. exact HP.
  - apply Forall_cons_iff in HL. destruct HL as [Hl HL].
    cbn [drain_b_c.lines_run]. cbv zeta. cbn [snd fst].
    apply IH; [apply rg_seen; [exact HP|exact Hl]|exact HL].
Qed.

Lemma rg_drain_run : forall f live mx s j a, Forall rg_pc (drain_b_c.ds_H s) ->
  Forall rg_pc (drain_b_c.ds_H (fst (snd (drain_b_c.drain_run f live mx s j a)))).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a HP.
  - cbn [drain_b_c.drain_run snd fst]. exact HP.
  - cbn [drain_b_c.drain_run]. cbv zeta. destruct (drain_b_c.ds_eintr s).
    + cbn [snd fst]. apply IH. cbn [drain_b_c.ds_H]. exact HP.
    + destruct (drain_b_c.ds_pend s) as [|r0 rs].
      { cbn [snd fst drain_b_c.ds_H]. exact HP. }
      match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end.
      { cbn [snd fst drain_b_c.ds_H]. exact HP. }
      match goal with |- context [RelayModel.chunk ?u ?k ?d] =>
        pose proof (rg_chunk6 u k d) as LC; destruct (RelayModel.chunk u k d) as [[u' sk'] rl] end.
      cbn [snd] in LC.
      match goal with
      |- context [drain_b_c.lines_run live mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                    (drain_b_c.ds_ka s) rl ?j3 ?o ?ha ?ks] =>
        pose proof (rg_lines_run live mx rl (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                      (drain_b_c.ds_ka s) j3 o ha ks HP LC) as LW;
        destruct (drain_b_c.lines_run live mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) (drain_b_c.ds_H s)
                    (drain_b_c.ds_ka s) rl j3 o ha ks) as [[tl [[oc' H'] ka']] [[o' ha'] ks']]
      end.
      cbn [snd fst] in LW |- *. apply IH. cbn [drain_b_c.ds_H]. exact LW.
Qed.

Lemma rg_fin : forall lv mx NO CAP e h, Forall rg_pc (drain_b_c.keys_texts (re_keys e)) ->
  Forall rg_pc (drain_b_c.ds_H (drain_b_c.drain_fin lv mx NO CAP e h)).
Proof.
  intros lv mx NO CAP e h HP. unfold drain_b_c.drain_fin, drain_b_c.drain_go. apply rg_drain_run. exact HP.
Qed.

Lemma rg_LL : Z.of_nat RelayModel.LINE_LIMIT = 6000.
Proof. reflexivity. Qed.

Lemma rg_keys_pc : forall ks, Forall rg_kok ks -> Forall rg_pc (drain_b_c.keys_texts ks).
Proof.
  intros ks H. unfold drain_b_c.keys_texts. apply Forall_map. eapply Forall_impl; [|exact H].
  intros k [_ Hl]. cbv beta. unfold rg_pc, HarnessRep.bzs. rewrite length_map. unfold APARTIAL in Hl.
  pose proof rg_LL. lia.
Qed.

Lemma rg_nz_of : forall U : list byte, ~ In (Z_to_bv 8 0) U -> RelayModel.nozero (HarnessRep.bzs U).
Proof.
  intros U H. unfold RelayModel.nozero, HarnessRep.bzs. apply Forall_map. apply Forall_forall.
  intros b Hb E. apply H. replace b with (Z_to_bv 8 0) in Hb; [exact Hb|].
  apply bv_eq. unfold HarnessRep.bz in E. rewrite E. reflexivity.
Qed.

Lemma rg_nz_to : forall U : list byte, RelayModel.nozero (HarnessRep.bzs U) -> ~ In (Z_to_bv 8 0) U.
Proof.
  intros U H Hin. unfold RelayModel.nozero, HarnessRep.bzs in H. rewrite Forall_forall in H.
  apply (H (HarnessRep.bz (Z_to_bv 8 0))); [apply in_map; exact Hin|reflexivity].
Qed.

Lemma rg_nz_firstn : forall n l, RelayModel.nozero l -> RelayModel.nozero (firstn n l).
Proof.
  intros n l H. unfold RelayModel.nozero in *. rewrite <- (firstn_skipn n l) in H.
  apply Forall_app in H. exact (proj1 H).
Qed.

Lemma rg_upds_in : forall ls G y, In y (RelayModel.upds G ls) ->
  In y G \/ exists l x, In l ls /\ RelayModel.gesture l = Some (RelayModel.GBegin, x) /\ y = x.
Proof.
  induction ls as [|l ls IH]; intros G y Hy; unfold RelayModel.upds in Hy; cbn [fold_left] in Hy.
  - left. exact Hy.
  - apply IH in Hy. destruct Hy as [Hy|(l' & x & Hl & Hg & ->)].
    + unfold RelayModel.upd in Hy. destruct (RelayModel.gesture l) as [[[|] x]|] eqn:EG.
      * apply RelayKeys.upd_in_begin in Hy. destruct Hy as [Hy| ->]; [left; exact Hy|].
        right. exists l, x. split; [left; reflexivity|split; [exact EG|reflexivity]].
      * apply RelayKeys.upd_in_end in Hy. left. exact (proj1 Hy).
      * left. exact Hy.
    + right. exists l', x. split; [right; exact Hl|split; [exact Hg|reflexivity]].
Qed.

(* 2. drain keeps the key clause and the 0-free partial line *)
Lemma rg_kok_drain : forall c mx no cap e h e1 h1 LB,
  dr_rel c mx no cap e h e1 h1 LB -> Forall rg_kok (re_keys e) ->
  RelayModel.nozero (bzs (hs_W h)) -> (hs_overlong h = 0 -> Z.of_nat (length (hs_W h)) <= APARTIAL) ->
  NoDup (drain_b_c.keys_texts (re_keys e1)) ->
  Forall rg_kok (re_keys e1) /\ RelayModel.nozero (bzs (hs_W h1)).
Proof.
  intros c mx no cap e h e1 h1 LB Hdr Hk Hw _ _.
  unfold dr_rel in Hdr. cbv zeta in Hdr.
  destruct Hdr as (_ & _ & _ & _ & _ & _ & HK & _ & _ & HSS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HST & _).
  destruct (rg_lines_nz (bzs (pending_stream h)) (hs_state h) Hw) as [HL1 HL2].
  split.
  2: { change (bzs (hs_W h1)) with (RelayModel.ls_w (hs_state h1)). rewrite HST. exact HL2. }
  pose proof (rg_fin (dr_live c h) mx no cap e h (rg_keys_pc _ Hk)) as HF.
  change (drain_b_c.drain_fin (dr_live c h) mx no cap e h) with (dr_fin c mx no cap e h) in HF.
  rewrite <- HK in HF.
  apply Forall_forall. intros k1 Hk1.
  assert (Hy : In (bzs (gestures_end_b_c.key_text k1)) (drain_b_c.keys_texts (re_keys e1))).
  { unfold drain_b_c.keys_texts. exact (in_map (fun k => bzs (gestures_end_b_c.key_text k)) _ _ Hk1). }
  assert (HC : rg_pc (bzs (gestures_end_b_c.key_text k1))).
  { rewrite Forall_forall in HF. exact (HF _ Hy). }
  assert (HZ : RelayModel.nozero (bzs (gestures_end_b_c.key_text k1))).
  { apply (proj1 (HSS _)) in Hy. apply rg_upds_in in Hy.
    destruct Hy as [Hy|(l & x & Hl & Hg & Ey)].
    - unfold drain_b_c.keys_texts in Hy. apply in_map_iff in Hy. destruct Hy as (k0 & E0 & Hk0).
      rewrite <- E0. apply rg_nz_of. rewrite Forall_forall in Hk. exact (proj1 (Hk k0 Hk0)).
    - rewrite Ey. destruct (rg_gesture l RelayModel.GBegin x Hg) as (Ex & _ & _). rewrite Ex.
      apply rg_nz_firstn. rewrite Forall_forall in HL1. exact (HL1 l Hl). }
  split; [exact (rg_nz_to _ HZ)|].
  unfold rg_pc, HarnessRep.bzs in HC. rewrite length_map in HC. pose proof rg_LL.
  unfold APARTIAL. lia.
Qed.

(* ---------------------------------------------------------------- 3. geik splits the keys *)

Lemma rg_nth_map : forall {X Y} (f : X -> Y) (l : list X) d d' n, f d = d' -> nth n (map f l) d' = f (nth n l d).
Proof. intros X Y f l d d' n <-. apply map_nth. Qed.

Lemma rg_set_nth_map : forall {X Y} (f : X -> Y) n y l,
  map f (RelayKeys.set_nth n y l) = RelayKeys.set_nth n (f y) (map f l).
Proof.
  intros X Y f n y l. revert n. induction l as [|a l IH]; intros n; [destruct n; reflexivity|].
  destruct n as [|n]; cbn [RelayKeys.set_nth map]; [reflexivity|]. f_equal. apply IH.
Qed.

Lemma rg_last_map : forall {X Y} (f : X -> Y) l d, last (map f l) (f d) = f (last l d).
Proof.
  intros X Y f l. induction l as [|a l IH]; intros d; [reflexivity|].
  destruct l as [|b l]; [reflexivity|].
  change (last (map f (b :: l)) (f d) = f (last (b :: l) d)). exact (IH d).
Qed.

Lemma rg_firstn_map : forall {X Y} (f : X -> Y) n l, firstn n (map f l) = map f (firstn n l).
Proof.
  intros X Y f n. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|a l]; [reflexivity|]. cbn [firstn map]. f_equal. apply IH.
Qed.

Lemma rg_swap_map : forall {X Y} (f : X -> Y) d n l,
  map f (RelayKeys.swap_remove d n l) = RelayKeys.swap_remove (f d) n (map f l).
Proof.
  intros X Y f d n l. unfold RelayKeys.swap_remove.
  rewrite length_map, (rg_last_map f l d), <- (rg_set_nth_map f n (last l d) l), (rg_firstn_map f).
  reflexivity.
Qed.

(* geik_loop against RelayKeys.gei_loop over the keys' texts: the keys ended and the keys kept *)
Lemma rg_geik_map : forall fu pre n ks,
  map (fun k => bzs (gestures_end_b_c.key_text k)) (fst (geik_loop fu pre n ks)) =
    fst (RelayKeys.gei_loop fu pre n (map (fun k => bzs (gestures_end_b_c.key_text k)) ks)) /\
  map (fun k => bzs (gestures_end_b_c.key_text k)) (snd (geik_loop fu pre n ks)) =
    snd (RelayKeys.gei_loop fu pre n (map (fun k => bzs (gestures_end_b_c.key_text k)) ks)).
Proof.
  induction fu as [|fu IH]; intros pre n ks; cbn [geik_loop RelayKeys.gei_loop]; [split; reflexivity|].
  rewrite length_map. destruct (Nat.ltb n (length ks)) eqn:Hl; [|split; reflexivity].
  rewrite (rg_nth_map (fun k => bzs (gestures_end_b_c.key_text k)) ks (0, [], []) [] n eq_refl). cbv beta.
  destruct (RelayKeys.has_prefix pre (bzs (gestures_end_b_c.key_text (nth n ks (0, [], []))))).
  - replace (RelayKeys.swap_remove [] n (map (fun k => bzs (gestures_end_b_c.key_text k)) ks))
      with (map (fun k => bzs (gestures_end_b_c.key_text k)) (RelayKeys.swap_remove (0, [], []) n ks))
      by (rewrite rg_swap_map; reflexivity).
    pose proof (IH pre n (RelayKeys.swap_remove (0, [], []) n ks)) as [E1 E2]. revert E1 E2.
    destruct (geik_loop fu pre n (RelayKeys.swap_remove (0, [], []) n ks)) as [Ea Ka].
    destruct (RelayKeys.gei_loop fu pre n
                (map (fun k => bzs (gestures_end_b_c.key_text k)) (RelayKeys.swap_remove (0, [], []) n ks)))
      as [Et Kt].
    cbn [fst snd map]. intros E1 E2. rewrite E1, E2. split; reflexivity.
  - exact (IH pre (S n) ks).
Qed.

Lemma rg_geik_loop_perm : forall fu pre n ks,
  Permutation ks (fst (geik_loop fu pre n ks) ++ snd (geik_loop fu pre n ks)).
Proof.
  induction fu as [|fu IH]; intros pre n ks; cbn [geik_loop].
  - cbn [fst snd app]. apply Permutation_refl.
  - destruct (Nat.ltb_spec n (length ks)) as [Hn|Hn].
    + destruct (RelayKeys.has_prefix pre (bzs (gestures_end_b_c.key_text (nth n ks (0, [], []))))).
      * pose proof (IH pre n (RelayKeys.swap_remove (0, [], []) n ks)) as I.
        destruct (geik_loop fu pre n (RelayKeys.swap_remove (0, [], []) n ks)) as [E K].
        cbn [fst snd app] in I |- *.
        destruct (nth_split ks (0, [], []) Hn) as (a & b & HH & Ha).
        pose proof (RelayKeys.swap_remove_perm (0, [], []) a (nth n ks (0, [], [])) b) as P.
        rewrite <- HH, Ha in P.
        eapply perm_trans; [exact P|]. apply perm_skip. exact I.
      * apply IH.
    + cbn [fst snd app]. apply Permutation_refl.
Qed.

(* 3. geik splits the keys *)
Lemma rg_geik_perm : forall pre ks, Permutation ks (fst (geik pre ks) ++ snd (geik pre ks)).
Proof. intros pre ks. unfold geik. apply rg_geik_loop_perm. Qed.

Lemma rg_geik_texts : forall pre ks, NoDup (drain_b_c.keys_texts ks) ->
  NoDup (drain_b_c.keys_texts (snd (geik pre ks))) /\
  (forall y, In y (drain_b_c.keys_texts (snd (geik pre ks))) <->
     In y (drain_b_c.keys_texts ks) /\ has_prefix pre y = false) /\
  map (fun k => bzs (gestures_end_b_c.key_text k)) (fst (geik pre ks)) =
    fst (RelayKeys.gei pre (drain_b_c.keys_texts ks)).
Proof.
  intros pre ks Hnd. apply NoDup_ListNoDup in Hnd. pose proof (RelayKeys.gei_ok pre _ Hnd) as G.
  unfold geik, RelayKeys.gei, drain_b_c.keys_texts in *. rewrite length_map in *.
  destruct (rg_geik_map (length ks) pre 0 ks) as [M1 M2]. rewrite M1, M2.
  destruct (RelayKeys.gei_loop (length ks) pre 0 (map (fun k => bzs (gestures_end_b_c.key_text k)) ks))
    as [E H'].
  destruct G as (_ & ND & _ & _ & SS). cbn [fst snd].
  split; [apply NoDup_ListNoDup; exact ND|]. split; [|reflexivity].
  intros y. rewrite (SS y), filter_In. cbv beta. rewrite negb_true_iff. reflexivity.
Qed.

(* ---------------------------------------------------------------- (from scratch E1) *)

(* ---------------------------------------------------------------- 1. the keys geik keeps cost no more *)

Lemma rg_keys_total_app : forall a b,
  gestures_end_b_c.keys_total (a ++ b) = gestures_end_b_c.keys_total a + gestures_end_b_c.keys_total b.
Proof.
  intros a b. unfold gestures_end_b_c.keys_total. induction a as [|k a IH]; cbn [app fold_right]; lia.
Qed.

Lemma rg_keys_total_perm : forall ks ks', Permutation ks ks' ->
  gestures_end_b_c.keys_total ks = gestures_end_b_c.keys_total ks'.
Proof. intros ks ks' P. unfold gestures_end_b_c.keys_total. induction P; cbn [fold_right]; lia. Qed.

Lemma rg_surv_total : forall pre ks,
  gestures_end_b_c.keys_total (snd (geik pre ks)) <= gestures_end_b_c.keys_total ks.
Proof.
  intros pre ks. rewrite (rg_keys_total_perm ks _ (rg_geik_perm pre ks)), rg_keys_total_app.
  pose proof (fr_keys_total_nonneg (fst (geik pre ks))). lia.
Qed.

(* ---------------------------------------------------------------- 2. one entry through the gone arm's end *)

Section s.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma rg_end_pair : forall (m mc : lmod) (t : Z) (e : rentry) (g0 : hsrc) (s : nat) (c : ctl) (mx no cap : Z)
    (e1 : rentry) (h1 : hsrc) (LB : list byte) (h' : hsrc) (E' H' : hlist) (h'' : hsrc) (H'' : hlist) (pre : list Z),
  0 <= t < OPS_MAX -> fr_entry_ok e -> fr_pair_ok m t e (g0, s) ->
  (re_eof e = 0 -> dr_rel c mx no cap e g0 e1 h1 LB) ->
  (re_eof e <> 0 -> e1 = e /\ h1 = g0) ->
  gn_cnl_ok h1 h' E' H' ->
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 ->
  h'' = set_held h' H'' -> hl_cap H'' = hl_cap (hs_held h') -> NoDup (texts H'') ->
  (forall y, In y (texts H'') <-> In y (texts H') /\ has_prefix pre y = false) ->
  nth s (lm_hs mc) None = Some h'' ->
  fr_pair_ok mc (t + 1) (entry_keys e1 (snd (geik pre (re_keys e1)))) (h'', s) /\
  fr_pair_cost (entry_keys e1 (snd (geik pre (re_keys e1)))) (h'', s) <= fr_pair_cost e (g0, s).
Proof.
  intros m mc t e g0 s c mx no cap e1 h1 LB h' E' H' h'' H'' pre Ht Hent Hpo Hop Hcl Hcnl Hb22 Eh'' Hcap'' HND''
    HT'' Hnth.
  destruct Hcnl as (Eh' & ER & _ & EC & _ & ET' & HC').
  destruct Hpo as (Hs4 & Hn0 & Hfd0 & Hre0 & Hss0 & Hnd0 & Hexp0 & Hec0 & Hhc0 & Hpe0 & Hoff0).
  cbn [fst snd] in Hs4, Hn0, Hfd0, Hre0, Hss0, Hnd0, Hexp0, Hec0, Hhc0, Hpe0, Hoff0.
  (* what the drained (open) or untouched (closed) entry and source give *)
  assert (F : re_fd e1 = hs_fd h1 /\
    (re_eof e1 = 0 -> re_skip e1 = hs_overlong h1 /\ (re_skip e1 = 0 -> bzs (re_U e1) = bzs (hs_W h1))) /\
    NoDup (drain_b_c.keys_texts (re_keys e1)) /\
    same_set (drain_b_c.keys_texts (re_keys e1)) (texts H') /\
    SlotInv.ecap_ok (hl_cap (hs_expected h1)) /\ hl_cap (hs_held h1) < 2 ^ 24 /\
    Z.of_nat (length (pending_stream h1)) <= SlotInv.WRITE_MAX * (t + 1) /\ 0 <= hs_off h1 /\
    fr_pair_cost e1 (h1, s) <= fr_pair_cost e (g0, s)).
  { destruct (Z.eq_dec (re_eof e) 0) as [E0 | E0].
    - (* open: the drain *)
      specialize (Hop E0). clear Hcl.
      destruct Hop as (Rfd & _ & _ & _ & _ & Rsk & _ & _ & RND & RSS & Recap & _ & Rhfd & _ & _ & RHP & Roff &
        _ & _ & _ & RST & Rexp & _ & Rheld & RS2 & RW2 & _).
      destruct (Hre0 E0) as (S1 & W1).
      destruct Hent as (_ & _ & _ & _ & Hsk).
      assert (O1 : hs_overlong g0 = 0 \/ hs_overlong g0 = 1) by (rewrite <- S1; exact Hsk).
      assert (O2 : hs_overlong h1 = 0 \/ hs_overlong h1 = 1).
      { rewrite <- RS2, Rsk. match goal with |- context [if ?b then _ else _] => destruct b end;
          [right | left]; reflexivity. }
      (* the expected list after the drain holds exactly the drained lines *)
      assert (Etx : texts (hs_expected h1) = dr_lines g0).
      { unfold texts.
        replace (map (fun r => bzs (snd r)) (hl_recs (hs_expected h1)))
          with (map bzs (map snd (hl_recs (hs_expected h1)))) by (rewrite List.map_map; reflexivity).
        rewrite Rexp, Hexp0. cbn [map app]. apply fr_bzs_lines.
        exact (proj1 (SlotReads.lines_range (bzs (pending_stream g0)) (hs_state g0) (SlotReads.zrange_bzs (hs_W g0))
          (SlotReads.zrange_bzs (pending_stream g0)))). }
      split; [rewrite Rfd, Rhfd; exact (eq_sym Hfd0)|].
      split; [intros _; split; [exact RS2 | exact RW2]|].
      split; [exact RND|].
      split.
      { rewrite ET', Rheld, Etx. intros y. rewrite (RSS y).
        exact (SlotReads.upds_same_set (dr_lines g0) _ _ Hss0 y). }
      split.
      { rewrite Recap. unfold dr_fin.
        apply SlotDrain3.drain3_ecap; [exact Hoff0 | exact Hec0 |].
        assert (P25 : 2 ^ 25 = 33554432) by reflexivity.
        unfold hl_n. rewrite Hexp0. cbn [length]. unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia. }
      split; [rewrite Rheld; exact Hhc0|].
      split; [unfold pending_stream; rewrite RHP; cbn [length]; unfold SlotInv.WRITE_MAX; lia|].
      split; [rewrite Roff; lia|].
      exact (SlotPass2Aux.p2_pair_cost (fr_ru e) (fr_ru e1) g0 h1 s S1 W1 O1 eq_refl RS2 RW2 O2 eq_refl RST RHP
        RND RSS).
    - (* closed: nothing *)
      destruct (Hcl E0) as (-> & ->). clear Hop.
      destruct Hent as (_ & _ & _ & HNDe & _).
      split; [exact (eq_sym Hfd0)|].
      split; [intros E; contradiction|].
      split; [exact HNDe|].
      split.
      { rewrite ET'. replace (texts (hs_expected g0)) with (@nil (list Z))
          by (unfold texts; rewrite Hexp0; reflexivity).
        exact Hss0. }
      split; [exact Hec0|].
      split; [exact Hhc0|].
      split; [unfold SlotInv.WRITE_MAX in *; lia|].
      split; [exact Hoff0|].
      lia. }
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  destruct (rg_geik_texts pre (re_keys e1) F3) as (_ & Gin & _).
  subst h'' h'.
  split.
  - unfold fr_pair_ok. cbn [fst snd].
    refine (conj Hs4 (conj Hnth (conj _ (conj _ (conj _ (conj HND'' (conj ER (conj _ (conj _ (conj _ _)))))))))).
    + exact (eq_sym F1).
    + exact F2.
    + change (same_set (drain_b_c.keys_texts (snd (geik pre (re_keys e1)))) (texts H'')).
      intros y. rewrite (Gin y), (HT'' y). pose proof (F4 y). tauto.
    + change (SlotInv.ecap_ok (hl_cap E')). rewrite EC. exact F5.
    + change (hl_cap H'' < 2 ^ 24).
      change (hl_cap H'' = hl_cap H') in Hcap''.
      assert (P22 : 2 ^ 22 = 4194304) by reflexivity. assert (P24 : 2 ^ 24 = 16777216) by reflexivity.
      lia.
    + exact F7.
    + exact F8.
  - change (gestures_end_b_c.keys_total (snd (geik pre (re_keys e1))) + Z.of_nat (length (pending_stream h1)) +
      (if re_skip e1 =? 0 then Z.of_nat (length (re_U e1)) else 0) <= fr_pair_cost e (g0, s)).
    pose proof (rg_surv_total pre (re_keys e1)) as Hst.
    change (gestures_end_b_c.keys_total (re_keys e1) + Z.of_nat (length (pending_stream h1)) +
      (if re_skip e1 =? 0 then Z.of_nat (length (re_U e1)) else 0) <= fr_pair_cost e (g0, s)) in F9.
    lia.
Qed.

End s.

(* ---------------------------------------------------------------- (from scratch E2) *)

(* ---------------------------------------------------------------- 1. keys_total of key lists *)

Lemma rg_kt_app : forall l l', gestures_end_b_c.keys_total (l ++ l') =
  gestures_end_b_c.keys_total l + gestures_end_b_c.keys_total l'.
Proof.
  unfold gestures_end_b_c.keys_total. induction l as [|k l IH]; intros l'; cbn [app fold_right]; [lia|].
  rewrite IH. lia.
Qed.

Lemma rg_kt_perm : forall l l', Permutation l l' ->
  gestures_end_b_c.keys_total l = gestures_end_b_c.keys_total l'.
Proof.
  intros l l' H. unfold gestures_end_b_c.keys_total. induction H; cbn [fold_right]; lia.
Qed.

(* the keys gestures_end_instance ends are part of the keys *)
Lemma rg_kt_geik : forall pre ks,
  gestures_end_b_c.keys_total (fst (geik pre ks)) <= gestures_end_b_c.keys_total ks.
Proof.
  intros pre ks. rewrite (rg_kt_perm _ _ (rg_geik_perm pre ks)), rg_kt_app.
  pose proof (fr_keys_total_nonneg (snd (geik pre ks))). lia.
Qed.

(* the end lines of the keys ks are keys_total ks bytes: each is the key's text then " end\0" *)
Lemma rg_end_lines_len : forall ks,
  Z.of_nat (length (concat (map (fun x => x ++ relay_instance_gone_b_c.END5Z)
    (map (fun k => bzs (gestures_end_b_c.key_text k)) ks)))) = gestures_end_b_c.keys_total ks.
Proof.
  unfold gestures_end_b_c.keys_total. induction ks as [|k ks IH]; cbn [map concat fold_right]; [reflexivity|].
  rewrite !length_app, SlotReads.bzs_length. change (length relay_instance_gone_b_c.END5Z) with 5%nat. lia.
Qed.

(* ---------------------------------------------------------------- 2. one entry's bytes *)

Lemma rg_seg_len : forall (m : lmod) (t : Z) (e : rentry) (g0 : hsrc) (s : nat) (c : ctl) (mx no cap : Z)
    (e1 : rentry) (h1 : hsrc) (LB : list byte) (pre : list Z),
  fr_entry_ok e -> fr_pair_ok m t e (g0, s) ->
  (re_eof e = 0 -> dr_rel c mx no cap e g0 e1 h1 LB) ->
  (re_eof e <> 0 -> e1 = e) ->
  Z.of_nat (length ((if re_eof e =? 0 then with_nul (dr_lines g0) else []) ++
    concat (map (fun x => x ++ relay_instance_gone_b_c.END5Z)
      (map (fun k => bzs (gestures_end_b_c.key_text k)) (fst (geik pre (re_keys e1))))))) <=
  2 * fr_pair_cost e (g0, s).
Proof.
  intros m t e g0 s c mx no cap e1 h1 LB pre Hent Hok Hdr Hcl.
  rewrite length_app, Nat2Z.inj_add, rg_end_lines_len.
  pose proof (rg_kt_geik pre (re_keys e1)) as KG.
  pose proof (fr_keys_total_nonneg (re_keys e)) as K0.
  assert (Pc : 0 <= Z.of_nat (length (pending_stream g0))) by lia.
  assert (Uc : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by (destruct (re_skip e =? 0); lia).
  unfold fr_pair_cost in *. cbn [fst] in *.
  destruct (Z.eqb_spec (re_eof e) 0) as [Heof | Heof].
  - (* open: drain's lines, then the ended keys of the drained entry *)
    cbn iota. specialize (Hdr Heof).
    unfold fr_pair_ok in Hok. cbn [fst snd] in Hok.
    destruct Hok as (_ & _ & _ & Hre & _ & _ & _ & _ & _ & _ & _).
    destruct (Hre Heof) as (S1 & W1).
    destruct Hent as (_ & _ & _ & _ & Hsk).
    assert (O1 : hs_overlong g0 = 0 \/ hs_overlong g0 = 1) by (rewrite <- S1; exact Hsk).
    unfold dr_rel in Hdr. cbv zeta in Hdr.
    destruct Hdr as (_ & _ & _ & _ & _ & Oskip & _ & _ & OND & OSS & _ & _ & _ & _ & _ & OHP & _ & _ & _ & _ &
      OST & _ & _ & _ & OS2 & OW2 & _).
    assert (Hsk' : re_skip e1 = 0 \/ re_skip e1 = 1).
    { rewrite Oskip. match goal with |- context [if ?b then _ else _] => destruct b end; [right | left]; reflexivity. }
    assert (O2 : hs_overlong h1 = 0 \/ hs_overlong h1 = 1) by (rewrite <- OS2; exact Hsk').
    (* the drained lines' bytes *)
    pose proof (SlotReads.reads_bound (fr_ru e) g0 S1 W1 O1 eq_refl) as RB.
    change (re_skip (fr_ru e)) with (re_skip e) in RB.
    change (re_used (fr_ru e)) with (Z.of_nat (length (re_U e))) in RB.
    fold (dr_lines g0) in RB.
    (* the drained entry's keys *)
    pose proof (SlotPass2Aux.p2_pair_cost (fr_ru e) (fr_ru e1) g0 h1 s S1 W1 O1 eq_refl
                OS2 OW2 O2 eq_refl OST OHP OND OSS) as PC.
    change (fr_pair_cost e1 (h1, s) <= fr_pair_cost e (g0, s)) in PC.
    unfold fr_pair_cost in PC. cbn [fst] in PC.
    pose proof (Zle_0_nat (length (pending_stream h1))) as Ph1.
    assert (Uc1 : 0 <= (if re_skip e1 =? 0 then Z.of_nat (length (re_U e1)) else 0))
      by (destruct (re_skip e1 =? 0); lia).
    lia.
  - (* closed: no drain, the entry's own keys *)
    pose proof (Hcl Heof) as E1. subst e1. cbn iota. cbn [length]. lia.
Qed.

Section rgm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ================================================================== the stream relay_instance_gone sends *)
Lemma rg_live_len : forall c len, sl_live c len = sl_live c 1 && negb (len =? 0).
Proof.
  intros [cl br dd ei ev] len. unfold sl_live, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct (cl <? 0), (br =? 1), (len =? 0), (dd =? 0); reflexivity.
Qed.
Lemma rg_live_ctl : forall c len, sl_live (sl_ctl c len) 1 = sl_live c 1.
Proof.
  intros [cl br dd ei ev] len. unfold sl_live, sl_ctl, send_line_c.send_live, send_line_c.send_off.
  cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  destruct (cl <? 0); [reflexivity|]. destruct (br =? 1) eqn:Eb; [cbn; rewrite Eb; reflexivity|].
  destruct (len =? 0); cbn; [rewrite Eb; reflexivity|].
  destruct (Z.eqb_spec dd 0) as [->|Hd]; [reflexivity|]. destruct (dd =? 1); reflexivity.
Qed.
Lemma rg_live_drctl : forall c h ev, sl_live (dr_ctl c h ev) 1 = sl_live c 1.
Proof.
  intros [cl br dd ei ev0] h ev. unfold sl_live, dr_ctl, send_line_c.send_live, send_line_c.send_off.
  cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  destruct (cl <? 0); [reflexivity|]. destruct (br =? 1) eqn:Eb; [cbn; rewrite Eb; reflexivity|].
  destruct (dr_tot h =? 0); cbn; [rewrite Eb; reflexivity|].
  destruct (Z.eqb_spec dd 0) as [->|Hd]; [reflexivity|]. destruct (dd =? 1); reflexivity.
Qed.
Lemma rg_slO_live : forall c O x, sl_live c 1 = true -> sl_O c O x = O ++ x.
Proof.
  intros c O x L. unfold sl_O. rewrite rg_live_len, L.
  destruct x as [|b x]; cbn; [rewrite app_nil_r|]; reflexivity.
Qed.
Lemma rg_slO_dead : forall c O x, sl_live c 1 = false -> sl_O c O x = O.
Proof. intros c O x L. unfold sl_O. rewrite rg_live_len, L. reflexivity. Qed.

(* the key sends of gestures_end_instance: every key and its " end\0" when live, nothing when dead *)
Lemma rg_sends : forall mx Er c O cap,
  sl_live (fst (fst (sl_sends mx c O cap (ge_bytes Er)))) 1 = sl_live c 1 /\
  (sl_live c 1 = true -> snd (fst (sl_sends mx c O cap (ge_bytes Er))) =
     O ++ concat (map (fun k => gestures_end_b_c.key_text k ++ gesture_end_c.END5) Er)) /\
  (sl_live c 1 = false -> snd (fst (sl_sends mx c O cap (ge_bytes Er))) = O).
Proof.
  intros mx Er. induction Er as [|k Er IH]; intros c O cap.
  - cbn [ge_bytes map concat sl_sends fst snd]. split; [reflexivity|].
    split; intros _; [rewrite app_nil_r|]; reflexivity.
  - change (ge_bytes (k :: Er)) with (gestures_end_b_c.key_text k :: gesture_end_c.END5 :: ge_bytes Er).
    cbn [sl_sends].
    match goal with |- context [sl_sends mx ?c' ?O' ?cap' (ge_bytes Er)] =>
      destruct (IH c' O' cap') as (L & HT & HF) end.
    split; [rewrite L, !rg_live_ctl; reflexivity|]. split.
    + intros Lc. rewrite HT by (rewrite !rg_live_ctl; exact Lc).
      rewrite (rg_slO_live _ _ gesture_end_c.END5) by (rewrite rg_live_ctl; exact Lc).
      rewrite (rg_slO_live c O _ Lc). cbn [map concat]. rewrite <- !app_assoc. reflexivity.
    + intros Lc. rewrite HF by (rewrite !rg_live_ctl; exact Lc).
      rewrite (rg_slO_dead _ _ gesture_end_c.END5) by (rewrite rg_live_ctl; exact Lc).
      exact (rg_slO_dead c O _ Lc).
Qed.

Lemma rg_bzs_end5 : bzs gesture_end_c.END5 = relay_instance_gone_b_c.END5Z.
Proof. vm_compute. reflexivity. Qed.
Lemma rg_bzs_ends : forall Er,
  bzs (concat (map (fun k => gestures_end_b_c.key_text k ++ gesture_end_c.END5) Er)) =
  concat (map (fun x => x ++ relay_instance_gone_b_c.END5Z) (map (fun k => bzs (gestures_end_b_c.key_text k)) Er)).
Proof.
  induction Er as [|k Er IH]; [reflexivity|]. cbn [map concat].
  unfold bzs in *. rewrite !map_app, IH. fold (bzs gesture_end_c.END5). rewrite rg_bzs_end5. reflexivity.
Qed.

Lemma bzs_app : forall a b, bzs (a ++ b) = bzs a ++ bzs b.
Proof. intros a b. unfold bzs. apply map_app. Qed.

(* drain's relayed bytes *)
Lemma rg_dr_LB : forall c mx no cap e h e1 h1 LB, dr_rel c mx no cap e h e1 h1 LB -> bzs LB = with_nul (dr_lines h).
Proof.
  intros c mx no cap e h e1 h1 LB D. unfold dr_rel in D. cbv zeta in D.
  destruct D as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & D). exact D.
Qed.

(* the ended keys' end lines, as texts *)
Definition rg_endz (pre : list Z) (e1 : rentry) : list Z :=
  concat (map (fun x => x ++ relay_instance_gone_b_c.END5Z)
    (map (fun k => bzs (gestures_end_b_c.key_text k)) (fst (geik pre (re_keys e1))))).
(* the stream relay_instance_gone sends, entry by entry: an open entry's drained lines, then its ended keys *)
Fixpoint rg_strm (pre : list Z) (ps : list (rentry * (hsrc * nat))) (e1s : list rentry) : list Z :=
  match ps, e1s with
  | p :: r, e1 :: r1 =>
      (if re_eof (fst p) =? 0 then with_nul (dr_lines (fst (snd p))) else []) ++ rg_endz pre e1 ++ rg_strm pre r r1
  | _, _ => []
  end.
(* what rig_rel says of one entry p, the entry e1 its drain left (p's own when closed) and its row q of qs *)
Definition rg_ent (pre : list Z) (mx : Z) (p : rentry * (hsrc * nat)) (e1 : rentry) (q : rentry * hsrc) : Prop :=
  (re_eof (fst p) = 0 -> exists c no cap LB, dr_rel c mx no cap (fst p) (fst (snd p)) e1 (snd q) LB) /\
  (re_eof (fst p) <> 0 -> e1 = fst p /\ snd q = fst (snd p)) /\
  fst q = entry_keys e1 (snd (geik pre (re_keys e1))).

Lemma rg_rel_dec : forall pre mx ps qs c O cap c2 O2 cap2,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  exists e1s, length e1s = length ps /\ length qs = length ps /\
    (forall i, (i < length ps)%nat ->
       rg_ent pre mx (nth i ps (gn_e0, gn_hj0)) (nth i e1s gn_e0) (nth i qs gn_q0)) /\
    sl_live c2 1 = sl_live c 1 /\
    (sl_live c 1 = true -> bzs O2 = bzs O ++ rg_strm pre ps e1s) /\
    (sl_live c 1 = false -> O2 = O) /\
    (forall gn, fr_ctl_ok gn c -> fr_ctl_ok gn c2).
Proof.
  intros pre mx ps. induction ps as [|[e [h jj]] r IH]; intros [|[e' h'] q] c O cap c2 O2 cap2 H;
    cbn [rig_rel] in H; try contradiction.
  - destruct H as (-> & -> & ->). exists []. cbn [length rg_strm].
    split; [reflexivity|]. split; [reflexivity|]. split; [intros i Hi; lia|].
    split; [reflexivity|]. split; [intros _; rewrite app_nil_r; reflexivity|].
    split; [intros _; reflexivity | intros gn Hg; exact Hg].
  - destruct H as (e1 & ev & LB & H). cbv zeta in H. destruct H as (Hd & He' & Hrest).
    revert Hd Hrest. destruct (Z.eqb_spec (re_eof e) 0) as [E0 | E0]; intros Hd Hrest; cbn [andb] in Hrest.
    + (* open: drain, then the key sends *)
      match type of Hrest with context [sl_sends ?m ?c1 ?O1 ?cp1 ?Bs] =>
        pose proof (rg_sends m (fst (geik pre (re_keys e1))) c1 O1 cp1) as (SL & ST & SF);
        destruct (sl_sends m c1 O1 cp1 Bs) as [[c3 O3] cap3] eqn:ES end.
      cbn [fst snd] in SL, ST, SF.
      destruct (IH q c3 O3 cap3 c2 O2 cap2 Hrest) as (e1s & L1 & L2 & HE & Lv & Hlive & Hdead & Hctl).
      exists (e1 :: e1s). cbn [length]. split; [lia|]. split; [lia|]. split.
      { intros [|i] Hi.
        - unfold rg_ent. cbn [nth fst snd]. split; [|split].
          + intros _. exists c, (Z.of_nat (length O)), cap, LB. exact Hd.
          + intros N. exfalso. exact (N E0).
          + exact He'.
        - cbn [nth]. apply HE. cbn [length] in Hi. lia. }
      assert (LC : sl_live (dr_ctl c h ev) 1 = sl_live c 1) by apply rg_live_drctl.
      split; [rewrite Lv, SL, LC; reflexivity|]. split; [|split].
      * intros L. rewrite (Hlive ltac:(rewrite SL, LC; exact L)), (ST ltac:(rewrite LC; exact L)).
        rewrite bzs_app, rg_bzs_ends. cbn [rg_strm fst snd]. rewrite (proj2 (Z.eqb_eq _ _) E0).
        unfold rg_endz.
        assert (EO1 : bzs (if dr_live c h then O ++ LB else O) = bzs O ++ with_nul (dr_lines h)).
        { unfold dr_live. rewrite rg_live_len, L. cbn [andb].
          destruct (dr_tot h =? 0) eqn:Et; cbn [negb].
          - apply Z.eqb_eq in Et. unfold dr_tot in Et.
            destruct (with_nul (dr_lines h)) as [|z0 zs] eqn:EW; [rewrite app_nil_r; reflexivity|].
            cbn [length] in Et. lia.
          - rewrite bzs_app, (rg_dr_LB _ _ _ _ _ _ _ _ _ Hd). reflexivity. }
        rewrite EO1. rewrite <- !app_assoc. reflexivity.
      * intros L. rewrite (Hdead ltac:(rewrite SL, LC; exact L)), (SF ltac:(rewrite LC; exact L)).
        unfold dr_live. rewrite rg_live_len, L. reflexivity.
      * intros gn Hg. apply Hctl. exact (fr_ctl_sends gn _ _ _ _ _ c3 O3 cap3 (fr_ctl_dr gn c h ev Hg) ES).
    + (* closed: no drain, the key sends only *)
      destruct Hd as [-> ->].
      match type of Hrest with context [sl_sends ?m ?c1 ?O1 ?cp1 ?Bs] =>
        pose proof (rg_sends m (fst (geik pre (re_keys e))) c1 O1 cp1) as (SL & ST & SF);
        destruct (sl_sends m c1 O1 cp1 Bs) as [[c3 O3] cap3] eqn:ES end.
      cbn [fst snd] in SL, ST, SF.
      destruct (IH q c3 O3 cap3 c2 O2 cap2 Hrest) as (e1s & L1 & L2 & HE & Lv & Hlive & Hdead & Hctl).
      exists (e :: e1s). cbn [length]. split; [lia|]. split; [lia|]. split.
      { intros [|i] Hi.
        - unfold rg_ent. cbn [nth fst snd]. split; [|split].
          + intros N. exfalso. exact (E0 N).
          + intros _. split; reflexivity.
          + exact He'.
        - cbn [nth]. apply HE. cbn [length] in Hi. lia. }
      split; [rewrite Lv, SL; reflexivity|]. split; [|split].
      * intros L. rewrite (Hlive ltac:(rewrite SL; exact L)), (ST L).
        rewrite bzs_app, rg_bzs_ends. cbn [rg_strm fst snd].
        rewrite (proj2 (Z.eqb_neq _ _) E0). unfold rg_endz. rewrite <- !app_assoc. reflexivity.
      * intros L. rewrite (Hdead ltac:(rewrite SL; exact L)), (SF L). reflexivity.
      * intros gn Hg. apply Hctl. exact (fr_ctl_sends gn _ _ _ _ _ c3 O3 cap3 Hg ES).
Qed.

End rgm.

(* a splitter that drops its line (overlong) emits only 0-free lines *)
Lemma rg_lines_nz_k : forall d w, Forall nozero (lines (LS w true) d).
Proof.
  induction d as [|b d IH]; intros w; [unfold lines; cbn; constructor|].
  unfold lines. cbn [feed_lines]. unfold step. cbn [ls_k ls_w].
  destruct (b =? 0).
  - pose proof (proj1 (rg_lines_nz d (LS [] false) (Forall_nil _))) as H. unfold lines in H.
    destruct (feed_lines (LS [] false) d) as [st2 ls]. exact H.
  - pose proof (IH w) as H. unfold lines in H. destruct (feed_lines (LS w true) d) as [st2 ls]. exact H.
Qed.
(* NAMED FACT: the harness's partial line W is 0-free whenever the reference splitter reads it.  When skip =
   overlong = 1 the splitter drops W (RelayModel.step with ls_k = true); when skip = 0, bzs W = bzs U and U is
   0-free.  So the lines drain reads are 0-free. *)
Lemma rg_W_read_lines_nz : forall e h, (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) -> ~ In (Z_to_bv 8 0) (re_U e) ->
  Forall nozero (dr_lines h).
Proof.
  intros e h Hsk01 Hsk HU HUz. unfold dr_lines, hs_state. destruct Hsk01 as [E | E].
  - rewrite <- (HU E). rewrite <- Hsk, E. exact (proj1 (rg_lines_nz _ (LS (bzs (re_U e)) false) (rg_nz_of _ HUz))).
  - rewrite <- Hsk, E. apply rg_lines_nz_k.
Qed.

(* ================================================================== the model around the table-order loop *)
Section loop.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (cx : lfcx) (t : Z) (m : lmod) (hs : list (hsrc * nat)) (qs : list (rentry * hsrc)) (c2 : ctl)
  (O2 : list byte) (cap2 out2 : Z) (m1 : lmod) (hj : list (hsrc * nat)) (e1s : list rentry).
Hypothesis HRI : fr_RINV cx t m.
Hypothesis HF : Forall2 (fr_pair_ok m t) (lm_es m) hj.
Hypothesis HND : List.NoDup (map snd hj).
Hypothesis HCL : forall j, (j < 4)%nat -> SlotInv.slot_open hj j = false -> nth j (lm_hs m) None = None.
Hypothesis HP : gn_pairs m hs.
Hypothesis HA : gn_after_rig cx m hs qs c2 O2 cap2 out2 m1.
Hypothesis HLE : length e1s = length (lm_es m).
Hypothesis HLQ : length qs = length (lm_es m).
Hypothesis HEN : forall i, (i < length (lm_es m))%nat ->
  rg_ent (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) (lm_mx m)
    (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (nth i e1s gn_e0) (nth i qs gn_q0).

Local Notation n := (length (lm_es m)).
Definition rg_ei (i : nat) : rentry := nth i (lm_es m) gn_e0.
Definition rg_sl (i : nat) : nat := snd (nth i hj gn_hj0).
Definition rg_g0 (i : nat) : hsrc := fst (nth i hj gn_hj0).
Definition rg_G (i : nat) : hsrc := if re_eof (rg_ei i) =? 0 then snd (nth i qs gn_q0) else rg_g0 i.

Lemma rg_lhj : length hj = n.
Proof. exact (eq_sym (Forall2_length HF)). Qed.
Lemma rg_lhs : length hs = n.
Proof. exact (proj1 HP). Qed.
Lemma rg_comb : forall i, nth i (combine (lm_es m) hs) (gn_e0, gn_hj0) = (rg_ei i, nth i hs gn_hj0).
Proof. intros i. unfold rg_ei. apply combine_nth. rewrite rg_lhs. reflexivity. Qed.
Lemma rg_pair : forall i, (i < n)%nat -> fr_pair_ok m t (rg_ei i) (nth i hj gn_hj0).
Proof. intros i Hi. unfold rg_ei. exact (fr_F2_nth _ _ _ _ _ HF i gn_e0 gn_hj0 Hi). Qed.
Lemma rg_sl_ok : forall i, (i < n)%nat ->
  (rg_sl i < 4)%nat /\ nth (rg_sl i) (lm_hs m) None = Some (rg_g0 i) /\ hs_fd (rg_g0 i) = re_fd (rg_ei i).
Proof.
  intros i Hi. destruct (rg_pair i Hi) as (H1 & H2 & H3 & _). unfold rg_sl, rg_g0.
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.
Lemma rg_sl_inj : forall i i', (i < n)%nat -> (i' < n)%nat -> rg_sl i = rg_sl i' -> i = i'.
Proof.
  intros i i' Hi Hi' E. pose proof (proj1 (NoDup_nth (map snd hj) (snd gn_hj0)) HND) as ND.
  apply ND; rewrite ?length_map, ?rg_lhj; try assumption.
  rewrite !(map_nth snd hj gn_hj0). exact E.
Qed.
Lemma rg_fds : List.NoDup (map re_fd (lm_es m)).
Proof. destruct HRI as (_ & (_ & Hnd & _) & _). exact (proj1 (NoDup_ListNoDup _) Hnd). Qed.
Lemma rg_fd_inj : forall i i', (i < n)%nat -> (i' < n)%nat -> re_fd (rg_ei i) = re_fd (rg_ei i') -> i = i'.
Proof.
  intros i i' Hi Hi' E. pose proof (proj1 (NoDup_nth (map re_fd (lm_es m)) (re_fd gn_e0)) rg_fds) as ND.
  apply ND; rewrite ?length_map; try assumption.
  rewrite !(map_nth re_fd (lm_es m) gn_e0). exact E.
Qed.
Lemma rg_slot_of : forall j h, (j < 4)%nat -> nth j (lm_hs m) None = Some h ->
  exists i, (i < n)%nat /\ rg_sl i = j /\ h = rg_g0 i.
Proof.
  intros j h Hj Hh. destruct (SlotInv.slot_open hj j) eqn:Eo.
  - unfold SlotInv.slot_open in Eo. apply existsb_exists in Eo as (x & Hx & Hjx).
    apply Nat.eqb_eq in Hjx. subst x. apply in_map_iff in Hx as (p & Hpj & Hp).
    apply (In_nth hj p gn_hj0) in Hp as (i & Hi & Hpi). rewrite rg_lhj in Hi.
    exists i. split; [exact Hi|].
    assert (Hs : rg_sl i = j) by (unfold rg_sl; rewrite Hpi; exact Hpj).
    split; [exact Hs|]. destruct (rg_sl_ok i Hi) as (_ & Hn & _). rewrite Hs, Hh in Hn.
    injection Hn as E. exact E.
  - rewrite (HCL j Hj Eo) in Hh. discriminate Hh.
Qed.
Lemma rg_free : forall j, (j < 4)%nat -> (forall i, (i < n)%nat -> rg_sl i <> j) -> nth j (lm_hs m) None = None.
Proof.
  intros j Hj Hn. destruct (nth j (lm_hs m) None) as [h|] eqn:E; [|reflexivity].
  destruct (rg_slot_of j h Hj E) as (i & Hi & Hs & _). exfalso. exact (Hn i Hi Hs).
Qed.
(* an open entry's gn_pairs row is its fr_RINV row *)
Lemma rg_hs_open : forall i, (i < n)%nat -> re_eof (rg_ei i) = 0 -> nth i hs gn_hj0 = nth i hj gn_hj0.
Proof.
  intros i Hi E0. destruct HP as (_ & HFa & _). rewrite Forall_forall in HFa.
  assert (Hin : In (rg_ei i, nth i hs gn_hj0) (combine (lm_es m) hs)).
  { rewrite <- rg_comb. apply nth_In. rewrite length_combine, rg_lhs, Nat.min_id. exact Hi. }
  pose proof (HFa _ Hin) as Hq. cbv beta in Hq. cbn [fst snd] in Hq.
  destruct (Hq E0) as (Hs4 & Hsn & Hsfd & _).
  destruct (rg_slot_of _ _ Hs4 Hsn) as (i' & Hi' & Hsi' & Hg).
  destruct (rg_sl_ok i' Hi') as (_ & _ & Hf').
  assert (Ei : i' = i) by (apply rg_fd_inj; [exact Hi' | exact Hi | rewrite <- Hf', <- Hg; exact Hsfd]).
  subst i'. apply injective_projections; [exact Hg | exact (eq_sym Hsi')].
Qed.
Lemma rg_in_rig_slots : forall j, In j (rig_slots (combine (lm_es m) hs)) ->
  exists i, (i < n)%nat /\ re_eof (rg_ei i) = 0 /\ rg_sl i = j.
Proof.
  intros j Hj. unfold rig_slots in Hj. apply in_concat in Hj as (l & Hl & Hjl).
  apply in_map_iff in Hl as (p & Hpl & Hp).
  apply (In_nth _ p (gn_e0, gn_hj0)) in Hp as (i & Hi & Hpi).
  rewrite length_combine, rg_lhs, Nat.min_id in Hi. rewrite rg_comb in Hpi. subst p. cbn [fst snd] in Hpl.
  destruct (Z.eqb_spec (re_eof (rg_ei i)) 0) as [E0 | E0]; [|subst l; destruct Hjl].
  subst l. destruct Hjl as [Hj | []]. exists i. split; [exact Hi|]. split; [exact E0|].
  rewrite <- Hj. unfold rg_sl. rewrite (rg_hs_open i Hi E0). reflexivity.
Qed.
Lemma rg_m1_slot : forall i, (i < n)%nat -> nth (rg_sl i) (lm_hs m1) None = Some (rg_G i).
Proof.
  intros i Hi. destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkeep & Hdr).
  destruct (rg_sl_ok i Hi) as (Hs4 & Hsn & _). unfold rg_G.
  destruct (Z.eqb_spec (re_eof (rg_ei i)) 0) as [E0 | E0].
  - pose proof (Hdr i Hi E0) as D. unfold rg_sl. rewrite <- (rg_hs_open i Hi E0). exact D.
  - rewrite (Hkeep (rg_sl i) Hs4); [exact Hsn|]. intros Hin.
    destruct (rg_in_rig_slots _ Hin) as (i' & Hi' & E0' & Hs').
    rewrite (rg_sl_inj i' i Hi' Hi Hs') in E0'. exact (E0 E0').
Qed.
Lemma rg_m1_free : forall j, (j < 4)%nat -> (forall i, (i < n)%nat -> rg_sl i <> j) ->
  nth j (lm_hs m1) None = None.
Proof.
  intros j Hj Hn. destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkeep & _).
  rewrite (Hkeep j Hj); [exact (rg_free j Hj Hn)|]. intros Hin.
  destruct (rg_in_rig_slots _ Hin) as (i & Hi & _ & Hs). exact (Hn i Hi Hs).
Qed.
Lemma rg_m1_es : forall i, nth i (lm_es m1) gn_e0 = fst (nth i qs gn_q0).
Proof.
  intros i. destruct HA as (_ & _ & Hes & _). rewrite Hes. change gn_e0 with (fst gn_q0). apply map_nth.
Qed.
Lemma rg_m1_len : length (lm_es m1) = n.
Proof. destruct HA as (_ & _ & Hes & _). rewrite Hes, length_map. exact HLQ. Qed.
(* the entry's row after relay_instance_gone keeps the fd, and so does its slot's source *)
Lemma rg_q_fd : forall i, (i < n)%nat -> re_fd (fst (nth i qs gn_q0)) = re_fd (rg_ei i).
Proof.
  intros i Hi. destruct (HEN i Hi) as (Hop & Hcl & Hq). rewrite rg_comb in Hop, Hcl. cbn [fst snd] in Hop, Hcl.
  rewrite Hq. change (re_fd (entry_keys (nth i e1s gn_e0) (snd (geik (relay_instance_gone_b_c.instance_prefix
    (gn_id cx m)) (re_keys (nth i e1s gn_e0)))))) with (re_fd (nth i e1s gn_e0)).
  destruct (Z.eq_dec (re_eof (rg_ei i)) 0) as [E0 | E0].
  - destruct (Hop E0) as (c & no & cap & LB & D). unfold dr_rel in D. cbv zeta in D. exact (proj1 D).
  - destruct (Hcl E0) as (-> & _). reflexivity.
Qed.
Lemma rg_G_fd : forall i, (i < n)%nat -> hs_fd (rg_G i) = re_fd (rg_ei i).
Proof.
  intros i Hi. destruct (rg_sl_ok i Hi) as (_ & _ & Hf). unfold rg_G.
  destruct (Z.eqb_spec (re_eof (rg_ei i)) 0) as [E0 | E0]; [|exact Hf].
  destruct (HEN i Hi) as (Hop & _ & _). rewrite rg_comb in Hop. cbn [fst snd] in Hop.
  destruct (Hop E0) as (c & no & cap & LB & D). unfold dr_rel in D. cbv zeta in D.
  destruct D as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D & _). rewrite D.
  rewrite (rg_hs_open i Hi E0). exact Hf.
Qed.


(* ---- the premise of both rows: the pre-call table's unfinished lines and keys carry no 0 byte, keys >= 14 ---- *)
Hypothesis HKEY : Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
    14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m).

Local Notation pre := (relay_instance_gone_b_c.instance_prefix (gn_id cx m)).
Definition rg_ek (i : nat) : rentry := nth i e1s gn_e0.
Definition rg_L (i : nat) : list (list Z) := if re_eof (rg_ei i) =? 0 then dr_lines (rg_g0 i) else [].

Lemma rg_entry_ok : forall i, (i < n)%nat -> fr_entry_ok (rg_ei i).
Proof.
  intros i Hi. destruct HRI as (_ & (_ & _ & _ & Hent & _) & _). rewrite Forall_forall in Hent.
  apply Hent. apply nth_In. exact Hi.
Qed.
Lemma rg_key_ok : forall i, (i < n)%nat -> ~ In (Z_to_bv 8 0) (re_U (rg_ei i)) /\
  Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
    14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys (rg_ei i)).
Proof. intros i Hi. rewrite Forall_forall in HKEY. apply HKEY. apply nth_In. exact Hi. Qed.

(* the harness's held texts of an entry's source carry no 0 byte: they are its keys' texts *)
Lemma rg_held_nz : forall i, (i < n)%nat -> Forall nozero (texts (hs_held (rg_g0 i))).
Proof.
  intros i Hi. destruct (rg_pair i Hi) as (_ & _ & _ & _ & SS & _). destruct (rg_key_ok i Hi) as (_ & HK).
  rewrite Forall_forall in HK |- *. intros y Hy. apply (proj2 (SS y)) in Hy.
  unfold drain_b_c.keys_texts in Hy. apply in_map_iff in Hy as (k & <- & Hk).
  apply rg_nz_of. exact (proj1 (HK k Hk)).
Qed.
(* the lines drain reads: the partial line W is read only when skip = overlong = 0, and then bzs W = bzs U *)
Lemma rg_drained_lines_nz : forall i, (i < n)%nat -> re_eof (rg_ei i) = 0 -> Forall nozero (dr_lines (rg_g0 i)).
Proof.
  intros i Hi E0. destruct (rg_pair i Hi) as (_ & _ & _ & Hre & _). destruct (Hre E0) as (Hsk & HU).
  destruct (rg_key_ok i Hi) as (HUz & _). destruct (rg_entry_ok i Hi) as (_ & _ & _ & _ & Hsk01).
  exact (rg_W_read_lines_nz (rg_ei i) (rg_g0 i) Hsk01 Hsk HU HUz).
Qed.

(* what relay_instance_gone left of entry i: the keys after drain, the source's held and expected lists *)
Lemma rg_post_drain : forall i, (i < n)%nat ->
  NoDup (drain_b_c.keys_texts (re_keys (rg_ek i))) /\
  same_set (drain_b_c.keys_texts (re_keys (rg_ek i))) (upds (drain_b_c.keys_texts (re_keys (rg_ei i))) (rg_L i)) /\
  hs_held (rg_G i) = hs_held (rg_g0 i) /\
  map snd (hl_recs (hs_expected (rg_G i))) = map (map (Z_to_bv 8)) (rg_L i) /\
  texts (hs_expected (rg_G i)) = rg_L i.
Proof.
  intros i Hi. destruct (HEN i Hi) as (Hop & Hcl & _). rewrite rg_comb in Hop, Hcl. cbn [fst snd] in Hop, Hcl.
  destruct (rg_pair i Hi) as (_ & _ & _ & _ & _ & _ & Hexp0 & _). cbn [fst] in Hexp0.
  unfold rg_G, rg_L, rg_ek, rg_g0 in *.
  destruct (Z.eqb_spec (re_eof (rg_ei i)) 0) as [E0 | E0].
  - destruct (Hop E0) as (c & no & cap & LB & D). rewrite (rg_hs_open i Hi E0) in D. unfold dr_rel in D. cbv zeta in D.
    destruct D as (_ & _ & _ & _ & _ & _ & _ & _ & ND & SS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Mexp & _ &
      Hheld & _).
    assert (Mx : map snd (hl_recs (hs_expected (snd (nth i qs gn_q0)))) =
                 map (map (Z_to_bv 8)) (dr_lines (fst (nth i hj gn_hj0)))) by (rewrite Mexp, Hexp0; reflexivity).
    split; [exact ND|]. split; [exact SS|]. split; [exact Hheld|]. split; [exact Mx|].
    unfold texts.
    replace (map (fun r => bzs (snd r)) (hl_recs (hs_expected (snd (nth i qs gn_q0)))))
      with (map bzs (map snd (hl_recs (hs_expected (snd (nth i qs gn_q0)))))) by (rewrite List.map_map; reflexivity).
    rewrite Mx. apply fr_bzs_lines.
    exact (proj1 (SlotReads.lines_range (bzs (pending_stream (fst (nth i hj gn_hj0))))
      (hs_state (fst (nth i hj gn_hj0))) (SlotReads.zrange_bzs (hs_W (fst (nth i hj gn_hj0))))
      (SlotReads.zrange_bzs (pending_stream (fst (nth i hj gn_hj0)))))).
  - destruct (Hcl E0) as (-> & _).
    destruct (rg_entry_ok i Hi) as (_ & _ & _ & ND & _).
    split; [exact ND|]. split; [intros y; unfold upds; cbn [fold_left]; tauto|]. split; [reflexivity|].
    split; [rewrite Hexp0; reflexivity | unfold texts; rewrite Hexp0; reflexivity].
Qed.
Lemma rg_exp_nz : forall i, (i < n)%nat -> Forall nozero (rg_L i).
Proof.
  intros i Hi. unfold rg_L. destruct (Z.eqb_spec (re_eof (rg_ei i)) 0) as [E0 | E0]; [|constructor].
  exact (rg_drained_lines_nz i Hi E0).
Qed.
(* check_no_loss at entry i's slot: the held list it leaves has 0-free records, distinct texts, the keys' texts *)
Lemma rg_cnl : forall i h' E' H', (i < n)%nat -> gn_cnl_ok (rg_G i) h' E' H' ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') /\ NoDup (texts H') /\
  same_set (drain_b_c.keys_texts (re_keys (rg_ek i))) (texts H').
Proof.
  intros i h' E' H' Hi Hc. destruct Hc as (_ & _ & _ & _ & NDH & TH & _).
  destruct (rg_post_drain i Hi) as (_ & SS1 & Eheld & _ & Etx). rewrite Eheld, Etx in TH.
  split.
  - rewrite Forall_forall. intros r Hr. apply rg_nz_to.
    assert (Hin : In (bzs (snd r)) (texts H')) by (unfold texts; apply (in_map (fun r => bzs (snd r))); exact Hr).
    rewrite TH in Hin. destruct (rg_upds_in _ _ _ Hin) as [Hy | (l & x & Hl & Hg & Ex)].
    + exact (proj1 (Forall_forall _ _) (rg_held_nz i Hi) _ Hy).
    + rewrite Ex. destruct (rg_gesture l _ x Hg) as (Ex' & _ & _). rewrite Ex'. apply rg_nz_firstn.
      exact (proj1 (Forall_forall _ _) (rg_exp_nz i Hi) l Hl).
  - split; [exact NDH|]. rewrite TH.
    destruct (rg_pair i Hi) as (_ & _ & _ & _ & SS0 & _).
    exact (SlotReads.same_set_trans _ _ _ SS1 (SlotReads.upds_same_set (rg_L i) _ _ SS0)).
Qed.
Lemma rg_bzs_pre : bzs (gn_pre cx m) = pre.
Proof.
  unfold gn_pre. apply fr_bzs_line. destruct (SlotPass5Check.g5_pre_ok (gn_id cx m)) as (F & _).
  unfold SlotReads.zrange. eapply Forall_impl; [|exact F]. intros z Hz. cbv beta in Hz |- *. lia.
Qed.
(* the keys gestures_end_instance ends at entry i, against any held list with the keys' texts *)
Lemma rg_E : forall i, (i < n)%nat ->
  NoDup (map (fun k => bzs (gestures_end_b_c.key_text k)) (fst (geik pre (re_keys (rg_ek i))))) /\
  forall H', same_set (drain_b_c.keys_texts (re_keys (rg_ek i))) (texts H') -> forall y,
    In y (map (fun k => bzs (gestures_end_b_c.key_text k)) (fst (geik pre (re_keys (rg_ek i))))) <->
    In y (SlotReads.rtexts (hl_recs H')) /\ has_prefix (bzs (gn_pre cx m)) y = true.
Proof.
  intros i Hi. destruct (rg_post_drain i Hi) as (ND1 & _).
  destruct (rg_geik_texts pre _ ND1) as (_ & _ & EM). rewrite EM.
  pose proof (gei_ok pre (drain_b_c.keys_texts (re_keys (rg_ek i))) (proj1 (NoDup_ListNoDup _) ND1)) as G.
  destruct (gei pre (drain_b_c.keys_texts (re_keys (rg_ek i)))) as [E0 H0]. destruct G as (NE & _ & _ & SE & _).
  cbn [fst]. split; [exact (proj2 (NoDup_ListNoDup _) NE)|].
  intros H' SS y. rewrite (SE y), filter_In, rg_bzs_pre. change (SlotReads.rtexts (hl_recs H')) with (texts H').
  rewrite (SS y). tauto.
Qed.


(* ================================================================== the loop invariant over gn_run *)
Local Notation gn := (lm_gn m1).
Lemma rg_setn_len : forall k x l, length (gn_setn k x l) = length l.
Proof. induction k as [|k IH]; intros x [|y l]; cbn [gn_setn length]; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma rg_setn_same : forall k x l, (k < length l)%nat -> nth k (gn_setn k x l) None = x.
Proof.
  induction k as [|k IH]; intros x [|y l] H; cbn [length] in H; try lia; cbn [gn_setn nth]; [reflexivity|].
  apply IH. lia.
Qed.
Lemma rg_setn_other : forall k j x l, j <> k -> nth j (gn_setn k x l) None = nth j l None.
Proof.
  induction k as [|k IH]; intros [|j] x [|y l] H; cbn [gn_setn nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

Definition rg_bl (i : nat) : Z := Z.of_nat (length (bstream (hs_expected (rg_G i)))).
Fixpoint rg_acc (cs : list Z) (j : nat) : Z :=
  match j with O => 0 | S j' => rg_acc cs j' + rg_bl j' + nth j' cs 0 end.
Definition rg_A (cs : list Z) (j : nat) : Z := if gn =? 0 then rg_acc cs j else 0.
Definition rg_nd (i k : nat) : nat := if Nat.ltb i n && Nat.ltb (rg_sl i) k then S i else Nat.min i n.
Definition rg_done (i k i' : nat) : Prop := (i' < i)%nat \/ (i' = i /\ (rg_sl i < k)%nat).
Definition rg_DONE (cs : list Z) (i' : nat) (h'' : hsrc) : Prop :=
  exists h' E' H' ds, gn_cnl_ok (rg_G i') h' E' H' /\
    gn_cshe_ok (gn_pre cx m) gn (gn_at1 gn (rg_A cs i') (rg_G i')) (lm_O m1) h' h'' ds (nth i' cs 0).
Definition rg_INV (mc : lmod) (A : Z) (i k : nat) : Prop :=
  lm_O mc = lm_O m1 /\ lm_es mc = lm_es m1 /\ lm_gn mc = gn /\ length (lm_hs mc) = 4%nat /\
  exists cs, length cs = n /\ A = rg_A cs (rg_nd i k) /\
    (forall i', (i' < n)%nat ->
       (rg_done i k i' -> exists h'', nth (rg_sl i') (lm_hs mc) None = Some h'' /\ rg_DONE cs i' h'') /\
       (~ rg_done i k i' -> nth (rg_sl i') (lm_hs mc) None = Some (rg_G i'))) /\
    (forall j, (j < 4)%nat -> (forall i', (i' < n)%nat -> rg_sl i' <> j) -> nth j (lm_hs mc) None = None).

Lemma rg_acc_ext : forall cs cs' j, (forall i', (i' < j)%nat -> nth i' cs 0 = nth i' cs' 0) ->
  rg_acc cs j = rg_acc cs' j.
Proof.
  intros cs cs' j. induction j as [|j IH]; intros H; [reflexivity|]. cbn [rg_acc].
  rewrite IH by (intros i' Hi'; apply H; lia). rewrite (H j ltac:(lia)). reflexivity.
Qed.
Lemma rg_A_ext : forall cs cs' j, (forall i', (i' < j)%nat -> nth i' cs 0 = nth i' cs' 0) -> rg_A cs j = rg_A cs' j.
Proof. intros cs cs' j H. unfold rg_A. rewrite (rg_acc_ext cs cs' j H). reflexivity. Qed.
(* a processed source keeps its fd *)
Lemma rg_DONE_fd : forall cs i' h'', rg_DONE cs i' h'' -> hs_fd h'' = hs_fd (rg_G i').
Proof.
  intros cs i' h'' (h' & E' & H' & ds & (Eh' & _) & (H'' & Eh'' & _)). rewrite Eh'', Eh'. reflexivity.
Qed.
Lemma rg_m1_slots4 : length (lm_hs m1) = 4%nat.
Proof. destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
Lemma rg_gn_m1 : gn = lm_gn m.
Proof. destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

Lemma rg_done_dec : forall i k i', {rg_done i k i'} + {~ rg_done i k i'}.
Proof.
  intros i k i'. unfold rg_done. destruct (lt_dec i' i) as [H | H]; [left; left; exact H|].
  destruct (Nat.eq_dec i' i) as [E | E]; [|right; intros [D | (D1 & _)]; [exact (H D) | exact (E D1)]].
  destruct (lt_dec (rg_sl i) k) as [L | L]; [left; right; split; assumption|].
  right. intros [D | (_ & D2)]; [exact (H D) | exact (L D2)].
Qed.
(* the slot a call works on is entry i's, and it holds what relay_instance_gone left there *)
Lemma rg_call_slot : forall mc A i k h, rg_INV mc A i k -> (i < n)%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  k = rg_sl i /\ h = rg_G i /\ ~ rg_done i k i.
Proof.
  intros mc A i k h (_ & _ & _ & _ & cs & _ & _ & HS & HFree) Hi Hk Hh Hfd.
  rewrite rg_m1_es, (rg_q_fd i Hi) in Hfd.
  assert (Hex : exists i', (i' < n)%nat /\ rg_sl i' = k).
  { destruct (in_dec Nat.eq_dec k (map rg_sl (seq 0 n))) as [Hin | Hnin].
    - apply in_map_iff in Hin as (i' & Hs & Hi'). apply in_seq in Hi'. exists i'. split; [lia | exact Hs].
    - exfalso. rewrite (HFree k Hk) in Hh; [discriminate Hh|]. intros i' Hi' Hs. apply Hnin.
      apply in_map_iff. exists i'. split; [exact Hs | apply in_seq; lia]. }
  destruct Hex as (i' & Hi' & Hs). subst k. destruct (HS i' Hi') as (Hd & Hu).
  destruct (rg_done_dec i (rg_sl i') i') as [D | ND].
  - destruct (Hd D) as (h'' & Eh & HD). rewrite Eh in Hh. injection Hh as <-.
    rewrite (rg_DONE_fd cs i' h'' HD), (rg_G_fd i' Hi') in Hfd.
    pose proof (rg_fd_inj i' i Hi' Hi Hfd) as ->. exfalso. destruct D as [D | (_ & D)]; lia.
  - rewrite (Hu ND) in Hh. injection Hh as <-. rewrite (rg_G_fd i' Hi') in Hfd.
    pose proof (rg_fd_inj i' i Hi' Hi Hfd) as ->. split; [reflexivity|]. split; [reflexivity | exact ND].
Qed.

Lemma rg_inv : forall mc A i k, gn_run (gn_pre cx m) m1 mc A i k -> rg_INV mc A i k.
Proof.
  intros mc A i k R. induction R as [|mc A i k R IH Hk Hskip|mc A i k h h' h'' E' H' ds c R IH Hk Hi Hh Hfd Hcnl Hcshe
    |mc A i R IH].
  - (* gn_run0 *)
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact rg_m1_slots4|].
    exists (repeat 0 n). split; [apply repeat_length|].
    split; [assert (E : Nat.ltb (rg_sl 0) 0 = false) by (apply Nat.ltb_ge; lia);
      unfold rg_nd; rewrite E, andb_false_r; cbn [Nat.min]; unfold rg_A; destruct (gn =? 0); reflexivity|].
    split.
    + intros i' Hi'. split; [intros [D | (_ & D)]; lia|]. intros _. exact (rg_m1_slot i' Hi').
    + exact rg_m1_free.
  - (* skip *)
    destruct IH as (Q1 & Q2 & Q3 & Q4 & cs & Lc & HAc & HS & HFree).
    assert (Hnk : forall i0, i0 = i -> (i < n)%nat -> rg_sl i <> k).
    { intros i0 _ Hi Hs. assert (ND : ~ rg_done i k i) by (intros [D | (_ & D)]; lia).
      pose proof (proj2 (HS i Hi) ND) as Eh. rewrite Hs in Eh. destruct Hskip as [E | E].
      - rewrite Eh in E. discriminate E.
      - apply (E (rg_G i) Eh). rewrite rg_m1_es, (rg_q_fd i Hi). exact (rg_G_fd i Hi). }
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
    exists cs. split; [exact Lc|]. split.
    + rewrite HAc. f_equal. unfold rg_nd. destruct (Nat.ltb_spec i n) as [Hi | Hi]; [|reflexivity].
      cbn [andb]. pose proof (Hnk i eq_refl Hi).
      destruct (Nat.ltb_spec (rg_sl i) k), (Nat.ltb_spec (rg_sl i) (S k)); reflexivity || lia.
    + split; [|exact HFree]. intros i' Hi'.
      assert (Eq : rg_done i (S k) i' <-> rg_done i k i').
      { unfold rg_done. split; [|intros [D | (D1 & D2)]; [left; exact D | right; split; [exact D1 | lia]]].
        intros [D | (D1 & D2)]; [left; exact D|]. right. split; [exact D1|]. subst i'.
        pose proof (Hnk i eq_refl Hi'). lia. }
      rewrite Eq. exact (HS i' Hi').
  - (* call *)
    pose proof IH as IH0. destruct IH as (Q1 & Q2 & Q3 & Q4 & cs & Lc & HAc & HS & HFree).
    rewrite rg_m1_len in Hi.
    destruct (rg_call_slot mc A i k h IH0 Hi Hk Hh Hfd) as (-> & -> & ND).
    assert (Nd0 : rg_nd i (rg_sl i) = i).
    { unfold rg_nd. rewrite (proj2 (Nat.ltb_lt i n) Hi). cbn [andb].
      rewrite (proj2 (Nat.ltb_ge (rg_sl i) (rg_sl i)) (Nat.le_refl _)). lia. }
    assert (Nd1 : rg_nd i (S (rg_sl i)) = S i).
    { unfold rg_nd. rewrite (proj2 (Nat.ltb_lt i n) Hi). cbn [andb].
      rewrite (proj2 (Nat.ltb_lt (rg_sl i) (S (rg_sl i))) (Nat.lt_succ_diag_r _)). reflexivity. }
    set (cs' := rm_set_nth i c cs).
    assert (Lc' : length cs' = n) by (unfold cs'; rewrite fr_rm_set_nth_length; exact Lc).
    assert (Ecs : forall i', i' <> i -> nth i' cs' 0 = nth i' cs 0) by (intros i' Hne; apply fr_rm_set_nth_other; lia).
    assert (Ecs_i : nth i cs' 0 = c) by (unfold cs'; apply fr_rm_set_nth_same; lia).
    assert (EA : forall j, (j <= i)%nat -> rg_A cs' j = rg_A cs j).
    { intros j Hj. apply rg_A_ext. intros i' Hi'. apply Ecs. lia. }
    rewrite Nd0 in HAc.
    assert (Hc0 : gn <> 0 -> c = 0 /\ A = 0).
    { intros G. split; [|rewrite HAc; unfold rg_A; rewrite (proj2 (Z.eqb_neq _ _) G); reflexivity].
      destruct Hcshe as (H2 & _ & _ & _ & _ & _ & [(_ & _ & _ & C) | (G' & _)]); [exact C | contradiction]. }
    split; [unfold gn_set; cbn [lm_O]; exact Q1|]. split; [unfold gn_set; cbn [lm_es]; exact Q2|].
    split; [unfold gn_set; cbn [lm_gn]; exact Q3|]. split; [unfold gn_set; cbn [lm_hs]; rewrite rg_setn_len; exact Q4|].
    exists cs'. split; [exact Lc'|]. split.
    + rewrite Nd1. unfold rg_A in *. destruct (Z.eqb_spec gn 0) as [G | G].
      * cbn [rg_acc]. rewrite (rg_acc_ext cs' cs i ltac:(intros i' Hi'; apply Ecs; lia)), Ecs_i, <- HAc.
        unfold gn_at1, rg_bl. rewrite G. cbn [Z.eqb]. reflexivity.
      * destruct (Hc0 G) as (-> & ->). unfold gn_at1. rewrite (proj2 (Z.eqb_neq _ _) G). reflexivity.
    + split.
      * intros i' Hi'. unfold gn_set. cbn [lm_hs].
        destruct (Nat.eq_dec i' i) as [-> | Hne].
        -- split; [|intros N; exfalso; apply N; right; split; [reflexivity | lia]].
           intros _. exists h''. split; [apply rg_setn_same; rewrite Q4; exact (proj1 (rg_sl_ok i Hi))|].
           exists h', E', H', ds. split; [exact Hcnl|]. rewrite Ecs_i, (EA i (Nat.le_refl i)), <- HAc, <- Q1. exact Hcshe.
        -- assert (Hsl : rg_sl i' <> rg_sl i) by (intros E; apply Hne; exact (rg_sl_inj i' i Hi' Hi E)).
           rewrite (rg_setn_other _ _ _ _ Hsl).
           assert (Eq : rg_done i (S (rg_sl i)) i' <-> rg_done i (rg_sl i) i').
           { unfold rg_done. split; intros [D | (D1 & D2)]; try (left; exact D); exfalso; exact (Hne D1). }
           rewrite Eq. destruct (HS i' Hi') as (Hd & Hu). split; [|exact Hu].
           intros D. destruct (Hd D) as (h0 & Eh0 & (g1 & g2 & g3 & g4 & G1 & G2)). exists h0. split; [exact Eh0|].
           exists g1, g2, g3, g4. split; [exact G1|].
           assert (Hlt : (i' < i)%nat) by (destruct D as [D | (D1 & _)]; [exact D | exfalso; exact (Hne D1)]).
           rewrite (Ecs i' Hne), (EA i' ltac:(lia)). exact G2.
      * intros j Hj Hn. unfold gn_set. cbn [lm_hs].
        rewrite rg_setn_other; [exact (HFree j Hj Hn)|]. intros E. exact (Hn i Hi (eq_sym E)).
  - (* next *)
    destruct IH as (Q1 & Q2 & Q3 & Q4 & cs & Lc & HAc & HS & HFree).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
    exists cs. split; [exact Lc|]. split.
    + rewrite HAc. f_equal.
      assert (Z0 : Nat.ltb (rg_sl (S i)) 0 = false) by (apply Nat.ltb_ge; lia).
      unfold rg_nd. rewrite Z0, andb_false_r.
      destruct (Nat.ltb_spec i n) as [Hi | Hi]; cbn [andb].
      * rewrite (proj2 (Nat.ltb_lt _ 4) (proj1 (rg_sl_ok i Hi))). lia.
      * lia.
    + split; [|exact HFree]. intros i' Hi'.
      assert (Eq : rg_done (S i) 0 i' <-> rg_done i 4 i').
      { unfold rg_done. pose proof (proj1 (rg_sl_ok i' Hi')) as S4. split.
        - intros [D | (D1 & D2)]; [|lia].
          destruct (Nat.eq_dec i' i) as [-> | Hne]; [right; split; [reflexivity | exact S4] | left; lia].
        - intros [D | (D1 & D2)]; left; lia. }
      rewrite Eq. exact (HS i' Hi').
Qed.

(* ================================================================== the stream, entry by entry *)
Hypothesis HO0 : lm_O m = [].
Hypothesis HLIVE : sl_live (lm_c m) 1 = true -> bzs O2 = bzs (lm_O m) ++ rg_strm pre (combine (lm_es m) hs) e1s.
Hypothesis HDEAD : sl_live (lm_c m) 1 = false -> O2 = lm_O m.

Definition rg_seg (i : nat) : list Z := with_nul (rg_L i) ++ rg_endz pre (rg_ek i).
Definition rg_segs : list (list Z) := map rg_seg (seq 0 n).
Definition rg_pos (i : nat) : nat := length (concat (firstn i rg_segs)).

Lemma rg_strm_gen : forall ps (f1s : list rentry), length f1s = length ps ->
  rg_strm pre ps f1s = concat (map (fun i =>
    (if re_eof (fst (nth i ps (gn_e0, gn_hj0))) =? 0 then with_nul (dr_lines (fst (snd (nth i ps (gn_e0, gn_hj0)))))
     else []) ++ rg_endz pre (nth i f1s gn_e0)) (seq 0 (length ps))).
Proof.
  induction ps as [|p r IH]; intros [|e1 r1] L; cbn [length] in L; try discriminate L; [reflexivity|].
  cbn [rg_strm length seq map concat nth]. rewrite <- app_assoc. f_equal. f_equal.
  rewrite (IH r1) by lia. rewrite <- seq_shift, List.map_map. reflexivity.
Qed.
Lemma rg_segs_len : length rg_segs = n.
Proof. unfold rg_segs. rewrite length_map, length_seq. reflexivity. Qed.
Lemma rg_segs_nth : forall i, (i < n)%nat -> nth i rg_segs [] = rg_seg i.
Proof.
  intros i Hi. unfold rg_segs. rewrite (nth_indep _ [] (rg_seg 0)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.
Lemma rg_strm_segs : rg_strm pre (combine (lm_es m) hs) e1s = concat rg_segs.
Proof.
  rewrite rg_strm_gen by (rewrite length_combine, rg_lhs, HLE, Nat.min_id; reflexivity).
  rewrite length_combine, rg_lhs, Nat.min_id. unfold rg_segs. f_equal. apply map_ext_in. intros i Hi.
  apply in_seq in Hi. rewrite rg_comb. cbn [fst snd]. unfold rg_seg, rg_L, rg_ek. f_equal.
  destruct (Z.eqb_spec (re_eof (rg_ei i)) 0) as [E0 | E0]; [|reflexivity].
  rewrite (rg_hs_open i ltac:(lia) E0). reflexivity.
Qed.
Lemma rg_live_gn0 : gn = 0 -> sl_live (lm_c m) 1 = true.
Proof.
  intros G. rewrite rg_gn_m1 in G. destruct HRI as (_ & _ & _ & (G0 & _)). destruct (G0 G) as (C1 & C2 & C3).
  unfold sl_live, send_line_c.send_live, send_line_c.send_off. rewrite C1, C2, C3. reflexivity.
Qed.
Lemma rg_O2_gn0 : gn = 0 -> bzs O2 = concat rg_segs.
Proof. intros G. rewrite (HLIVE (rg_live_gn0 G)), HO0, rg_strm_segs. reflexivity. Qed.
Lemma rg_L_range : forall i, (i < n)%nat -> Forall SlotReads.zrange (rg_L i).
Proof.
  intros i Hi. unfold rg_L. destruct (re_eof (rg_ei i) =? 0); [|constructor].
  exact (proj1 (SlotReads.lines_range (bzs (pending_stream (rg_g0 i))) (hs_state (rg_g0 i))
    (SlotReads.zrange_bzs (hs_W (rg_g0 i))) (SlotReads.zrange_bzs (pending_stream (rg_g0 i))))).
Qed.
Lemma rg_bl_eq : forall i, (i < n)%nat ->
  bzs (bstream (hs_expected (rg_G i))) = with_nul (rg_L i) /\ rg_bl i = Z.of_nat (length (with_nul (rg_L i))).
Proof.
  intros i Hi. destruct (rg_post_drain i Hi) as (_ & _ & _ & Mx & _).
  pose proof (SlotReads.bstream_bzs _ _ Mx (rg_L_range i Hi)) as B. split; [exact B|].
  unfold rg_bl. rewrite <- B. unfold bzs. rewrite length_map. reflexivity.
Qed.
Lemma rg_firstn_S : forall (L : list (list Z)) j, (j < length L)%nat ->
  concat (firstn (S j) L) = concat (firstn j L) ++ nth j L [].
Proof. intros L j H. rewrite (SlotPass5Check.g5_firstn_S L j [] H), concat_app. cbn [concat]. rewrite app_nil_r. reflexivity. Qed.
Lemma rg_done_of_nd : forall i k i', (i' < rg_nd i k)%nat -> (i' < n)%nat -> rg_done i k i'.
Proof.
  intros i k i' H Hn. unfold rg_nd in H. unfold rg_done.
  destruct (Nat.ltb i n && Nat.ltb (rg_sl i) k) eqn:E.
  - apply andb_true_iff in E as [_ E]. apply Nat.ltb_lt in E.
    destruct (Nat.eq_dec i' i) as [-> | Hne]; [right; split; [reflexivity | exact E] | left; lia].
  - left. lia.
Qed.
(* at gone = 0, check_shape_ends consumed exactly entry j's ended-key lines, so `at` is the stream's position *)
Lemma rg_acc_pos : forall (mc : lmod) i k cs,
  (forall i', (i' < n)%nat -> rg_done i k i' -> exists h'', nth (rg_sl i') (lm_hs mc) None = Some h'' /\ rg_DONE cs i' h'') ->
  gn = 0 -> forall j, (j <= rg_nd i k)%nat -> (j <= n)%nat -> rg_acc cs j = Z.of_nat (rg_pos j).
Proof.
  intros mc i k cs HS G. induction j as [|j IH]; intros Hj Hjn; [reflexivity|].
  destruct (HS j ltac:(lia) (rg_done_of_nd i k j ltac:(lia) ltac:(lia))) as (h'' & _ & (h' & E' & H' & ds & Hc & Hs)).
  pose proof (IH ltac:(lia) ltac:(lia)) as IHj.
  destruct (rg_bl_eq j ltac:(lia)) as (_ & Bl).
  destruct (rg_cnl j h' E' H' ltac:(lia) Hc) as (NZ & NDH & SSH).
  destruct (rg_E j ltac:(lia)) as (NE & CE).
  assert (Hh' : hs_held h' = H') by (destruct Hc as (-> & _); reflexivity).
  destruct Hs as (H'' & _ & _ & _ & _ & _ & [(G' & _) | (_ & ER)]); [contradiction|].
  rewrite Hh' in ER. unfold gn_at1, rg_A in ER. rewrite G in ER. cbn [Z.eqb] in ER.
  change (Z.of_nat (length (bstream (hs_expected (rg_G j))))) with (rg_bl j) in ER. rewrite IHj, Bl in ER.
  destruct HA as (_ & _ & _ & _ & EO & _). rewrite EO in ER.
  assert (Hseg : nth j rg_segs [] = with_nul (rg_L j) ++ rg_endz pre (rg_ek j)) by (rewrite rg_segs_nth by lia; reflexivity).
  pose proof (SlotPass5Check.g5_skip_in rg_segs j O2 (with_nul (rg_L j)) (rg_endz pre (rg_ek j)) _
    ltac:(rewrite rg_segs_len; lia) (rg_O2_gn0 G) Hseg eq_refl) as SK.
  unfold rg_pos in ER. unfold rg_endz in SK.
  destruct (rg_ends_res (gn_pre cx m) _ (hl_recs H') _ _ (hl_recs H'') ds (nth j cs 0) NE NDH (CE H' SSH) NZ SK ER)
    as (Ec & _).
  cbn [rg_acc]. rewrite IHj, Bl, Ec. unfold rg_pos. rewrite rg_firstn_S by (rewrite rg_segs_len; lia).
  rewrite length_app, Hseg, length_app. unfold rg_endz. lia.
Qed.

(* ================================================================== GN_RI_step's RINV-side conjuncts *)
Hypothesis HC : fr_cost (lm_es m) hj <= c_n cx.

Lemma rg_in_comb_hj : forall i, (i < n)%nat -> In (rg_ei i, (rg_g0 i, rg_sl i)) (combine (lm_es m) hj).
Proof.
  intros i Hi. assert (E : (rg_g0 i, rg_sl i) = nth i hj gn_hj0)
    by (unfold rg_g0, rg_sl; destruct (nth i hj gn_hj0); reflexivity).
  rewrite E. unfold rg_ei. rewrite <- combine_nth by (rewrite rg_lhj; reflexivity).
  apply nth_In. rewrite length_combine, rg_lhj, Nat.min_id. exact Hi.
Qed.
Lemma rg_counts_i : forall i, (i < n)%nat ->
  hl_n (hs_held (rg_G i)) + Z.of_nat (count_begin (texts (hs_expected (rg_G i)))) < 2 ^ 22 /\
  Z.of_nat (length (rg_L i)) < 2 ^ 26.
Proof.
  intros i Hi. destruct (rg_post_drain i Hi) as (_ & _ & Eheld & _ & Etx). rewrite Eheld, Etx.
  destruct (rg_pair i Hi) as (_ & _ & _ & Hre & SS & NDh & _).
  destruct (rg_entry_ok i Hi) as (_ & _ & _ & NDk & Hsk).
  destruct (rg_key_ok i Hi) as (_ & HK).
  assert (K14 : Forall (fun x => 14 <= Z.of_nat (length (gestures_end_b_c.key_text x))) (re_keys (rg_ei i)))
    by (eapply Forall_impl; [|exact HK]; intros kk (_ & Hk & _); exact Hk).
  pose proof HRI as (_ & _ & Hn & _).
  unfold rg_L. destruct (Z.eqb_spec (re_eof (rg_ei i)) 0) as [E0 | E0].
  - destruct (Hre E0) as (S1 & W1).
    apply (rg_counts_drain (lm_es m) hj (rg_ei i) (rg_g0 i) (rg_sl i) (c_n cx) (rg_in_comb_hj i Hi) HC Hn K14
      SS NDh NDk S1 W1). change (hs_overlong (rg_g0 i)) with (hs_overlong (fst (nth i hj gn_hj0))).
    rewrite <- S1. exact Hsk.
  - apply (rg_counts (lm_es m) hj (rg_ei i) (rg_g0 i) (rg_sl i) [] (c_n cx) (rg_in_comb_hj i Hi) HC Hn K14
      SS NDh NDk). cbn [with_nul map concat length].
    destruct (re_skip (rg_ei i) =? 0); lia.
Qed.
Lemma rg_exp_n : forall i, hl_n (hs_expected (rg_G i)) = Z.of_nat (length (rg_L i)) \/ (n <= i)%nat.
Proof.
  intros i. destruct (lt_dec i n) as [Hi | Hi]; [left | right; lia].
  destruct (rg_post_drain i Hi) as (_ & _ & _ & Mx & _). unfold hl_n.
  apply (f_equal (@length (list byte))) in Mx. rewrite !length_map in Mx. rewrite Mx. reflexivity.
Qed.
Lemma rg_concat_firstn_le : forall (L : list (list Z)) j, (length (concat (firstn j L)) <= length (concat L))%nat.
Proof.
  intros L j. rewrite <- (firstn_skipn j L) at 2. rewrite concat_app, length_app. lia.
Qed.
Lemma rg_O2_len_gn0 : gn = 0 -> length O2 = length (concat rg_segs).
Proof. intros G. rewrite <- (rg_O2_gn0 G). unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rg_bzs_prefix : forall (x y : list byte) z, bzs x = bzs y ++ z -> exists r, x = y ++ r.
Proof.
  intros x y z E. exists (skipn (length y) x). rewrite <- (firstn_skipn (length y) x) at 1. f_equal.
  apply SlotReads.bzs_inj.
  assert (F : bzs (firstn (length y) x) = firstn (length y) (bzs x)) by (unfold bzs; rewrite firstn_map; reflexivity).
  rewrite F, E. replace (length y) with (length (bzs y)) by (unfold bzs; apply length_map).
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r.
Qed.
Lemma rg_pos_le : forall j, (rg_pos j <= length (concat rg_segs))%nat.
Proof. intros j. apply rg_concat_firstn_le. Qed.
Lemma rg_pos_S : forall j, (j < n)%nat -> rg_pos (S j) = (rg_pos j + length (rg_seg j))%nat.
Proof.
  intros j Hj. unfold rg_pos. rewrite rg_firstn_S by (rewrite rg_segs_len; exact Hj).
  rewrite length_app, rg_segs_nth by exact Hj. reflexivity.
Qed.

(* the call's state: `at` is entry i's position in the stream when gone = 0, else 0 *)
Lemma rg_call_A : forall mc A i k h, gn_run (gn_pre cx m) m1 mc A i k ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat -> nth k (lm_hs mc) None = Some h ->
  hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (i < n)%nat /\ k = rg_sl i /\ h = rg_G i /\ lm_O mc = O2 /\
  A = (if gn =? 0 then Z.of_nat (rg_pos i) else 0).
Proof.
  intros mc A i k h R Hi Hk Hh Hfd. rewrite rg_m1_len in Hi.
  pose proof (rg_inv mc A i k R) as INV.
  destruct (rg_call_slot mc A i k h INV Hi Hk Hh Hfd) as (-> & -> & ND).
  destruct INV as (Q1 & _ & _ & _ & cs & _ & HAc & HS & _).
  split; [exact Hi|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite Q1; destruct HA as (_ & _ & _ & _ & EO & _); exact EO|].
  assert (Nd0 : rg_nd i (rg_sl i) = i).
  { unfold rg_nd. rewrite (proj2 (Nat.ltb_lt i n) Hi). cbn [andb].
    rewrite (proj2 (Nat.ltb_ge (rg_sl i) (rg_sl i)) (Nat.le_refl _)). lia. }
  rewrite HAc, Nd0. unfold rg_A. destruct (Z.eqb_spec gn 0) as [G | G]; [|reflexivity].
  apply (rg_acc_pos mc i (rg_sl i) cs (fun i' Hi' D => proj1 (HS i' Hi') D) G i); [rewrite Nd0; lia | lia].
Qed.

Lemma rg_step_rinv : forall mc A i k h, gn_run (gn_pre cx m) m1 mc A i k ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  (forall h' E' H', gn_cnl_ok h h' E' H' ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None)).
Proof.
  intros mc A i k h R Hi0 Hk Hh Hfd.
  destruct (rg_call_A mc A i k h R Hi0 Hk Hh Hfd) as (Hi & -> & -> & EO & EA). rewrite EO.
  destruct (rg_counts_i i Hi) as (Hcnt & HLn).
  destruct (rg_post_drain i Hi) as (_ & _ & Eheld & _ & Etx).
  destruct (rg_pair i Hi) as (_ & _ & _ & _ & _ & NDh & _ & _ & Hhc & _).
  destruct (rg_bl_eq i Hi) as (Bz & Bl).
  assert (Hseg : nth i rg_segs [] = with_nul (rg_L i) ++ rg_endz pre (rg_ek i))
    by (rewrite rg_segs_nth by exact Hi; reflexivity).
  assert (Hpi : (rg_pos i + length (with_nul (rg_L i)) <= length (concat rg_segs))%nat).
  { pose proof (rg_pos_le (S i)) as L1. rewrite (rg_pos_S i Hi) in L1. unfold rg_seg in L1.
    rewrite length_app in L1. lia. }
  split; [rewrite Eheld; exact NDh|].
  split; [destruct (rg_exp_n i) as [E | E]; [rewrite E; exact HLn | lia]|].
  split; [exact Hcnt|].
  split.
  { rewrite EA. destruct (Z.eqb_spec gn 0) as [G | G]; [|split; lia].
    rewrite (rg_O2_len_gn0 G). pose proof (rg_pos_le i). lia. }
  split.
  { intros G. rewrite EA, (proj2 (Z.eqb_eq _ _) G), Nat2Z.id.
    pose proof (SlotPass5Check.g5_skip_in rg_segs i O2 [] (nth i rg_segs []) 0%nat
      ltac:(rewrite rg_segs_len; exact Hi) (rg_O2_gn0 G) eq_refl eq_refl) as SK.
    rewrite <- Nat2Z.inj_add, Nat2Z.id, Nat.add_0_r in SK. fold (rg_pos i) in SK.
    rewrite Hseg, <- Bz, <- app_assoc in SK.
    exact (rg_bzs_prefix _ _ _ SK). }
  split.
  { rewrite Eheld. assert (P24 : 2 ^ 24 = 16777216) by reflexivity. assert (P22 : 2 ^ 22 = 4194304) by reflexivity.
    assert (P32 : 2 ^ 32 = 4294967296) by reflexivity. rewrite Eheld in Hcnt. unfold AREC.
    unfold rg_g0, hl_n in *. cbn [fst] in *. lia. }
  intros h' E' H' Hc.
  assert (Hh' : hs_held h' = H') by (destruct Hc as (-> & _); reflexivity).
  split.
  { rewrite Hh'. destruct Hc as (_ & _ & _ & _ & _ & TH & _).
    exact (SlotPass5Check.g5_held_n (hs_held (rg_G i)) H' (hs_expected (rg_G i)) TH Hcnt). }
  split.
  { unfold gn_at1. rewrite EA. destruct (Z.eqb_spec gn 0) as [G | G]; [|lia].
    rewrite (rg_O2_len_gn0 G). fold (rg_bl i). rewrite Bl. lia. }
  intros G. rewrite Hh'. unfold gn_at1. rewrite EA, (proj2 (Z.eqb_eq _ _) G).
  fold (rg_bl i). rewrite Bl, <- Nat2Z.inj_add.
  pose proof (SlotPass5Check.g5_skip_in rg_segs i O2 (with_nul (rg_L i)) (rg_endz pre (rg_ek i))
    (length (with_nul (rg_L i))) ltac:(rewrite rg_segs_len; exact Hi) (rg_O2_gn0 G) Hseg eq_refl) as SK.
  rewrite <- Nat2Z.inj_add in SK. fold (rg_pos i) in SK. unfold rg_endz in SK.
  destruct (rg_cnl i h' E' H' Hi Hc) as (NZ & NDH & SSH).
  destruct (rg_E i Hi) as (NE & CE).
  destruct (SlotPass5Check.g5_ends (gn_pre cx m) _ (hl_recs H') _ _ NE NDH (CE H' SSH) NZ SK) as (rs' & ds & ER).
  rewrite ER. discriminate.
Qed.

(* ================================================================== the stream's length *)
Lemma rg_zsum_le : forall (l : list nat) (f g : nat -> Z), (forall i, In i l -> f i <= g i) ->
  fold_right Z.add 0 (map f l) <= fold_right Z.add 0 (map g l).
Proof.
  induction l as [|x l IH]; intros f g H; cbn [map fold_right]; [lia|].
  pose proof (H x (or_introl eq_refl)). pose proof (IH f g (fun i Hi => H i (or_intror Hi))). lia.
Qed.
Lemma rg_concat_len : forall (L : list (list Z)),
  Z.of_nat (length (concat L)) = fold_right Z.add 0 (map (fun x => Z.of_nat (length x)) L).
Proof. induction L as [|x L IH]; cbn [concat map fold_right]; [reflexivity|]. rewrite length_app. lia. Qed.
Lemma rg_combine_seq : forall (X Y : Type) (l1 : list X) (l2 : list Y) d1 d2, length l1 = length l2 ->
  combine l1 l2 = map (fun i => (nth i l1 d1, nth i l2 d2)) (seq 0 (length l1)).
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] d1 d2 L; cbn [length] in L; try discriminate L;
    [reflexivity|].
  cbn [combine length seq map nth]. f_equal. rewrite (IH l2 d1 d2) by lia. rewrite <- seq_shift, List.map_map.
  reflexivity.
Qed.
Lemma rg_cost_seq : fr_cost (lm_es m) hj =
  fold_right Z.add 0 (map (fun i => fr_pair_cost (rg_ei i) (rg_g0 i, rg_sl i)) (seq 0 n)).
Proof.
  unfold fr_cost. rewrite (rg_combine_seq _ _ (lm_es m) hj gn_e0 gn_hj0) by (rewrite rg_lhj; reflexivity).
  rewrite List.map_map. f_equal.
Qed.
Lemma rg_seg_le : forall i, (i < n)%nat -> Z.of_nat (length (rg_seg i)) <= 2 * fr_pair_cost (rg_ei i) (rg_g0 i, rg_sl i).
Proof.
  intros i Hi. destruct (HEN i Hi) as (Hop & Hcl & _). rewrite rg_comb in Hop, Hcl. cbn [fst snd] in Hop, Hcl.
  pose proof (rg_pair i Hi) as HP0. change (fr_pair_ok m t (rg_ei i) (rg_g0 i, rg_sl i)) in HP0.
  assert (Hdr : re_eof (rg_ei i) = 0 -> exists c no cap LB, dr_rel c (lm_mx m) no cap (rg_ei i) (rg_g0 i) (rg_ek i)
    (snd (nth i qs gn_q0)) LB).
  { intros E0. destruct (Hop E0) as (c & no & cap & LB & D). exists c, no, cap, LB.
    unfold rg_g0. rewrite <- (rg_hs_open i Hi E0). exact D. }
  destruct (Z.eq_dec (re_eof (rg_ei i)) 0) as [E0 | E0].
  - destruct (Hdr E0) as (c & no & cap & LB & D).
    pose proof (rg_seg_len m t (rg_ei i) (rg_g0 i) (rg_sl i) c (lm_mx m) no cap (rg_ek i) (snd (nth i qs gn_q0)) LB
      pre (rg_entry_ok i Hi) HP0 (fun _ => D) (fun N => False_ind _ (N E0))) as L.
    unfold rg_seg, rg_L, rg_endz. rewrite (proj2 (Z.eqb_eq _ _) E0) in L |- *. exact L.
  - pose proof (rg_seg_len m t (rg_ei i) (rg_g0 i) (rg_sl i) (CTL 0 0 0 0 0) 0 0 0 (rg_ek i) (rg_g0 i) []
      pre (rg_entry_ok i Hi) HP0 (fun E => False_ind _ (E0 E)) (fun _ => proj1 (Hcl E0))) as L.
    unfold rg_seg, rg_L, rg_endz. rewrite (proj2 (Z.eqb_neq _ _) E0) in L |- *. exact L.
Qed.
Lemma rg_O2_len : Z.of_nat (length O2) < 2 ^ 32.
Proof.
  destruct (sl_live (lm_c m) 1) eqn:L.
  - assert (E : length O2 = length (concat rg_segs)).
    { assert (Eb : bzs O2 = concat rg_segs) by (rewrite (HLIVE eq_refl), HO0, rg_strm_segs; reflexivity).
      rewrite <- Eb. unfold bzs. rewrite length_map. reflexivity. }
    rewrite E, rg_concat_len. unfold rg_segs. rewrite List.map_map.
    pose proof (rg_zsum_le (seq 0 n) _ (fun i => 2 * fr_pair_cost (rg_ei i) (rg_g0 i, rg_sl i))
      (fun i Hi => rg_seg_le i ltac:(apply in_seq in Hi; lia))) as S.
    assert (S2 : forall l : list nat, fold_right Z.add 0 (map (fun i => 2 * fr_pair_cost (rg_ei i) (rg_g0 i, rg_sl i)) l)
      = 2 * fold_right Z.add 0 (map (fun i => fr_pair_cost (rg_ei i) (rg_g0 i, rg_sl i)) l))
      by (induction l as [|x l IH]; cbn [map fold_right]; lia).
    rewrite S2, <- rg_cost_seq in S. pose proof HRI as (_ & _ & Hn & _).
    assert (P : 2 ^ 26 = 67108864) by reflexivity. assert (P32 : 2 ^ 32 = 4294967296) by reflexivity. lia.
  - rewrite (HDEAD eq_refl), HO0. cbn. lia.
Qed.

(* ================================================================== GN_RI_end's RINV-side conjuncts *)
Hypothesis HCTL : forall g, fr_ctl_ok g (lm_c m) -> fr_ctl_ok g c2.
Hypothesis HT : 0 <= t < OPS_MAX.
Hypothesis HQM : Forall gn_entry_model (map fst qs).
Hypothesis HQF : NoDup (map re_fd (map fst qs)).

Lemma rg_kp_cons : forall (P : list byte) (r : Z * list byte) (l : list (Z * list byte)),
  filter (fun x => negb (prefixb P (snd x))) (r :: l) =
  if prefixb P (snd r) then filter (fun x => negb (prefixb P (snd x))) l
  else r :: filter (fun x => negb (prefixb P (snd x))) l.
Proof.
  intros P r l. rewrite list_basics.list.filter_cons.
  destruct (prefixb P (snd r)) eqn:E; match goal with |- context [decide ?X] => destruct (decide X) as [D|D] end;
    cbn in D |- *; first [reflexivity | (exfalso; apply D; rewrite E; exact I) | (rewrite E in D; contradiction)
    | contradiction].
Qed.
Lemma rg_kp_in : forall (P : list byte) (l : list (Z * list byte)) r,
  In r (filter (fun x => negb (prefixb P (snd x))) l) <-> In r l /\ prefixb P (snd r) = false.
Proof.
  intros P l r. induction l as [|x l IH]; [cbn; tauto|]. rewrite rg_kp_cons.
  destruct (prefixb P (snd x)) eqn:E; cbn [In]; rewrite ?IH; split.
  - intros (Hr & Hp). split; [right; exact Hr | exact Hp].
  - intros ([<- | Hr] & Hp); [rewrite E in Hp; discriminate Hp | split; assumption].
  - intros [<- | (Hr & Hp)]; [split; [left; reflexivity | exact E] | split; [right; exact Hr | exact Hp]].
  - intros ([<- | Hr] & Hp); [left; reflexivity | right; split; assumption].
Qed.

Lemma rg_run_keep : forall P mc A i k, gn_run P m1 mc A i k ->
  lm_nfd mc = lm_nfd m1 /\ lm_k mc = lm_k m1 /\ lm_c mc = lm_c m1.
Proof.
  intros P mc A i k R. induction R; [auto | exact IHR | | exact IHR].
  unfold gn_set. cbn [lm_nfd lm_k lm_c]. exact IHR.
Qed.
(* a processed entry's slot: what check_shape_ends kept is the held list minus the prefixed texts *)
Lemma rg_done_surv : forall cs i h'', (i < n)%nat -> rg_DONE cs i h'' ->
  (gn = 0 -> rg_acc cs i = Z.of_nat (rg_pos i)) ->
  exists h' E' H' H'', gn_cnl_ok (rg_G i) h' E' H' /\ h'' = set_held h' H'' /\ hl_cap H'' = hl_cap (hs_held h') /\
    NoDup (texts H'') /\ (forall y, In y (texts H'') <-> In y (texts H') /\ has_prefix pre y = false).
Proof.
  intros cs i h'' Hi (h' & E' & H' & ds & Hc & (H'' & Eh'' & _ & Hcap & NDH'' & _ & Hcase)) Hpos.
  exists h', E', H', H''. split; [exact Hc|]. split; [exact Eh''|]. split; [exact Hcap|]. split; [exact NDH''|].
  assert (Hh' : hs_held h' = H') by (destruct Hc as (-> & _); reflexivity). rewrite Hh' in Hcase.
  destruct Hcase as [(G & Ef & _ & _) | (G & ER)].
  - intros y. unfold texts. rewrite Ef. rewrite <- rg_bzs_pre. split.
    + intros Hy. apply in_map_iff in Hy as (r & <- & Hr). apply rg_kp_in in Hr as (Hr & Hp).
      rewrite SlotPass5Check.g5_prefixb in Hp.
      split; [apply in_map_iff; exists r; split; [reflexivity | exact Hr] | exact Hp].
    + intros (Hy & Hp). apply in_map_iff in Hy as (r & <- & Hr). apply in_map_iff. exists r.
      split; [reflexivity|]. apply rg_kp_in. split; [exact Hr|].
      rewrite SlotPass5Check.g5_prefixb. exact Hp.
  - destruct (rg_bl_eq i Hi) as (_ & Bl).
    unfold gn_at1, rg_A in ER. rewrite G in ER. cbn [Z.eqb] in ER.
    change (Z.of_nat (length (bstream (hs_expected (rg_G i))))) with (rg_bl i) in ER.
    rewrite (Hpos G), Bl, <- Nat2Z.inj_add, Nat2Z.id in ER.
    destruct HA as (_ & _ & _ & _ & EO & _). rewrite EO in ER.
    assert (Hseg : nth i rg_segs [] = with_nul (rg_L i) ++ rg_endz pre (rg_ek i))
      by (rewrite rg_segs_nth by exact Hi; reflexivity).
    pose proof (SlotPass5Check.g5_skip_in rg_segs i O2 (with_nul (rg_L i)) (rg_endz pre (rg_ek i))
      (length (with_nul (rg_L i))) ltac:(rewrite rg_segs_len; exact Hi) (rg_O2_gn0 G) Hseg eq_refl) as SK.
    rewrite <- Nat2Z.inj_add, Nat2Z.id in SK. fold (rg_pos i) in SK. unfold rg_endz in SK.
    destruct (rg_cnl i h' E' H' Hi Hc) as (NZ & NDH & SSH).
    destruct (rg_E i Hi) as (NE & CE).
    destruct (rg_ends_res (gn_pre cx m) _ (hl_recs H') _ _ (hl_recs H'') ds (nth i cs 0) NE NDH (CE H' SSH) NZ SK ER)
      as (_ & _ & HT3 & _).
    intros y. change (texts H'') with (SlotReads.rtexts (hl_recs H'')). change (texts H') with (SlotReads.rtexts (hl_recs H')).
    rewrite (HT3 y), rg_bzs_pre. reflexivity.
Qed.

Hypothesis HCK : fr_cost (lm_es m) hj <= lm_k m.

(* the loop's end: every entry's slot is processed, the free slots are closed *)
Lemma rg_end_state : forall mc A, gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  lm_O mc = O2 /\ lm_es mc = lm_es m1 /\ lm_gn mc = gn /\ length (lm_hs mc) = 4%nat /\
  exists cs, A = rg_A cs n /\
    (forall i, (i < n)%nat -> exists h'', nth (rg_sl i) (lm_hs mc) None = Some h'' /\ rg_DONE cs i h'') /\
    (forall i, (i < n)%nat -> rg_done n 0 i) /\
    (forall j, (j < 4)%nat -> (forall i', (i' < n)%nat -> rg_sl i' <> j) -> nth j (lm_hs mc) None = None).
Proof.
  intros mc A R. rewrite rg_m1_len in R. destruct (rg_inv mc A n 0 R) as (Q1 & Q2 & Q3 & Q4 & cs & _ & HAc & HS & HF0).
  assert (Nd : rg_nd n 0 = n) by (unfold rg_nd; rewrite Nat.ltb_irrefl; cbn [andb]; apply Nat.min_id).
  assert (D : forall i, (i < n)%nat -> rg_done n 0 i) by (intros i Hi; left; exact Hi).
  split; [rewrite Q1; destruct HA as (_ & _ & _ & _ & EO & _); exact EO|].
  split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
  exists cs. split; [rewrite HAc, Nd; reflexivity|]. split; [|split; [exact D | exact HF0]].
  intros i Hi. exact (proj1 (HS i Hi) (D i Hi)).
Qed.
Lemma rg_live_gn1 : gn = 1 -> sl_live (lm_c m) 1 = false.
Proof.
  intros G. rewrite rg_gn_m1 in G. destruct HRI as (_ & _ & _ & (_ & G1)). specialize (G1 G).
  destruct (lm_c m) as [cl br dd ei ev]. cbn [ct_cl ct_br ct_dd] in G1.
  unfold sl_live, send_line_c.send_live, send_line_c.send_off. cbn [ct_cl ct_br ct_dd].
  destruct G1 as [-> | [-> | ->]]; [reflexivity | destruct (cl <? 0); reflexivity | apply Bool.andb_false_r].
Qed.
Lemma rg_nopen_eq : forall l1 l2 : list (option hsrc), length l1 = length l2 ->
  (forall j, (nth j l1 None = None <-> nth j l2 None = None)) -> nopen l1 = nopen l2.
Proof.
  unfold nopen. intros l1 l2 L H. f_equal. revert l2 L H.
  induction l1 as [|o1 l1 IH]; intros [|o2 l2] L H; cbn [length] in L; try discriminate L; [reflexivity|].
  pose proof (H 0%nat) as H0. cbn [nth] in H0.
  assert (IHr : length (List.filter (fun o => match o with Some _ => true | None => false end) l1) =
                length (List.filter (fun o => match o with Some _ => true | None => false end) l2))
    by (apply IH; [lia | intros j; exact (H (S j))]).
  destruct o1 as [x1|], o2 as [x2|]; cbn [List.filter length]; try rewrite IHr; try reflexivity;
    exfalso; destruct H0 as [H0a H0b]; [discriminate (H0b eq_refl) | discriminate (H0a eq_refl)].
Qed.
Lemma rg_F2_nth : forall (T1 T2 : Type) (R : T1 -> T2 -> Prop) l1 l2 d1 d2, length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> R (nth i l1 d1) (nth i l2 d2)) -> Forall2 R l1 l2.
Proof.
  intros T1 T2 R l1. induction l1 as [|x l1 IH]; intros [|y l2] d1 d2 L H; cbn [length] in L; try discriminate L;
    constructor.
  - exact (H 0%nat ltac:(cbn; lia)).
  - apply (IH l2 d1 d2); [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.
Lemma rg_map_seq : forall (T : Type) (l : list T) d, l = map (fun i => nth i l d) (seq 0 (length l)).
Proof.
  intros T l d. induction l as [|x l IH]; [reflexivity|]. cbn [length seq map nth]. f_equal.
  rewrite <- seq_shift, List.map_map. exact IH.
Qed.
Lemma rg_nodup_inj : forall (X Y : Type) (f : X -> Y) l, (forall x y, f x = f y -> x = y) ->
  List.NoDup l -> List.NoDup (map f l).
Proof.
  intros X Y f l Hf N. induction N as [|x l Hx N IH]; cbn [map]; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & E & Hy). apply Hf in E. subst y. exact (Hx Hy).
Qed.

Definition rg_H (mc : lmod) (i : nat) : hsrc :=
  match nth (rg_sl i) (lm_hs mc) None with Some h => h | None => rg_g0 i end.

Lemma rg_nth_map_seq : forall (T : Type) (f : nat -> T) k i d, (i < k)%nat -> nth i (map f (seq 0 k)) d = f i.
Proof.
  intros T f k i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.
Lemma rg_slot_cases : forall j, (exists i, (i < n)%nat /\ rg_sl i = j) \/ (forall i, (i < n)%nat -> rg_sl i <> j).
Proof.
  intros j. destruct (in_dec Nat.eq_dec j (map rg_sl (seq 0 n))) as [Hin | Hnin].
  - left. apply in_map_iff in Hin as (i & Hs & Hi). apply in_seq in Hi. exists i. split; [lia | exact Hs].
  - right. intros i Hi Hs. apply Hnin. apply in_map_iff. exists i. split; [exact Hs | apply in_seq; lia].
Qed.
Lemma rg_end_rinv : forall mc A, gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> (gn = 0 \/ gn = 1) ->
  A = Z.of_nat (length (lm_O mc)) /\ fr_RINV cx (t + 1) mc.
Proof.
  intros mc A R HG.
  destruct (rg_run_keep _ mc A _ _ R) as (Knfd & Kk & Kc).
  destruct (rg_end_state mc A R) as (Q1 & Q2 & Q3 & Q4 & cs & HAc & HS & HD & HF0).
  pose proof HRI as ((HC0 & Hnfd) & (Hlen & Hnd & Hrng & Hent & _) & Hn & HG0).
  destruct HA as (Ak & _ & Aes & Ac & AO & _ & _ & _ & Agn & Anfd & _).
  assert (Hpos : gn = 0 -> forall i, (i <= n)%nat -> rg_acc cs i = Z.of_nat (rg_pos i)).
  { intros G i Hi. apply (rg_acc_pos mc n 0 cs (fun i' _ D => HS i' ltac:(destruct D as [D | (D & _)]; lia)) G i);
      [unfold rg_nd; rewrite Nat.ltb_irrefl; cbn [andb]; rewrite Nat.min_id; exact Hi | exact Hi]. }
  split.
  { rewrite HAc, Q1. unfold rg_A. destruct HG as [G | G].
    - rewrite G. cbn [Z.eqb]. rewrite (Hpos G n (Nat.le_refl n)). unfold rg_pos.
      rewrite firstn_all2 by (rewrite rg_segs_len; lia). rewrite (rg_O2_len_gn0 G). reflexivity.
    - rewrite G. cbn [Z.eqb]. rewrite (HDEAD (rg_live_gn1 G)), HO0. reflexivity. }
  (* the slots' pattern is m's *)
  assert (Pat : forall j, nth j (lm_hs mc) None = None <-> nth j (lm_hs m) None = None).
  { intros j. destruct (lt_dec j 4) as [Hj | Hj].
    - destruct (rg_slot_cases j) as [(i & Hi & Hs) | Hno].
      + subst j. destruct (HS i Hi) as (h'' & Eh & _). destruct (rg_sl_ok i Hi) as (_ & Eg & _).
        rewrite Eh, Eg. split; intros E; discriminate E.
      + rewrite (HF0 j Hj Hno), (rg_free j Hj Hno). tauto.
    - rewrite !nth_overflow by (rewrite ?Q4, ?Hlen; lia). tauto. }
  split; [|split; [|split]].
  - (* fr_count *)
    unfold fr_count. rewrite Knfd, Anfd. rewrite (rg_nopen_eq (lm_hs mc) (lm_hs m) ltac:(rewrite Q4, Hlen; reflexivity) Pat).
    split; lia.
  - (* fr_relay *)
    unfold fr_relay. rewrite Q2, Aes, Knfd, Anfd.
    split; [exact Q4|]. split; [exact HQF|].
    split.
    { apply Forall_forall. intros e He. apply (In_nth _ _ gn_e0) in He as (i & Hi & <-).
      rewrite length_map, HLQ in Hi. change gn_e0 with (fst gn_q0). rewrite map_nth, (rg_q_fd i Hi).
      rewrite Forall_forall in Hrng. apply Hrng. apply nth_In. exact Hi. }
    split.
    { eapply Forall_impl; [|exact HQM]. intros e (E1 & E2 & E3 & E4 & _ & _ & E7).
      unfold fr_entry_ok. split; [exact E1|]. split; [exact E3|]. split; [exact E4|]. split; [|exact E2].
      unfold drain_b_c.keys_texts. rewrite <- List.map_map with (f := gestures_end_b_c.key_text) (g := bzs).
      apply NoDup_ListNoDup. apply rg_nodup_inj; [exact SlotReads.bzs_inj|]. apply NoDup_ListNoDup. exact E7. }
    exists (map (fun i => (rg_H mc i, rg_sl i)) (seq 0 n)).
    assert (Lhj' : length (map (fun i => (rg_H mc i, rg_sl i)) (seq 0 n)) = n) by (rewrite length_map, length_seq; reflexivity).
    assert (Nhj' : forall i, (i < n)%nat -> nth i (map (fun i => (rg_H mc i, rg_sl i)) (seq 0 n)) gn_hj0 = (rg_H mc i, rg_sl i)).
    { intros i Hi. exact (rg_nth_map_seq _ (fun i => (rg_H mc i, rg_sl i)) n i gn_hj0 Hi). }
    assert (Msnd : map snd (map (fun i => (rg_H mc i, rg_sl i)) (seq 0 n)) = map snd hj).
    { rewrite List.map_map. rewrite (rg_map_seq _ hj gn_hj0) at 1. rewrite List.map_map, rg_lhj. reflexivity. }
    (* each entry's row *)
    assert (Row : forall i, (i < n)%nat ->
      fr_pair_ok mc (t + 1) (fst (nth i qs gn_q0)) (rg_H mc i, rg_sl i) /\
      fr_pair_cost (fst (nth i qs gn_q0)) (rg_H mc i, rg_sl i) <= fr_pair_cost (rg_ei i) (rg_g0 i, rg_sl i)).
    { intros i Hi. destruct (HS i Hi) as (h'' & Eh'' & HDn).
      assert (EH : rg_H mc i = h'') by (unfold rg_H; rewrite Eh''; reflexivity). rewrite EH.
      destruct (rg_done_surv cs i h'' Hi HDn (fun G => Hpos G i ltac:(lia))) as (h' & E' & H' & H'' & Hc & Eh & Hcap & NDH & SV).
      destruct (HEN i Hi) as (Hop & Hcl & Hq). rewrite rg_comb in Hop, Hcl. cbn [fst snd] in Hop, Hcl, Hq.
      rewrite Hq. pose proof (rg_pair i Hi) as HP0. change (fr_pair_ok m t (rg_ei i) (rg_g0 i, rg_sl i)) in HP0.
      destruct (rg_counts_i i Hi) as (Hcnt & _).
      destruct (Z.eq_dec (re_eof (rg_ei i)) 0) as [E0 | E0].
      - destruct (Hop E0) as (c & no & cap & LB & D). rewrite (rg_hs_open i Hi E0) in D.
        assert (EG : rg_G i = snd (nth i qs gn_q0)) by (unfold rg_G; rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
        rewrite EG in Hc, Hcnt.
        exact (rg_end_pair m mc t (rg_ei i) (rg_g0 i) (rg_sl i) c (lm_mx m) no cap (rg_ek i) (snd (nth i qs gn_q0)) LB
          h' E' H' h'' H'' pre HT (rg_entry_ok i Hi) HP0 (fun _ => D) (fun N => False_ind _ (N E0)) Hc Hcnt Eh Hcap NDH
          SV Eh'').
      - destruct (Hcl E0) as (Ek & _). fold (rg_ek i) in Ek.
        assert (EG : rg_G i = rg_g0 i) by (unfold rg_G; rewrite (proj2 (Z.eqb_neq _ _) E0); reflexivity).
        rewrite EG in Hc, Hcnt.
        exact (rg_end_pair m mc t (rg_ei i) (rg_g0 i) (rg_sl i) (CTL 0 0 0 0 0) 0 0 0 (rg_ek i) (rg_g0 i) []
          h' E' H' h'' H'' pre HT (rg_entry_ok i Hi) HP0 (fun E => False_ind _ (E0 E)) (fun _ => conj Ek eq_refl)
          Hc Hcnt Eh Hcap NDH SV Eh''). }
    split.
    { apply (rg_F2_nth _ _ _ _ _ gn_e0 gn_hj0); [rewrite length_map, Lhj', HLQ; reflexivity|].
      intros i Hi. rewrite length_map, HLQ in Hi. rewrite Nhj' by exact Hi.
      change gn_e0 with (fst gn_q0). rewrite map_nth. exact (proj1 (Row i Hi)). }
    split; [rewrite Msnd; apply NoDup_ListNoDup; exact HND|].
    split.
    { intros j Hj Ho. unfold SlotInv.slot_open in Ho. rewrite Msnd in Ho. apply HF0; [exact Hj|].
      intros i' Hi' Es. assert (Hin : existsb (Nat.eqb j) (map snd hj) = true).
      { apply existsb_exists. exists (rg_sl i'). split; [|apply Nat.eqb_eq; exact (eq_sym Es)].
        unfold rg_sl. apply in_map. apply nth_In. rewrite rg_lhj. exact Hi'. }
      rewrite Hin in Ho. discriminate Ho. }
    assert (Hcost : fr_cost (map fst qs) (map (fun i => (rg_H mc i, rg_sl i)) (seq 0 n)) <= fr_cost (lm_es m) hj).
    { unfold fr_cost at 1. rewrite (rg_combine_seq _ _ (map fst qs) _ gn_e0 gn_hj0) by (rewrite length_map, Lhj', HLQ; reflexivity).
      rewrite length_map, HLQ, List.map_map, rg_cost_seq. apply rg_zsum_le. intros i Hi. apply in_seq in Hi.
      cbn [fst snd]. rewrite Nhj' by lia. change gn_e0 with (fst gn_q0). rewrite map_nth. exact (proj2 (Row i ltac:(lia))). }
    rewrite Kk, Ak. split; [|lia].
    assert (Kq : lm_k m < gn_kq cx m) by (unfold gn_kq; destruct (gn_more cx m); lia). lia.
  - exact Hn.
  - (* fr_gone *)
    unfold fr_gone. rewrite Q3, Kc, Ac, rg_gn_m1. exact (HCTL (lm_gn m) HG0).
Qed.
(* the two rows' RINV-side conclusions, over every hypothesis of the Section (fixed argument list for the plugs) *)
Lemma rg_step_all : forall mc A i k h, gn_run (gn_pre cx m) m1 mc A i k ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  (forall h' E' H', gn_cnl_ok h h' E' H' ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None)).
Proof using All.
  intros mc A i k h R Hi Hk Hh Hfd.
  destruct (rg_call_A mc A i k h R Hi Hk Hh Hfd) as (_ & _ & _ & EO & _).
  destruct (rg_step_rinv mc A i k h R Hi Hk Hh Hfd) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
  split; [rewrite EO; exact rg_O2_len|]. split; [exact C5|]. split; [exact C6 | exact C7].
Qed.
Lemma rg_end_all : forall mc A, gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> (gn = 0 \/ gn = 1) ->
  A = Z.of_nat (length (lm_O mc)) /\ fr_RINV cx (t + 1) mc.
Proof using All. exact rg_end_rinv. Qed.
(* REQ5 at the loop's end: an open slot's held capacity does not shrink (check_no_loss's last conjunct; drain and
   check_shape_ends keep it) *)
Lemma rg_req5_all : forall mc A, gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  forall j hq hq', nth j (lm_hs m) None = Some hq -> nth j (lm_hs mc) None = Some hq' ->
    hl_cap (hs_held hq) <= hl_cap (hs_held hq').
Proof using All.
  intros mc A R j hq hq' Hj Hj'.
  destruct (rg_end_state mc A R) as (_ & _ & _ & _ & cs & _ & HS & _ & _).
  assert (Hj4 : (j < 4)%nat).
  { destruct (lt_dec j 4) as [L | L]; [exact L|]. exfalso.
    pose proof HRI as (_ & (Hlen & _) & _). rewrite nth_overflow in Hj by lia. discriminate Hj. }
  destruct (rg_slot_of j hq Hj4 Hj) as (i & Hi & Hs & ->).
  destruct (HS i Hi) as (h'' & Eh'' & (h' & E' & H' & ds & Hc & (H'' & Ehh & _ & Hcap & _))).
  rewrite Hs, Hj' in Eh''. injection Eh'' as <-. rewrite Ehh. cbn [hs_held set_held]. rewrite Hcap.
  (* the walk's gn_cnl_ok: REQ5(b) is its eighth conjunct; C1's exact capacity law follows it *)
  destruct Hc as (-> & _ & _ & _ & _ & _ & _ & Hmono & _). cbn [hs_held set_exp_held].
  destruct (rg_post_drain i Hi) as (_ & _ & Eheld & _). rewrite <- Eheld. exact Hmono.
Qed.

End loop.

(* ================================================================== the rows *)
Section rows.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the Section loop's hypotheses from the rows' premises *)
Lemma rg_setup : forall cx t m hs qs c2 O2 cap2,
  fr_RINV cx t m -> gn_pairs m hs -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  exists hj e1s,
    Forall2 (fr_pair_ok m t) (lm_es m) hj /\ List.NoDup (map snd hj) /\
    (forall j, (j < 4)%nat -> SlotInv.slot_open hj j = false -> nth j (lm_hs m) None = None) /\
    length e1s = length (lm_es m) /\ length qs = length (lm_es m) /\
    (forall i, (i < length (lm_es m))%nat ->
      rg_ent (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) (lm_mx m)
        (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (nth i e1s gn_e0) (nth i qs gn_q0)) /\
    (sl_live (lm_c m) 1 = true -> bzs O2 = bzs (lm_O m) ++
       rg_strm (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) (combine (lm_es m) hs) e1s) /\
    (sl_live (lm_c m) 1 = false -> O2 = lm_O m) /\
    fr_cost (lm_es m) hj <= c_n cx /\
    (forall g, fr_ctl_ok g (lm_c m) -> fr_ctl_ok g c2) /\
    Forall gn_entry_model (map fst qs) /\ NoDup (map re_fd (map fst qs)) /\
    fr_cost (lm_es m) hj <= lm_k m.
Proof.
  intros cx t m hs qs c2 O2 cap2 HRI HP (Hrig & _ & HQM & HQF).
  pose proof HRI as (_ & (_ & _ & _ & _ & hj & HF & HNDs & HCL & HCK & HC) & _ & _).
  destruct (rg_rel_dec _ _ _ _ _ _ _ _ _ _ Hrig) as (e1s & L1 & L2 & HEN & _ & Hlive & Hdead & Hctl).
  assert (Lc : length (combine (lm_es m) hs) = length (lm_es m))
    by (rewrite length_combine, (proj1 HP), Nat.min_id; reflexivity).
  rewrite Lc in L1, L2, HEN.
  exists hj, e1s. split; [exact HF|]. split; [exact (proj1 (NoDup_ListNoDup _) HNDs)|]. split; [exact HCL|].
  split; [exact L1|]. split; [exact L2|]. split; [exact HEN|]. split; [exact Hlive|]. split; [exact Hdead|].
  split; [exact HC|]. split; [exact Hctl|]. split; [exact HQM|]. split; [exact HQF | exact HCK].
Qed.

(* a39b599f92e's GN_RI_step (gone_base.v:583-624), verbatim, with its Section parameters as arguments *)
Definition GN_RI_step_d (B : asyms) (MT : ameter_ops) (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (RINV : lfcx -> Z -> lmod -> Prop) (MMAX : Z) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) /\
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)) /\
  (forall h' E' H' (Sy : astate) cst', gn_cnl_ok h h' E' H' -> mo_le MT Sx Sy cst' ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None) /\
     mo_ok MT Sy (hl_n (hs_held h') * mo_free MT)).

(* a39b599f92e's GN_RI_end (gone_base.v:628-648), verbatim, with its Section parameters as arguments, and REQ5 (the
   held lists' capacities do not shrink from m to mc) as one more, last, premise *)
Definition GN_RI_end_q5 (B : asyms) (MT : ameter_ops) (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (RINV : lfcx -> Z -> lmod -> Prop) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (lm_gn m = 0 \/ lm_gn m = 1) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
     hl_cap (hs_held hj) <= hl_cap (hs_held hj')) ->
  A = Z.of_nat (length (lm_O mc)) /\ RINV cx (t + 1) mc /\ LS cx (t + 1) mc lyx Sx.

(* the RINV side of both rows, for any LS *)
Lemma rg_step_rinv_side : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  (forall h' E' H', gn_cnl_ok h h' E' H' ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None)).
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h HRI (_ & HO0 & HT & _) HKEY HP HA Hrok R Hi Hk Hh Hfd.
  destruct (rg_setup cx t m hs qs c2 O2 cap2 HRI HP Hrok)
    as (hj & e1s & HF & HND & HCL & HLE & HLQ & HEN & HLIVE & HDEAD & HC & HCTL & HQM & HQF & HCK).
  exact (rg_step_all cx t m hs qs c2 O2 cap2 out2 m1 hj e1s HRI HF HND HCL HP HA HLE HLQ HEN HKEY HO0 HLIVE HDEAD
    HC HCTL ltac:(lia) HQM HQF HCK mc A i k h R Hi Hk Hh Hfd).
Qed.
Lemma rg_end_rinv_side : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (lm_gn m = 0 \/ lm_gn m = 1) ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  A = Z.of_nat (length (lm_O mc)) /\ fr_RINV cx (t + 1) mc.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI (_ & HO0 & HT & _) HKEY HG HP HA Hrok R.
  destruct (rg_setup cx t m hs qs c2 O2 cap2 HRI HP Hrok)
    as (hj & e1s & HF & HND & HCL & HLE & HLQ & HEN & HLIVE & HDEAD & HC & HCTL & HQM & HQF & HCK).
  assert (HG1 : lm_gn m1 = 0 \/ lm_gn m1 = 1) by (destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & -> & _); exact HG).
  exact (rg_end_all cx t m hs qs c2 O2 cap2 out2 m1 hj e1s HRI HF HND HCL HP HA HLE HLQ HEN HKEY HO0 HLIVE HDEAD
    HC HCTL ltac:(lia) HQM HQF HCK mc A R HG1).
Qed.

(* ---- the rows at the top's instance: MT := ameter_triv, RINV := fr_RINV, MMAX := WR_MMAX, LS := fr_LS3 B or
   fr_LS3c B; the LS-side conjuncts are a Theorem Labs lane's (ReplyLS3cTopxGoneF.v at b25d82fcf04) *)
Lemma RI_gone_step_holds : forall B,
  GN_RI_step_d B ameter_triv (ReplyLS3.fr_LS3 B) fr_RINV W_LLVMFuzzerTestOneInput_write.WR_MMAX.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS HP HA Hrok R
    Hmle Hfr Hi Hk Hh Hfd Hn4.
  pose proof (ReplyLS3cTopxGoneF.gx6_step_room B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop
    HE Hcap HE6 HS6 HLS HP HA Hrok R Hmle Hfr Hi Hk Hh Hfd Hn4) as Room.
  destruct (rg_step_rinv_side cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h HRI Hop HE HP HA Hrok R Hi Hk Hh Hfd)
    as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  do 7 (split; [assumption|]). split; [exact Room|]. split; [exact I|].
  intros h' E' H' Sy cst' Hc _. destruct (C8 h' E' H' Hc) as (D1 & D2 & D3).
  split; [exact D1|]. split; [exact D2|]. split; [exact D3 | exact I].
Qed.
Lemma RI_gone_step_holds_c : forall B,
  GN_RI_step_d B ameter_triv (ReplyLS3c.fr_LS3c B) fr_RINV W_LLVMFuzzerTestOneInput_write.WR_MMAX.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6 HLS HP HA Hrok R
    Hmle Hfr Hi Hk Hh Hfd Hn4.
  pose proof (ReplyLS3cTopxGoneF.gx6_step_room_c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop
    HE Hcap HE6 HS6 HLS HP HA Hrok R Hmle Hfr Hi Hk Hh Hfd Hn4) as Room.
  destruct (rg_step_rinv_side cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h HRI Hop HE HP HA Hrok R Hi Hk Hh Hfd)
    as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  do 7 (split; [assumption|]). split; [exact Room|]. split; [exact I|].
  intros h' E' H' Sy cst' Hc _. destruct (C8 h' E' H' Hc) as (D1 & D2 & D3).
  split; [exact D1|]. split; [exact D2|]. split; [exact D3 | exact I].
Qed.
Lemma RI_gone_end_holds_q5 : forall B, GN_RI_end_q5 B ameter_triv (ReplyLS3.fr_LS3 B) fr_RINV.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE HG Hcap HE6 HS6 HLS HP HA Hrok R Hmle Hfr H5.
  destruct (rg_end_rinv_side cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hop HE HG HP HA Hrok R) as (E1 & E2).
  split; [exact E1|]. split; [exact E2|].
  exact (ReplyLS3cTopxGoneF.gx6_end_LS3 B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6
    HS6 HLS HP HA Hrok R Hmle Hfr H5).
Qed.
Lemma RI_gone_end_holds_q5_c : forall B, GN_RI_end_q5 B ameter_triv (ReplyLS3c.fr_LS3c B) fr_RINV.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE HG Hcap HE6 HS6 HLS HP HA Hrok R Hmle Hfr H5.
  destruct (rg_end_rinv_side cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hop HE HG HP HA Hrok R) as (E1 & E2).
  split; [exact E1|]. split; [exact E2|].
  exact (ReplyLS3cTopxGoneF.gx6_end_LS3c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE Hcap HE6
    HS6 HLS HP HA Hrok R Hmle Hfr H5).
Qed.

End rows.

(* ---- the official rows (lib/A/W_LLVMFuzzerTestOneInput_gone_base.v's GN_RI_step / GN_RI_end at a Theorem Labs lane's KF-COUNT text 6151e809fb35: the binder
   q, the premises gn_runc / gn_cst after gn_run / mo_le, and GN_RI_step's inner check_no_loss post at cnl_cost) at
   MT := ameter_triv, RINV := fr_RINV, MMAX := fr_MMAX, LS := fr_LS3 B or fr_LS3c B.  GN_RI_step is GN_RI_step_d with
   the two new premises unused and its inner post (any cst') taken at cnl_cost.  GN_RI_end is GN_RI_end_q5 with REQ5
   from the rule's own premises (rg_end_req5_side: every open slot's held capacity at mc is the one check_no_loss left,
   which is at least the one before) *)
Section rows9.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rg_end_req5_side : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  forall j hj hj', nth j (lm_hs m) None = Some hj -> nth j (lm_hs mc) None = Some hj' ->
    hl_cap (hs_held hj) <= hl_cap (hs_held hj').
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI (_ & HO0 & HT & _) HKEY HP HA Hrok R.
  destruct (rg_setup cx t m hs qs c2 O2 cap2 HRI HP Hrok)
    as (hj & e1s & HF & HND & HCL & HLE & HLQ & HEN & HLIVE & HDEAD & HC & HCTL & HQM & HQF & HCK).
  exact (rg_req5_all cx t m hs qs c2 O2 cap2 out2 m1 hj e1s HRI HF HND HCL HP HA HLE HLQ HEN HKEY HO0 HLIVE HDEAD
    HC HCTL ltac:(lia) HQM HQF HCK mc A R).
Qed.
Lemma RI_gone_step_plug : forall B,
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B ameter_triv (ReplyLS3.fr_LS3 B) fr_RINV CfParamsReply.fr_MMAX.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q HRI Hop HE Hcap HE6 HS6 HLS HP HA Hrok R _
    Hmle _ Hfr Hi Hk Hh Hfd Hn4.
  destruct (RI_gone_step_holds B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6
    HLS HP HA Hrok R Hmle Hfr Hi Hk Hh Hfd Hn4) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  do 9 (split; [assumption|]). intros h' E' H' Sy Hc Hm. exact (D10 h' E' H' Sy _ Hc Hm).
Qed.
Lemma RI_gone_step_plug_c : forall B,
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B ameter_triv (ReplyLS3c.fr_LS3c B) fr_RINV CfParamsReply.fr_MMAX.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q HRI Hop HE Hcap HE6 HS6 HLS HP HA Hrok R _
    Hmle _ Hfr Hi Hk Hh Hfd Hn4.
  destruct (RI_gone_step_holds_c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI Hop HE Hcap HE6 HS6
    HLS HP HA Hrok R Hmle Hfr Hi Hk Hh Hfd Hn4) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  do 9 (split; [assumption|]). intros h' E' H' Sy Hc Hm. exact (D10 h' E' H' Sy _ Hc Hm).
Qed.
Lemma RI_gone_end_plug : forall B,
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B ameter_triv (ReplyLS3.fr_LS3 B) fr_RINV.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q HRI Hop HE HG Hcap HE6 HS6 HLS HP HA Hrok R _ Hmle _
    Hfr.
  exact (RI_gone_end_holds_q5 B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE HG Hcap HE6 HS6 HLS
    HP HA Hrok R Hmle Hfr (rg_end_req5_side cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hop HE HP HA Hrok R)).
Qed.
Lemma RI_gone_end_plug_c : forall B,
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B ameter_triv (ReplyLS3c.fr_LS3c B) fr_RINV.
Proof.
  intros B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q HRI Hop HE HG Hcap HE6 HS6 HLS HP HA Hrok R _ Hmle _
    Hfr.
  exact (RI_gone_end_holds_q5_c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI Hop HE HG Hcap HE6 HS6 HLS
    HP HA Hrok R Hmle Hfr (rg_end_req5_side cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hop HE HP HA Hrok R)).
Qed.
End rows9.

(* ================================================================== the RINV halves of the rows as a Theorem Labs lane's
   ReplyLS3cTopxGone8.v splits them (its module G8 states G8.GN_RI_step_ri :77 and G8.GN_RI_end_ri :189 over
   gone_base's own gn_run / gn_cnl_ok at a Theorem Labs lane's KF-COUNT text, cda28f0ce1d: binder q, gn_runc / gn_cst, the inner
   post at cnl_cost), for ANY LS and ANY meter; the RINV side reads neither cost premise.  The top's instance
   (LS := fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B) takes them through s5-r1d's gx8_* lemmas *)
Section rows8.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma RI_gone_step_ri : forall B MT LS, ReplyLS3cTopxGone8.G8.GN_RI_step_ri B MT LS fr_RINV.
Proof.
  intros B MT LS cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q HRI Hop HE Hcap HE6 HS6 HLS HP HA Hrok R
    _ Hmle _ Hfr Hi Hk Hh Hfd Hn4.
  destruct (rg_step_rinv_side cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h HRI Hop HE HP HA Hrok R Hi Hk Hh Hfd)
    as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  do 7 (split; [assumption|]). intros h' E' H' Sy Hc _. exact (C8 h' E' H' Hc).
Qed.
Lemma RI_gone_end_ri : forall B MT LS, ReplyLS3cTopxGone8.G8.GN_RI_end_ri B MT LS fr_RINV.
Proof.
  intros B MT LS cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q HRI Hop HE HG Hcap HE6 HS6 HLS HP HA Hrok R
    _ Hmle _ Hfr.
  exact (rg_end_rinv_side cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hop HE HG HP HA Hrok R).
Qed.
End rows8.

Section rg3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.


(* aa34c06e82c lib/A/W_LLVMFuzzerTestOneInput_gone_base.v:583-614, verbatim, with the Section parameters B, MT, LS, RINV, MMAX as arguments *)
Definition GN_RI_step_r3 (B : asyms) (MT : ameter_ops) (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop)
    (RINV : lfcx -> Z -> lmod -> Prop) (MMAX : Z) : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
    14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  (* the stream's length fits next_line's memchr bound (both check_* specs ask NO <= 2 ^ 40 and
     0 < NO -> NO < 2 ^ 32); one operation sends at most 33,488,385 bytes (W_contract.v:580-581).  The
     model's, like the size bounds above; aout_at alone bounds it only by the allocator's MALLOC_MAX.  (p5) *)
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) /\
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)) /\
  (forall h' E' H' (Sy : astate) cst', gn_cnl_ok h h' E' H' -> mo_le MT Sx Sy cst' ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None) /\
     mo_ok MT Sy (hl_n (hs_held h') * mo_free MT)).

(* ---------------------------------------------------------------- the counter-instance *)
(* the prefix of id 0 ("param_gesture 0 ", 16 bytes); the unfinished line W with a 0 byte; the pending text " begin"
   with its line end; the line drain relays *)
Definition rg3_pre : list Z := relay_instance_gone_b_c.instance_prefix 0.
Definition rg3_Wz : list Z := rg3_pre ++ [97; 0; 98].
Definition rg3_dz : list Z := [32; 98; 101; 103; 105; 110; 0].
Definition rg3_lz : list Z := rg3_Wz ++ [32; 98; 101; 103; 105; 110].
Definition rg3_W : list byte := map (Z_to_bv 8) rg3_Wz.
(* slot 0's source: " begin\0" pending, the partial line W (hs_W = W), not overlong, nothing expected or held *)
Definition rg3_g0 : hsrc :=
  HS 100 1 0 0 (HL 0 8 [(0, map (Z_to_bv 8) rg3_dz)] []) 0 0 rg3_W (Z.of_nat (length rg3_Wz)) 0 [] empty_list
     empty_list.
(* its relay entry: open, not skipping, no keys, the unfinished line W, no buffer yet *)
Definition rg3_e : rentry :=
  RE 100 0 0 (repeat (Z_to_bv 8 0) 4) 0 0 0 0 0 (repeat (Z_to_bv 8 0) 4) [] rg3_W [].
(* the model at the op-5 dispatch: lm_k = 26 = the entry's cost (|pending| 7 + |W| 19), the stream empty *)
Definition rg3_m0 : lmod := LM 26 [Some rg3_g0; None; None; None] 0 [rg3_e] rg_c0 [] 0 0 0 0 1.
(* after drain: the entry holds the key W (buffer 8192, key array 8 bytes, unfinished line empty); the source has
   nothing pending and expects the line W ++ " begin" *)
Definition rg3_key : Z * list byte * list byte := (0, rg3_W, []).
Definition rg3_e1 : rentry :=
  RE 100 0 0 (repeat (Z_to_bv 8 0) 4) 0 0 8192 1 8 (repeat (Z_to_bv 8 0) 4) [rg3_key] [] [].
Definition rg3_h1 : hsrc :=
  HS 100 1 0 0 (HL 0 8 [] []) 0 0 rg3_W 0 0 [] (HL 0 8 [(0, map (Z_to_bv 8) rg3_lz)] []) empty_list.
Definition rg3_LB : list byte := map (Z_to_bv 8) (rg3_lz ++ [0]).
(* after gestures_end_instance: the key W ended (W, then " end\0"), the entry keeps no key *)
Definition rg3_qs : list (rentry * hsrc) := [(entry_keys rg3_e1 [], rg3_h1)].
Definition rg3_c2 : ctl := CTL 3 0 0 0 0.
Definition rg3_O2 : list byte := rg3_LB ++ rg3_W ++ gesture_end_c.END5.
Definition rg3_cap2 : Z := 52.
Definition rg3_m1 (cx : lfcx) : lmod :=
  LM (gn_kq cx rg3_m0) [Some rg3_h1; None; None; None] 0 [entry_keys rg3_e1 []] rg3_c2 rg3_O2 0 rg3_cap2 0 0 1.
(* check_no_loss at slot 0: the expected list emptied, the held list [W] (upds [] [W ++ " begin"] = [W]) *)
Definition rg3_E : hlist := HL 0 8 [] [].
Definition rg3_H : hlist := HL 0 8 [(0, rg3_W)] [].

(* |pre| = 16, so c_n cx = lm_k + 1 = 27 gives gn_more = false and id 0 *)
Lemma rg3_id : forall cx, c_n cx = 27 -> gn_id cx rg3_m0 = 0.
Proof. intros cx Hn. unfold gn_id, gn_more, rg3_m0. cbn [lm_k]. rewrite Hn. reflexivity. Qed.

(* drain of the entry with " begin\0" pending after the unfinished line W *)
Lemma rg3_dr_rel : dr_rel rg_c0 0 0 0 rg3_e rg3_g0 rg3_e1 rg3_h1 rg3_LB.
Proof.
  unfold dr_rel. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; repeat constructor; intros [])
          | (apply NoDup_ListNoDup; constructor) | (intros y; split; intros Hy; exact Hy) | (intros _; reflexivity) ].
Qed.

(* the premises of the row at the counter-instance, gn_op and the key premise included *)
Lemma rg3_premises : forall cx, c_n cx = 27 -> in_byte cx 26 mod 10 = 5 ->
  fr_RINV cx 1 rg3_m0 /\ gn_op cx 1 rg3_m0 /\
  Forall (fun e => Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
    14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es rg3_m0) /\
  gn_pairs rg3_m0 [(rg3_g0, 0%nat)] /\ gn_after_rig cx rg3_m0 [(rg3_g0, 0%nat)] rg3_qs rg3_c2 rg3_O2 rg3_cap2 0 (rg3_m1 cx) /\
  gn_rig_ok cx rg3_m0 [(rg3_g0, 0%nat)] rg3_qs rg3_c2 rg3_O2 rg3_cap2.
Proof.
  intros cx Hn Hop.
  split; [|split; [|split; [|split; [|split]]]].
  - (* fr_RINV *)
    split; [|split; [|split]].
    + unfold fr_count, rg3_m0, nopen, OPS_MAX. cbn. lia.
    + unfold fr_relay, rg3_m0. cbn [lm_hs lm_es lm_nfd lm_k].
      split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [constructor; [cbn; lia | constructor]|].
      split.
      { constructor; [|constructor]. unfold fr_entry_ok. cbn.
        split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
      exists [(rg3_g0, 0%nat)].
      split.
      { constructor; [|constructor]. unfold fr_pair_ok. cbv zeta. cbn [fst snd lm_hs nth].
        split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; vm_compute; reflexivity]|].
        split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
        split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
        split; [vm_compute; intros Hx; discriminate Hx | vm_compute; intros Hx; discriminate Hx]. }
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split.
      { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
          first [discriminate Ho | reflexivity | lia]. }
      assert (Ec : fr_cost [rg3_e] [(rg3_g0, 0%nat)] = 26) by (vm_compute; reflexivity).
      rewrite Ec. lia.
    + lia.
    + unfold fr_gone, rg3_m0, rg_c0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros H; [auto | discriminate H].
  - (* gn_op *)
    unfold gn_op, rg3_m0. cbn [lm_k lm_O]. split; [exact Hop|]. split; [reflexivity|].
    split; [unfold OPS_MAX; lia | lia].
  - (* the keys: the table holds none *)
    unfold rg3_m0, rg3_e. cbn [lm_es re_keys]. apply Forall_cons; [apply Forall_nil | apply Forall_nil].
  - (* gn_pairs *)
    unfold gn_pairs, rg3_m0. cbn [lm_es]. split; [reflexivity|]. split.
    + constructor; [|constructor]. intros _. unfold gn_pair_ok. cbn [fst snd lm_hs nth].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; vm_compute; reflexivity|].
      unfold pending_stream, re_nheld. vm_compute. repeat match goal with |- _ /\ _ => split end; reflexivity.
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
  - (* gn_after_rig *)
    unfold gn_after_rig, rg3_m1, rg3_qs.
    do 11 (split; [reflexivity|]). split.
    + intros j _ Hj. destruct j as [|j]; [exfalso; apply Hj; cbn; left; reflexivity | reflexivity].
    + intros [|i] Hi _; [reflexivity | cbn [lm_es rg3_m0 length] in Hi; lia].
  - (* gn_rig_ok: drain, then gestures_end_instance ends the key W *)
    unfold gn_rig_ok. rewrite (rg3_id cx Hn). split; [|split; [reflexivity | split]].
    + unfold rg3_m0, rg3_qs. cbn [rig_rel combine lm_es lm_mx lm_c lm_O lm_cap].
      exists rg3_e1, 0, rg3_LB. cbv zeta. cbn [re_eof rg3_e Z.eqb].
      split; [exact rg3_dr_rel|]. split; [vm_compute; reflexivity|].
      vm_compute. split; [reflexivity | split; reflexivity].
    + constructor; [|constructor]. unfold gn_entry_model, rg3_e1, entry_keys, re_nheld. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ (left; reflexivity) | reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
Qed.

(* check_no_loss's result at slot 0 *)
Lemma rg3_cnl : gn_cnl_ok rg3_h1 (set_exp_held rg3_h1 rg3_E rg3_H) rg3_E rg3_H.
Proof.
  unfold gn_cnl_ok. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; repeat constructor; intros [])
          | (apply NoDup_ListNoDup; constructor) ].
Qed.

(* check_shape_ends' run on the stream after the drained line: split_nul stops at W's 0 byte, and
   "param_gesture 0 a" does not end with " end" *)
Lemma rg3_ends_none :
  ends_run (map (Z_to_bv 8) rg3_pre) [(0, rg3_W)] (rg3_W ++ gesture_end_c.END5) 1%nat = None.
Proof. vm_compute. reflexivity. Qed.

Lemma GN_RI_step_r3_counter : forall B MT LS MMAX cx ly S lyx Sx cst Sy cst',
  c_n cx = 27 -> in_byte cx 26 mod 10 = 5 -> LS cx 1 rg3_m0 ly S -> mo_le MT S Sx cst -> mo_le MT Sx Sy cst' ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks rg3_m0 ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks (rg3_m1 cx) ++ rest)) ->
  GN_RI_step_r3 B MT LS fr_RINV MMAX -> False.
Proof.
  intros B MT LS MMAX cx ly S lyx Sx cst Sy cst' Hn Hop HLS Hle Hle' HP HST.
  destruct (rg3_premises cx Hn Hop) as (HRI & HOP & HK & HPR & HAR & HOK).
  destruct (HST cx 1 rg3_m0 ly S [(rg3_g0, 0%nat)] rg3_qs rg3_c2 rg3_O2 rg3_cap2 0 (rg3_m1 cx)
    (rg3_m1 cx) 0 0%nat 0%nat rg3_h1 lyx Sx cst HRI HOP HK HLS HPR HAR HOK (gn_run0 _ _) Hle HP (Nat.lt_0_succ 0)
    ltac:(lia) eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlast).
  destruct (Hlast (set_exp_held rg3_h1 rg3_E rg3_H) rg3_E rg3_H Sy cst' rg3_cnl Hle') as (_ & _ & Hends & _).
  apply (Hends eq_refl). unfold gn_pre. rewrite (rg3_id cx Hn).
  vm_compute. reflexivity.
Qed.

(* a lawful meter (ameter_laws, the arm's MT) gives the step mo_le MT Sx Sx 0 *)
Lemma GN_RI_step_r3_counter_laws : forall B MT LS MMAX cx ly S lyx Sx cst, ameter_laws MT ->
  c_n cx = 27 -> in_byte cx 26 mod 10 = 5 -> LS cx 1 rg3_m0 ly S -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks rg3_m0 ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks (rg3_m1 cx) ++ rest)) ->
  GN_RI_step_r3 B MT LS fr_RINV MMAX -> False.
Proof.
  intros B MT LS MMAX cx ly S lyx Sx cst ML Hn Hop HLS Hle HP HST.
  exact (GN_RI_step_r3_counter B MT LS MMAX cx ly S lyx Sx cst Sx 0 Hn Hop HLS Hle (mo_le_refl MT ML Sx) HP HST).
Qed.
End rg3.

(* ================================================================== the NEW rows are not vacuous (VERIFY rule 10):
   one state meets every premise of a39b599f92e's GN_RI_step (at the loop's first call) and of its GN_RI_end (after
   the loop), at MT := ameter_triv, RINV := fr_RINV, LS := fr_LS3 B (and REQ5 holds there too).  The state: one
   operation done (t = 1), the gone op (byte 5) next at lm_k = 1 of a 2-byte input; one relay entry whose line buffer
   is allocated (an earlier drain), its source open at slot 0 with nothing pending; the live blocks are the input,
   the table, the entry's buffer and the source's partial buffer, each a chunk of the allocator state (as
   a Theorem Labs lane's fr_LS3_sat, ReplyLS3.v:464-505). *)
Section nsat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition rn_k0 : YG00.chunk := YG00.mkChunk (YG00.PPrim 0) 2 YG00.CAllocated.
Definition rn_k3 : YG00.chunk := YG00.mkChunk (YG00.PPrim 32768) 8192 YG00.CAllocated.
Definition rn_S : astate := YG00.set_chunks [rn_k0; ReplyLS3.ls3_k1; rn_k3; ReplyLS3.ls3_k2] YG00.init_state.
Definition rn_p : Z := sptr_addr B ReplyLS3.ls3_ly (YG00.ck_user rn_k0).
Definition rn_b : Z := sptr_addr B ReplyLS3.ls3_ly (YG00.ck_user rn_k3).
Definition rn_cx : lfcx (rc := rc) :=
  LFCX ReplyLS3.ls3_ly rn_S ReplyLS3.ls3_W bvmap_empty (fun _ => None) ReplyLS3.ls3_md rn_p 2
    [Z_to_bv 8 4; Z_to_bv 8 5] 0.
Definition rn_e : rentry := RE 100 0 0 (repeat (Z_to_bv 8 0) 4) rn_b 0 8192 0 0 (repeat (Z_to_bv 8 0) 4) [] [] [].
Definition rn_h : hsrc := oa_new_src 100 (ReplyLS3.ls3_q B) [].
Definition rn_m : lmod := LM 1 [Some rn_h; None; None; None] (ReplyLS3.ls3_G B) [rn_e] rg_c0 [] 0 0 0 0 1.
Definition rn_c2 : ctl := dr_ctl rg_c0 rn_h 0.
Definition rn_m1 : lmod :=
  LM (gn_kq rn_cx rn_m) (lm_hs rn_m) (ReplyLS3.ls3_G B) [rn_e] rn_c2 [] 0 0 0 0 1.
Definition rn_h' : hsrc := set_exp_held rn_h (hs_expected rn_h) (hs_held rn_h).
Definition rn_h'' : hsrc := set_held rn_h' (hs_held rn_h').
Definition rn_mc : lmod := gn_set rn_m1 0 rn_h''.

Lemma rn_dr_rel : dr_rel rg_c0 0 0 0 rn_e rn_h rn_e rn_h [].
Proof.
  unfold dr_rel. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor)
          | (intros y; split; intros []) | (intros _; reflexivity) ].
Qed.

(* the premises both rows share *)
Lemma rn_common :
  fr_RINV rn_cx 1 rn_m /\ gn_op rn_cx 1 rn_m /\
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es rn_m) /\
  0 <= lm_cap rn_m /\
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es rn_m) /\
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs rn_m) /\
  ReplyLS3.fr_LS3 B rn_cx 1 rn_m ReplyLS3.ls3_ly rn_S /\
  gn_pairs rn_m [(rn_h, 0%nat)] /\ gn_after_rig rn_cx rn_m [(rn_h, 0%nat)] [(rn_e, rn_h)] rn_c2 [] 0 0 rn_m1 /\
  gn_rig_ok rn_cx rn_m [(rn_h, 0%nat)] [(rn_e, rn_h)] rn_c2 [] 0.
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - split; [|split; [|split]].
    + unfold fr_count, rn_m, nopen, OPS_MAX. cbn. lia.
    + unfold fr_relay, rn_m. cbn [lm_hs lm_es lm_nfd lm_k].
      split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [constructor; [cbn; lia | constructor]|].
      split.
      { constructor; [|constructor]. unfold fr_entry_ok. cbn.
        split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
      exists [(rn_h, 0%nat)].
      split.
      { constructor; [|constructor]. unfold fr_pair_ok, rn_h. cbn.
        split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; reflexivity]|].
        split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
        split; [left; reflexivity|]. split; [lia|]. split; [unfold SlotInv.WRITE_MAX; lia | lia]. }
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split.
      { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
          first [discriminate Ho | reflexivity | lia]. }
      unfold fr_cost, fr_pair_cost. cbn. lia.
    + cbn. lia.
    + unfold fr_gone, rn_m, rg_c0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros H; [auto | discriminate H].
  - unfold gn_op, rn_m, rn_cx, in_byte. cbn. split; [reflexivity|]. split; [reflexivity|]. unfold OPS_MAX. lia.
  - constructor; [|constructor]. cbn. split; [intros []|constructor].
  - cbn. lia.
  - constructor; [|constructor]. cbn. split; [unfold APARTIAL; lia|].
    split; [right; left; reflexivity | left; split; reflexivity].
  - constructor; [|constructor; [exact I | constructor; [exact I | constructor; [exact I | constructor]]]].
    cbn. split; [left; split; reflexivity | constructor].
  - (* fr_LS3: the blocks are exactly the input, the table, the entry's buffer and the source's partial buffer *)
    exists [], 0.
    assert (EA : ablocks B ReplyLS3.ls3_ly rn_S = input_blks rn_cx ++ model_blks rn_m ++ []) by reflexivity.
    assert (Hbb : blocks_bytes rn_S = 2 + ATABLE + 8192 + APARTIAL) by (vm_compute; reflexivity).
    assert (Hin : bsum (input_blks rn_cx) = 2) by reflexivity.
    assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
    assert (HS : c_S rn_cx = rn_S) by reflexivity.
    assert (Hn : c_n rn_cx = 2) by reflexivity.
    assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
    assert (HL : LIVE_MAX = 17179869184) by reflexivity.
    assert (En : ReplyLS.npend rn_m = 0) by reflexivity.
    assert (Ek : ReplyLS.kk rn_cx rn_m = 1) by reflexivity.
    assert (Eo : nopen (lm_hs rn_m) = 1) by reflexivity.
    assert (Ep : ReplyLS3.PHI3 rn_m <= 100000) by (vm_compute; intros Hx; discriminate Hx).
    rewrite EA, HS, Hbb, Hn, Hin, Hrest, HC, HL, En, Ek, Eo.
    split; [apply Permutation_refl|].
    unfold ReplyLS3.W_OPEN, ReplyLS.MB_K, ReplyLS.MB_C, ATABLE, APARTIAL, ReplyLS3.E_ENT, ReplyLS3.K0.
    refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
  - unfold gn_pairs, rn_m. cbn [lm_es]. split; [reflexivity|]. split.
    + constructor; [|constructor]. intros _. unfold gn_pair_ok, rn_h, oa_new_src. cbn [fst snd lm_hs nth].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; reflexivity|].
      unfold pending_stream, re_nheld. vm_compute. repeat match goal with |- _ /\ _ => split end; reflexivity.
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
  - unfold gn_after_rig, rn_m1.
    do 11 (split; [reflexivity|]). split.
    + intros j _ _. reflexivity.
    + intros [|i] Hi _; [reflexivity | cbn in Hi; lia].
  - unfold gn_rig_ok. split; [|split; [reflexivity | split]].
    + generalize (relay_instance_gone_b_c.instance_prefix (gn_id rn_cx rn_m)). intros pre.
      unfold rn_m. cbn [rig_rel combine lm_es lm_mx lm_c lm_O lm_cap].
      exists rn_e, 0, []. cbv zeta. cbn [re_eof rn_e Z.eqb Pos.eqb].
      split; [exact rn_dr_rel|]. split; [reflexivity|].
      vm_compute. split; [reflexivity | split; reflexivity].
    + constructor; [|constructor]. unfold gn_entry_model, rn_e, re_nheld. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ (left; reflexivity) | reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
Qed.

(* GN_RI_step's own premises at the loop's first call (gn_run0: slot 0, entry 0, at = 0) *)
Lemma RI_gone_step_new_sat :
  gn_run (gn_pre rn_cx rn_m) rn_m1 rn_m1 0 0%nat 0%nat /\ mo_le ameter_triv rn_S rn_S 0 /\
  (forall rest, Permutation (ablocks B ReplyLS3.ls3_ly rn_S) (input_blks rn_cx ++ model_blks rn_m ++ rest) ->
     Permutation (ablocks B ReplyLS3.ls3_ly rn_S) (input_blks rn_cx ++ model_blks rn_m1 ++ rest)) /\
  (0 < length (lm_es rn_m1))%nat /\ (0 < 4)%nat /\
  nth 0 (lm_hs rn_m1) None = Some rn_h /\ hs_fd rn_h = re_fd (nth 0 (lm_es rn_m1) gn_e0) /\
  (forall j hj, nth j (lm_hs rn_m1) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)).
Proof.
  split; [exact (gn_run0 _ _)|]. split; [exact I|]. split; [intros rest H; exact H|].
  split; [cbn; lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  intros [|[|[|[|j]]]] hj Hj; cbn in Hj; try discriminate Hj; [|destruct j; discriminate Hj].
  injection Hj as <-. vm_compute. intros Hx; discriminate Hx.
Qed.

(* GN_RI_end's own premises after the loop: the call at slot 0, three slots passed, the next entry; REQ5 too *)
Lemma RI_gone_end_new_sat :
  (lm_gn rn_m = 0 \/ lm_gn rn_m = 1) /\
  gn_run (gn_pre rn_cx rn_m) rn_m1 rn_mc 0 (length (lm_es rn_m1)) 0%nat /\ mo_le ameter_triv rn_S rn_S 0 /\
  (forall rest, Permutation (ablocks B ReplyLS3.ls3_ly rn_S) (input_blks rn_cx ++ model_blks rn_m ++ rest) ->
     Permutation (ablocks B ReplyLS3.ls3_ly rn_S) (input_blks rn_cx ++ model_blks rn_mc ++ rest)) /\
  (forall j hj hj', nth j (lm_hs rn_m) None = Some hj -> nth j (lm_hs rn_mc) None = Some hj' ->
     hl_cap (hs_held hj) <= hl_cap (hs_held hj')).
Proof.
  split; [left; reflexivity|]. split.
  { change (length (lm_es rn_m1)) with 1%nat. apply gn_run_next.
    apply gn_run_skip; [|lia | left; reflexivity].
    apply gn_run_skip; [|lia | left; reflexivity].
    apply gn_run_skip; [|lia | left; reflexivity].
    unfold rn_mc.
    refine (gn_run_call _ _ rn_m1 0 0%nat 0%nat rn_h rn_h' rn_h'' (hs_expected rn_h) (hs_held rn_h)
      [] 0 (gn_run0 _ _) ltac:(lia) (Nat.lt_0_succ 0) eq_refl eq_refl _ _).
    - unfold gn_cnl_ok. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    - unfold gn_cshe_ok. exists (hs_held rn_h').
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply NoDup_ListNoDup; constructor|]. split; [lia|].
      right. split; reflexivity. }
  split; [exact I|]. split; [intros rest H; exact H|].
  intros [|[|[|[|j]]]] hj hj' Hj Hj'; cbn in Hj, Hj'; try discriminate Hj; [|destruct j; discriminate Hj].
  injection Hj as <-. injection Hj' as <-. vm_compute. intros Hx; discriminate Hx.
Qed.
End nsat.

(* the axiom audit, in the build log beside the lemmas (toolchain/allowed-axioms.txt) *)
Print Assumptions GN_RI_end_old_false.
Print Assumptions rn_common.
Print Assumptions RI_gone_step_new_sat.
Print Assumptions RI_gone_end_new_sat.
Print Assumptions RI_gone_pairs_plug.
Print Assumptions RI_gone_read_plug.
Print Assumptions RI_gone_pairs_holds.
Print Assumptions RI_gone_read_holds.
Print Assumptions RI_gone_read_sat.
Print Assumptions GN_RI_step_collapse_triv.
Print Assumptions GN_RI_end_collapse_triv.
Print Assumptions GN_RI_step_r2_counter.
Print Assumptions GN_RI_end_r2_counter.
Print Assumptions rg_ends_res.
Print Assumptions rg_counts.
Print Assumptions rg_counts_drain.
Print Assumptions rg_lines_nz.
Print Assumptions rg_kok_drain.
Print Assumptions rg_geik_perm.
Print Assumptions rg_geik_texts.
Print Assumptions rg_keys_total_app.
Print Assumptions rg_keys_total_perm.
Print Assumptions rg_surv_total.
Print Assumptions rg_end_pair.
Print Assumptions rg_seg_len.
Print Assumptions RI_gone_step_holds.
Print Assumptions RI_gone_step_holds_c.
Print Assumptions RI_gone_end_holds_q5.
Print Assumptions RI_gone_end_holds_q5_c.
Print Assumptions RI_gone_step_plug.
Print Assumptions RI_gone_step_plug_c.
Print Assumptions RI_gone_end_plug.
Print Assumptions RI_gone_end_plug_c.
Print Assumptions RI_gone_step_ri.
Print Assumptions RI_gone_end_ri.
Print Assumptions rg3_premises.
Print Assumptions GN_RI_step_r3_counter.
Print Assumptions GN_RI_step_r3_counter_laws.
