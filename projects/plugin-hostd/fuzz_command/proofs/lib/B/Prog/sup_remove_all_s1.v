(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tail of sup_connect's ASan walk (plugin-hostd/fuzz_command, 0x8ad20): at
   answer's entry after the epilogue and `j answer` (0x8af0c), answer's contract (answer_c.v tanswer_spec) gives
   sup_connect's post (sup_connect_s0.v SCN_T_stmt). No instruction runs here: the machine is at BASE + AF_answer.
   answer is printf-reaching and the last step, so its contract is taken at the entry's FP state (the rounding mode
   0 of sup_connect's pre) and its apost_baseF post, with the fx' it returns, closes sup_connect's apost_baseF by
   PaFx's apost_baseF_intro.

   answer is called with c the recorded slot, the shape "resp 0" (0x21ce0, RO_lit_21ce0 of cmd_ro_ok) and
   changes = 1, on the recorder state rec_record R REC_CONNECT (scn_args ...) that the tail state holds; then
   sup_connect_m R ... = rec_answer (rec_record R REC_CONNECT A) (REC_CONNECT, A) REC_MOD_HOST_SHAPE true
   (RecModel.v:73-75, :124-126). answer's journal (from the tail state, STK = ANSWER_STK, at the entry sp) is
   joined to the walk's journal (from the entry state, SUP_CONNECT_STK) by the core's ajournal_sub_wide: g_rec's
   answer and state fields are program statics inside scn_FP, and the old answer's block is one of the recorder's
   blocks, so it is in scn_FP's ablocks_fp O or is a block the walk made. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_connect_s5.v, with its module paths and module names changed; 356 of its 399 lines of code are new or changed and 259 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_remove_all_refit_s3.v, with its module paths changed; 65 of its 218 lines of code are new or changed and 246 lines of the source are left out. *)
(* Pure lemmas for sup_remove_all's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove_all = 0x8b434), over the recorder's representation arep_at (lib/B/Prog/CmdRep.v) and the
   allocator's block lists, with no machine semantics. The B twin of the pure part of a Theorem Labs lane's A walk
   (a working branch 59cc4017e62, lib/A/Prog/sup_remove_all_s1.v and the block lemmas of
   sup_remove_all_s3.v). B's sup_remove_all calls record() (lib/B/Prog/record_c.v) where A inlined it, so the A
   lemmas that rebuild the representation after record()'s two stores (arep_append, arep_spill_set, arep_kept) have
   no use here: record()'s contract gives the representation after the call.

   - the old value of the answer cell (bsra_answer_cell), which answer's contract takes as `old`;
   - the model fact the walk rewrites with (bsra_m_eq: sup_remove_all_m as rec_answer of rec_record);
   - the block conjuncts of the post-condition from answer's post-condition, over the block lists alone
     (bsra_post_blocksA in the A statement's forms, bsra_post_blocks in the B statement's forms,
     lib/B/Prog/sup_remove_all_c.v:105 and :112, which differ from A's lib/A/Prog/sup_remove_all_c.v:97, :102);
   - over AR (AR_laws): the bounds of a live block, two live blocks with one start are one block, no block is listed
     twice in a permutation of the live blocks, blocks_bytes as a sum, and the recorder's blocks are live. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the answer cell: 0, or the start of the answer's block *)
Lemma bsra_answer_cell : forall bl rd R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\
    ((l_answer Q = None /\ old = 0) \/ (exists pn, l_answer Q = Some pn /\ old = fst pn)).
Proof.
intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold aanswer_at in HA.
destruct (r_answer R) as [x|] eqn:E1; destruct (l_answer Q) as [pn|] eqn:E2; rewrite ?E1, ?E2 in HA;
  cbv beta iota in HA; try contradiction.
- exists (fst pn). split; [exact (proj1 HA)|]. right. exists pn. split; reflexivity.
- exists 0. split; [exact HA|]. left. split; reflexivity.
Qed.

Lemma bsra_in_answer : forall Q pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn Hp. unfold lay_blocks. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hp.
Qed.

(* sup_remove_all() records the call (REC_REMOVE_ALL, []) and answers it with the shape "resp 0", changes = 1
   (lib/Prog/RecModel.v sup_remove_all_m, rec_stub) *)
Lemma bsra_m_eq : forall R,
  sup_remove_all_m R = rec_answer (rec_record R REC_REMOVE_ALL []) (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true.
Proof. intros R. unfold sup_remove_all_m, rec_stub. reflexivity. Qed.

(* membership in a filter (stdpp's filter over a boolean predicate) *)
Lemma bsra_filter_in : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
  In pn (filter (fun q : Z * Z => f q) l) -> In pn l.
Proof.
intros f pn l. induction l as [|q l IH]; [intros []|].
cbn. destruct (decide (f q)) as [Hq|Hq].
- intros [Heq|Hin]; [left; exact Heq | right; exact (IH Hin)].
- intros Hin. right. exact (IH Hin).
Qed.

(* a block of an argument of a recorded call, of the answer or of the reply is a live block *)
Lemma bsra_call_blocks : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl.
Proof.
intros bl rd a c P pn (_ & _ & HL & _ & _ & _ & H7) Hin.
destruct (In_nth_error P pn Hin) as [k Hk].
assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
exact (proj1 (proj2 (proj2 (H7 k s pn Es Hk)))).
Qed.

Lemma bsra_rep_blocks : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HR & _ & _) Hin.
unfold lay_blocks in Hin. apply in_app_iff in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hp).
  destruct (In_nth_error _ _ HP) as [i Hi].
  assert (Hlt : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  exact (bsra_call_blocks bl rd _ c P pn (proj1 (C4 i c P Ec Hi)) Hp).
- apply in_app_iff in Hin as [Hin | Hin]; [exact (bsra_call_blocks bl rd _ _ _ pn C5 Hin)|].
  apply in_app_iff in Hin as [Hin | Hin].
  + unfold aanswer_at in HA. destruct (l_answer Q) as [pa|]; cbn [oblk In] in Hin; [|destruct Hin].
    destruct Hin as [<- | []]. destruct (r_answer R); [exact (proj1 (proj2 (proj2 HA))) | exact (False_ind _ HA)].
  + unfold areply_at in HR. destruct (l_reply Q) as [pa|]; cbn [oblk In] in Hin; [|destruct Hin].
    destruct Hin as [<- | []]. destruct (r_reply R); [exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))) | exact (False_ind _ HR)].
Qed.

Lemma bsra_bsum_nonneg : forall l, (forall pn, In pn l -> 0 <= snd pn) -> 0 <= bsum l.
Proof.
induction l as [|x l IH]; intros H; [unfold bsum; cbn; lia|].
rewrite bsum_cons. pose proof (H x (or_introl eq_refl)). pose proof (IH (fun pn Hp => H pn (or_intror Hp))). lia.
Qed.

(* the block conjuncts of the post-condition from answer's post-condition, over the block lists alone, in the A
   statement's forms (a Theorem Labs lane's s3_post_blocks). bl0: the entry's blocks; blc: the blocks at answer's entry, the
   entry's less the blocks `freed` that record()'s spill arm freed (all of them the recorder's, O); bl2: the blocks
   after answer; O1, O': the recorder's blocks at answer's entry and after it; old: the answer the recorder held at
   answer's entry (0 or the start of one of O1); p1, p2: answer's two fresh copies of the text (|t| + 1 = n bytes),
   p2 the caller's. *)
Lemma bsra_post_blocksA : forall (bl0 blc bl2 O O1 O' freed : list (Z * Z)) (old p1 p2 n : Z),
  Permutation bl0 (blc ++ freed) ->
  (forall pn, In pn freed -> In pn O) ->
  (forall pn, In pn O1 <-> In pn O /\ ~ In pn freed) ->
  (forall pn, In pn O1 -> In pn blc) ->
  (forall pn, In pn blc -> In pn freed -> False) ->
  (forall pn, In pn blc -> fst pn <> 0) ->
  (old = 0 \/ exists pn0, In pn0 O1 /\ old = fst pn0) ->
  (forall p a b, In (p, a) blc -> In (p, b) blc -> a = b) ->
  (forall p a b, In (p, a) bl2 -> In (p, b) bl2 -> a = b) ->
  p1 <> p2 -> (forall pn, In pn blc -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) ->
  (forall pn, In pn bl2 <-> (In pn blc /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
  (forall pn, In pn O' <-> (In pn O1 /\ fst pn <> old) \/ pn = (p1, n)) ->
  (forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
  (forall pn, In pn bl2 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)) /\
  (forall pn, In pn bl0 -> ~ In pn O -> In pn bl2) /\
  In (p2, n) bl2 /\
  (forall pn, In pn bl0 -> ~ In pn O -> pn <> (p2, n)) /\
  ~ In p2 (map fst O').
Proof.
intros bl0 blc bl2 O O1 O' freed old p1 p2 n HP HF HO1 HO1c ND H0 OLD SAMEc SAME2 Gne Gfr GBL GO.
assert (Dz : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x y; decide equality; apply Z.eq_dec).
(* a block of the entry the recorder did not own is a block at answer's entry, not the old answer's *)
assert (K : forall pn, In pn bl0 -> ~ In pn O -> In pn blc /\ fst pn <> old).
{ intros pn H1 H2.
  assert (Hc : In pn blc).
  { apply (Permutation_in _ HP) in H1. apply in_app_iff in H1 as [H1 | H1]; [exact H1 | exfalso; exact (H2 (HF _ H1))]. }
  split; [exact Hc|]. intros Eo.
  destruct OLD as [E0 | (pn0 & Hp0 & E0)].
  - exact (H0 pn Hc (eq_trans Eo E0)).
  - pose proof (HO1c _ Hp0) as Hc0.
    destruct pn as [p a], pn0 as [p0 b]. cbn [fst] in Eo, E0.
    assert (Ep : p0 = p) by congruence. rewrite Ep in Hc0, Hp0.
    pose proof (SAMEc p a b Hc Hc0) as Eab. rewrite <- Eab in Hp0.
    exact (H2 (proj1 (proj1 (HO1 _) Hp0))). }
split.
{ intros pn Hp. apply GO in Hp as [(Hp & _) | Ep].
  - left. exact (proj1 (proj1 (HO1 _) Hp)).
  - subst pn. destruct (in_dec Dz (p1, n) bl0) as [Hin | Hnin]; [left | right; exact Hnin].
    apply (Permutation_in _ HP) in Hin. apply in_app_iff in Hin as [Hin | Hin]; [|exact (HF _ Hin)].
    destruct (Z.eq_dec p1 old) as [Eo | Eo]; [|exfalso; exact (proj1 (Gfr _ Hin Eo) eq_refl)].
    destruct OLD as [E0 | (pn0 & Hp0 & E0)]; [exfalso; exact (H0 _ Hin (eq_trans Eo E0))|].
    pose proof (HO1c _ Hp0) as Hc0. destruct pn0 as [p0 b]. cbn [fst] in E0.
    assert (Ep : p0 = p1) by congruence. rewrite Ep in Hc0, Hp0.
    pose proof (SAMEc p1 n b Hin Hc0) as Eab. rewrite <- Eab in Hp0.
    exact (proj1 (proj1 (HO1 _) Hp0)). }
split.
{ intros pn Hp. apply GBL in Hp as [(Hc & Ho) | [Ep | Ep]].
  - destruct (in_dec Dz pn O1) as [H1 | H1].
    + right; left. apply GO. left. split; [exact H1 | exact Ho].
    + left. split.
      * apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hc.
      * intros HO. destruct (in_dec Dz pn freed) as [Hf | Hf].
        -- exact (ND pn Hc Hf).
        -- apply H1. apply HO1. split; [exact HO | exact Hf].
  - right; left. apply GO. right. exact Ep.
  - right; right. exact Ep. }
split.
{ intros pn H1 H2. destruct (K pn H1 H2) as [Hc Ho]. apply GBL. left. split; [exact Hc | exact Ho]. }
split; [apply GBL; right; right; reflexivity|].
split.
{ intros pn H1 H2 Ep. destruct (K pn H1 H2) as [Hc Ho]. exact (proj2 (Gfr pn Hc Ho) Ep). }
intros Hm. apply in_map_iff in Hm as ([p a] & Ep & Hp). cbn [fst] in Ep. subst p.
apply GO in Hp as [(Hp & Ho) | Ep].
- pose proof (HO1c _ Hp) as Hc.
  assert (H2a : In (p2, a) bl2) by (apply GBL; left; split; [exact Hc | exact Ho]).
  assert (H2n : In (p2, n) bl2) by (apply GBL; right; right; reflexivity).
  pose proof (SAME2 p2 a n H2a H2n) as Ea. subst a. exact (proj2 (Gfr _ Hc Ho) eq_refl).
- injection Ep as E1 _. exact (Gne (eq_sym E1)).
Qed.

(* the same in the B statement's forms (lib/B/Prog/sup_remove_all_c.v:105: a block of O' live at the entry is one
   of O; :112: the returned text's block, if live at the entry, was one of O). The second needs membership in a
   list of Z * Z to be decidable. *)
Lemma bsra_post_blocks : forall (bl0 blc bl2 O O1 O' freed : list (Z * Z)) (old p1 p2 n : Z),
  Permutation bl0 (blc ++ freed) ->
  (forall pn, In pn freed -> In pn O) ->
  (forall pn, In pn O1 <-> In pn O /\ ~ In pn freed) ->
  (forall pn, In pn O1 -> In pn blc) ->
  (forall pn, In pn blc -> In pn freed -> False) ->
  (forall pn, In pn blc -> fst pn <> 0) ->
  (old = 0 \/ exists pn0, In pn0 O1 /\ old = fst pn0) ->
  (forall p a b, In (p, a) blc -> In (p, b) blc -> a = b) ->
  (forall p a b, In (p, a) bl2 -> In (p, b) bl2 -> a = b) ->
  p1 <> p2 -> (forall pn, In pn blc -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) ->
  (forall pn, In pn bl2 <-> (In pn blc /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
  (forall pn, In pn O' <-> (In pn O1 /\ fst pn <> old) \/ pn = (p1, n)) ->
  (forall pn, In pn O' -> In pn bl0 -> In pn O) /\
  (forall pn, In pn bl2 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)) /\
  (forall pn, In pn bl0 -> ~ In pn O -> In pn bl2) /\
  In (p2, n) bl2 /\
  (In (p2, n) bl0 -> In (p2, n) O) /\
  ~ In p2 (map fst O').
Proof.
intros bl0 blc bl2 O O1 O' freed old p1 p2 n HP HF HO1 HO1c ND H0 OLD SAMEc SAME2 Gne Gfr GBL GO.
assert (Dz : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x y; decide equality; apply Z.eq_dec).
destruct (bsra_post_blocksA bl0 blc bl2 O O1 O' freed old p1 p2 n HP HF HO1 HO1c ND H0 OLD SAMEc SAME2 Gne Gfr GBL GO)
  as (A1 & A2 & A3 & A4 & A5 & A6).
split; [intros pn H1 H2; destruct (A1 pn H1) as [H | H]; [exact H | exact (False_ind _ (H H2))]|].
split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
split; [|exact A6].
intros H1. destruct (in_dec Dz (p2, n) O) as [H | H]; [exact H | exact (False_ind _ (A5 _ H1 H eq_refl))].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* a live block: its bounds and size (al_blocks) *)
Lemma bsra_blk : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n /\ 1 <= req_size n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
pose proof (req_size_pos n ltac:(lia)). lia.
Qed.

(* two live blocks with the same start are the same block (AR's separation) *)
Lemma bsra_same_start : forall ly S (W : world SEGS) mem md p a b, AR SEGS B ly S W mem md ->
  In (p, a) (ablocks B ly S) -> In (p, b) (ablocks B ly S) -> a = b.
Proof.
intros ly S W mem md p a b HAR H1 H2. destruct (Z.eq_dec a b) as [E|Hne]; [exact E|exfalso].
assert (Hd : zdisjoint (p, req_size a) (p, req_size b)).
{ apply (sep_blocks SEGS B LAWS ly S W mem md p a p b HAR H1 H2). intros E. injection E as E. exact (Hne E). }
destruct (bsra_blk ly S W mem md p a HAR H1) as (_ & _ & _ & R1).
destruct (bsra_blk ly S W mem md p b HAR H2) as (_ & _ & _ & R2).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* no block is listed twice in a permutation of the live blocks *)
Lemma bsra_nodup2 : forall ly S (W : world SEGS) mem md (l1 l2 : list (Z * Z)) pn, AR SEGS B ly S W mem md ->
  Permutation (ablocks B ly S) (l1 ++ l2) -> In pn l1 -> In pn l2 -> False.
Proof.
intros ly S W mem md l1 l2 pn HAR HP H1 H2.
apply in_split in H1 as (a1 & b1 & E1). apply in_split in H2 as (a2 & b2 & E2). subst l1 l2.
assert (HP2 : Permutation (pn :: pn :: (a1 ++ b1 ++ a2 ++ b2)) ((a1 ++ pn :: b1) ++ a2 ++ pn :: b2)).
{ rewrite <- app_assoc. cbn [app]. apply Permutation_cons_app.
  assert (E : a1 ++ b1 ++ a2 ++ pn :: b2 = (a1 ++ b1 ++ a2) ++ pn :: b2) by (rewrite <- !app_assoc; reflexivity).
  rewrite E. apply Permutation_cons_app. rewrite <- !app_assoc. apply Permutation_refl. }
pose proof (Permutation_trans HP (Permutation_sym HP2)) as HP3.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md pn pn _ HAR HP3) as Hd.
assert (Hin : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP3)); left; reflexivity).
destruct pn as [p n]. destruct (bsra_blk ly S W mem md p n HAR Hin) as (_ & _ & _ & R1).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma bsra_bb : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof.
intros ly S.
first [exact (blocks_bytes_bsum B ly S) | exact (blocks_bytes_bsum SEGS B ly S) | exact (blocks_bytes_bsum SEGS B LAWS ly S)].
Qed.

(* the recorder's blocks are live blocks *)
Lemma bsra_rep_live : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HQ & HO) Hin. exact (bsra_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HO pn) Hin)). Qed.
End e.
End f.
End d.
