(* omx-clap-core/fuzz_preset, Spec: the FRAME KEEPS of iface_room_pos, and nothing else.
   WHY THIS FILE EXISTS (the kit owner's ruling, 2026-10-29, on the driver-contract owner's point): these two lemmas were first proved in
   lib/A/PRH_Base.v, the kit. The driver-contract owner's leaf (the bulk twins of the same keeps) sits BELOW the kit and cannot cite
   them there, so a second pair would appear at the lower layer. The home is the LOWEST layer that needs them.
   PRH_Base.v takes them by Require and keeps its own names as aliases, so its citers change by zero lines
   (iface_room_pos_set_fs / iface_room_pos_stack_free). The parse_value proof walk (lib/A/VrdTop.v) cites them at the frame take
   and release; the names are stable.
   WHY THEY HOLD: iface_room_pos (lib/Spec/PresetRoomPos.v) reads blocks, st_chunks, the two quarantine caches and the
   batch list - never st_fs. set_fs changes st_fs alone (YG01.v:1842 stack_free_state is a set_fs too), so both are
   true BY CONVERSION, the same argument as the allocator-model owner's room_live_set_fs / room_live_stack_free. A fake-frame take
   (__asan_stack_malloc, astack_malloc_realizes_cf's post at S' = set_fs f S) and its release therefore keep the run
   position. The one kit text that needs them is ex_value (lib/A/PRH_FnEx.v), whose body takes a class-1 fake frame.
   Two lemmas, Qed, no definitions. *)
(* Modified by Theorem Labs, 2026-10-30, for the kit, for free_cf's size test
   (Quarantine::Put recycles a chunk above kQuarantineMax at once): rp_free_parts is the enqueue side (premise
   `req_size r <= kQuarantineMax`), rp_free_parts_big the recycle side; the free history is PresetRunQ.hfrees_q,
   so room_pos_keep_free / _realloc / _bulk_free hold for both sides and keep int102's statements;
   iface_room_pos_bulk reads PresetRunQ.qfilter (firstn k L). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRoomPos.

Lemma room_pos_set_fs : forall sm x os i H0 hist S f,
  iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist (set_fs f S).
Proof. intros sm x os i H0 hist S f H. exact H. Qed.

Lemma room_pos_stack_free : forall sm x os i H0 hist S c p,
  iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist (stack_free_state c p S).
Proof. intros sm x os i H0 hist S c p H. exact H. Qed.

(* ============================================================================================================ *)
(* PART B (the driver-contract owner's interface walk; the kit owner's ruling 08:38Z): the keeps of iface_room_pos across one allocator call,
   and the sub-position of a bulk free (pj_free of a tree: one model event HBulk L, |L| free_cf calls).
   THE EVENT PREMISE. A call is the run's event at i: `nth_error (PresetRun.hruns sm x os) i = Some e`, in the call's
   own request. HMal's request INCLUDES the harness head: rd_hev (EAlloc n) = [HMal (n + HEAD)] (PresetReqAt.v:84),
   HEAD = 16 = cf_head at CfParams_preset, and rs_live (room_of_cf S) holds ck_req, the allocator's request. So at
   fuzz_malloc's malloc_cf (n + cf_head) the event is HMal (n + cf_head); a harness call that goes to the C library
   directly (fuzz_copy, expected's scratch, tx_put's raw realloc) carries its request as made. HRe m n: m the old
   block's request, n the new one (PresetReqAt.v:86); HFr n: the freed block's request (:88). A refused allocation is
   no model event (rd_hev (EFail _) = [], :87): the position stays (the *_null keeps).
   THE CALL PREMISES are amalloc_realizes_cf's / afree_realizes_cf's (YG0dcf.v:335-342, :447-455), which every kit call site
   holds: acall_pre_cf first (it gives Wf_cf, universe_ok, qtight and ROOM_cf), the request bound, blocks_bytes,
   the trace in the universe; the realloc keep also takes ROOM_cf_k S RK_realloc (from room_live_cf, room_live_room_k),
   which pays the batch room of the inner free.
   THE BULK ORDER: the bulk keeps are stated over WHATEVER list the model's event carries (`nth_error (hruns ..) i =
   Some (HBulk L)` and `nth_error L k = Some r`), never over a named list function, because P8's fifo_ok (so
   cf_frees_follow) is an exact list equation and pj_free frees in post-order (the S6 walk, measured), which
   is not the order of the list the model carries today; the model owner restates it, and nothing here changes.
   THE CF FACTS, all on the base and cited: malloc_cf_apath_post / _success (YGcfApath.v), ml_free_cf (YG03dcf.v)
   with atok_cf_apath (YGcfTok.v), malloc_cf_fifo / free_cf_fifo / rpost_apath / quar_fifo_malloc_step (YGcfRoom.v),
   cf_frees_step_free (YGcfFrees.v), find_user_block_cf / WfR_of_WfP_cf (YG03cf.v), rl_free_null / rl_apath_ibind /
   rl_apath_ret / rl_of_acall_pre_cf (YGcfRoomLive.v), ROOM_cf_of_acall_pre_cf (YGcfRoomPre.v), malloc_room_keep_cf /
   ipost_apath / room_shape_cf_of_WfP_cf (YGcfRoomStep.v), RK_room (YGcfRoomKeep.v).
   Requires: PresetRoomPos's closure plus a8's call form and trees; no lib/Prog/*_c.v (measured on the build's
   dependency file). Nothing here is a function's proof (rule 24).
   THE COUNT (A15 / A16, 2026-10-30): iface_room_pos and iface_room_pos_bulk end
   with PresetRoomPos.rp_count (prefix) S, the COUNT meter (rp_nsec S <= rp_NB + nsec prefix and sec_T_cf S <=
   rp_TB + tsec prefix, the cf layer's Z counts, under the closed YGcfSecsStep.secs_steps_cf). Every keep carries it
   with NO new premise and no change of statement: the step of each call is read off secs_steps_cf itself
   (rp_secs_malloc / _free / _realloc / _realloc0, section 5), a granted malloc or realloc adds at most its event's
   counts (rp_post_mal / rp_post_re: one entry of sec_map_size r for a secondary request r, nothing for a primary), a
   refused call or a free adds nothing (rp_post_null, secs_same), and an HFr / HBulk event counts nothing in the
   model (A17's nsec / tsec), so frees on both sides of free_cf's size test, NULL frees and the bulk sub-positions
   keep the count. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG02cf YG03cf YG03dcf YG07cf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRoomStep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfFrees YGcfAmx YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetReqAt PresetRun PresetRunQ PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation RUN sm x os := (PresetRun.hruns sm x os).

(* ---------------------------------------------------------------------------- *)
(* 1. The model side of one event at position i.                                  *)
Lemma rp_firstn_S {A : Type} : forall (l : list A) i e, nth_error l i = Some e -> firstn (Datatypes.S i) l = firstn i l ++ [e].
Proof.
induction l as [|a l IH]; intros i e H; [destruct i; discriminate|].
destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity | rewrite (IH i e H); reflexivity].
Qed.

Lemma rp_hlive_snoc : forall l e, PresetReqAt.hlive (l ++ [e]) = PresetReqAt.hstep (PresetReqAt.hlive l) e.
Proof. intros l e. unfold PresetReqAt.hlive. rewrite PresetReqAt.hlive_from_app. reflexivity. Qed.

Lemma rp_hfrees_snoc : forall l e, PresetRun.hfrees (l ++ [e]) = PresetRun.hfrees l ++ PresetRun.hfree1 e.
Proof. intros l e. rewrite PresetRun.hfrees_app. unfold PresetRun.hfrees at 2. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma rp_okf_nth : forall es s i e, PresetReqAt.okf s es -> nth_error es i = Some e ->
  PresetReqAt.hits (PresetReqAt.hlive_from s (firstn i es)) e.
Proof.
induction es as [|e0 es IH]; intros s i e H He; [destruct i; discriminate|].
destruct H as [H0 H1]. destruct i as [|i]; cbn in He.
- injection He as <-. exact H0.
- cbn [firstn]. rewrite PresetReqAt.hlive_from_cons. exact (IH _ i e H1 He).
Qed.

(* the event at i hits the live list at i (every removal of the run finds its request live) *)
Lemma rp_hits_at : forall sm x os i e, nth_error (RUN sm x os) i = Some e ->
  PresetReqAt.hits (PresetReqAt.hlive (firstn i (RUN sm x os))) e.
Proof. intros sm x os i e He. exact (rp_okf_nth _ [] i e (PresetRun.hruns_okf sm x os) He). Qed.

Lemma rp_model_mal : forall sm x os i r, nth_error (RUN sm x os) i = Some (PresetReqAt.HMal r) ->
  PresetReqAt.hlive (firstn (Datatypes.S i) (RUN sm x os)) = r :: PresetReqAt.hlive (firstn i (RUN sm x os)) /\
  PresetRun.hfrees (firstn (Datatypes.S i) (RUN sm x os)) = PresetRun.hfrees (firstn i (RUN sm x os)).
Proof.
intros sm x os i r He. rewrite (rp_firstn_S _ i _ He), rp_hlive_snoc, rp_hfrees_snoc.
split; [reflexivity | cbn; apply app_nil_r].
Qed.

Lemma rp_model_fr : forall sm x os i r, nth_error (RUN sm x os) i = Some (PresetReqAt.HFr r) ->
  In r (PresetReqAt.hlive (firstn i (RUN sm x os))) /\
  PresetReqAt.hlive (firstn (Datatypes.S i) (RUN sm x os)) = PresetReqAt.rm1 r (PresetReqAt.hlive (firstn i (RUN sm x os))) /\
  PresetRun.hfrees (firstn (Datatypes.S i) (RUN sm x os)) = PresetRun.hfrees (firstn i (RUN sm x os)) ++ [r].
Proof.
intros sm x os i r He. pose proof (rp_hits_at sm x os i _ He) as Hh. cbn [PresetReqAt.hits] in Hh.
rewrite (rp_firstn_S _ i _ He), rp_hlive_snoc, rp_hfrees_snoc. split; [exact Hh | split; reflexivity].
Qed.

Lemma rp_model_re : forall sm x os i m r, nth_error (RUN sm x os) i = Some (PresetReqAt.HRe m r) ->
  In m (PresetReqAt.hlive (firstn i (RUN sm x os))) /\
  PresetReqAt.hlive (firstn (Datatypes.S i) (RUN sm x os)) =
    r :: PresetReqAt.rm1 m (PresetReqAt.hlive (firstn i (RUN sm x os))) /\
  PresetRun.hfrees (firstn (Datatypes.S i) (RUN sm x os)) = PresetRun.hfrees (firstn i (RUN sm x os)) ++ [m].
Proof.
intros sm x os i m r He. pose proof (rp_hits_at sm x os i _ He) as Hh. cbn [PresetReqAt.hits] in Hh.
rewrite (rp_firstn_S _ i _ He), rp_hlive_snoc, rp_hfrees_snoc. split; [exact Hh | split; reflexivity].
Qed.

Lemma rp_model_bulk : forall sm x os i L, nth_error (RUN sm x os) i = Some (PresetReqAt.HBulk L) ->
  PresetReqAt.subm L (PresetReqAt.hlive (firstn i (RUN sm x os))) /\
  PresetReqAt.hlive (firstn (Datatypes.S i) (RUN sm x os)) = PresetReqAt.rmall L (PresetReqAt.hlive (firstn i (RUN sm x os))) /\
  PresetRun.hfrees (firstn (Datatypes.S i) (RUN sm x os)) = PresetRun.hfrees (firstn i (RUN sm x os)) ++ L.
Proof.
intros sm x os i L He. pose proof (rp_hits_at sm x os i _ He) as Hh. cbn [PresetReqAt.hits] in Hh.
rewrite (rp_firstn_S _ i _ He), rp_hlive_snoc, rp_hfrees_snoc. split; [exact Hh | split; reflexivity].
Qed.

(* the quarantine's free history over one event: PresetRunQ.hfrees_q *)
Lemma rp_q_same : forall A B, PresetRun.hfrees A = PresetRun.hfrees B -> PresetRunQ.hfrees_q A = PresetRunQ.hfrees_q B.
Proof. intros A B E. rewrite !PresetRunQ.hfrees_q_eq, E. reflexivity. Qed.

Lemma rp_q_list : forall A B L, PresetRun.hfrees A = PresetRun.hfrees B ++ L ->
  PresetRunQ.hfrees_q A = PresetRunQ.hfrees_q B ++ PresetRunQ.qfilter L.
Proof. intros A B L E. rewrite !PresetRunQ.hfrees_q_eq, E, PresetRunQ.qfilter_app. reflexivity. Qed.

(* the bulk's k-th removal *)
Lemma rp_rmall_snoc : forall F z s, PresetReqAt.rmall (F ++ [z]) s = PresetReqAt.rm1 z (PresetReqAt.rmall F s).
Proof. intros F z s. unfold PresetReqAt.rmall. rewrite fold_left_app. reflexivity. Qed.

Lemma rp_subm_rmall : forall F T s, PresetReqAt.subm (F ++ T) s -> PresetReqAt.subm T (PresetReqAt.rmall F s).
Proof.
induction F as [|z F IH]; intros T s H; [exact H|].
cbn [PresetReqAt.rmall fold_left]. apply IH. destruct H as [d Hd].
exists d. pose proof (PresetReqAt.rm1_perm z _ _ Hd) as P. cbn [app] in P. rewrite PresetReqAt.rm1_cons_eq in P.
exact P.
Qed.

Lemma rp_bulk_in : forall L s k r, PresetReqAt.subm L s -> nth_error L k = Some r ->
  In r (PresetReqAt.rmall (firstn k L) s).
Proof.
intros L s k r H Hk. pose proof (firstn_skipn k L) as E.
assert (Hs : skipn k L = r :: skipn (Datatypes.S k) L).
{ clear H E. revert k Hk. induction L as [|a L IH]; intros k Hk; [destruct k; discriminate|].
  destruct k as [|k]; cbn in Hk |- *; [injection Hk as ->; reflexivity | exact (IH k Hk)]. }
rewrite Hs in E. rewrite <- E in H. pose proof (rp_subm_rmall _ _ _ H) as H2.
apply (PresetReqAt.subm_in r _ _ H2). left. reflexivity.
Qed.

Lemma rp_bulk_step : forall L s k r, nth_error L k = Some r ->
  PresetReqAt.rmall (firstn (Datatypes.S k) L) s = PresetReqAt.rm1 r (PresetReqAt.rmall (firstn k L) s) /\
  firstn (Datatypes.S k) L = firstn k L ++ [r].
Proof.
intros L s k r Hk. pose proof (rp_firstn_S L k r Hk) as E. rewrite E, rp_rmall_snoc. split; reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 1b. The COUNT meter (A15, PresetRoomPos.rp_count): one more model event, and the allocator step of the
      call that makes it. The model counts are A17's (PresetSecTotal.nsec / tsec, nsec_app / tsec_app), the
      steps the layer's (YGcfNames.secs_step / secs_call_post) and A14's (YGcfSecsStep.secs_same).              *)
(* one more model event e, and an allocator step of at most e's counts *)
Lemma rp_count_snoc : forall l e S S', PresetRoomPos.rp_count l S ->
  (YGcfSecsStep.secs_steps_cf ->
     YGcfNames.secs_step (Z.of_nat (PresetSecTotal.nsec [e])) (PresetSecTotal.tsec [e]) S S') ->
  PresetRoomPos.rp_count (l ++ [e]) S'.
Proof.
intros l e S S' H K A. destruct (H A) as (N & T). destruct (K A) as (N' & T').
unfold PresetRoomPos.rp_nsec in *. rewrite PresetSecTotal.nsec_app, PresetSecTotal.tsec_app. split; lia.
Qed.

(* one more model event that counts nothing (HFr, HBulk), and an allocator step that keeps both counts *)
Lemma rp_count_snoc_same : forall l e S S', PresetSecTotal.nsec [e] = 0%nat -> PresetSecTotal.tsec [e] = 0 ->
  PresetRoomPos.rp_count l S -> (YGcfSecsStep.secs_steps_cf -> YGcfSecsStep.secs_same S S') ->
  PresetRoomPos.rp_count (l ++ [e]) S'.
Proof.
intros l e S S' E1 E2 H K A. destruct (H A) as (N & T). destruct (K A) as (N' & T').
unfold PresetRoomPos.rp_nsec in *. rewrite PresetSecTotal.nsec_app, PresetSecTotal.tsec_app. split; lia.
Qed.

(* no model event (a refused call, a NULL free, a free inside a bulk event) *)
Lemma rp_count_keep : forall l S S', PresetRoomPos.rp_count l S ->
  (YGcfSecsStep.secs_steps_cf -> YGcfNames.secs_step 0 0 S S') -> PresetRoomPos.rp_count l S'.
Proof.
intros l S S' H K A. destruct (H A) as (N & T). destruct (K A) as (N' & T').
unfold PresetRoomPos.rp_nsec in *. split; lia.
Qed.

Lemma rp_count_keep_same : forall l S S', PresetRoomPos.rp_count l S ->
  (YGcfSecsStep.secs_steps_cf -> YGcfSecsStep.secs_same S S') -> PresetRoomPos.rp_count l S'.
Proof.
intros l S S' H K A. destruct (H A) as (N & T). destruct (K A) as (N' & T').
unfold PresetRoomPos.rp_nsec in *. split; lia.
Qed.

(* a granted call's post (q <> PNull) is a step of at most its event's counts: HMal r, or HRe m r for a realloc *)
Lemma rp_post_mal : forall r S q S', q <> PNull -> YGcfNames.secs_call_post r S (q, S') ->
  YGcfNames.secs_step (Z.of_nat (PresetSecTotal.nsec [PresetReqAt.HMal r]))
    (PresetSecTotal.tsec [PresetReqAt.HMal r]) S S'.
Proof.
intros r S q S' Hq H. revert H.
unfold YGcfNames.secs_call_post, YGcfNames.secs_call_d, YGcfNames.secs_call_t.
cbn [fst snd PresetSecTotal.nsec PresetRun.nprodR PresetRun.prod_evR PresetSecTotal.tsec PresetSecTotal.sec_mapped].
change (PresetRoom.is_primary r) with (from_primary r).
destruct q as [|o|rr o|c q1]; [exfalso; exact (Hq eq_refl)| | |];
  destruct (from_primary r); rewrite ?Nat.add_0_r, ?Z.add_0_r; intros H; exact H.
Qed.

Lemma rp_post_re : forall m r S q S', q <> PNull -> YGcfNames.secs_call_post r S (q, S') ->
  YGcfNames.secs_step (Z.of_nat (PresetSecTotal.nsec [PresetReqAt.HRe m r]))
    (PresetSecTotal.tsec [PresetReqAt.HRe m r]) S S'.
Proof.
intros m r S q S' Hq H. revert H.
unfold YGcfNames.secs_call_post, YGcfNames.secs_call_d, YGcfNames.secs_call_t.
cbn [fst snd PresetSecTotal.nsec PresetRun.nprodR PresetRun.prod_evR PresetSecTotal.tsec PresetSecTotal.sec_mapped].
change (PresetRoom.is_primary r) with (from_primary r).
destruct q as [|o|rr o|c q1]; [exfalso; exact (Hq eq_refl)| | |];
  destruct (from_primary r); rewrite ?Nat.add_0_r, ?Z.add_0_r; intros H; exact H.
Qed.

(* a refused call's post (PNull) moves neither count *)
Lemma rp_post_null : forall r S S', YGcfNames.secs_call_post r S (PNull, S') -> YGcfNames.secs_step 0 0 S S'.
Proof. intros r S S' H. exact H. Qed.

(* a bulk event counts nothing, so the count at the position after it is the count before it *)
Lemma rp_count_bulk_eq : forall sm x os i L S, nth_error (RUN sm x os) i = Some (PresetReqAt.HBulk L) ->
  PresetRoomPos.rp_count (firstn (Datatypes.S i) (RUN sm x os)) S = PresetRoomPos.rp_count (firstn i (RUN sm x os)) S.
Proof.
intros sm x os i L S He. rewrite (rp_firstn_S _ i _ He). unfold PresetRoomPos.rp_count.
rewrite PresetSecTotal.nsec_app, PresetSecTotal.tsec_app.
change (PresetSecTotal.nsec [PresetReqAt.HBulk L]) with 0%nat. change (PresetSecTotal.tsec [PresetReqAt.HBulk L]) with 0.
rewrite Nat.add_0_r, Z.add_0_r. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The live-set list steps.                                                     *)
(* a new block r joins the model's live list *)
Lemma rp_live_add : forall (M A d : list Z) r, Permutation M (A ++ d) -> Permutation (M ++ [r]) ((r :: A) ++ d).
Proof.
intros M A d r H. apply (Permutation_trans (Permutation_sym (Permutation_cons_append M r))). cbn [app].
apply perm_skip. exact H.
Qed.

(* a block r of the model's live list leaves it *)
Lemma rp_live_remove : forall (M' A d : list Z) r, Permutation (r :: M') (A ++ d) -> In r A ->
  Permutation M' (PresetReqAt.rm1 r A ++ d).
Proof.
intros M' A d r H Hin. rewrite <- (PresetReqAt.rm1_app_l r A d Hin).
apply Permutation_sym. apply PresetReqAt.rm1_perm_cons. apply Permutation_sym. exact H.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The trivial keep (the frame keeps room_pos_set_fs / room_pos_stack_free are above, the kit's).             *)
Lemma room_pos_keep_eq : forall sm x os i H0 hist S S', S' = S ->
  iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist S'.
Proof. intros sm x os i H0 hist S S' -> H. exact H. Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The bulk sub-position: inside the model event HBulk L at i, after the first k frees of L. The count is the
      position's at i: a bulk event counts nothing (rp_count_bulk_eq), and a free keeps both counts.             *)
Definition iface_room_pos_bulk (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
  (i : nat) (L : list Z) (k : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) : Prop :=
(exists d : list Z, (length d <= 3)%nat /\
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rmall (firstn k L) (PresetReqAt.hlive (firstn i (RUN sm x os))) ++ d)) /\
YGcfRoom.room_inv_cf S /\
YGcfRoom.quar_fifo_cf hist S /\ YGcfFrees.cf_hist_ok hist /\
YGcfFrees.cf_frees_follow H0 (PresetRunQ.hfrees_q (firstn i (RUN sm x os)) ++ PresetRunQ.qfilter (firstn k L)) hist /\
PresetRoomPos.rp_count (firstn i (RUN sm x os)) S.

Lemma room_pos_bulk_enter : forall sm x os i L H0 hist S,
  iface_room_pos sm x os i H0 hist S -> iface_room_pos_bulk sm x os i L 0 H0 hist S.
Proof.
intros sm x os i L H0 hist S (Hd & T & Q & N & F & C). unfold iface_room_pos_bulk.
assert (E0 : PresetRunQ.qfilter (firstn 0 L) = []) by reflexivity. rewrite E0, app_nil_r. cbn [firstn].
split; [exact Hd|]. split; [exact T|]. split; [exact Q|]. split; [exact N|]. split; [exact F | exact C].
Qed.

Lemma room_pos_bulk_exit : forall sm x os i L H0 hist S,
  nth_error (RUN sm x os) i = Some (PresetReqAt.HBulk L) ->
  iface_room_pos_bulk sm x os i L (length L) H0 hist S -> iface_room_pos sm x os (Datatypes.S i) H0 hist S.
Proof.
intros sm x os i L H0 hist S He (Hd & T & Q & N & F & C). rewrite firstn_all in Hd, F.
assert (C' : PresetRoomPos.rp_count (firstn (Datatypes.S i) (RUN sm x os)) S)
  by (rewrite (rp_count_bulk_eq sm x os i L S He); exact C).
destruct (rp_model_bulk sm x os i L He) as (_ & E1 & E2).
unfold PresetRoomPos.iface_room_pos. rewrite E1, (rp_q_list _ _ _ E2).
split; [exact Hd|]. split; [exact T|]. split; [exact Q|]. split; [exact N|]. split; [exact F | exact C'].
Qed.

Lemma room_pos_bulk_keep_eq : forall sm x os i L k H0 hist S S', S' = S ->
  iface_room_pos_bulk sm x os i L k H0 hist S -> iface_room_pos_bulk sm x os i L k H0 hist S'.
Proof. intros sm x os i L k H0 hist S S' -> H. exact H. Qed.

(* the frame keeps, by conversion: set_fs leaves st_chunks, so blocks, and both queues alone *)
Lemma room_pos_bulk_set_fs : forall sm x os i L k H0 hist S f,
  iface_room_pos_bulk sm x os i L k H0 hist S -> iface_room_pos_bulk sm x os i L k H0 hist (set_fs f S).
Proof. intros sm x os i L k H0 hist S f H. exact H. Qed.

Lemma room_pos_bulk_stack_free : forall sm x os i L k H0 hist S c p,
  iface_room_pos_bulk sm x os i L k H0 hist S -> iface_room_pos_bulk sm x os i L k H0 hist (stack_free_state c p S).
Proof. intros sm x os i L k H0 hist S c p H. exact H. Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The allocator keeps.                                                         *)
Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* free_cf PNull, the realloc trees' entry step, moves st_nev / st_internal_inited only *)
Lemma rp_frame_null : forall U tr S trc u S', Wf_cf U S -> apath (free_cf PNull tr S) trc (u, S') ->
  Wf_cf U S' /\ blocks S' = blocks S /\ blocks_bytes S' = blocks_bytes S /\ YGcfRoom.q_fifo S' = YGcfRoom.q_fifo S /\
  (ROOM_cf S -> ROOM_cf S') /\ (forall k, ROOM_cf_k S k -> ROOM_cf_k S' k) /\ (qtight S -> qtight S') /\
  (forall sm x os i H0 hist, iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist S').
Proof.
intros U tr S trc u S' W Hp. pose proof (ipost_apath _ _ _ _ (rl_free_null tr S) Hp) as E. cbn [snd] in E.
subst S'. destruct (st_internal_inited S).
- split; [exact (WfP_cf_tick _ 0 0 0 S W)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros H; exact H|].
  split; [intros k H; exact H|]. split; [intros H; exact H|]. intros sm x os i H0 hist H; exact H.
- split; [exact (WfP_cf_set_internal_inited_cf _ 0 0 0 _ true (WfP_cf_tick _ 0 0 0 S W))|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros H; exact H|].
  split; [intros k H; exact H|]. split; [intros H; exact H|]. intros sm x os i H0 hist H; exact H.
Qed.

(* one malloc_cf, at the cf level: the blocks, qtight, the FIFO suffix. The trace premise is the ADMISSION at S
   (the B' walker's restatement, commit 4564dd337bcd, taken here as the one home, owner
   ruling 2026-10-30 04:07Z); a fixed-trace caller passes admits_fix U tr S HU (In tr U), as this lemma did inside. *)
Lemma rp_alloc_parts : forall U S r tr trc p S' hist,
  universe_ok U -> Wf_cf U S -> ROOM_cf S -> 0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> admits U tr S ->
  apath (malloc_cf r tr S) trc (p, S') -> YGcfRoom.room_inv_cf S -> YGcfRoom.quar_fifo_cf hist S ->
  Wf_cf U S' /\ YGcfRoom.room_inv_cf S' /\ YGcfRoom.quar_fifo_cf hist S' /\
  (p = PNull -> blocks S' = blocks S) /\ (p <> PNull -> blocks S' = blocks S ++ [(p, r)]).
Proof.
intros U S r tr trc p S' hist HU W (Rs & Re & Rb) Hr Hl Htr Hap T HQ.
pose proof (malloc_cf_apath_post U S r tr trc (p, S') HU W Hr Hl Htr Rs Re Rb Hap) as MP.
destruct (YGcfRoom.rpost_apath _ true _ trc (p, S') (YGcfRoom.malloc_cf_fifo S r tr true) Hap) as (b & Ef & _).
cbn [snd] in Ef.
unfold malloc_post_cf in MP. destruct MP as (W' & _ & _ & _ & Bl & Q).
split; [exact W'|]. split; [exact (Q T)|]. split; [exact (YGcfRoom.quar_fifo_malloc_step hist S S' HQ Ef)|].
destruct p as [|o|rr o|c q]; cbv beta iota in Bl.
- split; [intros _; exact Bl | intros H; exfalso; exact (H eq_refl)].
- split; [intros H; discriminate H | intros _; exact (proj1 Bl)].
- split; [intros H; discriminate H | intros _; exact (proj1 Bl)].
- split; [intros H; discriminate H | intros _; exact (proj1 Bl)].
Qed.

(* one free_cf of a live (p, r), at the cf level, against any model list A that holds r.
   TWO CASES (free_cf's size test, Quarantine::Put: a chunk above kQuarantineMax is recycled at once; the ASan owner's
   change, commit 6e4492231127): rp_free_parts is the SMALL case (req_size r <= kQuarantineMax), its
   body today's; rp_free_parts_big below is the BIG case (the chunk is not quarantined: freed_cf S p = [], no history
   entry, mf unchanged). *)
Lemma rp_free_parts : forall U S p r tr trc S' (A d : list Z) H0 mf hist,
  universe_ok U -> Wf_cf U S -> batch_room_cf S -> admits U tr S -> In (p, r) (blocks S) -> p <> PNull ->
  req_size r <= kQuarantineMax ->
  apath (free_cf p tr S) trc (tt, S') ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (A ++ d) -> In r A ->
  YGcfRoom.room_inv_cf S -> YGcfRoom.quar_fifo_cf hist S -> YGcfFrees.cf_hist_ok hist ->
  YGcfFrees.cf_frees_follow H0 mf hist ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.rm1 r A ++ d) /\
  YGcfRoom.room_inv_cf S' /\ YGcfRoom.quar_fifo_cf (hist ++ YGcfRoom.freed_cf S p) S' /\
  YGcfFrees.cf_hist_ok (hist ++ YGcfRoom.freed_cf S p) /\
  YGcfFrees.cf_frees_follow H0 (mf ++ [r]) (hist ++ YGcfRoom.freed_cf S p).
Proof.
intros U S p r tr trc S' A d H0 mf hist HU W Rb Htr Hin Hnn Hsz Hap Hp Hr T HQ HN HF.
destruct (atok_cf_apath _ true _ trc (tt, S') (ml_free_cf U HU S p r tr W Rb (or_intror Hin) Htr) Hap) as (ns' & FP).
unfold free_post_ycf in FP. cbv zeta in FP. cbn [snd] in FP.
destruct FP as (_ & _ & _ & _ & (l1 & l2 & [[Hpn _] | Hb] & Hb') & Q); [exfalso; exact (Hnn Hpn)|].
destruct (YGcfRoom.rpost_apath _ true _ trc (tt, S') (YGcfRoom.free_cf_fifo p tr S true) Hap) as (b & P & E).
cbn [snd] in E.
destruct (YGcfFrees.cf_frees_step_free U H0 mf hist S p S' P W HQ HN HF E) as (Q' & N' & F').
assert (Ereq : map ck_req (YGcfRoom.freed_cf S p) = [r]).
{ destruct (find_user_block_cf U 0 0 0 S p r (WfR_of_WfP_cf U 0 0 0 S W) Hin) as (k & Hf & _ & _ & _ & Hk).
  assert (Hck : (ck_n k <=? kQuarantineMax) = true) by (apply Z.leb_le; unfold ck_n; rewrite Hk; exact Hsz).
  unfold YGcfRoom.freed_cf. destruct p as [|o|rr o|c q]; [exfalso; apply Hnn; reflexivity| | |];
  cbv beta iota; rewrite Hf, Hck; cbn [map ck_req]; rewrite Hk; reflexivity. }
rewrite Ereq in F'.
split; [|split; [exact (Q T)|split; [exact Q'|split; [exact N' | exact F']]]].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) with (map snd (blocks S')).
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in Hp.
rewrite Hb'. rewrite Hb in Hp. apply rp_live_remove; [|exact Hr].
rewrite map_app in Hp |- *. cbn [map fst snd] in Hp.
apply (Permutation_trans (Permutation_middle (map snd l1) (map snd l2) r)). exact Hp.
Qed.

(* the BIG case: the chunk is recycled at once, so the history and the model's free list stay *)
Lemma rp_free_parts_big : forall U S p r tr trc S' (A d : list Z) H0 mf hist,
  universe_ok U -> Wf_cf U S -> batch_room_cf S -> admits U tr S -> In (p, r) (blocks S) -> p <> PNull ->
  kQuarantineMax < req_size r ->
  apath (free_cf p tr S) trc (tt, S') ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (A ++ d) -> In r A ->
  YGcfRoom.room_inv_cf S -> YGcfRoom.quar_fifo_cf hist S -> YGcfFrees.cf_hist_ok hist ->
  YGcfFrees.cf_frees_follow H0 mf hist ->
  YGcfRoom.freed_cf S p = [] /\
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) (PresetReqAt.rm1 r A ++ d) /\
  YGcfRoom.room_inv_cf S' /\ YGcfRoom.quar_fifo_cf hist S' /\
  YGcfFrees.cf_hist_ok hist /\ YGcfFrees.cf_frees_follow H0 mf hist.
Proof.
intros U S p r tr trc S' A d H0 mf hist HU W Rb Htr Hin Hnn Hsz Hap Hp Hr T HQ HN HF.
destruct (atok_cf_apath _ true _ trc (tt, S') (ml_free_cf U HU S p r tr W Rb (or_intror Hin) Htr) Hap) as (ns' & FP).
unfold free_post_ycf in FP. cbv zeta in FP. cbn [snd] in FP.
destruct FP as (_ & _ & _ & _ & (l1 & l2 & [[Hpn _] | Hb] & Hb') & Q); [exfalso; exact (Hnn Hpn)|].
destruct (YGcfRoom.rpost_apath _ true _ trc (tt, S') (YGcfRoom.free_cf_fifo p tr S true) Hap) as (b & P & E).
cbn [snd] in E.
assert (Efr : YGcfRoom.freed_cf S p = []).
{ destruct (find_user_block_cf U 0 0 0 S p r (WfR_of_WfP_cf U 0 0 0 S W) Hin) as (k & Hf & _ & _ & _ & Hk).
  assert (Hck : (ck_n k <=? kQuarantineMax) = false) by (apply Z.leb_gt; unfold ck_n; rewrite Hk; exact Hsz).
  unfold YGcfRoom.freed_cf. destruct p as [|o|rr o|c q]; [exfalso; apply Hnn; reflexivity| | |];
  cbv beta iota; rewrite Hf, Hck; reflexivity. }
pose proof (YGcfRoom.quar_fifo_free_step hist S p S' P HQ E) as Q'. rewrite Efr, app_nil_r in Q'.
split; [exact Efr|].
split; [|split; [exact (Q T)|split; [exact Q'|split; [exact HN | exact HF]]]].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) with (map snd (blocks S')).
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in Hp.
rewrite Hb'. rewrite Hb in Hp. apply rp_live_remove; [|exact Hr].
rewrite map_app in Hp |- *. cbn [map fst snd] in Hp.
apply (Permutation_trans (Permutation_middle (map snd l1) (map snd l2) r)). exact Hp.
Qed.

(* THE A14 STEPS (A15): the allocator call's count step, read off the closed premise
   YGcfSecsStep.secs_steps_cf at this Section's image ci; its proof is the allocator-model owner's
   YGcfSecsStep.secs_steps_cf_holds, so these lemmas carry no hypothesis of their own. *)
Lemma rp_secs_malloc : forall n tr S trc r, YGcfSecsStep.secs_steps_cf ->
  apath (malloc_cf n tr S) trc r -> YGcfNames.secs_call_post n S r.
Proof. intros n tr S trc r A H. exact (proj1 (A ci) n tr S trc r H). Qed.

Lemma rp_secs_free : forall p tr S trc S', YGcfSecsStep.secs_steps_cf ->
  apath (free_cf p tr S) trc (tt, S') -> YGcfSecsStep.secs_same S S'.
Proof. intros p tr S trc S' A H. exact (proj1 (proj2 (A ci)) p tr S trc S' H). Qed.

Lemma rp_secs_realloc : forall p n tr S trc r, YGcfSecsStep.secs_steps_cf ->
  apath (realloc_tree_with malloc_cf free_cf p n tr S) trc r -> YGcfNames.secs_call_post n S r.
Proof. intros p n tr S trc r A H. exact (proj1 (proj2 (proj2 (A ci))) p n tr S trc r H). Qed.

Lemma rp_secs_realloc0 : forall n tr S trc r, YGcfSecsStep.secs_steps_cf ->
  apath (realloc_null_tree_with malloc_cf free_cf n tr S) trc r -> YGcfNames.secs_call_post n S r.
Proof. intros n tr S trc r A H. exact (proj1 (proj2 (proj2 (proj2 (A ci)))) n tr S trc r H). Qed.

Variable segs : list Segment.
Variable B : asyms.

Theorem room_pos_keep_alloc :
  forall ly S Hp W regs mem md ch sm x os i H0 hist r tr trc p S',
  acall_pre_cf segs B ly S Hp W regs mem md ch ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> In tr (as_universe B) ->
  apath (malloc_cf r tr S) trc (p, S') -> p <> PNull ->
  iface_room_pos sm x os i H0 hist S -> nth_error (RUN sm x os) i = Some (PresetReqAt.HMal r) ->
  iface_room_pos sm x os (Datatypes.S i) H0 hist S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist r tr trc p S' Hpre Hr Hl Htr Hap Hnn Hpos He.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
pose proof (ROOM_cf_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as R0.
destruct Hpos as ((d & Hd & Hp') & T & HQ & HN & HF & HC).
destruct (rp_alloc_parts _ S r tr trc p S' hist HU W0 R0 Hr Hl (admits_fix _ tr S HU Htr) Hap T HQ) as (_ & T' & Q' & _ & Bl).
assert (HC' : PresetRoomPos.rp_count (firstn (Datatypes.S i) (RUN sm x os)) S').
{ rewrite (rp_firstn_S _ i _ He). apply (rp_count_snoc _ _ S S' HC). intros A.
  exact (rp_post_mal r S p S' Hnn (rp_secs_malloc r tr S trc (p, S') A Hap)). }
destruct (rp_model_mal sm x os i r He) as (E1 & E2).
unfold PresetRoomPos.iface_room_pos. rewrite E1, (rp_q_same _ _ E2).
split; [|split; [exact T'|split; [exact Q'|split; [exact HN | split; [exact HF | exact HC']]]]].
exists d. split; [exact Hd|].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) with (map snd (blocks S')).
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in Hp'.
rewrite (Bl Hnn), map_app. cbn [map fst snd]. exact (rp_live_add _ _ _ r Hp').
Qed.

Theorem room_pos_keep_alloc_null :
  forall ly S Hp W regs mem md ch sm x os i H0 hist r tr trc S',
  acall_pre_cf segs B ly S Hp W regs mem md ch ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> In tr (as_universe B) ->
  apath (malloc_cf r tr S) trc (PNull, S') ->
  iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist r tr trc S' Hpre Hr Hl Htr Hap Hpos.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
pose proof (ROOM_cf_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as R0.
destruct Hpos as ((d & Hd & Hp') & T & HQ & HN & HF & HC).
destruct (rp_alloc_parts _ S r tr trc PNull S' hist HU W0 R0 Hr Hl (admits_fix _ tr S HU Htr) Hap T HQ) as (_ & T' & Q' & Bl & _).
assert (HC' : PresetRoomPos.rp_count (firstn i (RUN sm x os)) S').
{ apply (rp_count_keep _ S S' HC). intros A. exact (rp_post_null r S S' (rp_secs_malloc r tr S trc (PNull, S') A Hap)). }
split; [|split; [exact T'|split; [exact Q'|split; [exact HN | split; [exact HF | exact HC']]]]].
exists d. split; [exact Hd|].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) with (map snd (blocks S')).
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in Hp'.
rewrite (Bl eq_refl). exact Hp'.
Qed.

(* both sides of free_cf's size test: the enqueue side appends r to the quarantine's history, the recycle side
   appends nothing (freed_cf S p = [], and hfrees_q drops r) *)
Theorem room_pos_keep_free :
  forall ly S Hp W regs mem md ch sm x os i H0 hist p r tr trc S',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> admits (as_universe B) tr S ->
  In (p, r) (blocks S) -> p <> PNull -> apath (free_cf p tr S) trc (tt, S') ->
  iface_room_pos sm x os i H0 hist S -> nth_error (RUN sm x os) i = Some (PresetReqAt.HFr r) ->
  iface_room_pos sm x os (Datatypes.S i) H0 (hist ++ YGcfRoom.freed_cf S p) S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist p r tr trc S' Hpre Htr Hin Hnn Hap Hpos He.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
destruct (ROOM_cf_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (_ & _ & Rb).
destruct Hpos as ((d & Hd & Hp') & T & HQ & HN & HF & HC).
assert (HC' : PresetRoomPos.rp_count (firstn (Datatypes.S i) (RUN sm x os)) S').
{ rewrite (rp_firstn_S _ i _ He). apply (rp_count_snoc_same _ (PresetReqAt.HFr r) S S' eq_refl eq_refl HC). intros A.
  exact (rp_secs_free p tr S trc S' A Hap). }
destruct (rp_model_fr sm x os i r He) as (Hlv & E1 & E2).
unfold PresetRoomPos.iface_room_pos. rewrite E1, (rp_q_list _ _ [r] E2).
destruct (Z_le_gt_dec (req_size r) kQuarantineMax) as [Hsz|Hbig].
- destruct (rp_free_parts _ S p r tr trc S' _ d H0 _ hist HU W0 Rb Htr Hin Hnn Hsz Hap Hp' Hlv T HQ HN HF)
    as (P' & T' & Q' & N' & F').
  rewrite (PresetRunQ.qfilter_small _ Hsz).
  split; [exists d; split; [exact Hd | exact P']|].
  split; [exact T'|split; [exact Q'|split; [exact N' | split; [exact F' | exact HC']]]].
- destruct (rp_free_parts_big _ S p r tr trc S' _ d H0 _ hist HU W0 Rb Htr Hin Hnn ltac:(lia) Hap Hp' Hlv T HQ HN HF)
    as (Efr & P' & T' & Q' & N' & F').
  rewrite Efr, (PresetRunQ.qfilter_big r ltac:(lia)), !app_nil_r.
  split; [exists d; split; [exact Hd | exact P']|].
  split; [exact T'|split; [exact Q'|split; [exact N' | split; [exact F' | exact HC']]]].
Qed.

Theorem room_pos_keep_free_null :
  forall ly S Hp W regs mem md ch sm x os i H0 hist tr trc S',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> In tr (as_universe B) ->
  apath (free_cf PNull tr S) trc (tt, S') ->
  iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist tr trc S' Hpre Htr Hap Hpos.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & _ & _).
destruct (rp_frame_null _ tr S trc tt S' W0 Hap) as (_ & _ & _ & _ & _ & _ & _ & K). exact (K _ _ _ _ _ _ Hpos).
Qed.

(* a realloc's model step is a malloc of r and a free of m: from the live list A to r :: rm1 m A *)
Lemma rp_rm1_cons_perm : forall m r (A : list Z), In m A ->
  Permutation (PresetReqAt.rm1 m (r :: A)) (r :: PresetReqAt.rm1 m A).
Proof.
intros m r A Hm. cbn [PresetReqAt.rm1]. destruct (Z.eqb_spec r m) as [->|_]; [|apply Permutation_refl].
exact (PresetReqAt.rm1_in m A Hm).
Qed.

(* THE ADMISSION AT THE CALL STATE S, not the fixed-trace `In tr (as_universe B)` (the B' walker's restatement,
   TxPutRoomPos102.v c05c5ea74cc0 at commit 4564dd337bcd, taken as the one home on the
   unit owner's ruling 2026-10-30 04:07Z; the second half of the free lemmas' move to `admits .. S`). The
   state-free prhtx_trace gives tx_put's realloc trace in the engine's form `inU (as_universe B) ..`, which the fixed
   list does not hold. The admission is carried S -> S1 -> S2 by YG01.admits_keep over the depot steps of the free
   (NULL) frame step (YGcfAmx2.ipost_free_null_depot) and of malloc_cf (YGcfAmx.dep_malloc_cf). A fixed-trace caller
   passes admits_fix (as_universe B) tr S HU (In tr ..), HU from rl_of_acall_pre_cf. *)
Theorem room_pos_keep_realloc :
  forall ly S Hp W regs mem md ch sm x os i H0 hist p m r tr trc q S',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf_k S RK_realloc ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> admits (as_universe B) tr S ->
  In (p, m) (blocks S) -> p <> PNull ->
  apath (realloc_tree_with malloc_cf free_cf p r tr S) trc (q, S') -> q <> PNull ->
  iface_room_pos sm x os i H0 hist S -> nth_error (RUN sm x os) i = Some (PresetReqAt.HRe m r) ->
  exists hist', iface_room_pos sm x os (Datatypes.S i) H0 hist' S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist p m r tr trc q S' Hpre RK Hr Hl Htr Hin Hnn Hap Hqn Hpos He.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
assert (HC' : PresetRoomPos.rp_count (firstn (Datatypes.S i) (RUN sm x os)) S').
{ pose proof Hpos as (_ & _ & _ & _ & _ & HC). rewrite (rp_firstn_S _ i _ He). apply (rp_count_snoc _ _ S S' HC).
  intros A. exact (rp_post_re m r S q S' Hqn (rp_secs_realloc p r tr S trc (q, S') A Hap)). }
unfold realloc_tree_with, YG00.bind in Hap.
destruct (rl_apath_ibind _ _ _ _ Hap) as (tr1 & tr2 & [u S1] & H1 & H2). cbv beta iota in H2.
pose proof (ipost_apath _ _ _ _ (YGcfAmx2.ipost_free_null_depot tr S) H1) as D1. cbn [snd] in D1.
pose proof (admits_keep _ tr S S1 Htr (or_introl D1)) as Htr1.
destruct (rp_frame_null _ tr S tr1 u S1 W0 H1) as (W1 & Bl1 & Bb1 & Ef1 & _ & RKk & _ & Kp).
pose proof (Kp _ _ _ _ _ _ Hpos) as Hpos1. pose proof (RKk _ RK) as RK1. clear Kp RKk.
destruct (rl_apath_ibind _ _ _ _ H2) as (tr3 & tr4 & [q0 S2] & H3 & H4). cbv beta iota in H4.
pose proof (ipost_apath _ _ _ _ (YGcfAmx.dep_malloc_cf r tr S1) H3) as D2. cbn [snd] in D2.
pose proof (admits_keep _ tr S1 S2 Htr1 D2) as Htr2.
destruct Hpos1 as ((d & Hd & Hp1) & T1 & HQ1 & HN & HF & _).
pose proof (RK_room S1 _ RK1) as R1.
destruct (rp_alloc_parts _ S1 r tr tr3 q0 S2 hist HU W1 R1 Hr ltac:(rewrite Bb1; exact Hl) Htr1 H3 T1 HQ1)
  as (W2 & T2 & Q2 & _ & Bl2).
pose proof (malloc_room_keep_cf 1 r tr S1 tr3 q0 S2 (room_shape_cf_of_WfP_cf _ _ _ _ _ W1) RK1 H3) as RK2.
destruct (RK_room S2 _ RK2) as (_ & _ & Rb2).
destruct (rp_model_re sm x os i m r He) as (Hlv & E1 & E2).
destruct q0 as [|o|rr o|c q1]; cbv beta iota in H4;
  [apply rl_apath_ret in H4; injection H4 as E4 _; exfalso; exact (Hqn E4) | | |].
all: destruct (rl_apath_ibind _ _ _ _ H4) as (tr5 & tr6 & [u5 S3] & H5 & H6); cbv beta iota in H6;
  apply rl_apath_ret in H6; injection H6 as _ E6; subst S3; destruct u5.
all: specialize (Bl2 ltac:(discriminate));
  assert (Hin2 : In (p, m) (blocks S2)) by (rewrite Bl2, Bl1; apply in_or_app; left; exact Hin);
  assert (Hp2 : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    ((r :: PresetReqAt.hlive (firstn i (RUN sm x os))) ++ d))
    by (change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2));
        change (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) with (map snd (blocks S1)) in Hp1;
        rewrite Bl2, map_app; cbn [map fst snd]; exact (rp_live_add _ _ _ r Hp1));
  exists (hist ++ YGcfRoom.freed_cf S2 p); unfold PresetRoomPos.iface_room_pos; rewrite E1, (rp_q_list _ _ [m] E2);
  destruct (Z_le_gt_dec (req_size m) kQuarantineMax) as [Hsz|Hbig];
  first
  [ destruct (rp_free_parts _ S2 p m tr tr5 S' _ d H0 _ hist HU W2 Rb2 Htr2 Hin2 Hnn Hsz H5 Hp2 (or_intror Hlv) T2 Q2 HN HF)
      as (P' & T' & Q' & N' & F');
    rewrite (PresetRunQ.qfilter_small _ Hsz)
  | destruct (rp_free_parts_big _ S2 p m tr tr5 S' _ d H0 _ hist HU W2 Rb2 Htr2 Hin2 Hnn ltac:(lia) H5 Hp2 (or_intror Hlv)
      T2 Q2 HN HF) as (Efr & P' & T' & Q' & N' & F');
    rewrite Efr, (PresetRunQ.qfilter_big m ltac:(lia)), !app_nil_r ];
  (split; [exists d; split; [exact Hd|];
           exact (Permutation_trans P' (Permutation_app_tail d (rp_rm1_cons_perm m r _ Hlv)))|]);
  (split; [exact T'|split; [exact Q'|split; [exact N' | split; [exact F' | exact HC']]]]).
Qed.

Theorem room_pos_keep_realloc_null :
  forall ly S Hp W regs mem md ch sm x os i H0 hist p r tr trc S',
  acall_pre_cf segs B ly S Hp W regs mem md ch ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> In tr (as_universe B) ->
  apath (realloc_tree_with malloc_cf free_cf p r tr S) trc (PNull, S') ->
  iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist p r tr trc S' Hpre Hr Hl Htr Hap Hpos.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
assert (HC' : PresetRoomPos.rp_count (firstn i (RUN sm x os)) S').
{ pose proof Hpos as (_ & _ & _ & _ & _ & HC). apply (rp_count_keep _ S S' HC).
  intros A. exact (rp_post_null r S S' (rp_secs_realloc p r tr S trc (PNull, S') A Hap)). }
pose proof (ROOM_cf_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as R0.
unfold realloc_tree_with, YG00.bind in Hap.
destruct (rl_apath_ibind _ _ _ _ Hap) as (tr1 & tr2 & [u S1] & H1 & H2). cbv beta iota in H2.
destruct (rp_frame_null _ tr S tr1 u S1 W0 H1) as (W1 & Bl1 & Bb1 & Ef1 & Rk & _ & _ & Kp).
pose proof (Kp _ _ _ _ _ _ Hpos) as Hpos1. pose proof (Rk R0) as R1. clear Kp Rk.
destruct (rl_apath_ibind _ _ _ _ H2) as (tr3 & tr4 & [q0 S2] & H3 & H4). cbv beta iota in H4.
destruct Hpos1 as ((d & Hd & Hp1) & T1 & HQ1 & HN & HF & _).
destruct (rp_alloc_parts _ S1 r tr tr3 q0 S2 hist HU W1 R1 Hr ltac:(rewrite Bb1; exact Hl) (admits_fix _ tr S1 HU Htr) H3 T1 HQ1)
  as (_ & T2 & Q2 & Bl2 & _).
destruct q0 as [|o|rr o|c q1]; cbv beta iota in H4.
- apply rl_apath_ret in H4. assert (ES : S' = S2) by congruence. subst S'.
  split; [|split; [exact T2|split; [exact Q2|split; [exact HN | split; [exact HF | exact HC']]]]].
  exists d. split; [exact Hd|].
  change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
  change (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) with (map snd (blocks S1)) in Hp1.
  rewrite (Bl2 eq_refl). exact Hp1.
- destruct (rl_apath_ibind _ _ _ _ H4) as (tr5 & tr6 & [u5 S3] & H5 & H6). cbv beta iota in H6.
  apply rl_apath_ret in H6. discriminate H6.
- destruct (rl_apath_ibind _ _ _ _ H4) as (tr5 & tr6 & [u5 S3] & H5 & H6). cbv beta iota in H6.
  apply rl_apath_ret in H6. discriminate H6.
- destruct (rl_apath_ibind _ _ _ _ H4) as (tr5 & tr6 & [u5 S3] & H5 & H6). cbv beta iota in H6.
  apply rl_apath_ret in H6. discriminate H6.
Qed.

(* realloc(NULL, r) is a malloc event (EGrow 0 n => HMal, PresetReqAt.v:85) *)
(* the admission at the call state S, as room_pos_keep_realloc above (the same restatement) *)
Theorem room_pos_keep_realloc0 :
  forall ly S Hp W regs mem md ch sm x os i H0 hist r tr trc q S',
  acall_pre_cf segs B ly S Hp W regs mem md ch ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> admits (as_universe B) tr S ->
  apath (realloc_null_tree_with malloc_cf free_cf r tr S) trc (q, S') -> q <> PNull ->
  iface_room_pos sm x os i H0 hist S -> nth_error (RUN sm x os) i = Some (PresetReqAt.HMal r) ->
  iface_room_pos sm x os (Datatypes.S i) H0 hist S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist r tr trc q S' Hpre Hr Hl Htr Hap Hqn Hpos He.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
pose proof (ROOM_cf_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as R0.
assert (HC' : PresetRoomPos.rp_count (firstn (Datatypes.S i) (RUN sm x os)) S').
{ pose proof Hpos as (_ & _ & _ & _ & _ & HC). rewrite (rp_firstn_S _ i _ He). apply (rp_count_snoc _ _ S S' HC).
  intros A. exact (rp_post_mal r S q S' Hqn (rp_secs_realloc0 r tr S trc (q, S') A Hap)). }
unfold realloc_null_tree_with, YG00.bind in Hap.
destruct (rl_apath_ibind _ _ _ _ Hap) as (tr1 & tr2 & [u S1] & H1 & H2). cbv beta iota in H2.
pose proof (ipost_apath _ _ _ _ (YGcfAmx2.ipost_free_null_depot tr S) H1) as D1. cbn [snd] in D1.
pose proof (admits_keep _ tr S S1 Htr (or_introl D1)) as Htr1.
destruct (rp_frame_null _ tr S tr1 u S1 W0 H1) as (W1 & Bl1 & Bb1 & Ef1 & Rk & _ & _ & Kp).
pose proof (Kp _ _ _ _ _ _ Hpos) as Hpos1. pose proof (Rk R0) as R1. clear Kp Rk.
destruct Hpos1 as ((d & Hd & Hp1) & T1 & HQ1 & HN & HF & _).
destruct (rp_alloc_parts _ S1 r tr tr2 q S' hist HU W1 R1 Hr ltac:(rewrite Bb1; exact Hl) Htr1 H2 T1 HQ1)
  as (_ & T' & Q' & _ & Bl).
destruct (rp_model_mal sm x os i r He) as (E1 & E2).
unfold PresetRoomPos.iface_room_pos. rewrite E1, (rp_q_same _ _ E2).
split; [|split; [exact T'|split; [exact Q'|split; [exact HN | split; [exact HF | exact HC']]]]].
exists d. split; [exact Hd|].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) with (map snd (blocks S')).
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) with (map snd (blocks S1)) in Hp1.
rewrite (Bl Hqn), map_app. cbn [map fst snd]. exact (rp_live_add _ _ _ r Hp1).
Qed.

Theorem room_pos_keep_realloc0_null :
  forall ly S Hp W regs mem md ch sm x os i H0 hist r tr trc S',
  acall_pre_cf segs B ly S Hp W regs mem md ch ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> In tr (as_universe B) ->
  apath (realloc_null_tree_with malloc_cf free_cf r tr S) trc (PNull, S') ->
  iface_room_pos sm x os i H0 hist S -> iface_room_pos sm x os i H0 hist S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i H0 hist r tr trc S' Hpre Hr Hl Htr Hap Hpos.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
pose proof (ROOM_cf_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as R0.
assert (HC' : PresetRoomPos.rp_count (firstn i (RUN sm x os)) S').
{ pose proof Hpos as (_ & _ & _ & _ & _ & HC). apply (rp_count_keep _ S S' HC).
  intros A. exact (rp_post_null r S S' (rp_secs_realloc0 r tr S trc (PNull, S') A Hap)). }
unfold realloc_null_tree_with, YG00.bind in Hap.
destruct (rl_apath_ibind _ _ _ _ Hap) as (tr1 & tr2 & [u S1] & H1 & H2). cbv beta iota in H2.
destruct (rp_frame_null _ tr S tr1 u S1 W0 H1) as (W1 & Bl1 & Bb1 & Ef1 & Rk & _ & _ & Kp).
pose proof (Kp _ _ _ _ _ _ Hpos) as Hpos1. pose proof (Rk R0) as R1. clear Kp Rk.
destruct Hpos1 as ((d & Hd & Hp1) & T1 & HQ1 & HN & HF & _).
destruct (rp_alloc_parts _ S1 r tr tr2 PNull S' hist HU W1 R1 Hr ltac:(rewrite Bb1; exact Hl) (admits_fix _ tr S1 HU Htr) H2 T1 HQ1)
  as (_ & T' & Q' & Bl & _).
split; [|split; [exact T'|split; [exact Q'|split; [exact HN | split; [exact HF | exact HC']]]]].
exists d. split; [exact Hd|].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S')) with (map snd (blocks S')).
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S1)) with (map snd (blocks S1)) in Hp1.
rewrite (Bl eq_refl). exact Hp1.
Qed.

(* one free_cf inside a bulk event: the k-th element of the model's L, on either side of free_cf's size test *)
Theorem room_pos_keep_bulk_free :
  forall ly S Hp W regs mem md ch sm x os i L k H0 hist p r tr trc S',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> admits (as_universe B) tr S ->
  In (p, r) (blocks S) -> p <> PNull -> apath (free_cf p tr S) trc (tt, S') ->
  nth_error (RUN sm x os) i = Some (PresetReqAt.HBulk L) -> nth_error L k = Some r ->
  iface_room_pos_bulk sm x os i L k H0 hist S ->
  iface_room_pos_bulk sm x os i L (Datatypes.S k) H0 (hist ++ YGcfRoom.freed_cf S p) S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i L k H0 hist p r tr trc S' Hpre Htr Hin Hnn Hap He Hk Hpos.
destruct (rl_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (W0 & HU & _).
destruct (ROOM_cf_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) as (_ & _ & Rb).
destruct Hpos as ((d & Hd & Hp') & T & HQ & HN & HF & HC).
assert (HC' : PresetRoomPos.rp_count (firstn i (RUN sm x os)) S').
{ apply (rp_count_keep_same _ S S' HC). intros A. exact (rp_secs_free p tr S trc S' A Hap). }
destruct (rp_model_bulk sm x os i L He) as (Hsub & _ & _).
pose proof (rp_bulk_in L _ k r Hsub Hk) as Hlv.
destruct (rp_bulk_step L (PresetReqAt.hlive (firstn i (RUN sm x os))) k r Hk) as (E1 & E2).
unfold iface_room_pos_bulk. rewrite E1, E2, PresetRunQ.qfilter_app.
destruct (Z_le_gt_dec (req_size r) kQuarantineMax) as [Hsz|Hbig].
- destruct (rp_free_parts _ S p r tr trc S' _ d H0 _ hist HU W0 Rb Htr Hin Hnn Hsz Hap Hp' Hlv T HQ HN HF)
    as (P' & T' & Q' & N' & F').
  rewrite (PresetRunQ.qfilter_small _ Hsz), app_assoc.
  split; [exists d; split; [exact Hd | exact P']|].
  split; [exact T'|split; [exact Q'|split; [exact N' | split; [exact F' | exact HC']]]].
- destruct (rp_free_parts_big _ S p r tr trc S' _ d H0 _ hist HU W0 Rb Htr Hin Hnn ltac:(lia) Hap Hp' Hlv T HQ HN HF)
    as (Efr & P' & T' & Q' & N' & F').
  rewrite Efr, (PresetRunQ.qfilter_big r ltac:(lia)), !app_nil_r.
  split; [exists d; split; [exact Hd | exact P']|].
  split; [exact T'|split; [exact Q'|split; [exact N' | split; [exact F' | exact HC']]]].
Qed.

(* a NULL free inside a bulk event (pj_free's fuzz_free(NULL): no model event, the B' walker's internal file PJFREE-ORDER.md): the
   sub-position k stays; free_cf PNull moves st_nev / st_internal_inited only (YGcfRoomLive.rl_free_null) *)
Theorem room_pos_bulk_keep_free_null :
  forall ly S Hp W regs mem md ch sm x os i L k H0 hist tr trc S',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> In tr (as_universe B) ->
  apath (free_cf PNull tr S) trc (tt, S') ->
  iface_room_pos_bulk sm x os i L k H0 hist S -> iface_room_pos_bulk sm x os i L k H0 hist S'.
Proof.
intros ly S Hp W regs mem md ch sm x os i L k H0 hist tr trc S' _ _ Hap Hpos.
pose proof (ipost_apath _ _ _ _ (rl_free_null tr S) Hap) as E. cbn [snd] in E. subst S'.
destruct (st_internal_inited S); exact Hpos.
Qed.

End K.

(* The audit of the COUNT keeps (A15 / A16): no axiom and no hypothesis beyond each statement's own premises;
   the count conjunct's secs_steps_cf is a premise INSIDE iface_room_pos, proved closed by
   YGcfSecsStep.secs_steps_cf_holds. *)
Print Assumptions room_pos_keep_alloc.
Print Assumptions room_pos_keep_realloc.
Print Assumptions room_pos_keep_bulk_free.
Print Assumptions room_pos_bulk_exit.
Print Assumptions YGcfSecsStep.secs_steps_cf_holds.
