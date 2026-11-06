(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/PixChk.v; 568 of its 592 lines of code are new or changed and 47 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the cf layer's realloc facts at the INDEX-KEYED dead set, image-free (only the generic model),
   taken by path by fuzz_preset's primed realloc composition and by the layer's. They are the PRODUCER side of the
   primed realloc composition (YGcfReallocComposeRh, YGcfInstReallocK.arealloc_realizes_cf_k_of_parts) at the index key: the realloc's dead set is
   the per-call dead set over the slots live at the realloc's ENTRY S, and the inner free's set, keyed at the inner
   free's own entry (after the inner malloc), must lie in it.
   - realloc_dead_ix_compose: that inclusion, from rec_live_lt (the backward liveness below an index L) across the inner
     malloc and the keep of every st_secs entry at an index >= L across the inner free.
   - malloc_cf_secs_keep: malloc_cf only appends to st_secs and, below the entry length, rewrites only errbuf control
     entries, into not-live ones (sec_alloc YG00.v:349-365; errb_set_size, errb_retire, errb_map_cf YG00cf.v:93-129).
     So the backward liveness holds below the entry length. Without the index guard it fails at the live secondary that
     sec_alloc appends (YG00.v:358), which is why rec_live_lt is the step relation here.
   - free_cf_fresh_keep: free_cf leaves every st_secs entry at an index >= L as it is.
   - realloc_dead_ix_of_paths: the chain along the realloc tree (ReallocP.v:28-35: free_cf PNull, malloc_cf n, free_cf p)
     from Wf_cf at the realloc's entry and q <> p.
   THE QUARANTINE-DRAIN RISK (measured first). free_cf may recycle chunks: the freed chunk itself when it is above the
   quarantine's max_size (YG00cf.v:353), and the quarantine's items when it drains (maybe_drain_cf YG00cf.v:305-321,
   do_recycle YG00.v:516-523). A recycled secondary marks its own st_secs entry dead IN PLACE (sec_dealloc, YG00.v:491):
   no path of free_cf reorders, removes or appends an st_secs entry (free_cf_secs_mark). But the recycled index is the
   recycled chunk's own, and the model checks that chunk only by mem_chunk (YG00.v:503), so the model alone does not keep
   a drain off an entry at an index >= L. free_cf_fresh_keep therefore takes two premises:
   (P1) every item of q_items S (YG01.v:302) that is a secondary PSec r _ has r < L;
   (P2) so has the freed chunk, find_user (st_chunks S) p.
   realloc_dead_ix_of_paths discharges both from Wf_cf at the realloc's entry: wq_items (YG01.v:389) puts every item in
   st_chunks, chunk_ok_cf (YG01cf.v:110-119) gives every secondary chunk an st_secs entry, the entry step free_cf PNull and
   malloc_cf leave both queues alone (rx_null_free, malloc_cf_frame_ix), and malloc_cf adds only the chunk of the block q
   it returns, so the freed chunk is an entry chunk when q <> p.
   THE KEY. The per-call dead set is the core's YGcfRehidePost.dead_shadow_new (:62-64), keyed by slot index: the slots
   live at the call's entry S and dead at its exit. Its body is the core's (cgif/cgif_file_fuzzer lib/YGcfRehidePost.v, file sha256 628cbbe8b0a2; donor not
   released), which is the text of F6DeadShadowNull.v:247-249 (sha256 5d190a293bbb; internal record) verbatim under the name
   dead_shadow_new. dead_sec, rh_lo and rh_hi are YGcfRehidePost.v's too (:34-36, :29-30).
   rec_live_lt is backward liveness (a slot live at the step's exit was live at its entry, with the same length) with
   an index guard.
   The every-return posts are YG0k.v's apost; rx_bind is YGcfRecStep.v's apost_bind_P and rx_base its sc_step, restated
   with a case for a match added.
   No image constant; no function is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM05.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The index-guarded backward liveness, and the realloc composer's set.        *)
(* For the slots below L only: a slot live at S' below L was live at S, with the same length. *)
Definition rec_live_lt (L : nat) (S S' : astate) : Prop :=
  forall r sm', (r < L)%nat -> nth_error (st_secs S') r = Some sm' -> sm_live sm' = true ->
    exists sm, nth_error (st_secs S) r = Some sm /\ sm_live sm = true /\ sm_len sm = sm_len sm'.

Section c. Context {rc : YM05.RunCeil}.
(* The inner free's set (entry S1, layout ly1) lies in the realloc's set (entry S, layout ly). A witness r < L was live at
   S by rec_live_lt, and layout_le pins its ly_sec; a witness r >= L keeps at S2 the live entry it had at S1, which
   contradicts dead_sec. *)
Lemma realloc_dead_ix_compose : forall L ly ly1 S S1 S2 a,
  rec_live_lt L S S1 ->
  (forall r, (L <= r)%nat -> nth_error (st_secs S2) r = nth_error (st_secs S1) r) ->
  layout_le L ly ly1 ->
  dead_shadow_new ly1 S1 S2 a -> dead_shadow_new ly S S2 a.
Proof.
intros L ly ly1 S S1 S2 a RL KF LE (r & sm & sm0 & (Hn & Hl & Hr & Hia & Hl0) & Hn0 & Hv0 & Hlen & Ha).
destruct (Nat.lt_ge_cases r L) as [Lt|Ge].
- destruct (RL r sm0 Lt Hn0 Hv0) as (sm1 & Hn1 & Hv1 & E1).
  assert (ES : ly_sec ly1 r = ly_sec ly r).
  { unfold layout_le in LE. destruct LE as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&X). exact (X r Lt). }
  rewrite ES in Hia, Ha.
  exists r, sm, sm1. split; [exact (conj Hn (conj Hl (conj Hr (conj Hia Hl0))))|].
  split; [exact Hn1|]. split; [exact Hv1|]. split; [lia | exact Ha].
- exfalso. rewrite (KF r Ge) in Hn. rewrite Hn in Hn0. injection Hn0 as <-. rewrite Hl in Hv0. discriminate.
Qed.
End c.

(* ---------------------------------------------------------------------------- *)
(* 2. Every-return posts: the bind step and the walk tactic.                       *)
Lemma rx_bind {A B} : forall (m : M B) (k : B -> M A) s (P : astate -> Prop),
  apost (m s) (fun r => P (snd r)) -> (forall b s1, P s1 -> apost (k b s1) (fun r => P (snd r))) ->
  apost (bind m k s) (fun r => P (snd r)).
Proof. intros m k s P H1 H2. apply apost_bind. eapply apost_mono; [|exact H1]. intros [b s1] H. exact (H2 b s1 H). Qed.

(* One step of a proof that P holds of every returned state, for an M term built from the model's primitives. *)
Local Ltac rx_base :=
  cbn [fst snd] in *;
  first
  [ match goal with |- apost (bind get _ _) _ => apply apost_bind; apply apost_get end
  | match goal with H : ?P ?s |- apost (bind _ _ ?s) (fun r => ?P (snd r)) =>
      apply (rx_bind _ _ s P); [|let b := fresh "b" in let s1 := fresh "s" in let H1 := fresh "HP" in
                                 intros b s1 H1] end
  | match goal with |- apost ((match ?x with _ => _ end) _) _ => destruct x end
  | apply apost_fail | apply apost_spin
  | apply apost_mcheck; intros _
  | apply apost_askz; intros ? _
  | apply apost_tick
  | apply apost_get_region | apply apost_get_pc | apply apost_set_region | apply apost_set_pc
  | apply apost_get | apply apost_put | apply apost_modify | apply apost_ret
  | match goal with H : ?P ?s |- ?P _ => exact H end ].

(* Membership in a chunk list after upd_chunk (YGcfXs.v's cfx_upd_in, restated). *)
Lemma rx_upd_in : forall l k' x, In x (upd_chunk l k') -> x = k' \/ In x l.
Proof.
induction l as [|k t IH]; intros k' x H; cbn [upd_chunk] in H.
- destruct H as [<-|[]]. left. reflexivity.
- destruct (sptr_eqb (ck_beg k) (ck_beg k')).
  + destruct H as [<-|H]; [left; reflexivity | right; right; exact H].
  + destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH k' x H) as [E|E]; [left; exact E | right; right; exact E].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The callees that write none of st_secs, st_chunks and the two queues.        *)
Definition rx_same (s0 s : astate) : Prop :=
  st_secs s = st_secs s0 /\ st_chunks s = st_chunks s0 /\ st_qthread s = st_qthread s0 /\ st_qglobal s = st_qglobal s0.

Lemma rx_same_refl : forall s, rx_same s s.
Proof. intros s. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. Qed.

Create HintDb rxs.
Local Ltac rxs_step :=
  cbn [fst snd] in *;
  first
  [ solve [auto with rxs]
  | match goal with |- apost (init_cache_if_needed _) _ => unfold init_cache_if_needed end
  | rx_base ].

Lemma rxs_ensure : forall s0 c need b s, rx_same s0 s -> apost (ensure_free_array c need b s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c need b s H. unfold ensure_free_array. repeat rxs_step. Qed.
#[local] Hint Extern 1 (apost (ensure_free_array ?c ?n ?b ?s) (fun r => rx_same ?s0 (snd r))) =>
  match goal with H : rx_same s0 s |- _ => exact (rxs_ensure s0 c n b s H) end : rxs.

Lemma rxs_mmu : forall s0 c need s, rx_same s0 s -> apost (map_more_user c need s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c need s H. unfold map_more_user. repeat rxs_step. Qed.
#[local] Hint Extern 1 (apost (map_more_user ?c ?n ?s) (fun r => rx_same ?s0 (snd r))) =>
  match goal with H : rx_same s0 s |- _ => exact (rxs_mmu s0 c n s H) end : rxs.

Lemma rxs_populate : forall s0 c need s, rx_same s0 s -> apost (populate c need s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c need s H. unfold populate. repeat rxs_step. Qed.
#[local] Hint Extern 1 (apost (populate ?c ?n ?s) (fun r => rx_same ?s0 (snd r))) =>
  match goal with H : rx_same s0 s |- _ => exact (rxs_populate s0 c n s H) end : rxs.

Lemma rxs_gfa : forall s0 c n s, rx_same s0 s -> apost (get_from_allocator c n s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c n s H. unfold get_from_allocator. repeat rxs_step. Qed.
#[local] Hint Extern 1 (apost (get_from_allocator ?c ?n ?s) (fun r => rx_same ?s0 (snd r))) =>
  match goal with H : rx_same s0 s |- _ => exact (rxs_gfa s0 c n s H) end : rxs.

Lemma rxs_refill : forall s0 c s, rx_same s0 s -> apost (refill_if_empty c s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c s H. unfold refill_if_empty. repeat rxs_step. Qed.
#[local] Hint Extern 1 (apost (refill_if_empty ?c ?s) (fun r => rx_same ?s0 (snd r))) =>
  match goal with H : rx_same s0 s |- _ => exact (rxs_refill s0 c s H) end : rxs.

Lemma rxs_cache_alloc : forall s0 c s, rx_same s0 s -> apost (cache_alloc c s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c s H. unfold cache_alloc. repeat rxs_step. Qed.

Lemma rxs_depot : forall s0 tr s, rx_same s0 s -> apost (depot_put tr s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 tr s H. unfold depot_put. repeat rxs_step. Qed.

Lemma rxs_rta : forall s0 c offs s, rx_same s0 s -> apost (return_to_allocator c offs s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c offs s H. unfold return_to_allocator. repeat rxs_step. Qed.
#[local] Hint Extern 1 (apost (return_to_allocator ?c ?o ?s) (fun r => rx_same ?s0 (snd r))) =>
  match goal with H : rx_same s0 s |- _ => exact (rxs_rta s0 c o s H) end : rxs.

Lemma rxs_cache_dealloc : forall s0 c z s, rx_same s0 s -> apost (cache_dealloc c z s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c z s H. unfold cache_dealloc. repeat rxs_step. Qed.

Lemma rxs_set_exh : forall s0 c s, rx_same s0 s -> apost (set_exh_cf c s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c s H. unfold set_exh_cf. repeat rxs_step. Qed.

Lemma rxs_clear_exh : forall s0 c s, rx_same s0 s -> apost (clear_exh_cf c s) (fun r => rx_same s0 (snd r)).
Proof. intros s0 c s H. unfold clear_exh_cf. repeat rxs_step. Qed.

(* The entry step free_cf PNull: a tick and the internal-init flag (YGcfRmodel.v's cfr_null_state, as a frame). *)
Lemma rx_null_free : forall tr S, apost (free_cf PNull tr S) (fun x => rx_same S (snd x)).
Proof.
intros tr S. unfold free_cf.
apply apost_bind. apply apost_tick. cbn [fst snd].
apply apost_bind. apply apost_get. cbn [fst snd].
apply (rx_bind _ _ _ (rx_same S)).
{ apply apost_if; intros _; [apply apost_ret | apply apost_modify]; exact (rx_same_refl S). }
intros u S1 H1. cbn [fst snd]. apply apost_ret. exact H1.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. malloc_cf: st_secs only grows, below the entry length it rewrites only      *)
(*    errbuf control entries into not-live ones; queues kept; one new chunk.     *)
Definition rx_keep (X Y : list secmap) : Prop :=
  (length X <= length Y)%nat /\
  forall r sm, nth_error X r = Some sm ->
    nth_error Y r = Some sm \/
    (is_errb_any sm = true /\ exists sm', nth_error Y r = Some sm' /\ is_errb_any sm' = true /\ sm_live sm' = false).

Lemma rx_keep_refl : forall X, rx_keep X X.
Proof. intros X. split; [lia|]. intros r sm E. left. exact E. Qed.

Lemma rx_keep_trans : forall X Y Z, rx_keep X Y -> rx_keep Y Z -> rx_keep X Z.
Proof.
intros X Y Z [LY HY] [LZ HZ]. split; [lia|]. intros r sm E.
destruct (HY r sm E) as [E1|[N1 (sm1 & E1 & N1' & L1)]].
- exact (HZ r sm E1).
- right. split; [exact N1|]. destruct (HZ r sm1 E1) as [E2|[_ (sm2 & E2 & N2 & L2)]].
  + exists sm1. exact (conj E2 (conj N1' L1)).
  + exists sm2. exact (conj E2 (conj N2 L2)).
Qed.

Lemma rx_keep_app : forall l x, rx_keep l (l ++ x).
Proof.
intros l x. split; [rewrite length_app; lia|]. intros r sm E. left.
rewrite nth_error_app1; [exact E|]. apply nth_error_Some. rewrite E. discriminate.
Qed.

Lemma rx_keep_retire : forall l,
  rx_keep l (map (fun sm => if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm) l).
Proof.
intros l. split; [rewrite length_map; lia|]. intros r sm E. rewrite nth_error_map, E. cbn [option_map].
destruct (is_errb_cap sm) eqn:C; [right | left; reflexivity]. split.
- unfold is_errb_cap in C. apply Z.eqb_eq in C. unfold is_errb_any. rewrite C. reflexivity.
- exists (mkSec (sm_len sm) ERRB_DEAD_TAG false). split; [reflexivity|]. split; reflexivity.
Qed.

(* YG06bcf.v's find_sz_spec, restated (YG06bcf is not in this file's closure). *)
Lemma rx_find_sz_spec : forall l i j, find_sz l i = Some j ->
  (i <= j)%nat /\ exists sm, nth_error l (j - i) = Some sm /\ is_errb_sz sm = true.
Proof.
induction l as [|sm t IH]; intros i j H; cbn [find_sz] in H; [discriminate|].
destruct (is_errb_sz sm) eqn:E.
- injection H as <-. split; [lia|]. exists sm. rewrite Nat.sub_diag. cbn. auto.
- destruct (IH (S i) j H) as [Hle (sm' & E' & S')]. split; [lia|]. exists sm'.
  replace (j - i)%nat with (S (j - S i)) by lia. cbn. auto.
Qed.

Lemma rx_keep_sz : forall l i v, find_sz l 0 = Some i -> rx_keep l (lupd l i (mkSec v ERRB_SZ_TAG false)).
Proof.
intros l i v F. destruct (rx_find_sz_spec l 0 i F) as [_ (sm & E & Sz)]. rewrite Nat.sub_0_r in E.
split; [rewrite lupd_length; lia|]. intros r sm' E'. destruct (Nat.eq_dec r i) as [->|Ne].
- right. rewrite E in E'. injection E' as <-. split.
  + unfold is_errb_sz in Sz. apply Z.eqb_eq in Sz. unfold is_errb_any. rewrite Sz. reflexivity.
  + exists (mkSec v ERRB_SZ_TAG false). split; [|split; reflexivity].
    apply nth_error_lupd_same. apply nth_error_Some. rewrite E. discriminate.
- left. rewrite nth_error_lupd_other; [exact E' | intros X; apply Ne; symmetry; exact X].
Qed.

Definition rx_mk (s0 s : astate) : Prop :=
  rx_keep (st_secs s0) (st_secs s) /\ st_chunks s = st_chunks s0 /\ st_qthread s = st_qthread s0 /\
  st_qglobal s = st_qglobal s0.

Lemma rx_mk_refl : forall s, rx_mk s s.
Proof. intros s. split; [apply rx_keep_refl|]. split; [reflexivity|]. split; reflexivity. Qed.

Lemma rx_mk_step : forall s0 s s', rx_mk s0 s -> rx_keep (st_secs s) (st_secs s') ->
  st_chunks s' = st_chunks s -> st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s -> rx_mk s0 s'.
Proof.
intros s0 s s' (K & C & T & G) K' C' T' G'. split; [exact (rx_keep_trans _ _ _ K K')|].
split; [congruence|]. split; congruence.
Qed.

Lemma rx_mk_app : forall s0 s l, rx_mk s0 s -> rx_mk s0 (set_secs (st_secs s ++ l) s).
Proof.
intros s0 s l H. apply (rx_mk_step s0 s _ H); [|reflexivity..]. cbn [st_secs set_secs]. apply rx_keep_app.
Qed.

Lemma rxm_lift {X : Type} : forall (t : itree astate (X * astate)) s0 s, rx_mk s0 s ->
  apost t (fun r => rx_same s (snd r)) -> apost t (fun r => rx_mk s0 (snd r)).
Proof.
intros t s0 s H1 H2. eapply apost_mono; [|exact H2]. intros [x sx] (E1 & E2 & E3 & E4). cbn [snd] in *.
apply (rx_mk_step s0 s sx H1); [rewrite E1; apply rx_keep_refl | exact E2 | exact E3 | exact E4].
Qed.

Create HintDb rxm.
#[local] Hint Extern 1 (rx_mk ?s0 (set_secs (st_secs ?s ++ ?l) ?s)) =>
  match goal with H : rx_mk s0 s |- _ => exact (rx_mk_app s0 s l H) end : rxm.
#[local] Hint Extern 1 (apost (ensure_free_array ?c ?n ?b ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_lift _ s0 s H (rxs_ensure s c n b s (rx_same_refl s))) end : rxm.
#[local] Hint Extern 1 (apost (map_more_user ?c ?n ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_lift _ s0 s H (rxs_mmu s c n s (rx_same_refl s))) end : rxm.
#[local] Hint Extern 1 (apost (populate ?c ?n ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_lift _ s0 s H (rxs_populate s c n s (rx_same_refl s))) end : rxm.
#[local] Hint Extern 1 (apost (set_exh_cf ?c ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_lift _ s0 s H (rxs_set_exh s c s (rx_same_refl s))) end : rxm.
#[local] Hint Extern 1 (apost (clear_exh_cf ?c ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_lift _ s0 s H (rxs_clear_exh s c s (rx_same_refl s))) end : rxm.

Local Ltac rxm_step :=
  cbn [fst snd] in *;
  first
  [ solve [auto with rxm]
  | match goal with |- apost (init_cache_if_needed _) _ => unfold init_cache_if_needed end
  | rx_base ].

Lemma rxm_errb_retire : forall s0 s, rx_mk s0 s -> apost (errb_retire s) (fun r => rx_mk s0 (snd r)).
Proof.
intros s0 s H. unfold errb_retire. apply apost_modify. cbn [snd].
apply (rx_mk_step s0 s _ H); [|reflexivity..]. cbn [st_secs set_secs]. apply rx_keep_retire.
Qed.
#[local] Hint Extern 1 (apost (errb_retire ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_errb_retire s0 s H) end : rxm.

Lemma rxm_errb_set_size : forall s0 v s, rx_mk s0 s -> apost (errb_set_size v s) (fun r => rx_mk s0 (snd r)).
Proof.
intros s0 v s H. unfold errb_set_size. apply apost_modify. cbn [snd].
destruct (find_sz (st_secs s) 0) as [i|] eqn:F.
- apply (rx_mk_step s0 s _ H); [|reflexivity..]. cbn [st_secs set_secs]. exact (rx_keep_sz _ _ _ F).
- exact (rx_mk_app s0 s _ H).
Qed.
#[local] Hint Extern 1 (apost (errb_set_size ?v ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_errb_set_size s0 v s H) end : rxm.

Lemma rxm_sec_alloc : forall s0 n s, rx_mk s0 s -> apost (sec_alloc n s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 n s H. unfold sec_alloc. repeat rxm_step. Qed.

Section m. Context {ci : CfImg}.

Lemma rxm_errb_map : forall s0 w s, rx_mk s0 s -> apost (errb_map_cf w s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 w s H. unfold errb_map_cf. repeat rxm_step. Qed.
#[local] Hint Extern 1 (apost (errb_map_cf ?w ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_errb_map s0 w s H) end : rxm.

Lemma rxm_errb_append : forall s0 len s, rx_mk s0 s -> apost (errb_append_cf len s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 len s H. unfold errb_append_cf. repeat rxm_step. Qed.
#[local] Hint Extern 1 (apost (errb_append_cf ?l ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_errb_append s0 l s H) end : rxm.

Lemma rxm_errb_report : forall s0 c s, rx_mk s0 s -> apost (errb_report_cf c s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 c s H. unfold errb_report_cf. repeat rxm_step. Qed.
#[local] Hint Extern 1 (apost (errb_report_cf ?c ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_errb_report s0 c s H) end : rxm.

Lemma rxm_mmu_cf : forall s0 c need s, rx_mk s0 s -> apost (map_more_user_cf c need s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 c need s H. unfold map_more_user_cf. repeat rxm_step. Qed.
#[local] Hint Extern 1 (apost (map_more_user_cf ?c ?n ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_mmu_cf s0 c n s H) end : rxm.

Lemma rxm_populate_cf : forall s0 c need s, rx_mk s0 s -> apost (populate_cf c need s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 c need s H. unfold populate_cf. repeat rxm_step. Qed.
#[local] Hint Extern 1 (apost (populate_cf ?c ?n ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_populate_cf s0 c n s H) end : rxm.

Lemma rxm_gfa_cf : forall s0 c n s, rx_mk s0 s -> apost (get_from_allocator_cf c n s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 c n s H. unfold get_from_allocator_cf. repeat rxm_step. Qed.
#[local] Hint Extern 1 (apost (get_from_allocator_cf ?c ?n ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_gfa_cf s0 c n s H) end : rxm.

Lemma rxm_refill_cf : forall s0 c s, rx_mk s0 s -> apost (refill_if_empty_cf c s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 c s H. unfold refill_if_empty_cf. repeat rxm_step. Qed.
#[local] Hint Extern 1 (apost (refill_if_empty_cf ?c ?s) (fun r => rx_mk ?s0 (snd r))) =>
  match goal with H : rx_mk s0 s |- _ => exact (rxm_refill_cf s0 c s H) end : rxm.

Lemma rxm_cache_alloc_cf : forall s0 c s, rx_mk s0 s -> apost (cache_alloc_cf c s) (fun r => rx_mk s0 (snd r)).
Proof. intros s0 c s H. unfold cache_alloc_cf. repeat rxm_step. Qed.

(* Every path of malloc_cf: st_secs kept (rx_keep), both queues kept, and every chunk an entry chunk or the returned
   block's. *)
Lemma rxm_malloc_cf : forall n tr s, apost (malloc_cf n tr s) (fun r =>
  rx_keep (st_secs s) (st_secs (snd r)) /\ st_qthread (snd r) = st_qthread s /\ st_qglobal (snd r) = st_qglobal s /\
  (forall c, In c (st_chunks (snd r)) -> In c (st_chunks s) \/ ck_user c = fst r)).
Proof.
intros n tr s. unfold malloc_cf.
apply apost_bind. apply apost_tick. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind.
apply (apost_mono _ (fun r => rx_mk s (snd r))).
2:{ apply apost_if; intros _.
    - apply (rx_bind _ _ _ (rx_mk s)); [exact (rxm_cache_alloc_cf s _ (set_nev (st_nev s + 1) s) (rx_mk_refl s))|].
      intros o s2 H2. cbn [fst snd]. apply apost_ret. exact H2.
    - exact (rxm_sec_alloc s n (set_nev (st_nev s + 1) s) (rx_mk_refl s)). }
intros [ob s2] H2. cbn [fst snd] in *.
destruct ob as [beg|]; cbn [fst snd].
2:{ apply apost_ret. cbn [fst snd]. destruct H2 as (K & C & T & G). split; [exact K|]. split; [exact T|].
    split; [exact G|]. intros c Hc. left. rewrite <- C. exact Hc. }
apply apost_bind. eapply apost_mono; [|exact (rxm_lift _ s s2 H2 (rxs_depot s2 tr s2 (rx_same_refl s2)))].
intros [u3 s3] H3. cbn [fst snd] in *.
apply apost_bind. apply (apost_mono _ (fun r => rx_mk s (snd r))).
2:{ apply apost_if; intros _; [|apply apost_ret; exact H3].
    apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
    apply apost_if; intros _; [apply apost_ret; exact H3 | apply apost_spin]. }
intros [u4 s4] H4. cbn [fst snd] in *.
apply apost_bind. apply apost_modify. cbn [fst snd]. apply apost_ret.
cbn [fst snd st_secs st_chunks st_qthread st_qglobal set_chunks].
destruct H4 as (K & C & T & G). split; [exact K|]. split; [exact T|]. split; [exact G|].
intros c Hc. destruct (rx_upd_in _ _ _ Hc) as [->|Hc']; [right; reflexivity | left; rewrite <- C; exact Hc'].
Qed.

Lemma malloc_cf_frame_ix : forall n tr S trc q S1, apath (malloc_cf n tr S) trc (q, S1) ->
  rx_keep (st_secs S) (st_secs S1) /\ st_qthread S1 = st_qthread S /\ st_qglobal S1 = st_qglobal S /\
  (forall c, In c (st_chunks S1) -> In c (st_chunks S) \/ ck_user c = q).
Proof. intros n tr S trc q S1 H. exact (apost_apath _ _ trc (q, S1) (rxm_malloc_cf n tr S) H). Qed.

(* (2) THE MALLOC STEP. *)
Lemma malloc_cf_secs_keep : forall n tr S trc q S1,
  apath (malloc_cf n tr S) trc (q, S1) ->
  (length (st_secs S) <= length (st_secs S1))%nat /\
  rec_live_lt (length (st_secs S)) S S1 /\
  (forall r sm, nth_error (st_secs S) r = Some sm -> is_errb_any sm = false -> nth_error (st_secs S1) r = Some sm).
Proof.
intros n tr S trc q S1 H. destruct (malloc_cf_frame_ix n tr S trc q S1 H) as ((LK & K) & _).
split; [exact LK|]. split.
- intros r sm' Hr Hn Hl. destruct (nth_error (st_secs S) r) as [sm|] eqn:E.
  + destruct (K r sm E) as [E'|(_ & sm'' & E'' & _ & Hl'')].
    * rewrite Hn in E'. injection E' as <-. exists sm'. split; [reflexivity|]. split; [exact Hl | reflexivity].
    * rewrite Hn in E''. injection E'' as <-. rewrite Hl in Hl''. discriminate.
  + apply nth_error_None in E. lia.
- intros r sm E N. destruct (K r sm E) as [E'|(N' & _)]; [exact E' | rewrite N in N'; discriminate].
Qed.

End m.

(* ---------------------------------------------------------------------------- *)
(* 5. free_cf: each st_secs entry is kept or marked dead in place, and only at a   *)
(*    recycled chunk's own index.                                                 *)
(* A list step that keeps the length and marks entries dead in place, only at indices in A. *)
Definition rx_mark (A : nat -> Prop) (X Y : list secmap) : Prop :=
  length Y = length X /\
  forall r sm, nth_error X r = Some sm ->
    nth_error Y r = Some sm \/ (A r /\ nth_error Y r = Some (mkSec (sm_len sm) (sm_size sm) false)).

Lemma rx_mark_refl : forall A X, rx_mark A X X.
Proof. intros A X. split; [reflexivity|]. intros r sm E. left. exact E. Qed.

Lemma rx_mark_trans : forall A X Y Z, rx_mark A X Y -> rx_mark A Y Z -> rx_mark A X Z.
Proof.
intros A X Y Z [LY HY] [LZ HZ]. split; [congruence|]. intros r sm E.
destruct (HY r sm E) as [E1|[Ar E1]].
- exact (HZ r sm E1).
- right. split; [exact Ar|]. destruct (HZ r _ E1) as [E2|[_ E2]]; exact E2.
Qed.

Lemma rx_mark_lupd : forall A l r sm, nth_error l r = Some sm -> A r ->
  rx_mark A l (lupd l r (mkSec (sm_len sm) (sm_size sm) false)).
Proof.
intros A l r sm E HA. split; [apply lupd_length|]. intros r' sm' E'. destruct (Nat.eq_dec r' r) as [->|Ne].
- right. rewrite E in E'. injection E' as <-. split; [exact HA|].
  apply nth_error_lupd_same. apply nth_error_Some. rewrite E. discriminate.
- left. rewrite (nth_error_lupd_other _ _ _ _ (not_eq_sym Ne)). exact E'.
Qed.

Definition rx_fstep (A : nat -> Prop) (s0 s : astate) : Prop := rx_mark A (st_secs s0) (st_secs s).

(* The items of the two queues of s, in maybe_drain_cf's order (YG00cf.v:309), all at indices in A. *)
Definition rx_qi (A : nat -> Prop) (s : astate) : Prop :=
  forall c r o, In c (flat_map b_items (qc_list (st_qglobal s) ++ qc_list (st_qthread s))) -> ck_beg c = PSec r o -> A r.

(* recycle_chunk (YG00.v:501-509): a secondary marks its own entry dead (YGcfRecStep.v's recycle_chunk_rec_step, at
   this relation); neither queue moves. *)
Lemma rxf_recycle_chunk : forall A k s0 s, (forall r o, ck_beg k = PSec r o -> A r) -> rx_fstep A s0 s ->
  apost (recycle_chunk k s)
    (fun x => rx_fstep A s0 (snd x) /\ st_qthread (snd x) = st_qthread s /\ st_qglobal (snd x) = st_qglobal s).
Proof.
intros A k s0 s HA H. unfold recycle_chunk.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_put. cbn [fst snd].
set (X1 := set_chunks (del_chunk (st_chunks s) (ck_beg k)) s).
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; [apply apost_fail | | | apply apost_fail].
- eapply apost_mono; [|exact (rxs_cache_dealloc X1 (prim_class off) off X1 (rx_same_refl X1))].
  intros [x sx] (E1 & _ & E3 & E4). cbn [snd] in *. unfold rx_fstep. rewrite E1, E3, E4.
  exact (conj H (conj eq_refl eq_refl)).
- unfold sec_dealloc. apply apost_bind. apply apost_get. cbn [fst snd].
  change (st_secs X1) with (st_secs s). change (st_sec_arr X1) with (st_sec_arr s).
  destruct (nth_error (st_secs s) r) as [sm|] eqn:En; [|apply apost_fail].
  destruct (index_of (st_sec_arr s) r 0) as [i|]; [|apply apost_fail].
  apply apost_bind. apply (apost_mono _ (fun r0 => snd r0 = X1)).
  2:{ apply apost_if; intros _; [|apply apost_ret; reflexivity].
      apply apost_bind. apply apost_askz. intros z0 _. cbn [fst snd].
      apply apost_if; intros _; [apply apost_ret; reflexivity | apply apost_spin]. }
  intros [u1 s1] Hs. cbn [fst snd] in Hs |- *. subst s1.
  apply apost_bind. apply apost_askz. intros z1 _. cbn [fst snd].
  apply apost_modify. cbn [snd]. unfold X1, rx_fstep in *.
  cbn [st_secs st_chunks st_sec_arr st_qthread st_qglobal set_chunks set_sec_arr set_secs] in *.
  split; [|split; reflexivity].
  exact (rx_mark_trans _ _ _ _ H (rx_mark_lupd _ _ _ _ En (HA r o eq_refl))).
Qed.

Lemma rxf_recycle_items : forall A fuel items s0 s,
  (forall k r o, In k items -> ck_beg k = PSec r o -> A r) -> rx_fstep A s0 s ->
  apost (recycle_items fuel items s) (fun x => rx_fstep A s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros items s0 s HI H; destruct items as [|k t]; cbn [recycle_items].
- apply apost_ret. exact H.
- apply apost_fail.
- apply apost_ret. exact H.
- apply (rx_bind _ _ s (rx_fstep A s0)).
  + eapply apost_mono; [|exact (rxf_recycle_chunk A k s0 s (fun r o Hb => HI k r o (or_introl eq_refl) Hb) H)].
    intros x [X _]. exact X.
  + intros b s1 H1. apply IH; [intros k' r o Hk Hb; exact (HI k' r o (or_intror Hk) Hb) | exact H1].
Qed.

Lemma rxf_do_recycle : forall A fuel bs s0 s,
  (forall b k r o, In b bs -> In k (b_items b) -> ck_beg k = PSec r o -> A r) -> rx_fstep A s0 s ->
  apost (do_recycle fuel bs s) (fun x => rx_fstep A s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros bs s0 s HI H; destruct bs as [|b t]; cbn [do_recycle].
- apply apost_ret. exact H.
- apply apost_fail.
- apply apost_ret. exact H.
- apply (rx_bind _ _ s (rx_fstep A s0)).
  + apply rxf_recycle_items; [intros k r o Hk Hb; exact (HI b k r o (or_introl eq_refl) Hk Hb) | exact H].
  + intros u s1 H1. apply (rx_bind _ _ s1 (rx_fstep A s0)).
    * eapply apost_mono; [|exact (rxs_cache_dealloc s1 kBatchClass (b_self b) s1 (rx_same_refl s1))].
      intros [x sx] (E1 & _). cbn [snd] in *. unfold rx_fstep in *. rewrite E1. exact H1.
    * intros u2 s2 H2. apply IH; [intros b' k r o Hb' Hk Hbg; exact (HI b' k r o (or_intror Hb') Hk Hbg) | exact H2].
Qed.

(* MergeBatches (YG00cf.v:285-299) only moves items, and the batches it extracts are empty. *)
Lemma rx_merge_spec : forall fuel l, let '(rest, ex) := merge_batches_cf fuel l in
  (forall b, In b ex -> b_items b = []) /\ (forall k, In k (flat_map b_items rest) -> In k (flat_map b_items l)).
Proof.
induction fuel as [|f IH]; intros l; cbn [merge_batches_cf].
- split; [intros b [] | intros k Hk; exact Hk].
- destruct l as [|b1 [|b2 t]]; cbn [fst snd]; [split; [intros b [] | intros k Hk; exact Hk] .. |].
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst snd].
  + pose proof (IH (mkBatch (b_self b1) (b_items b1 ++ b_items b2) :: t)) as IH1. revert IH1.
    destruct (merge_batches_cf f (mkBatch (b_self b1) (b_items b1 ++ b_items b2) :: t)) as [rest' ex'].
    cbn [fst snd]. intros [IE IR]. split.
    * intros b [<-|Hb]; [reflexivity | exact (IE b Hb)].
    * intros k Hk. pose proof (IR k Hk) as Hk'. cbn [flat_map b_items] in Hk' |- *.
      rewrite <- app_assoc in Hk'. exact Hk'.
  + pose proof (IH (b2 :: t)) as IH1. revert IH1. destruct (merge_batches_cf f (b2 :: t)) as [rest' ex'].
    cbn [fst snd]. intros [IE IR]. split; [exact IE|].
    intros k Hk. cbn [flat_map] in Hk |- *. apply in_app_iff in Hk as [Hk|Hk]; apply in_app_iff;
      [left; exact Hk | right; exact (IR k Hk)].
Qed.

(* pop_batches (YG00.v:524-532) returns batches of the queue or of its accumulator. *)
Lemma rx_pop_spec : forall fuel q acc, let '(q', popped) := pop_batches fuel q acc in
  forall b, In b popped -> In b (qc_list q) \/ In b acc.
Proof.
induction fuel as [|f IH]; intros q acc; cbn [pop_batches].
- intros b Hb. right. exact (proj2 (in_rev acc b) Hb).
- destruct (qc_bytes q <=? kQuarantineMin); cbn [fst snd]; [intros b Hb; right; exact (proj2 (in_rev acc b) Hb)|].
  destruct (qc_list q) as [|b0 t] eqn:Eq; cbn [fst snd]; [intros b Hb; right; exact (proj2 (in_rev acc b) Hb)|].
  pose proof (IH (mkQC t (qc_bytes q - b_bytes b0)) (b0 :: acc)) as IH1. revert IH1.
  destruct (pop_batches f (mkQC t (qc_bytes q - b_bytes b0)) (b0 :: acc)) as [q' popped].
  cbn [fst snd]. intros IH1 b Hb. destruct (IH1 b Hb) as [H1|[<-|H1]].
  + left. right. exact H1.
  + left. left. reflexivity.
  + right. exact H1.
Qed.

(* maybe_drain_cf (YG00cf.v:305-321): every chunk it recycles is an item of the two queues at its start. *)
Lemma rxf_maybe_drain : forall A s0 s, rx_qi A s -> rx_fstep A s0 s ->
  apost (maybe_drain_cf s) (fun x => rx_fstep A s0 (snd x)).
Proof.
intros A s0 s HI H. unfold maybe_drain_cf.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact H|].
apply apost_bind. apply apost_put. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact H|].
cbn [fst snd].
match goal with |- context [merge_batches_cf ?f ?l] =>
  pose proof (rx_merge_spec f l) as MS; revert MS; destruct (merge_batches_cf f l) as [l' ex] end.
cbn [fst snd]. intros [ME MR].
match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst snd].
- match goal with |- context [pop_batches ?f ?q ?a] =>
    pose proof (rx_pop_spec f q a) as PS; revert PS; destruct (pop_batches f q a) as [g' popped] end.
  cbn [fst snd]. intros PS.
  apply apost_bind. apply apost_modify. cbn [fst snd].
  apply rxf_do_recycle; [|exact H].
  intros b c r o Hb Hc Hbg. apply in_app_iff in Hb as [Hb|Hb].
  + rewrite (ME b Hb) in Hc. destruct Hc.
  + destruct (PS b Hb) as [Hq|[]]. cbn [qc_list] in Hq.
    apply (HI c r o); [|exact Hbg]. apply MR. apply in_flat_map. exists b. split; [exact Hq | exact Hc].
- match goal with |- context [pop_batches ?f ?q ?a] =>
    pose proof (rx_pop_spec f q a) as PS; revert PS; destruct (pop_batches f q a) as [g' popped] end.
  cbn [fst snd]. intros PS.
  apply apost_bind. apply apost_modify. cbn [fst snd].
  apply rxf_do_recycle; [|exact H].
  intros b c r o Hb Hc Hbg. apply in_app_iff in Hb as [Hb|Hb]; [destruct Hb|].
  destruct (PS b Hb) as [Hq|[]]. cbn [qc_list] in Hq.
  apply (HI c r o); [|exact Hbg]. apply in_flat_map. exists b. split; [exact Hq | exact Hc].
Qed.

(* qc_push (YG00.v:435-442) adds the one chunk k to the thread queue's items. *)
Lemma rx_qc_push_items : forall q k nb c, In c (flat_map b_items (qc_list (qc_push q k nb))) ->
  In c (flat_map b_items (qc_list q)) \/ c = k.
Proof.
intros q k nb c. unfold qc_push. destruct nb as [b|]; cbn [qc_list].
- rewrite flat_map_app. cbn [flat_map b_items]. rewrite app_nil_r. intros H.
  apply in_app_iff in H as [H|[H|[]]]; [left; exact H | right; symmetry; exact H].
- destruct (rev (qc_list q)) as [|lastb initr] eqn:Er; cbn [flat_map]; [intros []|].
  assert (Eq : qc_list q = rev initr ++ [lastb]) by (rewrite <- (rev_involutive (qc_list q)), Er; reflexivity).
  rewrite Eq, !flat_map_app. cbn [flat_map b_items]. rewrite !app_nil_r. intros H.
  apply in_app_iff in H as [H|H]; [left; apply in_app_iff; left; exact H|].
  apply in_app_iff in H as [H|[H|[]]]; [left; apply in_app_iff; right; exact H | right; symmetry; exact H].
Qed.

(* enqueue (YG00.v:448-457): st_secs and the global queue kept; the thread queue gains k. *)
Lemma rx_enqueue : forall k s, apost (enqueue k s) (fun r => st_secs (snd r) = st_secs s /\
  st_qglobal (snd r) = st_qglobal s /\
  forall c, In c (flat_map b_items (qc_list (st_qthread (snd r)))) -> In c (flat_map b_items (qc_list (st_qthread s))) \/ c = k).
Proof.
intros k s. unfold enqueue.
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply (apost_mono _ (fun r => rx_same s (snd r))).
2:{ apply apost_if; intros _; [|apply apost_ret; exact (rx_same_refl s)].
    apply (rx_bind _ _ s (rx_same s)); [exact (rxs_cache_alloc s kBatchClass s (rx_same_refl s))|].
    intros ob s1 H1. destruct ob as [off|]; cbn [fst snd]; [apply apost_ret; exact H1 | apply apost_spin]. }
intros [nb s1] (E1 & _ & E3 & E4). cbn [fst snd] in *.
apply apost_modify. cbn [snd st_secs st_qglobal st_qthread set_qthread].
split; [exact E1|]. split; [exact E4|].
intros c Hc. destruct (rx_qc_push_items (st_qthread s1) k nb c Hc) as [X|X]; [left; rewrite <- E3; exact X | right; exact X].
Qed.

(* free_cf after its depot put (YG00cf.v:351-354): the freed chunk's state change, its enqueue or its immediate
   recycle, and the drain. *)
Lemma rxf_free_tail : forall A S S3 k',
  (forall c r o, In c (q_items S) -> ck_beg c = PSec r o -> A r) ->
  (forall r o, ck_beg k' = PSec r o -> A r) ->
  rx_same S S3 ->
  apost (bind (modify (fun s => set_chunks (upd_chunk (st_chunks s) k') s))
          (fun _ => bind (if ck_n k' <=? kQuarantineMax then enqueue k' else recycle_chunk k') (fun _ => maybe_drain_cf)) S3)
        (fun x => rx_fstep A S (snd x)).
Proof.
intros A S S3 k' HQ HK (E1 & E2 & E3 & E4).
assert (HG : forall c r o, In c (flat_map b_items (qc_list (st_qglobal S3))) -> ck_beg c = PSec r o -> A r).
{ intros c r o Hc Hb. apply (HQ c r o); [|exact Hb]. unfold q_items, all_batches. rewrite flat_map_app.
  apply in_app_iff. right. rewrite <- E4. exact Hc. }
assert (HT : forall c r o, In c (flat_map b_items (qc_list (st_qthread S3))) -> ck_beg c = PSec r o -> A r).
{ intros c r o Hc Hb. apply (HQ c r o); [|exact Hb]. unfold q_items, all_batches. rewrite flat_map_app.
  apply in_app_iff. left. rewrite <- E3. exact Hc. }
apply apost_bind. apply apost_modify. cbn [fst snd].
set (S4 := set_chunks (upd_chunk (st_chunks S3) k') S3).
assert (F4 : rx_fstep A S S4) by (unfold rx_fstep, S4; cbn [st_secs set_chunks]; rewrite E1; apply rx_mark_refl).
apply apost_bind.
apply (apost_mono _ (fun r => rx_fstep A S (snd r) /\ rx_qi A (snd r))).
{ intros [u5 S5] [F G]. cbn [fst snd] in *. exact (rxf_maybe_drain A S S5 G F). }
apply apost_if; intros _.
- eapply apost_mono; [|exact (rx_enqueue k' S4)].
  intros [u5 S5] (F1 & F2 & F3). cbn [fst snd] in *. split.
  + unfold rx_fstep in *. rewrite F1. exact F4.
  + intros c r o Hc Hb. rewrite flat_map_app in Hc. apply in_app_iff in Hc as [Hc|Hc].
    * rewrite F2 in Hc. exact (HG c r o Hc Hb).
    * destruct (F3 c Hc) as [Hc' | ->]; [exact (HT c r o Hc' Hb) | exact (HK r o Hb)].
- eapply apost_mono; [|exact (rxf_recycle_chunk A k' S S4 HK F4)].
  intros [u5 S5] (F & G1 & G2). cbn [fst snd] in *. split; [exact F|].
  intros c r o Hc Hb. rewrite flat_map_app in Hc. apply in_app_iff in Hc as [Hc|Hc].
  + rewrite G2 in Hc. exact (HG c r o Hc Hb).
  + rewrite G1 in Hc. exact (HT c r o Hc Hb).
Qed.

(* Every path of free_cf, when every queue item and the freed chunk sit at indices in A. *)
Lemma rxf_free_cf : forall A p tr S,
  (forall k r o, In k (q_items S) -> ck_beg k = PSec r o -> A r) ->
  (forall k r o, find_user (st_chunks S) p = Some k -> ck_beg k = PSec r o -> A r) ->
  apost (free_cf p tr S) (fun x => rx_fstep A S (snd x)).
Proof.
intros A p tr S HQ HP. unfold free_cf.
apply apost_bind. apply apost_tick. cbn [fst snd].
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply (apost_mono _ (fun r => rx_same S (snd r))).
2:{ apply apost_if; intros _; [apply apost_ret | apply apost_modify]; exact (rx_same_refl S). }
intros [u S1] H1. cbn [fst snd] in *.
destruct p as [|off|r0 o0|cid pos]; cbn [fst snd].
{ apply apost_ret. cbn [snd]. destruct H1 as (E1 & _). unfold rx_fstep. rewrite E1. apply rx_mark_refl. }
all: apply apost_bind; apply apost_get; cbn [fst snd].
all: pose proof H1 as (E1 & E2 & E3 & E4); rewrite E2.
all: match goal with |- context [find_user ?l ?q] =>
       destruct (find_user l q) as [k|] eqn:Ef end; cbn [fst snd]; [|apply apost_fail].
all: apply apost_bind; apply (apost_mono _ (fun r => rx_same S (snd r)));
       [intros [u2 S2] H2; cbn [fst snd] in * | apply apost_if; intros _; [apply apost_ret; exact H1 | apply apost_fail]].
all: apply apost_bind; apply (apost_mono _ (fun r => rx_same S (snd r)));
       [intros [u3 S3] H3; cbn [fst snd] in * | exact (rxs_depot S tr S2 H2)].
all: cbn [fst snd].
all: apply (rxf_free_tail A S S3 (mkChunk (ck_beg k) (ck_req k) CQuarantined) HQ);
       [intros r o Hb; exact (HP k r o eq_refl Hb) | exact H3].
Qed.

(* The verdict of the drain measurement, with no premise: free_cf keeps the length of st_secs, and each entry is kept or
   is the same entry with sm_live false. *)
Lemma free_cf_secs_mark : forall p tr S trc S', apath (free_cf p tr S) trc (tt, S') ->
  length (st_secs S') = length (st_secs S) /\
  forall r sm, nth_error (st_secs S) r = Some sm ->
    nth_error (st_secs S') r = Some sm \/ nth_error (st_secs S') r = Some (mkSec (sm_len sm) (sm_size sm) false).
Proof.
intros p tr S trc S' Hp.
destruct (apost_apath _ _ trc (tt, S')
  (rxf_free_cf (fun _ => True) p tr S (fun _ _ _ _ _ => I) (fun _ _ _ _ _ => I)) Hp) as [LEN K].
cbn [snd] in LEN, K. split; [exact LEN|]. intros r sm E. destruct (K r sm E) as [E'|[_ E']]; [left | right]; exact E'.
Qed.

(* (3) THE FREE STEP. *)
Lemma free_cf_fresh_keep : forall L p tr S trc S',
  apath (free_cf p tr S) trc (tt, S') ->
  (forall k r o, In k (q_items S) -> ck_beg k = PSec r o -> (r < L)%nat) ->
  (forall k r o, find_user (st_chunks S) p = Some k -> ck_beg k = PSec r o -> (r < L)%nat) ->
  forall r, (L <= r)%nat -> nth_error (st_secs S') r = nth_error (st_secs S) r.
Proof.
intros L p tr S trc S' Hp HQ HF r Hr.
destruct (apost_apath _ _ trc (tt, S') (rxf_free_cf (fun r => (r < L)%nat) p tr S HQ HF) Hp) as [LEN K].
cbn [snd] in LEN, K.
destruct (nth_error (st_secs S) r) as [sm|] eqn:E.
- destruct (K r sm E) as [E'|[Lt _]]; [exact E' | lia].
- apply nth_error_None. rewrite LEN. apply nth_error_None. exact E.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. The chain along the realloc tree, for the primed realloc composition.         *)
Section ch. Context {ci : CfImg} {cp : CfParams} {rc : YM05.RunCeil}.

Theorem realloc_dead_ix_of_paths : forall U ly ly2 S S1 S2 S3 n p q tr1 tr2 tr3 trc1 trc2 trc3 a,
  Wf_cf U S ->
  apath (free_cf PNull tr1 S) trc1 (tt, S1) ->
  apath (malloc_cf n tr2 S1) trc2 (q, S2) ->
  q <> p ->
  apath (free_cf p tr3 S2) trc3 (tt, S3) ->
  layout_le (length (st_secs S)) ly ly2 ->
  dead_shadow_new ly2 S2 S3 a -> dead_shadow_new ly S S3 a.
Proof.
intros U ly ly2 S S1 S2 S3 n p q tr1 tr2 tr3 trc1 trc2 trc3 a W H1 H2 Hqp H3 LE HD.
pose proof (apost_apath _ _ trc1 (tt, S1) (rx_null_free tr1 S) H1) as (N1 & N2 & N3 & N4).
cbn [snd] in N1, N2, N3, N4.
destruct (malloc_cf_frame_ix n tr2 S1 trc2 q S2 H2) as (_ & M3 & M4 & MC).
unfold Wf_cf in W.
assert (CK : forall k r o, In k (st_chunks S) -> ck_beg k = PSec r o -> (r < length (st_secs S))%nat).
{ intros k r o Hk Hb.
  pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k Hk) as Hok.
  unfold chunk_ok_cf in Hok. rewrite Hb in Hok. destruct Hok as (_ & _ & _ & sm & Hn & _).
  apply nth_error_Some. rewrite Hn. discriminate. }
assert (RL : rec_live_lt (length (st_secs S)) S S2).
{ destruct (malloc_cf_secs_keep n tr2 S1 trc2 q S2 H2) as (_ & RL1 & _).
  rewrite N1 in RL1. intros r sm' Hr Hn Hl. destruct (RL1 r sm' Hr Hn Hl) as (sm & Hs & Hl' & El).
  rewrite N1 in Hs. exists sm. exact (conj Hs (conj Hl' El)). }
assert (KF : forall r, (length (st_secs S) <= r)%nat -> nth_error (st_secs S3) r = nth_error (st_secs S2) r).
{ apply (free_cf_fresh_keep (length (st_secs S)) p tr3 S2 trc3 S3 H3).
  - intros k r o Hk Hb. apply (CK k r o); [|exact Hb].
    assert (Hk' : In k (q_items S)).
    { unfold q_items, all_batches in Hk |- *. rewrite M3, M4, N3, N4 in Hk. exact Hk. }
    exact (proj1 (proj1 (Forall_forall _ _) (wq_items _ (wfc_quarantine _ _ _ _ _ W)) k Hk')).
  - intros k r o Hf Hb. destruct (find_user_spec _ _ _ Hf) as [Hk Hu].
    destruct (MC k Hk) as [Hk1|Hu'].
    + apply (CK k r o); [rewrite <- N2; exact Hk1 | exact Hb].
    + exfalso. apply Hqp. congruence. }
exact (realloc_dead_ix_compose (length (st_secs S)) ly ly2 S S2 S3 a RL KF LE HD).
Qed.

End ch.

Print Assumptions realloc_dead_ix_compose.
Print Assumptions malloc_cf_secs_keep.
Print Assumptions free_cf_fresh_keep.
Print Assumptions free_cf_secs_mark.
Print Assumptions realloc_dead_ix_of_paths.
