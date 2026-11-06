(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the PURE (machine-free) model layer of segment VALUE of parse_items' image-B walk (lane
   PItemsB.PItemsValue of a Theorem Labs lane's image-B walk list). Rule 24: no function is proved here; these are grammar and
   ledger lemmas over PjGrammar (lib/Spec) at the strtod model PRH_Reader.prh_jr_strtod.
   CONTENTS:
   1. pvm_wf_from / pvm_wf: a trace frees or regrows only blocks it allocated itself. The algebra of the live-size
      list lsz_evR / lszR under it (append, prefix monotonicity, held = sum of live sizes, nliveR = live count), and
      that EVERY trace of the grammar (jrv / jrl by mutual fuel induction, then jr_value / jr_items) is well formed.
   2. pvm_ledger_app: the record text ledger move rd_ledger_move of a prefix then a callee composes; pvm_ledger_nil;
      pvm_lsum_app; pvm_blocks_move_app: rd_blocks_move of a prefix then a callee at the next depth composes.
   3. The live room rd_room along a trace split (prefix, and after a callee that kept blocks_bytes within its
      PRH_Charge.prh_held), the continuation PItems_value_pres.pv_kont of PItems_pres.pi_val_k and its granted
      remainder pvm_gafter, the granted-run normalisation of a successful callee and of its ok list, two PjGrammar
      fuel facts, and pvm_value_suffix / pvm_items_suffix: the rest a successful run leaves is a suffix of its input
      (ported from preset's plain lib/Prog/ReaderKB.v:27-145 rk_suf_*, at prh_jr_strtod; no plain lemma is cited).
      THE GRANTED EVENTS AT A BLOCK (form (b), PItems_posb.v): pvm_gt_pref, the whole call's all-granted heap
      events (PRH_Charge.prhPi_gtrace) begin with the prefix trace's, then the block continuation's (by
      PjGrammar.agrees_jr_items: an ok list that refuses a call stops the run there, at an event-free EFail), and
      pvm_lc_call, a callee's peak-count premise at the block from pi_ent's (PItems_posb.pi_lc_at, PresetRun.pkR_app).
   4. The peak bound of a whole jr_items / jr_value run (rd_blocks_move's fourth conjunct); pvm_hpeak_prefix.
   5. The half-built container PItems_defs.pi_cont: freeable to depth MAXD - d over any NoDup permutation D0 of its
      blocks (pi_cont_fd, every refusal exit), and kept by a memory that agrees on the bytes it reads
      (pvm_cont_frame_core; pi_cont_frame over the whole footprint, every call; pi_cont_frame_slot /
      pi_cont_frame_slot_gen over the footprint minus a write [lo, hi) past the members' slots), through
      PItems_shape.v's pis_open / pis_exit_open / pis_fd_hdr0 and PRH_Reader.v's frame lemmas.
   6. THE BATCH KIT TOOLS (240b06ed4fd4): pvm_some_granted (a run that returned had every outcome granted),
      pvm_calls_le_granted, pvm_gt_grant (under pi_grant the whole call's all-granted run is the prefix then the block's
      continuation at ok = []), pvm_jf_det / pvm_jfv_det (PresetReqAt.jfv / jfl depend only on the outcomes of the calls
      the run makes), pvm_kids_snoc / pvm_ncaps_snoc, pvm_foR_perm, and the FRAME lemmas of the batch kit's invariants over
      pi_cont's read bytes pvm_cont_ufoot: pvm_forder_frame (PRH_PjOrder.pf_oitemsR_frame) and pvm_ncaps_frame
      (PvB_Frees.pvf_ncap_frame along pi_cont's items).
   NUMERALS: 56 and 8 are LENGTH (the kids slot and the keys pointer, PjGrammar.grow's realloc sizes); 123, 91, 34,
   116, 102, 110, 58 and 44 are DERIVED (the byte values PjGrammar.jrv / jr_name / jrl test, copied verbatim); 224 and
   512 are DERIVED (PjGrammar.G10_2 / G10_2_items); 2 ^ 64 and SIZE_MAXZ are WORD. No ADDRESS.
   ASSUMPTIONS: sections 1-4 are closed under the global context. The section-5 lemmas list only Rocq's
   primitive PrimInt63 / PrimString declarations (12), which enter through the memory vocabulary of their statements:
   PRH_Reader.pj_hdrR_frame and PItems_shape.pis_fd_hdr0 list the same 12. No user axiom. Author lane
   PItemsB.PItemsValue. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YG00 YG01 YG0f YGcfNames YGcfRoomKeep YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_model PItems_defs PItems_pres
PItems_value_pres PItems_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_ledk1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ================= 1. trace well-formedness ================= *)

Fixpoint pvm_wf_from (s : list nat) (t : list PjGrammar.ev) : Prop :=
  match t with
  | [] => True
  | PjGrammar.EFree n :: r => In n s /\ pvm_wf_from (rm1nR n s) r
  | PjGrammar.EGrow (S m) n :: r => In (S m) s /\ pvm_wf_from (n :: rm1nR (S m) s) r
  | e :: r => pvm_wf_from (lsz_evR s e) r
  end.
Definition pvm_wf (t : list PjGrammar.ev) : Prop := pvm_wf_from [] t.

(* ---- rm1nR facts ---- *)
Lemma pvm_rm1n_app : forall k l s0, In k l -> rm1nR k (l ++ s0) = rm1nR k l ++ s0.
Proof.
  intros k l s0. induction l as [|x l IH]; intros H; [destruct H|].
  cbn [app rm1nR]. destruct (Nat.eqb x k) eqn:E; [reflexivity|].
  apply Nat.eqb_neq in E. destruct H as [H|H]; [contradiction|]. rewrite (IH H). reflexivity.
Qed.

Lemma pvm_rm1n_in : forall k s a, In a s -> a <> k -> In a (rm1nR k s).
Proof.
  intros k s a. induction s as [|x s IH]; intros H1 H2; [destruct H1|].
  cbn [rm1nR]. destruct (Nat.eqb x k) eqn:E.
  - apply Nat.eqb_eq in E. subst x. destruct H1 as [H1|H1]; [exfalso; apply H2; symmetry; exact H1|exact H1].
  - cbn [In]. destruct H1 as [H1|H1]; [left; exact H1|right; apply IH; assumption].
Qed.

Lemma pvm_rm1n_zsum : forall k s, In k s ->
  fold_right Z.add 0 (map Z.of_nat (rm1nR k s)) = fold_right Z.add 0 (map Z.of_nat s) - Z.of_nat k.
Proof.
  intros k s. induction s as [|x s IH]; intros H; [destruct H|].
  cbn [rm1nR]. destruct (Nat.eqb x k) eqn:E.
  - apply Nat.eqb_eq in E. subst x. cbn [map fold_right]. lia.
  - apply Nat.eqb_neq in E. destruct H as [H|H]; [contradiction|]. cbn [map fold_right]. rewrite (IH H). lia.
Qed.

Lemma pvm_rm1n_len : forall k s, In k s -> length s = S (length (rm1nR k s)).
Proof.
  intros k s. induction s as [|x s IH]; intros H; [destruct H|].
  cbn [rm1nR]. destruct (Nat.eqb x k) eqn:E; [reflexivity|].
  apply Nat.eqb_neq in E. destruct H as [H|H]; [contradiction|]. cbn [length]. rewrite (IH H). reflexivity.
Qed.

(* ---- the algebra of pvm_wf_from ---- *)
Lemma pvm_wf_from_app : forall s t1 t2,
  pvm_wf_from s (t1 ++ t2) <-> pvm_wf_from s t1 /\ pvm_wf_from (fold_left lsz_evR t1 s) t2.
Proof.
  intros s t1. revert s. induction t1 as [|e t1 IH]; intros s t2.
  - cbn [app fold_left pvm_wf_from]. tauto.
  - destruct e as [n|[|m] n|n|n]; cbn [app fold_left pvm_wf_from lsz_evR];
      match goal with |- context [pvm_wf_from ?X (t1 ++ t2)] => pose proof (IH X t2) end; tauto.
Qed.

Lemma pvm_fold_app : forall l t s0, pvm_wf_from l t ->
  fold_left lsz_evR t (l ++ s0) = fold_left lsz_evR t l ++ s0.
Proof.
  intros l t. revert l. induction t as [|e t IH]; intros l s0 H; [reflexivity|].
  destruct e as [n|[|m] n|n|n]; cbn [fold_left pvm_wf_from lsz_evR] in *.
  - rewrite app_comm_cons. apply IH. exact H.
  - rewrite app_comm_cons. apply IH. exact H.
  - destruct H as [Hin H]. rewrite (pvm_rm1n_app (S m) l s0 Hin), app_comm_cons. apply IH. exact H.
  - apply IH. exact H.
  - destruct H as [Hin H]. rewrite (pvm_rm1n_app n l s0 Hin). apply IH. exact H.
Qed.

Lemma pvm_wf_from_mono : forall l t s0, pvm_wf_from l t -> pvm_wf_from (l ++ s0) t.
Proof.
  intros l t. revert l. induction t as [|e t IH]; intros l s0 H; [exact I|].
  destruct e as [n|[|m] n|n|n]; cbn [pvm_wf_from lsz_evR] in *.
  - rewrite app_comm_cons. apply IH. exact H.
  - rewrite app_comm_cons. apply IH. exact H.
  - destruct H as [Hin H]. split; [apply in_or_app; left; exact Hin|].
    rewrite (pvm_rm1n_app _ _ _ Hin), app_comm_cons. apply IH. exact H.
  - apply IH. exact H.
  - destruct H as [Hin H]. split; [apply in_or_app; left; exact Hin|].
    rewrite (pvm_rm1n_app _ _ _ Hin). apply IH. exact H.
Qed.

Lemma pvm_lszR_app : forall t1 t2, pvm_wf t2 -> lszR (t1 ++ t2) = lszR t2 ++ lszR t1.
Proof.
  intros t1 t2 H. unfold lszR. rewrite fold_left_app.
  exact (pvm_fold_app [] t2 (fold_left lsz_evR t1 []) H).
Qed.

Lemma pvm_held_from : forall s t, pvm_wf_from s t ->
  fold_right Z.add 0 (map Z.of_nat (fold_left lsz_evR t s)) = fold_right Z.add 0 (map Z.of_nat s) + held t.
Proof.
  intros s t. revert s. induction t as [|e t IH]; intros s H; cbn [fold_left held]; [lia|].
  destruct e as [n|[|m] n|n|n]; cbn [pvm_wf_from lsz_evR held_ev] in *.
  - rewrite (IH _ H). cbn [map fold_right]. lia.
  - rewrite (IH _ H). cbn [map fold_right]. lia.
  - destruct H as [Hin H]. rewrite (IH _ H). cbn [map fold_right]. rewrite (pvm_rm1n_zsum _ _ Hin). lia.
  - rewrite (IH _ H). lia.
  - destruct H as [Hin H]. rewrite (IH _ H). rewrite (pvm_rm1n_zsum _ _ Hin). lia.
Qed.

Lemma pvm_held_lsz : forall t, pvm_wf t -> held t = fold_right Z.add 0 (map Z.of_nat (lszR t)).
Proof. intros t H. unfold lszR. rewrite (pvm_held_from [] t H). cbn [map fold_right]. lia. Qed.

Lemma pvm_zsum_nat_nonneg : forall l, 0 <= fold_right Z.add 0 (map Z.of_nat l).
Proof. induction l as [|x l IH]; cbn [map fold_right]; lia. Qed.

Lemma pvm_held_nonneg : forall t, pvm_wf t -> 0 <= held t.
Proof. intros t H. rewrite (pvm_held_lsz t H). apply pvm_zsum_nat_nonneg. Qed.

Lemma pvm_nlive_from : forall s t, pvm_wf_from s t ->
  Z.of_nat (length (fold_left lsz_evR t s)) = Z.of_nat (length s) + nliveR t.
Proof.
  intros s t. revert s. induction t as [|e t IH]; intros s H; cbn [fold_left nliveR]; [lia|].
  destruct e as [n|[|m] n|n|n]; cbn [pvm_wf_from lsz_evR nlive_evR] in *.
  - rewrite (IH _ H). cbn [length]. lia.
  - rewrite (IH _ H). cbn [length]. lia.
  - destruct H as [Hin H]. rewrite (IH _ H). cbn [length]. pose proof (pvm_rm1n_len _ _ Hin). lia.
  - rewrite (IH _ H). lia.
  - destruct H as [Hin H]. rewrite (IH _ H). pose proof (pvm_rm1n_len _ _ Hin). lia.
Qed.

Lemma pvm_nlive_len : forall t, pvm_wf t -> nliveR t = Z.of_nat (length (lszR t)).
Proof. intros t H. unfold lszR. rewrite (pvm_nlive_from [] t H). cbn [length]. lia. Qed.

Lemma pvm_nlive_app : forall t1 t2, nliveR (t1 ++ t2) = nliveR t1 + nliveR t2.
Proof. induction t1 as [|e t1 IH]; intros t2; cbn [app nliveR]; [lia|]. rewrite IH. lia. Qed.

Lemma pvm_in_fold : forall t s a, pvm_wf_from [] t -> In a s -> In a (fold_left lsz_evR t s).
Proof.
  intros t s a H Ha. pose proof (pvm_fold_app [] t s H) as E. cbn [app] in E. rewrite E.
  apply in_or_app. right. exact Ha.
Qed.

Lemma pvm_inv_fold : forall t s (o : bool) cap, pvm_wf_from [] t ->
  (cap = 0%nat \/ (In (56 * cap)%nat s /\ (o = true -> In (8 * cap)%nat s))) ->
  (cap = 0%nat \/ (In (56 * cap)%nat (fold_left lsz_evR t s) /\
     (o = true -> In (8 * cap)%nat (fold_left lsz_evR t s)))).
Proof.
  intros t s o cap H [Hc|(H1 & H2)]; [left; exact Hc|right].
  split; [apply pvm_in_fold; assumption|intros Ho; apply pvm_in_fold; [exact H|exact (H2 Ho)]].
Qed.

(* ---- the reader monad ---- *)
Lemma pvm_wf_bind : forall (A B : Type) (m : M A) (k : A -> M B) ok s,
  pvm_wf_from s (snd (fst (m ok))) ->
  (forall a, fst (fst (m ok)) = Some a ->
     pvm_wf_from (fold_left lsz_evR (snd (fst (m ok))) s) (snd (fst (k a (snd (m ok)))))) ->
  pvm_wf_from s (snd (fst (jbind m k ok))).
Proof.
  intros A B m k ok s H1 H2. unfold jbind.
  destruct (m ok) as [[[a|] t] ok1]; cbn [fst snd] in *; [|exact H1].
  specialize (H2 a eq_refl). destruct (k a ok1) as [[r t'] ok2]; cbn [fst snd] in *.
  apply pvm_wf_from_app. split; assumption.
Qed.

Lemma pvm_wf_grow_cons : forall m k s r, (m = 0%nat \/ In m s) -> pvm_wf_from (lsz_evR s (EGrow m k)) r ->
  pvm_wf_from s (EGrow m k :: r).
Proof.
  intros [|m] k s r H1 H2; cbn [pvm_wf_from]; [exact H2|].
  destruct H1 as [H1|H1]; [discriminate|]. split; [exact H1|exact H2].
Qed.

Lemma pvm_in_grow_new : forall m k s, In k (lsz_evR s (EGrow m k)).
Proof. intros [|m] k s; cbn [lsz_evR In]; left; reflexivity. Qed.

Lemma pvm_in_grow_old : forall m k s a, In a s -> a <> m -> In a (lsz_evR s (EGrow m k)).
Proof.
  intros [|m] k s a H1 H2; cbn [lsz_evR In]; right; [exact H1|apply pvm_rm1n_in; assumption].
Qed.

(* ---- the grammar's pieces ---- *)
Lemma pvm_wf_string : forall z ok s, pvm_wf_from s (snd (fst (jr_string z ok))).
Proof.
  intros z ok s. unfold jr_string.
  destruct (scan z) as [q|]; [|exact I].
  unfold jbind, jalloc. cbv beta.
  destruct (take ok) as [[|] ok1]; cbv beta iota; [|exact I].
  destruct (decode z) as [sr|]; [exact I|].
  cbn [jfree jrefuse fst snd app pvm_wf_from]. split; [left; reflexivity|exact I].
Qed.

Lemma pvm_string_some_tr : forall z ok a, fst (fst (jr_string z ok)) = Some a ->
  snd (fst (jr_string z ok)) = [EAlloc (sblock z)].
Proof.
  intros z ok a H. unfold jr_string, sblock in *.
  destruct (scan z) as [q|]; [|cbn in H; discriminate].
  unfold jbind, jalloc in *. cbv beta in *.
  destruct (take ok) as [[|] ok1]; cbv beta iota in *; [|cbn in H; discriminate].
  destruct (decode z) as [sr|]; cbn in *; [reflexivity|discriminate].
Qed.

Lemma pvm_wf_name : forall o y ok s, pvm_wf_from s (snd (fst (jr_name o y ok))).
Proof.
  intros o y ok s. unfold jr_name. destruct o; [|exact I].
  destruct (skip y) as [|b z]; [exact I|].
  destruct (b =? 34); [|exact I].
  apply pvm_wf_bind; [apply pvm_wf_string|].
  intros [nm r] Ha. rewrite (pvm_string_some_tr z _ (nm, r) Ha). cbn [fold_left lsz_evR].
  cbv beta iota.
  destruct (skip r) as [|c r1]; [|destruct (c =? 58); [exact I|]];
    cbn [jbind jfree jrefuse fst snd app pvm_wf_from]; (split; [left; reflexivity|exact I]).
Qed.

Lemma pvm_wf_lit : forall w v x ok s, pvm_wf_from s (snd (fst (lit w v x ok))).
Proof. intros w v x ok s. unfold lit. destruct (prefixb w x); exact I. Qed.

Lemma pvm_wf_number : forall x ok s, pvm_wf_from s (snd (fst (jr_number prh_jr_strtod x ok))).
Proof.
  intros x ok s. unfold jr_number. cbv zeta.
  destruct (skipn _ x) as [|c z]; [exact I|].
  destruct (negb (digit c)); [exact I|].
  destruct (_ && _); [exact I|].
  destruct (span numch z) as [a r]. cbv beta iota.
  apply pvm_wf_bind.
  - unfold jalloc. destruct (take ok) as [[|] ok1]; exact I.
  - intros u _. destruct (whole _ _); exact I.
Qed.

Lemma pvm_wf_grow : forall o n cap ok s,
  (cap = 0%nat \/ (In (56 * cap)%nat s /\ (o = true -> In (8 * cap)%nat s))) ->
  pvm_wf_from s (snd (fst (grow o n cap ok))) /\
  (forall cap1, fst (fst (grow o n cap ok)) = Some cap1 ->
     cap1 = 0%nat \/ (In (56 * cap1)%nat (fold_left lsz_evR (snd (fst (grow o n cap ok))) s) /\
       (o = true -> In (8 * cap1)%nat (fold_left lsz_evR (snd (fst (grow o n cap ok))) s)))).
Proof.
  intros o n cap ok s Hc. unfold grow.
  destruct (Nat.ltb n cap) eqn:Elt.
  { cbn [jret fst snd fold_left]. split; [exact I|]. intros cap1 H. injection H as <-. exact Hc. }
  cbv zeta.
  destruct (Nat.eqb cap 0) eqn:E0.
  - apply Nat.eqb_eq in E0. subst cap.
    unfold jbind, jrealloc, jret. cbv beta.
    destruct (take ok) as [[|] ok1]; cbv beta iota.
    2: { split; [exact I|]. intros cap1 H. discriminate. }
    destruct o; [destruct (take ok1) as [[|] ok2]|]; cbv beta iota.
    + cbn. split; [exact I|]. intros cap1 H. injection H as <-. right.
      split; [right; left; reflexivity|intros _; left; reflexivity].
    + cbn. split; [exact I|]. intros cap1 H. discriminate.
    + cbn. split; [exact I|]. intros cap1 H. injection H as <-. right.
      split; [left; reflexivity|intros H; discriminate].
  - apply Nat.eqb_neq in E0.
    destruct Hc as [Hc|[H56 H8]]; [contradiction|].
    unfold jbind, jrealloc, jret. cbv beta.
    destruct (take ok) as [[|] ok1]; cbv beta iota.
    2: { cbn [fst snd pvm_wf_from lsz_evR]. split; [exact I|]. intros cap1 H. discriminate. }
    destruct o; [destruct (take ok1) as [[|] ok2]|]; cbv beta iota.
    + cbn [fst snd app fold_left]. split.
      * apply pvm_wf_grow_cons; [right; exact H56|]. apply pvm_wf_grow_cons; [|exact I].
        right. apply pvm_in_grow_old; [exact (H8 eq_refl)|lia].
      * intros cap1 H. injection H as <-. right. split; [|intros _; apply pvm_in_grow_new].
        apply pvm_in_grow_old; [apply pvm_in_grow_new|lia].
    + cbn [fst snd app fold_left]. split; [|intros cap1 H; discriminate].
      apply pvm_wf_grow_cons; [right; exact H56|exact I].
    + cbn [fst snd app fold_left]. split.
      * apply pvm_wf_grow_cons; [right; exact H56|exact I].
      * intros cap1 H. injection H as <-. right. split; [apply pvm_in_grow_new|intros H; discriminate].
Qed.

Lemma pvm_wf_fuel : forall f,
  (forall d x ok s, pvm_wf_from s (snd (fst (jrv prh_jr_strtod f d x ok)))) /\
  (forall d o n cap acc y ok s, (cap = 0%nat \/ (In (56 * cap)%nat s /\ (o = true -> In (8 * cap)%nat s))) ->
     pvm_wf_from s (snd (fst (jrl prh_jr_strtod f d o n cap acc y ok)))).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; exact I.
  - split.
    + intros d x ok s. cbn [jrv].
      destruct (skip x) as [|b y]; [exact I|].
      assert (Hc : forall o, pvm_wf_from s (snd (fst (jr_cont (jrl prh_jr_strtod f) d o (b :: y) ok)))).
      { intros o. unfold jr_cont. destruct (Nat.ltb MAXD (S d)); [exact I|].
        destruct (skip (tl (b :: y))) as [|c r]; [apply IHl; left; reflexivity|].
        destruct (c =? closer o); [exact I|apply IHl; left; reflexivity]. }
      destruct (b =? 123); [apply Hc|].
      destruct (b =? 91); [apply Hc|].
      destruct (b =? 34).
      { apply pvm_wf_bind; [apply pvm_wf_string|]. intros [s0 r] _. exact I. }
      destruct (b =? 116); [apply pvm_wf_lit|].
      destruct (b =? 102); [apply pvm_wf_lit|].
      destruct (b =? 110); [apply pvm_wf_lit|].
      apply pvm_wf_number.
    + intros d o n cap acc y ok s Hcap. cbn [jrl].
      apply pvm_wf_bind; [exact (proj1 (pvm_wf_grow o n cap ok s Hcap))|].
      intros cap1 Hg. pose proof (proj2 (pvm_wf_grow o n cap ok s Hcap) cap1 Hg) as Hc1. cbv beta.
      apply pvm_wf_bind; [apply pvm_wf_name|].
      intros [nm y1] _. cbv beta iota.
      apply pvm_wf_bind; [apply IHv|].
      intros [v r] _. cbv beta iota.
      destruct (skip r) as [|c r1]; [exact I|].
      destruct (c =? 44); [|destruct (c =? closer o); exact I].
      apply IHl. apply pvm_inv_fold; [apply IHv|]. apply pvm_inv_fold; [apply pvm_wf_name|]. exact Hc1.
Qed.

Lemma pvm_wf_jrv : forall f d x ok s, pvm_wf_from s (snd (fst (jrv prh_jr_strtod f d x ok))).
Proof. intros f. exact (proj1 (pvm_wf_fuel f)). Qed.

Lemma pvm_wf_jrl : forall f d o n cap acc y ok s,
  (cap = 0%nat \/ (In (56 * cap)%nat s /\ (o = true -> In (8 * cap)%nat s))) ->
  pvm_wf_from s (snd (fst (jrl prh_jr_strtod f d o n cap acc y ok))).
Proof. intros f. exact (proj2 (pvm_wf_fuel f)). Qed.

Lemma pvm_wf_value : forall d x ok, pvm_wf (snd (fst (jr_value prh_jr_strtod d x ok))).
Proof. intros d x ok. unfold pvm_wf, jr_value. apply pvm_wf_jrv. Qed.

Lemma pvm_wf_items : forall d o x ok, pvm_wf (snd (fst (jr_items prh_jr_strtod d o x ok))).
Proof.
  intros d o x ok. unfold pvm_wf, jr_items, jr_cont. destruct (Nat.ltb MAXD (S d)); [exact I|].
  destruct (skip (tl x)) as [|c r]; [apply pvm_wf_jrl; left; reflexivity|].
  destruct (c =? closer o); [exact I|apply pvm_wf_jrl; left; reflexivity].
Qed.

(* ================= 2. the ledger move of a prefix then a callee ================= *)

Lemma pvm_zsum_perm : forall l l', Permutation l l' -> fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof. intros l l' H. induction H; cbn [fold_right]; lia. Qed.

Lemma pvm_zsum_app : forall l1 l2, fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof. induction l1 as [|a l1 IH]; intros l2; cbn [app fold_right]; [lia|]. rewrite IH. lia. Qed.

Lemma pvm_lsum_map : forall D, Ledger.lsum D = fold_right Z.add 0 (map snd D).
Proof.
  induction D as [|[a k] D IH]; cbn [Ledger.lsum map fold_right snd]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma pvm_lsum_app : forall D1 D2, Ledger.lsum (D1 ++ D2) = Ledger.lsum D1 + Ledger.lsum D2.
Proof. induction D1 as [|[a k] D1 IH]; intros D2; cbn [app Ledger.lsum]; [reflexivity|]. rewrite IH. lia. Qed.

(* the batch kit ledger move (PRH_FnParse.v 4fe5b038ae41:173-182) across a GRANTED prefix (over its own trace, gt := tr1)
   and one call (over its own all-granted trace gt2): the whole move is over tr1 ++ gt2 ++ rest for any rest *)
Lemma pvm_nth_map_add : forall (c : Z) (l : list Z) (j : nat), (j < length l)%nat ->
  nth j (map (Z.add c) l) 0 = c + nth j l 0.
Proof. intros c l. induction l as [|x l IH]; intros [|j] H; cbn [length map nth] in *; try lia. apply IH. lia. Qed.

Lemma pvm_fold_max_zero : forall (f : nat -> Z) l, (forall i, In i l -> f i = 0) -> fold_right Z.max 0 (map f l) = 0.
Proof.
intros f l H. induction l as [|i l IH]; [reflexivity|]. cbn [map fold_right].
rewrite (H i (or_introl eq_refl)), IH by (intros j Hj; apply H; right; exact Hj). reflexivity.
Qed.

Lemma pvm_ledger_app : forall Lam peak cnt fail ran most ok1 tr1 D1 Lam1 peak1 cnt1 fail1 ran1
    ok2 gt2 tr2 D2 Lam2 peak2 cnt2 fail2 ran2 rest,
  pvm_wf tr1 -> pvm_wf tr2 -> length ok1 = PjGrammar.calls tr1 ->
  0 <= cnt -> cnt + Z.of_nat (PjGrammar.calls tr1 + PjGrammar.calls tr2) < SIZE_MAXZ -> 0 <= fail < 2 ^ 64 ->
  prh_granted ok1 cnt fail (PjGrammar.calls tr1) -> (PjGrammar.calls tr2 <= PjGrammar.calls gt2)%nat ->
  rd_ledger_move Lam peak cnt fail ran most ok1 tr1 tr1 D1 Lam1 peak1 cnt1 fail1 ran1 ->
  rd_ledger_move Lam1 peak1 cnt1 fail1 ran1 most ok2 gt2 tr2 D2 Lam2 peak2 cnt2 fail2 ran2 ->
  rd_ledger_move Lam peak cnt fail ran most (ok1 ++ ok2) (tr1 ++ gt2 ++ rest) (tr1 ++ tr2) (D2 ++ D1)
    Lam2 peak2 cnt2 fail2 ran2.
Proof.
  intros Lam peak cnt fail ran most ok1 tr1 D1 Lam1 peak1 cnt1 fail1 ran1 ok2 gt2 tr2 D2 Lam2 peak2 cnt2 fail2 ran2 rest
    W1 W2 Hlen Hc0 Hcb Hf G1 Hk2 L1 L2.
  unfold rd_ledger_move, fail_afterR in *.
  destruct L1 as ((O1a & O1b & O1c) & C1 & (F1a & F1b) & P1 & S1 & N1 & K1).
  destruct L2 as ((O2a & O2b & O2c) & C2 & (F2a & F2b) & P2 & S2 & N2 & K2).
  assert (EL1 : Ledger.lsum Lam1 = Ledger.lsum D1 + Ledger.lsum Lam).
  { rewrite !pvm_lsum_map. rewrite (pvm_zsum_perm _ _ (Permutation_map snd P1)), map_app, pvm_zsum_app.
    reflexivity. }
  assert (ED1 : Ledger.lsum D1 = held tr1).
  { rewrite pvm_lsum_map, (pvm_zsum_perm _ _ S1). symmetry. apply pvm_held_lsz. exact W1. }
  rewrite calls_app.
  unfold SIZE_MAXZ in *.
  remember (PjGrammar.calls tr1) as c1 eqn:Ec1. remember (PjGrammar.calls tr2) as c2 eqn:Ec2.
  assert (Ecnt1 : cnt1 = cnt + Z.of_nat c1) by (rewrite C1; apply Z.mod_small; lia).
  assert (HF1 : (cnt <= fail < cnt + Z.of_nat c1 /\ fail1 = 2 ^ 64 - 1) \/
                (~ (cnt <= fail < cnt + Z.of_nat c1) /\ fail1 = fail)).
  { destruct (Z_lt_dec fail cnt) as [Hl|Hl]; [right; split; [lia|apply F1b; lia]|].
    destruct (Z_lt_dec fail (cnt + Z.of_nat c1)) as [Hu|Hu];
      [left; split; [lia|apply F1a; lia]|right; split; [lia|apply F1b; lia]]. }
  assert (Hnth : forall i, nth i (ok1 ++ ok2) true =
                   if Nat.ltb i c1 then nth i ok1 true else nth (i - c1) ok2 true).
  { intros i. destruct (Nat.ltb i c1) eqn:E.
    - apply Nat.ltb_lt in E. apply app_nth1. lia.
    - apply Nat.ltb_ge in E. rewrite app_nth2 by lia. rewrite Hlen. reflexivity. }
  (* the granted prefix made no refusal: ran1 = ran and its refusal peak is 0 *)
  assert (NR1 : forall i, (i < c1)%nat -> prh_refused ok1 cnt fail i = false).
  { intros i Hi. unfold prh_refused. destruct (nth i ok1 true) eqn:E; [reflexivity|].
    rewrite (proj2 (Z.eqb_eq _ _) (G1 i Hi E)). reflexivity. }
  assert (ER1 : ran1 = ran).
  { destruct O1b as [E|(_ & i & Hi & Hr & _)]; [exact E|]. rewrite (NR1 i Hi) in Hr. discriminate. }
  assert (EP1 : prh_refused_peak ok1 cnt fail c1 (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds tr1)) = 0).
  { apply prh_refused_peak_granted. exact G1. }
  (* the refusal index shift and the requests list *)
  (* the call's refusals are judged against fail1 (the failure index after the prefix): the same as the whole's at
     the shifted index, whether or not the chosen failure fell in the prefix's window *)
  assert (RS : forall j, (j < c2)%nat -> prh_refused (ok1 ++ ok2) cnt fail (c1 + j) = prh_refused ok2 cnt1 fail1 j).
  { intros j Hj. unfold prh_refused. rewrite app_nth2 by lia. rewrite Hlen. replace (c1 + j - c1)%nat with j by lia.
    f_equal. f_equal. destruct HF1 as [(Hr & ->)|(Hr & ->)].
    - destruct (Z.eqb_spec (cnt + Z.of_nat (c1 + j)) fail) as [E|E];
        destruct (Z.eqb_spec (cnt1 + Z.of_nat j) (2 ^ 64 - 1)) as [E'|E']; try reflexivity; lia.
    - rewrite Ecnt1. f_equal. lia. }
  assert (RP : forall i, (i < c1)%nat -> prh_refused (ok1 ++ ok2) cnt fail i = false).
  { intros i Hi. apply (pik1_refused_pre ok1 ok2 cnt fail c1 i Hlen Hi G1). }
  assert (NS : forall j, nth (c1 + j) (prh_ev_reqs (tr1 ++ tr2)) 0 = nth j (prh_ev_reqs tr2) 0).
  { intros j. rewrite pik1_reqs_app, app_nth2 by (rewrite pik1_reqs_len; lia).
    rewrite pik1_reqs_len, <- Ec1. f_equal. lia. }
  split.
  { split; [|split].
    - intros i Hi Hie. rewrite Hnth. destruct (Nat.ltb i c1) eqn:E.
      + apply Nat.ltb_lt in E. apply O1a; assumption.
      + apply Nat.ltb_ge in E. apply O2a; [lia|]. rewrite Ecnt1.
        destruct HF1 as [(Hr & _)|(_ & ->)]; lia.
    - destruct O2b as [E2|(E2 & j & Hj & Hjr & Hjm)].
      + left. rewrite E2, ER1. reflexivity.
      + right. split; [exact E2|]. exists (c1 + j)%nat. split; [lia|]. rewrite (RS j Hj), NS. split; [exact Hjr | exact Hjm].
    - intros i Hi Hir Him. destruct (Nat.ltb i c1) eqn:E.
      + apply Nat.ltb_lt in E. rewrite (RP i E) in Hir. discriminate.
      + apply Nat.ltb_ge in E. replace i with (c1 + (i - c1))%nat in Hir, Him by lia.
        rewrite (RS (i - c1)%nat ltac:(lia)) in Hir. rewrite NS in Him. apply (O2c (i - c1)%nat); [lia|exact Hir|exact Him]. }
  split; [rewrite C2, Ecnt1; f_equal; lia|].
  split.
  { split; intros H.
    - destruct HF1 as [(Hr & E1)|(Hr & E1)].
      + rewrite F2b; [exact E1|]. rewrite Ecnt1, E1. lia.
      + apply F2a. rewrite Ecnt1, E1. lia.
    - assert (E1 : fail1 = fail) by (apply F1b; lia).
      rewrite F2b; [exact E1|]. rewrite Ecnt1, E1. lia. }
  split; [rewrite <- app_assoc; eapply Permutation_trans; [exact P2|apply Permutation_app_head; exact P1]|].
  split; [rewrite (pvm_lszR_app tr1 tr2 W2), !map_app; apply Permutation_app; assumption|].
  split; [rewrite length_app, pvm_nlive_app; lia|].
  (* the peak: the prefix's refusal peak is 0, and the call's re-indexes into the whole granted trace's helds *)
  assert (HRP : prh_refused_peak (ok1 ++ ok2) cnt fail (c1 + c2)
                  (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (tr1 ++ gt2 ++ rest))) =
                prh_refused_peak ok2 cnt1 fail1 c2 (map (Z.add (Ledger.lsum Lam1)) (prh_ev_helds gt2))).
  { unfold prh_refused_peak. rewrite pik1_seq_split, map_app, pik1_fold_max_app.
    rewrite (pvm_fold_max_zero _ (List.seq 0 c1)) by
      (intros i Hi; apply List.in_seq in Hi; rewrite (RP i ltac:(lia)); reflexivity).
    rewrite map_map. rewrite Z.max_r by apply pik1_fold_max_nonneg. f_equal.
    apply map_ext_in. intros j Hj. apply List.in_seq in Hj. rewrite (RS j ltac:(lia)).
    destruct (prh_refused ok2 cnt1 fail1 j); [|reflexivity]. f_equal.
    assert (Hl1 : length (prh_ev_helds tr1) = c1) by (rewrite pik1_helds_len; exact (eq_sym Ec1)).
    assert (Hj2 : (j < length (prh_ev_helds gt2))%nat) by (rewrite pik1_helds_len; lia).
    rewrite pik1_helds_app, map_app, app_nth2 by (rewrite length_map; lia).
    rewrite length_map, Hl1. replace (c1 + j - c1)%nat with j by lia.
    rewrite pvm_nth_map_add by (rewrite length_map, pik1_helds_app, length_app; lia).
    rewrite pik1_helds_app, pvm_nth_map_add by (rewrite length_app; lia).
    rewrite app_nth1 by exact Hj2. rewrite pvm_nth_map_add by exact Hj2. rewrite EL1, ED1. lia. }
  rewrite HRP, K2, K1, EP1, hpeak_app, EL1, ED1.
  pose proof (pik1_fold_max_nonneg []) as _.
  assert (H0 : 0 <= prh_refused_peak ok2 cnt1 fail1 c2 (map (Z.add (held tr1 + Ledger.lsum Lam)) (prh_ev_helds gt2)))
    by (unfold prh_refused_peak; apply pik1_fold_max_nonneg).
  lia.
Qed.

Lemma pvm_ledger_nil : forall Lam peak cnt fail ran most, 0 <= cnt < 2 ^ 64 -> 0 <= Ledger.lsum Lam <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [] [] [] [] Lam peak cnt fail ran.
Proof.
  intros Lam peak cnt fail ran most Hcnt Hsum. unfold rd_ledger_move. cbn [PjGrammar.calls lszR nliveR hpeakR map length].
  split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
  split; [rewrite Z.add_0_r; symmetry; apply Z.mod_small; lia|].
  split; [split; [intros H; lia | intros _; reflexivity]|].
  split; [cbn [app]; apply Permutation_refl|].
  split; [apply Permutation_refl|].
  split; [reflexivity|]. unfold prh_refused_peak. cbn [List.seq map fold_right]. lia.
Qed.

(* the allocator's blocks and frames across a prefix then a callee (one level deeper) *)
Section bmove.
Variable B : asyms.
Context {cp : CfParams}.

Lemma pvm_blocks_move_app : forall ly S ly1 S1 ly2 S2 D1 tr1 D2 tr2 x d y,
  rd_blocks_move B ly S ly1 S1 D1 tr1 x d -> rd_blocks_move B ly1 S1 ly2 S2 D2 tr2 y (Nat.succ d) ->
  hpeakR (tr1 ++ tr2) <= 224 * Z.of_nat (length x) + 512 * Z.of_nat (PjGrammar.MAXD - d) ->
  rd_blocks_move B ly S ly2 S2 (D2 ++ D1) (tr1 ++ tr2) x d.
Proof.
  intros ly S0 ly1 S1 ly2 S2 D1 tr1 D2 tr2 x d y M1 M2 Hpk. unfold rd_blocks_move in *.
  destruct M1 as (A1 & P1 & F1 & _). destruct M2 as (A2 & P2 & F2 & _).
  split.
  { intros a k Hin. apply in_app_or in Hin as [Hin|Hin]; [|exact (A1 a k Hin)].
    intros Hab. apply (A2 a k Hin). eapply Permutation_in; [apply Permutation_sym; exact P1|].
    apply in_or_app. right. exact Hab. }
  split.
  { assert (E : prhReader_ab (D2 ++ D1) = prhReader_ab D2 ++ prhReader_ab D1) by (unfold prhReader_ab; apply map_app).
    rewrite E, <- app_assoc. eapply Permutation_trans; [exact P2|]. apply Permutation_app_head. exact P1. }
  split; [eapply Permutation_trans; [exact F2|exact F1]|exact Hpk].
Qed.

End bmove.

(* ================= 3. the room of a member call; the continuation of pi_val_k ================= *)

Lemma pvm_zmax_app : forall l1 l2, 0 <= fold_right Z.max 0 l2 ->
  fold_right Z.max 0 (l1 ++ l2) = Z.max (fold_right Z.max 0 l1) (fold_right Z.max 0 l2).
Proof. induction l1 as [|a l1 IH]; intros l2 H; cbn [app fold_right]; [lia|]. rewrite (IH l2 H). lia. Qed.

Lemma pvm_maxreq_nonneg : forall t, 0 <= prh_maxreq t.
Proof. intros t. unfold prh_maxreq. induction (map _ t) as [|a l IH]; cbn [fold_right]; lia. Qed.

Lemma pvm_maxreq_app : forall t1 t2, prh_maxreq (t1 ++ t2) = Z.max (prh_maxreq t1) (prh_maxreq t2).
Proof.
  intros t1 t2. pose proof (pvm_maxreq_nonneg t2) as H. unfold prh_maxreq in *. rewrite map_app.
  apply pvm_zmax_app. exact H.
Qed.

Lemma pvm_room_suffix_maxreq : forall t1 t2, prh_maxreq t2 <= prh_maxreq (t1 ++ t2).
Proof. intros t1 t2. rewrite pvm_maxreq_app. lia. Qed.

Section room.
Context {cp : CfParams} {RL : PrhRoomLive}.

Lemma pvm_prh_held_app : forall t1 t2, prh_held (t1 ++ t2) = prh_held t1 + prh_held t2.
Proof. intros t1 t2. unfold prh_held. rewrite held_app, calls_app, Nat2Z.inj_add. ring. Qed.

(* the room of a trace split (the batch kit's tip 03fcabb582d0: rd_room's third conjunct is prh_live_evs, the live bytes along
   the trace's events from the state's live requests): the prefix's room at the same state, and the rest's room at a
   state whose live requests are the first one's moved by the prefix's events (PItems_ledk1.pik1_live_evs_pre /
   pik1_live_evs_after) *)
Lemma pvm_room_pre : forall S t1 t2, rd_room S (t1 ++ t2) -> rd_room S t1.
Proof.
  intros S0 t1 t2 (R1 & R2 & R3).
  unfold rd_room in *. rewrite pvm_maxreq_app in R2. rewrite PresetReqAt.rd_hevs_app in R3.
  split; [exact R1|]. split; [lia|]. exact (pik1_live_evs_pre S0 _ _ R3).
Qed.

Lemma pvm_room_after : forall S S' t1 t2, rd_room S (t1 ++ t2) -> room_live_cf S' ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs t1)) ->
  rd_room S' t2.
Proof.
  intros S0 S1 t1 t2 (R1 & R2 & R3) L Hp.
  unfold rd_room in *. rewrite pvm_maxreq_app in R2. rewrite PresetReqAt.rd_hevs_app in R3.
  split; [exact L|]. split; [lia|]. exact (pik1_live_evs_after S0 S1 _ _ R3 Hp).
Qed.

End room.

(* the continuation of pi_val_k after the value is PItems_value_pres.pv_kont; its granted remainder follows *)
Lemma pvm_val_k_eq : forall f D o n cap accr nm y1,
  pi_val_k f D o n cap accr nm y1 = jbind (jrv prh_jr_strtod f D y1) (pv_kont f D o n cap accr nm).
Proof. intros. reflexivity. Qed.

Definition pvm_gafter (f D : nat) (o : bool) (n cap : nat) (accr : list (list Z * jv)) (nm y1 : list Z)
  : list ev :=
  match fst (fst (jr_value prh_jr_strtod D y1 [])) with
  | Some tr => snd (fst (pv_kont f D o n cap accr nm tr []))
  | None => [] end.

Lemma pvm_gt_split : forall f D o n cap accr nm y1, (2 * length y1 + 1 <= f)%nat ->
  snd (fst (pi_val_k f D o n cap accr nm y1 [])) = prhPv_gtrace D y1 ++ pvm_gafter f D o n cap accr nm y1.
Proof.
  intros f D o n cap accr nm y1 Hf. rewrite pvm_val_k_eq. unfold jbind, prhPv_gtrace, pvm_gafter.
  rewrite (jr_value_fuel prh_jr_strtod f D y1 [] Hf).
  pose proof (agrees_nil _ _ (agrees_jr_value prh_jr_strtod D y1)) as N.
  destruct (jr_value prh_jr_strtod D y1 []) as [[[tr|] t] ok1]; cbn [fst snd] in *.
  - assert (E1 : ok1 = []) by (injection N; auto). subst ok1.
    destruct (pv_kont f D o n cap accr nm tr []) as [[r t'] ok2]. reflexivity.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma pvm_granted_some : forall D y ok t r tr okr, jr_value prh_jr_strtod D y ok = (Some (t, r), tr, okr) ->
  jr_value prh_jr_strtod D y [] = (Some (t, r), tr, []).
Proof.
  intros D y ok t r tr okr E.
  exact (proj1 (agrees_some _ _ ok (t, r) tr okr (agrees_jr_value prh_jr_strtod D y) E)).
Qed.

Lemma pvm_value_consumes : forall D y ok t r tr okr, jr_value prh_jr_strtod D y ok = (Some (t, r), tr, okr) ->
  (length r < length y)%nat.
Proof. intros D y ok t r tr okr E. exact (jr_value_rest prh_jr_strtod D y ok t r tr okr E). Qed.

Lemma pvm_jrv_value : forall f D y, (2 * length y + 1 <= f)%nat ->
  forall ok, jrv prh_jr_strtod f D y ok = jr_value prh_jr_strtod D y ok.
Proof. intros f D y H ok. exact (jr_value_fuel prh_jr_strtod f D y ok H). Qed.

(* ---- THE GRANTED EVENTS AT A BLOCK (form (b), PItems_posb.v): the whole call's ALL-GRANTED heap events begin with
   the events of the block's prefix trace tr0, then the granted events of the block's continuation K. A block whose
   run splits as `jr_items (ok0 ++ ok1) = (r, tr0 ++ t, ok2)` whenever `K ok1 = (r, t, ok2)` (PItems_defs.v
   pi_run_eq, PItems_pres.v pi_val_eq, PItems_value_pres.v pv_run_after) meets the granted run (ok = []) through
   PjGrammar.agrees_jr_items: if ok0 grants every call of the granted trace the two runs are the same; otherwise ok0
   refuses one of them, the run with ok0 stops there (its trace ends in that EFail, which makes no heap event: tr0
   ends in it) and K adds no event. ---- *)
Lemma pvm_gt_pref : forall d o x0 ok0 tr0 (K : PjGrammar.M (jv * list Z)),
  (forall ok1 r t ok2, K ok1 = (r, t, ok2) -> jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2)) ->
  length ok0 = calls tr0 ->
  exists E, PresetReqAt.rd_hevs (prhPi_gtrace d o x0) =
    PresetReqAt.rd_hevs tr0 ++ PresetReqAt.rd_hevs (snd (fst (K []))) ++ E.
Proof.
  intros d o x0 ok0 tr0 K HK Hlen.
  destruct (K []) as [[r t] ok2] eqn:EK. cbn [fst snd].
  pose proof (HK [] r t ok2 EK) as EI. rewrite app_nil_r in EI.
  pose proof (agrees_jr_items prh_jr_strtod d o x0 ok0) as [AG1 AG2].
  unfold prhPi_gtrace.
  destruct (ok_upto_dec ok0 (calls (snd (fst (jr_items prh_jr_strtod d o x0 []))))) as [Hu | (j & Hj & Hf & Hu)].
  - pose proof (AG1 Hu) as E2. rewrite EI in E2. injection E2 as E2r Et E2o.
    exists []. rewrite <- Et, PresetReqAt.rd_hevs_app, app_nil_r. reflexivity.
  - destruct (AG2 j Hj Hf Hu) as (P & E & rest & E2 & EG & HcP & HcE).
    rewrite EI in E2. injection E2 as E2r Et E2o.
    assert (Hjl : (j < length ok0)%nat).
    { destruct (Nat.lt_ge_cases j (length ok0)) as [Hl | Hge]; [exact Hl|].
      rewrite nth_overflow in Hf by exact Hge. discriminate Hf. }
    assert (Hc : (calls tr0 + calls t)%nat = S j).
    { rewrite <- calls_app, Et, calls_app, HcP. cbn [calls is_call]. clear; lia. }
    assert (Ht : t = []).
    { destruct (rev t) as [|x rt] eqn:Er.
      - rewrite <- (rev_involutive t), Er. reflexivity.
      - exfalso. assert (Et' : t = rev rt ++ [x]) by (rewrite <- (rev_involutive t), Er; reflexivity).
        rewrite Et', app_assoc in Et. apply app_inj_tail in Et as [_ Ex]. subst x.
        rewrite Et', calls_app in Hc. cbn [calls is_call] in Hc. clear - Hc Hjl Hlen; lia. }
    subst t. rewrite app_nil_r in Et. subst tr0.
    exists (PresetReqAt.rd_hevs (E :: rest)). rewrite EG, !PresetReqAt.rd_hevs_app.
    cbn [PresetReqAt.rd_hevs flat_map PresetReqAt.rd_hev app]. rewrite !app_nil_r. reflexivity.
Qed.

(* a callee's count premise at the block (the peak of a count along the callee's granted events T2, from the block's
   live requests sc), from the entry's over the whole call's granted events: the block's continuation begins with
   T2, PItems_posb.pi_lc_at at the block's pi_live, and the peak along a prefix of the events is at most the peak
   along all of them (PresetRun.pkR_app) *)
Lemma pvm_lc_call : forall f s sc d o x0 ok0 tr0 (K : PjGrammar.M (jv * list Z)) T2 b,
  (forall ok1 r t ok2, K ok1 = (r, t, ok2) -> jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2)) ->
  length ok0 = calls tr0 ->
  PItems_posb.pi_live s sc tr0 ->
  (exists T3, snd (fst (K [])) = T2 ++ T3) ->
  Z.of_nat (PresetRun.pkR f s (PresetReqAt.rd_hevs (prhPi_gtrace d o x0))) <= b ->
  Z.of_nat (PresetRun.pkR f sc (PresetReqAt.rd_hevs T2)) <= b.
Proof.
  intros f s sc d o x0 ok0 tr0 K T2 b HK Hlen Hl (T3 & ET) Hb.
  destruct (pvm_gt_pref d o x0 ok0 tr0 K HK Hlen) as (E & EG).
  rewrite ET, PresetReqAt.rd_hevs_app, <- app_assoc in EG. rewrite EG in Hb.
  assert (H : PItems_posb.pi_lc f sc (PresetReqAt.rd_hevs T2 ++ (PresetReqAt.rd_hevs T3 ++ E)) b)
    by (apply (PItems_posb.pi_lc_at f s sc tr0 (PresetReqAt.rd_hevs tr0)); [exact Hl | reflexivity | exact Hb]).
  unfold PItems_posb.pi_lc in H. rewrite PresetRun.pkR_app in H. clear - H. lia.
Qed.

(* ---- the rest a successful run leaves is a suffix of its input (plain ReaderKB.v rk_suf_*, ported) ---- *)
Definition pvm_suf (r x : list Z) : Prop := exists u, x = u ++ r.

Lemma pvm_suf_refl : forall x, pvm_suf x x.
Proof. intros x. exists []. reflexivity. Qed.

Lemma pvm_suf_trans : forall r y x, pvm_suf r y -> pvm_suf y x -> pvm_suf r x.
Proof. intros r y x (u & Hu) (v & Hv). exists (v ++ u). rewrite Hv, Hu. apply app_assoc. Qed.

Lemma pvm_suf_skipn : forall n x, pvm_suf (skipn n x) x.
Proof. intros n x. exists (firstn n x). symmetry. apply firstn_skipn. Qed.

Lemma pvm_suf_skip : forall x, pvm_suf (skip x) x.
Proof.
  induction x as [|b r IH]; [apply pvm_suf_refl|]. cbn [skip]. destruct (ws b).
  - destruct IH as (u & Hu). exists (b :: u). cbn [app]. f_equal. exact Hu.
  - apply pvm_suf_refl.
Qed.

Lemma pvm_suf_tl : forall x, pvm_suf (tl x) x.
Proof. intros [|b r]; [apply pvm_suf_refl|]. exists [b]. reflexivity. Qed.

Lemma pvm_suf_cons : forall b r y, pvm_suf (b :: r) y -> pvm_suf r y.
Proof. intros b r y (u & Hu). exists (u ++ [b]). rewrite Hu, <- app_assoc. reflexivity. Qed.

Lemma pvm_suf_string : forall z ok s r t ok', jr_string z ok = (Some (s, r), t, ok') -> pvm_suf r z.
Proof.
  intros z ok s r t ok' H. pose proof (jr_string_spec z ok) as Sp. rewrite H in Sp.
  destruct Sp as (q & Hq & Hd & _). destruct (G1_4 z s r Hd) as (q' & _ & Hr & _). rewrite Hr. apply pvm_suf_skipn.
Qed.

Lemma pvm_suf_lit : forall w v x ok u r t ok', lit w v x ok = (Some (u, r), t, ok') -> pvm_suf r x.
Proof.
  intros w v x ok u r t ok' H. unfold lit in H.
  destruct (prefixb w x); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as E1 E2 E3 E4. rewrite <- E2. apply pvm_suf_skipn.
Qed.

Lemma pvm_suf_number : forall x ok u r t ok', jr_number prh_jr_strtod x ok = (Some (u, r), t, ok') -> pvm_suf r x.
Proof.
  intros x ok u r t ok' H. unfold jr_number in H. cbv zeta in H.
  destruct (skipn _ x) as [|c z] eqn:E; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (_ && _); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r'] eqn:SP. cbv beta iota in H.
  apply jbind_some in H as (a0 & t1 & ok1 & t2 & _ & H & _).
  destruct (whole _ _); [|unfold jrefuse in H; discriminate].
  unfold jret in H. injection H as E1 E2 E3 E4. subst r.
  apply (pvm_suf_trans r' (c :: z) x).
  - apply span_app in SP. exists (c :: a). rewrite SP. reflexivity.
  - rewrite <- E. apply pvm_suf_skipn.
Qed.

Lemma pvm_suf_name : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) -> pvm_suf y1 y.
Proof.
  intros o y ok nm y1 tn ok2 H. unfold jr_name in H. destruct o.
  - destruct (skip y) as [|b z] eqn:E; [unfold jrefuse in H; discriminate|].
    destruct (b =? 34); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([name r] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
    destruct (skip r) as [|c r1] eqn:E2; [unfold jbind, jfree, jrefuse in H; cbn in H; discriminate H|].
    destruct (c =? 58); [|unfold jbind, jfree, jrefuse in H; cbn in H; discriminate H].
    unfold jret in H. injection H as F1 F2 F3 F4. subst y1.
    apply (pvm_suf_trans r1 r y); [apply (pvm_suf_cons c); rewrite <- E2; apply pvm_suf_skip|].
    apply (pvm_suf_trans r z y); [exact (pvm_suf_string z ok name r t1 ok1 Hs)|].
    apply (pvm_suf_cons b). rewrite <- E. apply pvm_suf_skip.
  - unfold jret in H. injection H as F1 F2 F3 F4. subst y1. apply pvm_suf_refl.
Qed.

Lemma pvm_suf_cont : forall loop d o x ok t r tr ok',
  (forall o' n cap acc y ok1 t1 r1 tr1 ok2, loop (S d) o' n cap acc y ok1 = (Some (t1, r1), tr1, ok2) ->
     pvm_suf r1 y) ->
  jr_cont loop d o x ok = (Some (t, r), tr, ok') -> pvm_suf r x.
Proof.
  intros loop d o x ok t r tr ok' HL H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbv zeta in H.
  destruct (skip (tl x)) as [|c r0] eqn:E; cbv beta iota in H.
  - pose proof (pvm_suf_trans _ _ _ (pvm_suf_skip (tl x)) (pvm_suf_tl x)) as SY. rewrite E in SY.
    exact (pvm_suf_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) SY).
  - pose proof (pvm_suf_trans _ _ _ (pvm_suf_skip (tl x)) (pvm_suf_tl x)) as SY. rewrite E in SY.
    destruct (c =? closer o); cbv beta iota in H.
    + unfold jret in H. injection H as F1 F2 F3 F4. subst r. exact (pvm_suf_cons c _ _ SY).
    + exact (pvm_suf_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) SY).
Qed.

Lemma pvm_suf_fuel : forall f,
  (forall d x ok t r tr ok', jrv prh_jr_strtod f d x ok = (Some (t, r), tr, ok') -> pvm_suf r x) /\
  (forall d o n cap acc y ok t r tr ok', jrl prh_jr_strtod f d o n cap acc y ok = (Some (t, r), tr, ok') ->
     pvm_suf r y).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y] eqn:SX; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (SY : pvm_suf (b :: y) x) by (rewrite <- SX; apply pvm_suf_skip).
      apply (pvm_suf_trans r (b :: y) x); [|exact SY].
      destruct (b =? 123); cbv beta iota in H.
      { exact (pvm_suf_cont _ _ _ _ _ _ _ _ _
          (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 91); cbv beta iota in H.
      { exact (pvm_suf_cont _ _ _ _ _ _ _ _ _
          (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) H). }
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hs & H & _). cbv beta iota in H.
        unfold jret in H. injection H as F1 F2 F3 F4. subst r.
        apply (pvm_suf_trans r1 y); [exact (pvm_suf_string y ok s r1 t1 ok1 Hs)|]. exists [b]. reflexivity. }
      destruct (b =? 116); cbv beta iota in H; [exact (pvm_suf_lit _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota in H; [exact (pvm_suf_lit _ _ _ _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota in H; [exact (pvm_suf_lit _ _ _ _ _ _ _ _ H)|].
      exact (pvm_suf_number _ _ _ _ _ _ H).
    + intros d o n cap acc y ok t r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & Hn & H & _). cbv beta iota in H.
      apply jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (pvm_suf_trans _ _ _ (IHv d y1 ok2 v r0 tv ok3 Ev) (pvm_suf_name o y ok1 nm y1 tn ok2 Hn)) as S0.
      destruct (skip r0) as [|c r1] eqn:E; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      assert (S1 : pvm_suf r1 y).
      { apply (pvm_suf_trans r1 r0 y); [apply (pvm_suf_cons c); rewrite <- E; apply pvm_suf_skip | exact S0]. }
      destruct (c =? 44); cbv beta iota in H.
      { exact (pvm_suf_trans _ _ _ (IHl d o (S n) cap1 ((nm, v) :: acc) r1 ok3 t r t4 ok' H) S1). }
      destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
      unfold jret in H. injection H as F1 F2 F3 F4. subst r. exact S1.
Qed.

Lemma pvm_value_suffix : forall D y ok t r tr okr, jr_value prh_jr_strtod D y ok = (Some (t, r), tr, okr) ->
  exists pre, y = pre ++ r.
Proof. intros D y ok t r tr okr E. exact (proj1 (pvm_suf_fuel _) D y ok t r tr okr E). Qed.

Lemma pvm_items_suffix : forall d o x ok t r tr okr, jr_items prh_jr_strtod d o x ok = (Some (t, r), tr, okr) ->
  exists pre, x = pre ++ r.
Proof.
  intros d o x ok t r tr okr E. unfold jr_items in E.
  exact (pvm_suf_cont _ d o x ok t r tr okr
    (fun o' n cap acc y0 ok1 t1 r1 tr1 ok2 => proj2 (pvm_suf_fuel _) (S d) o' n cap acc y0 ok1 t1 r1 tr1 ok2) E).
Qed.

Lemma pvm_nth_firstn : forall (l : list bool) k i d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  induction l as [|b l IH]; intros k i d H; destruct k as [|k]; try lia.
  - cbn [firstn]. reflexivity.
  - destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma pvm_skipn_len : forall (l1 l2 : list bool) j, length l1 = j -> skipn j (l1 ++ l2) = l2.
Proof. intros l1 l2 j <-. induction l1 as [|a l1 IH]; cbn [length skipn app]; [reflexivity|exact IH]. Qed.

Lemma pvm_jr_value_norm : forall D y ok res tr okr, jr_value prh_jr_strtod D y ok = (res, tr, okr) ->
  exists okn, length okn = PjGrammar.calls tr /\
    (forall i, (i < PjGrammar.calls tr)%nat -> nth i okn true = nth i ok true) /\
    forall ok', jr_value prh_jr_strtod D y (okn ++ ok') = (res, tr, ok').
Proof.
  intros D y ok res tr okr E.
  remember (PjGrammar.calls tr) as k eqn:Ek.
  exists (firstn k (ok ++ repeat true k)).
  assert (Hl : length (firstn k (ok ++ repeat true k)) = k).
  { rewrite length_firstn, length_app, repeat_length. lia. }
  assert (Hn : forall i, (i < k)%nat -> nth i (firstn k (ok ++ repeat true k)) true = nth i ok true).
  { intros i Hi. rewrite pvm_nth_firstn by exact Hi.
    destruct (Nat.lt_ge_cases i (length ok)) as [H|H].
    - apply app_nth1. exact H.
    - rewrite app_nth2 by exact H. rewrite nth_repeat. symmetry. apply nth_overflow. exact H. }
  split; [exact Hl|]. split; [exact Hn|].
  intros ok'.
  rewrite (agrees_det _ _ ok (firstn k (ok ++ repeat true k) ++ ok') res tr okr
             (agrees_jr_value prh_jr_strtod D y) E).
  - rewrite <- Ek. rewrite (pvm_skipn_len _ ok' k Hl). reflexivity.
  - intros i Hi. rewrite <- Ek in Hi. rewrite app_nth1 by lia. apply Hn. exact Hi.
Qed.

(* ================= 4. the peak bound of a whole run ================= *)

Lemma pvm_hpeak_items : forall d o x ok res tr okr, x <> [] ->
  jr_items prh_jr_strtod d o x ok = (res, tr, okr) ->
  hpeakR tr <= 224 * Z.of_nat (length x) + 512 * Z.of_nat (PjGrammar.MAXD - d).
Proof.
  intros d o x ok res tr okr Hx E. destruct x as [|b y]; [contradiction|].
  apply hpeak_le; [lia|]. intros p r Ep.
  apply (G10_2_items prh_jr_strtod d o b y ok p r). rewrite E. exact Ep.
Qed.

Lemma pvm_hpeak_value : forall d x ok res tr okr, jr_value prh_jr_strtod d x ok = (res, tr, okr) ->
  hpeakR tr <= 224 * Z.of_nat (length x) + 512 * Z.of_nat (PjGrammar.MAXD - d).
Proof.
  intros d x ok res tr okr E.
  apply hpeak_le; [lia|]. intros p r Ep.
  apply (G10_2 prh_jr_strtod d x ok p r). rewrite E. exact Ep.
Qed.

(* a prefix's peak never exceeds the whole trace's (no well-formedness needed: hpeak_app's first argument) *)
Lemma pvm_hpeak_prefix : forall t1 t2, hpeakR t1 <= hpeakR (t1 ++ t2).
Proof. intros t1 t2. rewrite hpeak_app. lia. Qed.

(* ================= 5. the half-built container: freeable on refusal, kept across a call ================= *)

(* pj_fdR fixes its block list only up to order (PItems_body_loop.v pil_fshape_perm / pil_fd_perm, re-proved here:
   that file is a walk file) *)
Lemma pvm_fshape_perm : forall segs m lblk Pi p D D', Permutation D D' ->
  pj_fshapeR segs m lblk Pi p D -> pj_fshapeR segs m lblk Pi p D'.
Proof.
  intros segs m lblk Pi p D D' HP HF.
  destruct HF as (HN & HA & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Hh & Hs & Hk & Hy & HPm & HPi).
  split; [ first [ eapply Permutation_NoDup; [exact HP | exact HN]
                 | apply NoDup_ListNoDup; eapply Permutation_NoDup;
                   [exact HP | apply NoDup_ListNoDup; exact HN] ] |].
  split.
  - intros b x Hb Hx. eapply HA; [|exact Hx]. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb].
  - exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
    split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|].
    split; [|exact HPi]. eapply Permutation_trans; [apply Permutation_sym; exact HP | exact HPm].
Qed.

Lemma pvm_fd_perm : forall segs m lblk d p D D', Permutation D D' ->
  pj_fdR segs m lblk d p D -> pj_fdR segs m lblk d p D'.
Proof.
  intros segs m lblk d p D D' HP H. destruct d as [|d']; cbn [pj_fdR] in H |- *;
    exact (pvm_fshape_perm segs m lblk _ p D D' HP H).
Qed.

(* pi_sblk (PItems_pres.v) is PItems_shape.v's pis_slots at the nat capacity *)
Lemma pvm_sblk_slots : forall o kids keys cap, pi_sblk o kids keys cap = pis_slots o kids keys (Z.of_nat cap).
Proof. intros [|] kids keys cap; reflexivity. Qed.

Section cont. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Variable B : asyms.

(* pi_cont is PItems_shape.v's pis_open at num = 0, the members split into values and names *)
Lemma pvm_cont_open : forall m lblk (o : bool) v kids keys n cap acc Di,
  pi_cont m lblk o v kids keys n cap acc Di -> pj_apartR (pi_sblk o kids keys cap) v ->
  NoDup (pi_sblk o kids keys cap ++ Di) ->
  pis_open pa_segs m lblk v o 0 kids keys (Z.of_nat cap) (Z.of_nat n) (map snd acc) (map fst acc) Di.
Proof.
  intros m lblk o v kids keys n cap acc Di HC HAs HN. unfold pi_cont in HC.
  destruct HC as (Hh & En & Hn & Hc54 & Hcap & Hk & HND & HA & Hi).
  unfold pis_open. rewrite <- pvm_sblk_slots.
  split; [exact HN|].
  split; [apply pis_r_apart_app; assumption|].
  split; [destruct o; exact Hh|].
  split.
  { unfold pj_slots_atR. split; [unfold pis_oz; destruct o; lia|]. split; [lia|]. split.
    - intros H0. destruct Hcap as [(C0 & K0 & Y0)|(C1 & _)]; [|lia]. split; [exact K0|]. intros _. exact Y0.
    - intros H0. destruct Hcap as [(C0 & _)|(C1 & L0 & L1)]; [lia|]. split; [exact L0|].
      intros H6. apply L1. destruct o; [reflexivity|]. unfold pis_oz in H6. lia. }
  split; [exact Hk|].
  unfold pis_items. destruct o.
  - split; [rewrite !length_map; reflexivity|]. rewrite pis_combine_map. exact Hi.
  - exact Hi.
Qed.

Lemma pi_cont_fd : forall m Lam (o : bool) v kids keys n cap acc Di D0 d,
  pi_cont m (prh_lin Lam) o v kids keys n cap acc Di ->
  Forall (fun mb => (PjTree.depth (snd mb) <= PjGrammar.MAXD - Nat.succ d)%nat) acc ->
  pj_apartR (pi_sblk o kids keys cap) v -> Permutation D0 (pi_sblk o kids keys cap ++ Di) -> NoDup D0 ->
  ((d < PjGrammar.MAXD)%nat \/ D0 = []) -> pj_fdR pa_segs m (prh_lin Lam) (PjGrammar.MAXD - d) v D0.
Proof.
  intros m Lam o v kids keys n cap acc Di D0 d HC HF HAs HP HN [Hd|E0].
  - assert (HN' : NoDup (pi_sblk o kids keys cap ++ Di)).
    { first [ eapply Permutation_NoDup; [exact HP | exact HN]
            | apply NoDup_ListNoDup; eapply Permutation_NoDup; [exact HP | apply NoDup_ListNoDup; exact HN] ]. }
    pose proof (pvm_cont_open m (prh_lin Lam) o v kids keys n cap acc Di HC HAs HN') as HO.
    unfold pi_cont in HC. destruct HC as (_ & En & _).
    replace (Z.of_nat n) with (Z.of_nat (length (map snd acc))) in HO by (rewrite length_map, <- En; reflexivity).
    pose proof (pis_exit_open pa_segs m (prh_lin Lam) v o 0 kids keys (Z.of_nat cap) (map snd acc) (map fst acc) Di d
      HO Hd) as HE.
    rewrite <- pvm_sblk_slots in HE.
    apply (pvm_fd_perm _ _ _ _ _ _ _ (Permutation_sym HP)). apply HE.
    apply Forall_map. exact HF.
  - subst D0. apply Permutation_nil in HP. apply app_eq_nil in HP as [Hs Hdi].
    unfold pi_cont in HC. destruct HC as (Hh & En & Hn & _ & Hcap & _).
    unfold pi_sblk, kids_blkR in Hs. apply app_eq_nil in Hs as [Hs _].
    destruct (Z.of_nat cap =? 0) eqn:Ec; [|discriminate]. apply Z.eqb_eq in Ec.
    assert (Ec0 : cap = 0%nat) by lia. subst cap.
    destruct Hcap as [(_ & K0 & Y0)|(C1 & _)]; [|lia]. subst kids keys.
    assert (En0 : n = 0%nat) by lia. rewrite En0 in Hh.
    change (Z.of_nat 0) with 0 in Hh.
    exact (pis_fd_hdr0 pa_segs m (prh_lin Lam) (PjGrammar.MAXD - d) v _ 0 0 Hh).
Qed.

(* the bytes pi_cont actually reads: the header, the n member slots of the kids block, the n key pointers of an
   object, and the blocks of Di *)
Definition pvm_cont_ufoot (o : bool) (v kids keys : Z) (n : nat) (Di : list (Z * Z)) (x : Z) : Prop :=
  (v <= x < v + 56) \/
  (exists i, (i < n)%nat /\ kids + 56 * Z.of_nat i <= x < kids + 56 * Z.of_nat i + 56) \/
  (o = true /\ exists i, (i < n)%nat /\ keys + 8 * Z.of_nat i <= x < keys + 8 * Z.of_nat i + 8) \/
  (exists b, In b Di /\ pj_holdsR b x).

Lemma pvm_cont_le : forall m lblk (o : bool) v kids keys n cap acc Di,
  pi_cont m lblk o v kids keys n cap acc Di -> (n <= cap)%nat.
Proof. intros m lblk o v kids keys n cap acc Di HC. unfold pi_cont in HC. destruct HC as (_ & _ & Hn & _). exact Hn. Qed.

(* the read bytes lie in the container's footprint *)
Lemma pvm_ufoot_foot : forall (o : bool) v kids keys n cap Di x, (n <= cap)%nat ->
  pvm_cont_ufoot o v kids keys n Di x -> pj_footR v (pi_sblk o kids keys cap ++ Di) x.
Proof.
  intros o v kids keys n cap Di x Hn [Hx|[(i & Hi & Hx)|[(Ho & i & Hi & Hx)|(b & Hb & Hx)]]].
  - left. exact Hx.
  - right. exists (kids, 56 * Z.of_nat cap).
    assert (Ec : (Z.of_nat cap =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (EK : kids_blkR kids (Z.of_nat cap) = [(kids, 56 * Z.of_nat cap)]) by (unfold kids_blkR; rewrite Ec; reflexivity).
    split; [|unfold pj_holdsR; cbn [fst snd]; lia].
    apply in_or_app. left. unfold pi_sblk. rewrite EK. apply in_or_app. left. left. reflexivity.
  - subst o. right. exists (keys, 8 * Z.of_nat cap).
    assert (Ec : (Z.of_nat cap =? 0) = false) by (apply Z.eqb_neq; lia).
    assert (EK : kids_blkR kids (Z.of_nat cap) = [(kids, 56 * Z.of_nat cap)]) by (unfold kids_blkR; rewrite Ec; reflexivity).
    assert (EY : keys_blkR (if true then 6 else 5) keys (Z.of_nat cap) = [(keys, 8 * Z.of_nat cap)])
      by (unfold keys_blkR; rewrite Ec; reflexivity).
    split; [|unfold pj_holdsR; cbn [fst snd]; lia].
    apply in_or_app. left. unfold pi_sblk. rewrite EK, EY. apply in_or_app. right. left. reflexivity.
  - right. exists b. split; [apply in_or_app; right; exact Hb | exact Hx].
Qed.

(* THE CORE: a memory that agrees on the read bytes keeps pi_cont *)
Lemma pvm_cont_frame_core : forall m m' lblk (o : bool) v kids keys n cap acc Di,
  pi_cont m lblk o v kids keys n cap acc Di ->
  pj_agreeR pa_segs m m' (pvm_cont_ufoot o v kids keys n Di) ->
  pi_cont m' lblk o v kids keys n cap acc Di.
Proof.
  intros m m' lblk o v kids keys n cap acc Di HC HA. unfold pi_cont in HC |- *. unfold pj_agreeR in HA.
  destruct HC as (Hh & En & Hn & Hc54 & Hcap & Hk & HND & HAp & Hi).
  assert (NF : forall i u D1, (i < n)%nat -> incl D1 Di ->
                 pj_nodeR pa_segs m lblk (kids + 56 * Z.of_nat i) u D1 ->
                 pj_nodeR pa_segs m' lblk (kids + 56 * Z.of_nat i) u D1).
  { intros i u D1 Hi0 Hinc HP. apply (pj_nodeR_frame pa_segs u m m' lblk _ D1 HP).
    intros y Hy. apply HA. destruct Hy as [Hy|(b & Hb & Hy)].
    - right. left. exists i. split; [exact Hi0 | exact Hy].
    - right. right. right. exists b. split; [apply Hinc; exact Hb | exact Hy]. }
  split; [apply (pj_hdrR_frame pa_segs m m'); [exact Hh | intros x Hx; apply HA; left; exact Hx]|].
  split; [exact En|]. split; [exact Hn|]. split; [exact Hc54|]. split; [exact Hcap|]. split; [exact Hk|].
  split; [exact HND|]. split; [exact HAp|].
  destruct o.
  - apply (pis_r_mems_mono pa_segs m lblk m' lblk (pj_nodeR pa_segs m lblk) (pj_nodeR pa_segs m' lblk)
      acc kids keys Di); [|exact Hi].
    intros i nm u x k D1 Hi' Hu Hxk Hinc Hx Hc HP. rewrite <- En in Hi'.
    split.
    { apply (rd_u64_frame pa_segs m m' _ _ Hx). intros y Hy. refine (proj1 (HA y _)).
      right. right. left. split; [reflexivity|]. exists i. split; [exact Hi' | exact Hy]. }
    split; [|exact (NF i u D1 Hi' Hinc HP)].
    apply (pj_cstrR_frame pa_segs m m' lblk x k nm Hc). intros y Hy. refine (proj1 (HA y _)).
    right. right. right. exists (x, k). split; [exact Hxk|]. unfold pj_holdsR. cbn [fst snd]. lia.
  - apply (pis_r_items_mono (pj_nodeR pa_segs m lblk) (pj_nodeR pa_segs m' lblk) (map snd acc) kids Di); [|exact Hi].
    intros i u D1 Hi' Hu Hinc HP. rewrite length_map, <- En in Hi'. exact (NF i u D1 Hi' Hinc HP).
Qed.

Lemma pi_cont_frame : forall m m' lblk (o : bool) v kids keys n cap acc Di,
  pi_cont m lblk o v kids keys n cap acc Di ->
  pj_agreeR pa_segs m m' (pj_footR v (pi_sblk o kids keys cap ++ Di)) ->
  pi_cont m' lblk o v kids keys n cap acc Di.
Proof.
  intros m m' lblk o v kids keys n cap acc Di HC HA.
  pose proof (pvm_cont_le m lblk o v kids keys n cap acc Di HC) as Hn.
  apply (pvm_cont_frame_core m m' lblk o v kids keys n cap acc Di HC).
  unfold pj_agreeR in HA |- *. intros x Hx. apply HA. exact (pvm_ufoot_foot o v kids keys n cap Di x Hn Hx).
Qed.

(* a write [lo, hi) outside the read bytes keeps pi_cont; the keys clause also admits a write outside the keys block
   (a kid-slot write of an object whose keys block lies above it) *)
Lemma pi_cont_frame_slot_gen : forall m m' lblk (o : bool) v kids keys n cap acc Di lo hi,
  pi_cont m lblk o v kids keys n cap acc Di ->
  (forall x, lo <= x < hi ->
     (keys + 8 * Z.of_nat n <= x \/ x < keys \/ keys + 8 * Z.of_nat cap <= x \/ o = false) /\
     (kids + 56 * Z.of_nat n <= x \/ x < kids \/ kids + 56 * Z.of_nat cap <= x) /\
     (forall b, In b Di -> ~ pj_holdsR b x) /\ ~ (v <= x < v + 56)) ->
  pj_agreeR pa_segs m m' (fun x => pj_footR v (pi_sblk o kids keys cap ++ Di) x /\ ~ (lo <= x < hi)) ->
  pi_cont m' lblk o v kids keys n cap acc Di.
Proof.
  intros m m' lblk o v kids keys n cap acc Di lo hi HC HS HA.
  pose proof (pvm_cont_le m lblk o v kids keys n cap acc Di HC) as Hn.
  apply (pvm_cont_frame_core m m' lblk o v kids keys n cap acc Di HC).
  unfold pj_agreeR in HA |- *. intros x Hx. apply HA.
  split; [exact (pvm_ufoot_foot o v kids keys n cap Di x Hn Hx)|].
  intros Hlh. destruct (HS x Hlh) as (Sa & Sb & Sc & Sd).
  destruct Hx as [Hx|[(i & Hi & Hx)|[(Ho & i & Hi & Hx)|(b & Hb & Hx)]]].
  - exact (Sd Hx).
  - lia.
  - subst o. destruct Sa as [Sa|[Sa|[Sa|Sa]]]; [lia | lia | lia | discriminate].
  - exact (Sc b Hb Hx).
Qed.

Lemma pi_cont_frame_slot : forall m m' lblk (o : bool) v kids keys n cap acc Di lo hi,
  pi_cont m lblk o v kids keys n cap acc Di ->
  (forall x, lo <= x < hi -> (keys + 8 * Z.of_nat n <= x \/ o = false) /\
     (kids + 56 * Z.of_nat n <= x \/ x < kids \/ kids + 56 * Z.of_nat cap <= x) /\
     (forall b, In b Di -> ~ pj_holdsR b x) /\ ~ (v <= x < v + 56)) ->
  pj_agreeR pa_segs m m' (fun x => pj_footR v (pi_sblk o kids keys cap ++ Di) x /\ ~ (lo <= x < hi)) ->
  pi_cont m' lblk o v kids keys n cap acc Di.
Proof.
  intros m m' lblk o v kids keys n cap acc Di lo hi HC HS HA.
  apply (pi_cont_frame_slot_gen m m' lblk o v kids keys n cap acc Di lo hi HC); [|exact HA].
  intros x Hx. destruct (HS x Hx) as (Sa & Sb & Sc & Sd).
  split; [destruct Sa as [Sa|Sa]; [left; exact Sa | right; right; right; exact Sa]|].
  split; [exact Sb|]. split; [exact Sc | exact Sd].
Qed.

End cont.

(* ================= 6. The batch kit's invariants (the batch kit 240b06ed4fd4) ================= *)

(* ---- the outcome list of a run that RETURNED: every allocation it made was granted (an ok list that refuses a call
   stops the run there with None, PjGrammar.agrees' second clause) ---- *)
Lemma pvm_some_granted : forall (A : Type) (m : M A) ok a t ok', agrees m -> m ok = (Some a, t, ok') ->
  forall i, (i < calls t)%nat -> nth i ok true = true.
Proof.
intros A m ok a t ok' H E. destruct (agrees_some A m ok a t ok' H E) as [E0 _].
destruct (ok_upto_dec ok (calls t)) as [Hu | (j & Hj & Hf & Hu)]; [exact Hu|].
pose proof (proj2 (H ok) j) as G. rewrite E0 in G. cbn [fst snd] in G.
destruct (G Hj Hf Hu) as (P & e & rest & E2 & _). rewrite E in E2. discriminate E2.
Qed.

Lemma pvm_repeat_of_nth : forall (l : list bool) k, length l = k -> (forall i, (i < k)%nat -> nth i l true = true) ->
  l = repeat true k.
Proof.
induction l as [|b l IH]; intros k Hl H; cbn [length] in Hl; subst k; [reflexivity|].
cbn [repeat]. f_equal; [exact (H 0%nat ltac:(lia))|]. apply IH; [reflexivity|].
intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

(* ---- a run's trace makes at most the all-granted run's calls (a refusal stops at the refused call) ---- *)
Lemma pvm_calls_le_granted : forall (A : Type) (m : M A) ok r t ok', agrees m -> m ok = (r, t, ok') ->
  (calls t <= calls (snd (fst (m []))))%nat.
Proof.
intros A m ok r t ok' H E.
destruct (ok_upto_dec ok (calls (snd (fst (m []))))) as [Hu | (j & Hj & Hf & Hu)].
- pose proof (proj1 (H ok) Hu) as E2. rewrite E in E2. injection E2 as _ Et _. rewrite Et. lia.
- destruct (proj2 (H ok) j Hj Hf Hu) as (P & e & rest & E2 & _ & HcP & _). rewrite E in E2.
  injection E2 as _ Et _. rewrite Et, calls_app. cbn [calls is_call]. clear - Hj HcP. lia.
Qed.

(* ---- under the GRANTED PREFIX (pi_grant), the whole call's all-granted run IS the prefix then the block's continuation
   at ok = [] (PItems_ledk1.pik1_run_granted on agrees_jr_items) ---- *)
Lemma pvm_gt_grant : forall d o x0 ok0 tr0 (K : PjGrammar.M (jv * list Z)),
  (forall ok1 r t ok2, K ok1 = (r, t, ok2) -> jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (r, tr0 ++ t, ok2)) ->
  ok0 = repeat true (calls tr0) ->
  fst (jr_items prh_jr_strtod d o x0 []) = (fst (fst (K [])), tr0 ++ snd (fst (K []))).
Proof.
intros d o x0 ok0 tr0 K HK Hg. destruct (K []) as [[r t] ok2] eqn:EK. cbn [fst snd].
pose proof (HK [] r t ok2 EK) as EI. rewrite app_nil_r, Hg in EI.
exact (pik1_run_granted _ (jr_items prh_jr_strtod d o x0) (calls tr0) r (tr0 ++ t) ok2
  (agrees_jr_items prh_jr_strtod d o x0) EI).
Qed.

(* ---- the FREE LIST of a run depends only on the outcomes of the calls the run makes (jfv / jfl follow jrv / jrl) ---- *)
Lemma pvm_bind_det : forall (A B : Type) (m : M A) (k : A -> M B) ok ok' r t1 ok1, agrees m -> m ok = (r, t1, ok1) ->
  (forall i, (i < calls (snd (fst (jbind m k ok))))%nat -> nth i ok' true = nth i ok true) ->
  m ok' = (r, t1, skipn (calls t1) ok') /\ ok1 = skipn (calls t1) ok /\
  (forall i, (i < calls t1)%nat -> nth i ok' true = nth i ok true) /\
  (forall a, r = Some a -> forall i, (i < calls (snd (fst (k a ok1))))%nat ->
     nth i (skipn (calls t1) ok') true = nth i ok1 true).
Proof.
intros A B m k ok ok' r t1 ok1 Hm E Hag.
assert (Hall : forall i, (i < calls t1)%nat -> nth i ok' true = nth i ok true).
{ intros i Hi. apply Hag. unfold jbind. rewrite E. destruct r as [a|]; cbn [fst snd]; [|exact Hi].
  destruct (k a ok1) as [[r2 t2] ok2]. cbn [fst snd]. rewrite calls_app. lia. }
pose proof (agrees_det A m ok ok' r t1 ok1 Hm E Hall) as E'.
pose proof (agrees_det A m ok ok r t1 ok1 Hm E (fun i _ => eq_refl)) as E''. rewrite E in E''.
injection E'' as Eo.
split; [exact E'|]. split; [exact Eo|]. split; [exact Hall|].
intros a -> i Hi. destruct (k a ok1) as [[r2 t2] ok2] eqn:Ek. cbn [fst snd] in Hi.
rewrite nth_skipn_b, Eo, nth_skipn_b. apply Hag. unfold jbind. rewrite E. cbn [fst snd]. rewrite Ek. cbn [fst snd].
rewrite calls_app. lia.
Qed.

Lemma pvm_jfc_det : forall sm f d o x ok ok' r t o1,
  (forall d' o' n cap acc af y ok ok',
     (forall i, (i < calls (snd (fst (jrl sm f d' o' n cap acc y ok))))%nat -> nth i ok' true = nth i ok true) ->
     PresetReqAt.jfl sm f d' o' n cap af y ok' = PresetReqAt.jfl sm f d' o' n cap af y ok) ->
  jr_cont (jrl sm f) d o x ok = (r, t, o1) -> (forall i, (i < calls t)%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x ok' = PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x ok.
Proof.
intros sm f d o x ok ok' r t o1 IH E Hag. unfold PresetReqAt.jf_cont. unfold jr_cont in E.
destruct (Nat.ltb MAXD (S d)); [reflexivity|]. cbv zeta in E |- *.
destruct (skip (tl x)) as [|c r0].
- apply (IH (S d) o 0%nat 0%nat [] [] [] ok ok'). rewrite E. exact Hag.
- destruct (c =? closer o); [reflexivity|].
  apply (IH (S d) o 0%nat 0%nat [] [] (c :: r0) ok ok'). rewrite E. exact Hag.
Qed.

Lemma pvm_jf_det : forall sm f,
  (forall d x ok ok', (forall i, (i < calls (snd (fst (jrv sm f d x ok))))%nat -> nth i ok' true = nth i ok true) ->
     PresetReqAt.jfv sm f d x ok' = PresetReqAt.jfv sm f d x ok) /\
  (forall d o n cap acc af y ok ok',
     (forall i, (i < calls (snd (fst (jrl sm f d o n cap acc y ok))))%nat -> nth i ok' true = nth i ok true) ->
     PresetReqAt.jfl sm f d o n cap af y ok' = PresetReqAt.jfl sm f d o n cap af y ok).
Proof.
intros sm f. induction f as [|f [IHv IHl]]; [split; intros; reflexivity|]. split.
- intros d x ok ok' Hag.
  destruct (jrv sm (S f) d x ok) as [[r t] o1] eqn:EJ0. cbn [fst snd] in Hag.
  pose proof (agrees_det _ _ ok ok' r t o1 (proj1 (agrees_fuel sm (S f)) d x) EJ0 Hag) as EJ1.
  cbn [PresetReqAt.jfv]. rewrite EJ1, EJ0. cbn [jrv] in EJ0.
  destruct (skip x) as [|b y]; cbv beta iota in EJ0 |- *; [reflexivity|].
  destruct (b =? 123); cbv beta iota in EJ0 |- *; [exact (pvm_jfc_det sm f d true (b :: y) ok ok' r t o1 IHl EJ0 Hag)|].
  destruct (b =? 91); cbv beta iota in EJ0 |- *; [exact (pvm_jfc_det sm f d false (b :: y) ok ok' r t o1 IHl EJ0 Hag)|].
  reflexivity.
- intros d o n cap acc af y ok ok' Hag. cbn [jrl] in Hag. cbn [PresetReqAt.jfl].
  destruct (grow o n cap ok) as [[g tg] okg] eqn:EG.
  destruct (pvm_bind_det _ _ (grow o n cap) _ ok ok' g tg okg (agrees_grow o n cap) EG Hag) as (EG' & _ & _ & Hag1).
  rewrite EG'. destruct g as [cap1|]; cbv beta iota; [|reflexivity].
  specialize (Hag1 cap1 eq_refl). cbv beta in Hag1.
  destruct (jr_name o y okg) as [[nr tn] okn] eqn:EN.
  destruct (pvm_bind_det _ _ (jr_name o y) _ okg (skipn (calls tg) ok') nr tn okn (agrees_jr_name o y) EN Hag1)
    as (EN' & _ & _ & Hag2).
  rewrite EN'. destruct nr as [[nm y1]|]; cbv beta iota; [|reflexivity].
  specialize (Hag2 (nm, y1) eq_refl). cbv beta iota in Hag2.
  destruct (jrv sm f d y1 okn) as [[rv tv] okv] eqn:EV.
  destruct (pvm_bind_det _ _ (jrv sm f d y1) _ okn (skipn (calls tn) (skipn (calls tg) ok')) rv tv okv
    (proj1 (agrees_fuel sm f) d y1) EV Hag2) as (EV' & _ & HallV & Hag3).
  rewrite (IHv d y1 okn (skipn (calls tn) (skipn (calls tg) ok')) ltac:(rewrite EV; exact HallV)).
  rewrite EV'. destruct rv as [[v r]|]; cbv beta iota; [|reflexivity].
  specialize (Hag3 (v, r) eq_refl). cbv beta iota in Hag3.
  destruct (skip r) as [|c r1]; cbv beta iota in Hag3 |- *; [reflexivity|].
  destruct (c =? 44); cbv beta iota in Hag3 |- *; [|reflexivity].
  exact (IHl d o (S n) cap1 ((nm, v) :: acc) _ r1 okv _ Hag3).
Qed.

(* the free list of a value run, at the run's normalised outcome list (pvm_jr_value_norm) and at its own *)
Lemma pvm_jfv_det : forall sm f d x ok ok' r t o1, jrv sm f d x ok = (r, t, o1) ->
  (forall i, (i < calls t)%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.jfv sm f d x ok' = PresetReqAt.jfv sm f d x ok.
Proof.
intros sm f d x ok ok' r t o1 E H. apply (proj1 (pvm_jf_det sm f)). rewrite E. exact H.
Qed.

(* ---- the frame lemmas of the batch kit's invariants (stated over pi_cont's read bytes, pvm_cont_ufoot) ---- *)
Lemma pvm_ufoot_kids : forall (o : bool) v kids keys n Di x, kids <= x < kids + 56 * Z.of_nat n ->
  pvm_cont_ufoot o v kids keys n Di x.
Proof.
intros o v kids keys n Di x Hx. right. left. exists (Z.to_nat ((x - kids) / 56)).
split; [|rewrite Z2Nat.id by lia; lia]. lia.
Qed.

Lemma pvm_ofoot_ufoot : forall (o : bool) v kids keys n Di x,
  PRH_PjOrder.pf_ofoot o kids keys n Di x -> pvm_cont_ufoot o v kids keys n Di x.
Proof.
intros o v kids keys n Di x [Hx | [(Ho & Hx) | (b & Hb & Hx)]].
- exact (pvm_ufoot_kids o v kids keys n Di x Hx).
- right. right. left. split; [exact Ho|]. exists (Z.to_nat ((x - keys) / 8)).
  split; [|rewrite Z2Nat.id by lia; lia]. lia.
- right. right. right. exists b. split; [exact Hb | exact Hx].
Qed.

(* pj_kidsR over one more element, and pj_foR over a permutation of its block list *)
Lemma pvm_kids_snoc : forall (A : Type) (P : Z -> A -> Prop) (l : list A) a x,
  pj_kidsR P a (l ++ [x]) <-> pj_kidsR P a l /\ P (a + 56 * Z.of_nat (length l)) x.
Proof.
intros A P l. induction l as [|y l IH]; intros a x; cbn [app pj_kidsR length].
- replace (a + 56 * Z.of_nat 0) with a by lia. tauto.
- rewrite IH. replace (a + 56 + 56 * Z.of_nat (length l)) with (a + 56 * Z.of_nat (S (length l))) by lia. tauto.
Qed.

Lemma pvm_foR_perm : forall segs m lblk d p D D' F, Permutation D D' ->
  PRH_PjOrder.pj_foR segs m lblk d p D F -> PRH_PjOrder.pj_foR segs m lblk d p D' F.
Proof.
intros segs m lblk d p D D' F HP H.
assert (G : forall Pi, PRH_PjOrder.pj_oshapeR segs m lblk Pi p D F -> PRH_PjOrder.pj_oshapeR segs m lblk Pi p D' F).
{ intros Pi (HN & HA & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi & Hh & Hs & Hk & Hy & HPm &
    HPi & HF).
  split; [ first [ eapply Permutation_NoDup; [exact HP | exact HN]
                 | apply NoDup_ListNoDup; eapply Permutation_NoDup;
                   [exact HP | apply NoDup_ListNoDup; exact HN] ] |].
  split; [intros b x Hb Hx; eapply HA; [|exact Hx]; eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb]|].
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi.
  split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|].
  split; [eapply Permutation_trans; [apply Permutation_sym; exact HP | exact HPm]|]. split; [exact HPi | exact HF]. }
destruct d; cbn [PRH_PjOrder.pj_foR] in H |- *; apply G; exact H.
Qed.

Section k1frame. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Notation mrestrict := YK04.mrestrict.

(* THE COMPLETED SLOTS' FREE ORDER across a memory (and a ledger growth) that keeps pi_cont's read bytes *)
Lemma pvm_forder_frame : forall m m' (lblk lblk' : Z -> Z -> Prop) (o : bool) v kids keys n Di
    (acc : list (list Z * jv)) af,
  pi_forder m lblk o kids keys n Di acc af ->
  (forall x k, lblk x k -> lblk' x k) ->
  pj_agreeR pa_segs m m' (pvm_cont_ufoot o v kids keys n Di) ->
  pi_forder m' lblk' o kids keys n Di acc af.
Proof.
intros m m' lblk lblk' o v kids keys n Di acc af HF HL HA Hh nn Hnn.
destruct (HF Hh nn Hnn) as (Facc & HO & HM). exists Facc. split; [|exact HM].
apply (PRH_PjOrder.pf_oitemsR_frame pa_segs nn m m' lblk lblk' o kids keys n Di Facc HO).
- intros x k Hin. apply HL. exact (PRH_PjOrder.pf_oitemsR_lblk pa_segs m lblk nn o kids keys n Di Facc HO x k Hin).
- apply (PRH_PjOrder.pf_agree_mono pa_segs _ _ _ _ HA). intros x Hx. exact (pvm_ofoot_ufoot o v kids keys n Di x Hx).
Qed.

Lemma pvm_ncaps_items : forall (H : word -> bool) mem m' lblk (X : Z -> Prop) (accs : list (list Z * jv)) a Di,
  pj_itemsR (pj_nodeR pa_segs (mrestrict H mem) lblk) a (map snd accs) Di ->
  pi_ncaps (mrestrict H mem) a accs ->
  pj_agreeR pa_segs (mrestrict H mem) m' X ->
  (forall x, a <= x < a + 56 * Z.of_nat (length accs) -> X x) ->
  (forall b x, In b Di -> pj_holdsR b x -> X x) ->
  pi_ncaps m' a accs.
Proof.
intros H mem m' lblk X accs. unfold pi_ncaps.
induction accs as [|[nm u] r IH]; intros a Di HI HK HA HX HD; cbn [map pj_itemsR pj_kidsR] in HI, HK |- *; [exact I|].
destruct HI as (D1 & D2 & -> & H1 & H2). destruct HK as (K1 & K2). cbn [snd] in K1 |- *. split.
- apply (PvB_Frees.pvf_ncap_frame pa_segs u H mem m' lblk a D1 H1); [|exact K1].
  apply (PRH_PjOrder.pf_agree_mono pa_segs _ _ X _ HA). intros x [Hx | (b & Hb & Hx)].
  + apply HX. cbn [length]. lia.
  + apply (HD b x); [apply in_or_app; left; exact Hb | exact Hx].
- apply (IH (a + 56) D2 H2 K2 HA).
  + intros x Hx. apply HX. cbn [length]. lia.
  + intros b x Hb Hx. apply (HD b x); [apply in_or_app; right; exact Hb | exact Hx].
Qed.

Lemma pvm_ncaps_mems : forall (H : word -> bool) mem m' lblk (X : Z -> Prop) (accs : list (list Z * jv)) a ka Di,
  pj_memsR pa_segs (mrestrict H mem) lblk (pj_nodeR pa_segs (mrestrict H mem) lblk) a ka accs Di ->
  pi_ncaps (mrestrict H mem) a accs ->
  pj_agreeR pa_segs (mrestrict H mem) m' X ->
  (forall x, a <= x < a + 56 * Z.of_nat (length accs) -> X x) ->
  (forall b x, In b Di -> pj_holdsR b x -> X x) ->
  pi_ncaps m' a accs.
Proof.
intros H mem m' lblk X accs. unfold pi_ncaps.
induction accs as [|[nm u] r IH]; intros a ka Di HI HK HA HX HD; cbn [pj_memsR pj_kidsR] in HI, HK |- *; [exact I|].
destruct HI as (x0 & k0 & D1 & D2 & -> & _ & _ & H1 & H2). destruct HK as (K1 & K2). cbn [snd] in K1 |- *. split.
- apply (PvB_Frees.pvf_ncap_frame pa_segs u H mem m' lblk a D1 H1); [|exact K1].
  apply (PRH_PjOrder.pf_agree_mono pa_segs _ _ X _ HA). intros x [Hx | (b & Hb & Hx)].
  + apply HX. cbn [length]. lia.
  + apply (HD b x); [right; apply in_or_app; left; exact Hb | exact Hx].
- apply (IH (a + 56) (ka + 8) D2 H2 K2 HA).
  + intros x Hx. apply HX. cbn [length]. lia.
  + intros b x Hb Hx. apply (HD b x); [right; apply in_or_app; right; exact Hb | exact Hx].
Qed.

(* THE MEMBERS' CAPACITIES across a memory that keeps pi_cont's read bytes *)
Lemma pvm_ncaps_frame : forall (H : word -> bool) mem m' lblk (o : bool) v kids keys n cap acc Di,
  pi_cont (mrestrict H mem) lblk o v kids keys n cap acc Di ->
  pi_ncaps (mrestrict H mem) kids acc ->
  pj_agreeR pa_segs (mrestrict H mem) m' (pvm_cont_ufoot o v kids keys n Di) ->
  pi_ncaps m' kids acc.
Proof.
intros H mem m' lblk o v kids keys n cap acc Di HC HK HA.
pose proof HC as (_ & En & _ & _ & _ & _ & _ & _ & Hi).
assert (HX : forall x, kids <= x < kids + 56 * Z.of_nat (length acc) -> pvm_cont_ufoot o v kids keys n Di x)
  by (intros x Hx; apply pvm_ufoot_kids; rewrite En; exact Hx).
assert (HD : forall b x, In b Di -> pj_holdsR b x -> pvm_cont_ufoot o v kids keys n Di x)
  by (intros b x Hb Hx; right; right; right; exists b; split; [exact Hb | exact Hx]).
destruct o.
- exact (pvm_ncaps_mems H mem m' lblk _ acc kids keys Di Hi HK HA HX HD).
- exact (pvm_ncaps_items H mem m' lblk _ acc kids Di Hi HK HA HX HD).
Qed.

(* the members' capacities of a container one member longer (v->n++ after a value that was read) *)
Lemma pvm_ncaps_snoc : forall m kids acc nm t,
  pi_ncaps m kids (acc ++ [(nm, t)]) <-> pi_ncaps m kids acc /\ pj_ncapR pa_segs m (kids + 56 * Z.of_nat (length acc)) t.
Proof. intros m kids acc nm t. unfold pi_ncaps. rewrite pvm_kids_snoc. cbn [snd]. tauto. Qed.

End k1frame.
