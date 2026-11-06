(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_tables MallocInv_steps.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wcov (w : fct) (x : Z) : bool := (f_a w <=? x) && (x <? f_a w + f_n w).

Fixpoint wlook (ws : list fct) (x : Z) : option Z :=
  match ws with
  | [] => None
  | w :: ws' => if wcov w x then Some (byte_of (f_v w) (x - f_a w)) else wlook ws' x
  end.

(* [comment removed for export] *)
Definition wfree (ws : list fct) (x : Z) : Prop :=
  Forall (fun w => x < f_a w \/ f_a w + f_n w <= x) ws.

Lemma wcov_spec : forall w x, wcov w x = true <-> f_a w <= x < f_a w + f_n w.
Proof. intros w x. unfold wcov. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma wlook_free : forall ws x, wfree ws x -> wlook ws x = None.
Proof.
  induction ws as [|w ws IH]; intros x Hf; [reflexivity|].
  inversion Hf as [| w' ws' Hw Hws]; subst. cbn.
  destruct (wcov w x) eqn:E; [apply wcov_spec in E; llia|]. apply IH. exact Hws.
Qed.

Lemma wfree_nil : forall x, wfree [] x.
Proof. intros x. constructor. Qed.

Lemma wfree_cons : forall w ws x, (x < f_a w \/ f_a w + f_n w <= x) -> wfree ws x -> wfree (w :: ws) x.
Proof. intros w ws x H1 H2. constructor; assumption. Qed.

(* [comment removed for export] *)
Definition wfree_range (ws : list fct) (a n : Z) : Prop :=
  Forall (fun w => a + n <= f_a w \/ f_a w + f_n w <= a) ws.

Lemma wfree_range_at : forall ws a n x, wfree_range ws a n -> a <= x < a + n -> wfree ws x.
Proof.
  intros ws a n x Hr Hx. unfold wfree, wfree_range in *. rewrite Forall_forall in *.
  intros w Hw. destruct (Hr w Hw); llia.
Qed.

Lemma wfree_range_nil : forall a n, wfree_range [] a n.
Proof. intros. constructor. Qed.

Lemma wfree_range_cons : forall w ws a n,
  (a + n <= f_a w \/ f_a w + f_n w <= a) -> wfree_range ws a n -> wfree_range (w :: ws) a n.
Proof. intros w ws a n H1 H2. constructor; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wzone (w : fct) : Prop :=
  f_a w + f_n w <= IMG_LO \/ IMG_HI <= f_a w \/
  (ERRNO <= f_a w /\ f_a w + f_n w <= ERRNO + 4) \/ (CTX <= f_a w /\ f_a w + f_n w <= CTX_END).

Record RepW (A : astate) (m0 : word -> option byte) (ws : list fct) (m : word -> option byte) : Prop := {
  rw_fact : forall x b, wlook ws x = None -> facts A x b -> mbyte m x = Some b;
  rw_wr : forall x b, wlook ws x = Some b -> mbyte m x = Some b;
  rw_dom : forall x, dom A x -> m (Z_to_bv 64 x) <> None;
  rw_range : forall w, In w ws -> 0 <= f_a w /\ 0 <= f_n w /\ f_a w + f_n w <= 2^64 /\ 0 <= f_v w;
  rw_frange : forall x b, facts A x b -> 0 <= x < 2^64;
  (* [comment removed for export] *)
  rw_frame : forall a : word, wfree ws (bv_unsigned a) -> m a = m0 a;
  (* [comment removed for export] *)
  rw_mapped : forall a : word, m0 a <> None -> m a <> None;
  rw_zone : forall w, In w ws -> wzone w
}.

Lemma repw_init : forall A m, WF A -> Rep A m -> RepW A m [] m.
Proof.
  intros A m HW HR. constructor.
  - intros x b _ Hf. apply (rep_facts A m HR). exact Hf.
  - intros x b H. discriminate.
  - apply (rep_dom A m HR).
  - intros w [].
  - exact (facts_addr64 A HW).
  - intros a _. reflexivity.
  - intros a H. exact H.
  - intros w [].
Qed.

Lemma wbytes_keeps : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 -> m x <> None -> wbytes m a bs x <> None.
Proof.
  intros bs m a x Hnw Hm.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hl|Hl].
  - rewrite wbytes_below; [exact Hm | llia | exact Hl].
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hi|Hi].
    + rewrite (wbytes_at_in bs m a x) by llia. discriminate.
    + rewrite wbytes_above; [exact Hm | exact Hi].
Qed.

Definition ws_ok (ws : list fct) : Prop :=
  forall w, In w ws -> 0 <= f_a w /\ 0 <= f_n w /\ f_a w + f_n w <= 2^64 /\ 0 <= f_v w.

Lemma wlook_some_range : forall ws x b, ws_ok ws -> wlook ws x = Some b -> 0 <= x < 2^64 /\ 0 <= b < 256.
Proof.
  induction ws as [|w ws IH]; intros x b Hok Hl; [discriminate|]. cbn in Hl.
  destruct (wcov w x) eqn:E.
  - apply wcov_spec in E. destruct (Hok w (or_introl eq_refl)) as (R1 & R2 & R3 & R4).
    injection Hl as <-. pose proof (byte_of_range (f_v w) (x - f_a w)). llia.
  - apply (IH x b); [| exact Hl]. intros w' Hw'. apply Hok. right. exact Hw'.
Qed.

Lemma wcov_false : forall w x, wcov w x = false -> x < f_a w \/ f_a w + f_n w <= x.
Proof.
  intros w x E. destruct (Z.lt_ge_cases x (f_a w)); [left; assumption|]. right.
  destruct (Z.lt_ge_cases x (f_a w + f_n w)); [| assumption].
  exfalso. assert (wcov w x = true) by (apply wcov_spec; llia). congruence.
Qed.

(* [comment removed for export] *)
Lemma repw_store : forall A m0 ws m a (n : nat) (v : word),
  RepW A m0 ws m -> 0 <= a < 2^64 -> a + Z.of_nat n <= 2^64 -> wzone (FCT a (Z.of_nat n) (bv_unsigned v)) ->
  RepW A m0 (FCT a (Z.of_nat n) (bv_unsigned v) :: ws) (wbytes m (Z_to_bv 64 a) (word_to_le_bytes n v)).
Proof.
  intros A m0 ws m a n v HR Ha Hnw Hz. pose proof (u64_range v) as Hv.
  constructor.
  - intros x b Hl Hf. cbn in Hl. destruct (wcov (FCT a (Z.of_nat n) (bv_unsigned v)) x) eqn:E; [discriminate|].
    pose proof (rw_frange A m0 ws m HR x b Hf). pose proof (wcov_false _ _ E) as Hx. cbn in Hx.
    rewrite mbyte_store_out by llia. apply (rw_fact A m0 ws m HR); assumption.
  - intros x b Hl. cbn in Hl. destruct (wcov (FCT a (Z.of_nat n) (bv_unsigned v)) x) eqn:E.
    + apply wcov_spec in E. cbn in E. injection Hl as <-. cbn.
      replace x with (a + (x - a)) at 1 by llia. apply mbyte_store_in; llia.
    + pose proof (wlook_some_range ws x b (rw_range A m0 ws m HR) Hl). pose proof (wcov_false _ _ E) as Hx. cbn in Hx.
      rewrite mbyte_store_out by llia. apply (rw_wr A m0 ws m HR). exact Hl.
  - intros x Hd. apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by llia; llia|]. apply (rw_dom A m0 ws m HR). exact Hd.
  - intros w [<- | Hw]; [cbn; llia|]. apply (rw_range A m0 ws m HR). exact Hw.
  - exact (rw_frange A m0 ws m HR).
  - intros x Hf. inversion Hf as [| w' ws' Hw Hws]; subst. cbn in Hw.
    pose proof (u64_range x).
    rewrite wbytes_other_Z by (rewrite ?length_N_to_le_bytes; llia).
    apply (rw_frame A m0 ws m HR). exact Hws.
  - intros x Hx. apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by llia; llia|]. apply (rw_mapped A m0 ws m HR). exact Hx.
  - intros w [<- | Hw]; [exact Hz|]. apply (rw_zone A m0 ws m HR). exact Hw.
Qed.

(* [comment removed for export] *)
Lemma repw_read_fact : forall A m0 ws m a (n : nat) v,
  RepW A m0 ws m -> has A (FCT a (Z.of_nat n) v) -> wfree_range ws a (Z.of_nat n) ->
  0 <= a -> a + Z.of_nat n <= 2^64 -> 0 <= v ->
  exists bs, rdn ml_segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
             bytes_le_to_Z bs = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros A m0 ws m a n v HR Hf Hfree Ha Hn Hv.
  destruct (rdn_of_mbytes m n a (fun k => byte_of v k) Ha Hn) as (bs & Hbs & Hlen & Hnth).
  { intros k Hk. apply (rw_fact A m0 ws m HR).
    - apply wlook_free. eapply wfree_range_at; [exact Hfree | llia].
    - exists (FCT a (Z.of_nat n) v). split; [exact Hf|]. unfold fbyte. cbn. split; [llia|]. f_equal. llia. }
  exists bs. split; [exact Hbs | split; [exact Hlen |]].
  rewrite <- Hlen. apply bytes_le_to_Z_of_bytes; [exact Hv |].
  intros k Hk. rewrite Hnth by llia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma repw_read_last : forall A m0 ws m a (n : nat) v,
  RepW A m0 (FCT a (Z.of_nat n) v :: ws) m ->
  exists bs, rdn ml_segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
             bytes_le_to_Z bs = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros A m0 ws m a n v HR.
  destruct (rw_range A m0 _ m HR (FCT a (Z.of_nat n) v) (or_introl eq_refl)) as (R1 & R2 & R3 & R4). cbn in R1, R2, R3, R4.
  destruct (rdn_of_mbytes m n a (fun k => byte_of v k) R1 R3) as (bs & Hbs & Hlen & Hnth).
  { intros k Hk. apply (rw_wr A m0 _ m HR). cbn.
    replace (wcov (FCT a (Z.of_nat n) v) (a + k)) with true by (symmetry; apply wcov_spec; cbn; llia).
    cbn. f_equal. f_equal. llia. }
  exists bs. split; [exact Hbs | split; [exact Hlen |]].
  rewrite <- Hlen. apply bytes_le_to_Z_of_bytes; [exact R4 |].
  intros k Hk. rewrite Hnth by llia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma repw_read_writes : forall A m0 ws m a (n : nat) v,
  RepW A m0 ws m -> 0 <= a -> a + Z.of_nat n <= 2^64 -> 0 <= v ->
  (forall k, 0 <= k < Z.of_nat n -> wlook ws (a + k) = Some (byte_of v k)) ->
  exists bs, rdn ml_segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
             bytes_le_to_Z bs = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros A m0 ws m a n v HR Ha Hn Hv Hl.
  destruct (rdn_of_mbytes m n a (fun k => byte_of v k) Ha Hn) as (bs & Hbs & Hlen & Hnth).
  { intros k Hk. apply (rw_wr A m0 ws m HR). apply Hl. exact Hk. }
  exists bs. split; [exact Hbs | split; [exact Hlen |]].
  rewrite <- Hlen. apply bytes_le_to_Z_of_bytes; [exact Hv |].
  intros k Hk. rewrite Hnth by llia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma repw_final : forall A A' m0 ws m,
  RepW A m0 ws m ->
  (forall x b, facts A' x b -> wlook ws x = Some b \/ (wlook ws x = None /\ facts A x b)) ->
  (forall x, dom A' x -> dom A x) ->
  Rep A' m.
Proof.
  intros A A' m0 ws m HR Hf Hd. constructor.
  - intros x b Hxb. destruct (Hf x b Hxb) as [Hw | [Hn Ho]].
    + apply (rw_wr A m0 ws m HR). exact Hw.
    + apply (rw_fact A m0 ws m HR); assumption.
  - intros x Hx. apply (rw_dom A m0 ws m HR). apply Hd. exact Hx.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wlook_hit : forall w ws x, f_a w <= x < f_a w + f_n w ->
  wlook (w :: ws) x = Some (byte_of (f_v w) (x - f_a w)).
Proof. intros w ws x Hx. cbn. replace (wcov w x) with true by (symmetry; apply wcov_spec; exact Hx). reflexivity. Qed.

Lemma wlook_skip : forall w ws x, (x < f_a w \/ f_a w + f_n w <= x) ->
  wlook (w :: ws) x = wlook ws x.
Proof.
  intros w ws x Hx. cbn. destruct (wcov w x) eqn:E; [| reflexivity]. apply wcov_spec in E. llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_domw : forall A m0 ws m x (n : nat),
  RepW A m0 ws m -> (forall k, 0 <= k < Z.of_nat n -> dom A (x + k)) ->
  0 <= x < 2^64 -> x + Z.of_nat n <= 2^64 ->
  store_ok ml_segs m (Z_to_bv 64 x) n = true.
Proof.
  intros A m0 ws m x n HR Hd Hx Hnw.
  apply store_ok_of_all; [rewrite u_lit by llia; llia|].
  intros y Hy. rewrite u_lit in Hy by llia. unfold wview.
  pose proof (rw_dom A m0 ws m HR (bv_unsigned y) ltac:(replace (bv_unsigned y) with (x + (bv_unsigned y - x)) by llia; apply Hd; llia)) as Hm.
  rewrite Z_to_bv_bv_unsigned in Hm. destruct (m y); [discriminate | exfalso; apply Hm; reflexivity].
Qed.

Section StepsW.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  (* [comment removed for export] *)
  Lemma ts_st_domw : forall s (m0 : word -> option byte) ws n a v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> (0 < n)%nat ->
    (forall j, 0 <= j < Z.of_nat n -> dom A (a + j)) ->
    tsafe (k tt (upd s (wbytes (ms_mem s) (Z_to_bv 64 a) (word_to_le_bytes n v)) (ms_vm s))) P ->
    tsafe ((x <- m_st n (Z_to_bv 64 a) v ;; k x) s) P.
  Proof.
    intros s m0 ws n a v k P HR HWn Hn Hd Hk.
    pose proof (dom_addr A HW a ltac:(replace a with (a + 0) by llia; apply Hd; llia)) as Ha.
    pose proof (dom_addr A HW (a + (Z.of_nat n - 1)) ltac:(apply Hd; llia)) as Hb.
    ceil.
    eapply ts_st.
    - apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia].
    - apply (st_zone_dom A); [exact HW | exact Hd | exact Hn].
    - eapply store_ok_domw; [exact HR | exact Hd | llia | llia].
    - exact Hk.
  Qed.

  Lemma repw_st_dom : forall s (m0 : word -> option byte) ws n a v,
    RepW A m0 ws (ms_mem s) -> (0 < n)%nat -> (forall j, 0 <= j < Z.of_nat n -> dom A (a + j)) ->
    RepW A m0 (FCT a (Z.of_nat n) (bv_unsigned v) :: ws) (wbytes (ms_mem s) (Z_to_bv 64 a) (word_to_le_bytes n v)).
  Proof.
    intros s m0 ws n a v HR Hn Hd.
    pose proof (dom_addr A HW a ltac:(replace a with (a + 0) by llia; apply Hd; llia)) as Ha.
    pose proof (dom_addr A HW (a + (Z.of_nat n - 1)) ltac:(apply Hd; llia)) as Hb.
    pose proof (st_zone_dom A a n HW Hd Hn) as Hz. apply (proj1 (st_zone_spec _ _)) in Hz.
    ceil. rewrite u_lit in Hz by llia.
    apply repw_store; [exact HR | llia | llia | unfold wzone; cbn; llia].
  Qed.

  (* [comment removed for export] *)
  Lemma ts_st_ctxw : forall s (m0 : word -> option byte) ws ck v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> cvalid ck ->
    tsafe (k tt (upd s (wbytes (ms_mem s) (Z_to_bv 64 (caddr ck)) (word_to_le_bytes (Z.to_nat (clen ck)) v)) (ms_vm s))) P ->
    tsafe ((x <- m_st (Z.to_nat (clen ck)) (Z_to_bv 64 (caddr ck)) v ;; k x) s) P.
  Proof.
    intros s m0 ws ck v k P HR HWn Hk Hc.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    eapply ts_st.
    - apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia].
    - apply st_zone_ctx; unfold LOCKA, CTX, CTX_END; llia.
    - apply store_ok_ctx; unfold LOCKA, CTX_END; llia.
    - exact Hc.
  Qed.

  Lemma repw_st_ctx : forall s (m0 : word -> option byte) ws ck v,
    RepW A m0 ws (ms_mem s) -> cvalid ck ->
    RepW A m0 (FCT (caddr ck) (clen ck) (bv_unsigned v) :: ws) (wbytes (ms_mem s) (Z_to_bv 64 (caddr ck)) (word_to_le_bytes (Z.to_nat (clen ck)) v)).
  Proof.
    intros s m0 ws ck v HR Hk. pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    rewrite <- (Z2Nat.id (clen ck)) at 1 by llia. apply repw_store; [exact HR | llia | llia | unfold wzone; cbn; llia].
  Qed.

  (* [comment removed for export] *)
  Lemma ts_ld_factw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> has A (FCT a 8 v) -> wfree_range ws a 8 -> 0 <= v ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Hf Hfree Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
    destruct (repw_read_fact A m0 ws (ms_mem s) a 8 v HR Hf Hfree ltac:(llia) ltac:(cbn; llia) Hv) as (bs & Hrd & Hl & Hval).
    eapply ts_ld; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs (v mod 2^64)); [rewrite ZZ_mod; exact Hk|]. rewrite Hval. reflexivity.
  Qed.

  Lemma ts_lw_factw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> has A (FCT a 4 v) -> wfree_range ws a 4 -> 0 <= v < 2^32 ->
    tsafe (k (w32 v) s) P ->
    tsafe ((x <- m_lw (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Hf Hfree Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
    destruct (repw_read_fact A m0 ws (ms_mem s) a 4 v HR Hf Hfree ltac:(llia) ltac:(cbn; llia) ltac:(llia)) as (bs & Hrd & Hl & Hval).
    eapply ts_lw; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs v); [rewrite v_lw_w32 by llia; exact Hk|]. rewrite Hval. apply Z.mod_small. change (2^(8*Z.of_nat 4)) with (2^32). llia.
  Qed.

  Lemma ts_lwu_factw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> has A (FCT a 4 v) -> wfree_range ws a 4 -> 0 <= v < 2^32 ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_lwu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Hf Hfree Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
    destruct (repw_read_fact A m0 ws (ms_mem s) a 4 v HR Hf Hfree ltac:(llia) ltac:(cbn; llia) ltac:(llia)) as (bs & Hrd & Hl & Hval).
    eapply ts_lwu; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs v); [exact Hk|]. rewrite Hval. apply Z.mod_small. change (2^(8*Z.of_nat 4)) with (2^32). llia.
  Qed.

  Lemma ts_lhu_factw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> has A (FCT a 2 v) -> wfree_range ws a 2 -> 0 <= v < 2^16 ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_lhu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Hf Hfree Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
    destruct (repw_read_fact A m0 ws (ms_mem s) a 2 v HR Hf Hfree ltac:(llia) ltac:(cbn; llia) ltac:(llia)) as (bs & Hrd & Hl & Hval).
    eapply ts_lhu; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs v); [exact Hk|]. rewrite Hval. apply Z.mod_small. change (2^(8*Z.of_nat 2)) with (2^16). llia.
  Qed.

  Lemma ts_lbu_factw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> has A (FCT a 1 v) -> wfree_range ws a 1 -> 0 <= v < 256 ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Hf Hfree Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
    destruct (repw_read_fact A m0 ws (ms_mem s) a 1 v HR Hf Hfree ltac:(llia) ltac:(cbn; llia) ltac:(llia)) as (bs & Hrd & Hl & Hval).
    destruct bs as [|b [|]]; try (cbn in Hl; llia).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite bytes_le_single in Hval. rewrite Hval. rewrite Z.mod_small by (change (2^(8*Z.of_nat 1)) with 256; llia). exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_ld_wrw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> 0 <= a -> a + 8 <= alloc_ceiling -> 0 <= v ->
    (forall j, 0 <= j < 8 -> wlook ws (a + j) = Some (byte_of v j)) ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Ha Hc Hv Hl Hk. ceil.
    destruct (repw_read_writes A m0 ws (ms_mem s) a 8 v HR Ha ltac:(cbn; llia) Hv Hl) as (bs & Hrd & Hlen & Hval).
    eapply ts_ld; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs (v mod 2^64)); [rewrite ZZ_mod; exact Hk|]. rewrite Hval. reflexivity.
  Qed.

  Lemma ts_lw_wrw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> 0 <= a -> a + 4 <= alloc_ceiling -> 0 <= v ->
    (forall j, 0 <= j < 4 -> wlook ws (a + j) = Some (byte_of v j)) ->
    tsafe (k (w32 v) s) P ->
    tsafe ((x <- m_lw (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Ha Hc Hv Hl Hk. ceil.
    destruct (repw_read_writes A m0 ws (ms_mem s) a 4 v HR Ha ltac:(cbn; llia) Hv Hl) as (bs & Hrd & Hlen & Hval).
    eapply ts_lw; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs (v mod 2^32)); [| rewrite Hval; reflexivity].
    rewrite v_lw_w32 by (pose proof (Z.mod_pos_bound v (2^32)); llia). rewrite w32_mod. exact Hk.
  Qed.

  Lemma ts_lbu_wrw : forall s (m0 : word -> option byte) ws a v (k : word -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> 0 <= a -> a + 1 <= alloc_ceiling -> 0 <= v ->
    wlook ws a = Some (byte_of v 0) ->
    tsafe (k (Z_to_bv 64 (v mod 256)) s) P ->
    tsafe ((x <- m_lbu (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros s m0 ws a v k P HR HWn Ha Hc Hv Hl Hk. ceil.
    destruct (repw_read_writes A m0 ws (ms_mem s) a 1 v HR Ha ltac:(cbn; llia) Hv) as (bs & Hrd & Hlen & Hval).
    { intros j Hj. replace j with 0 by llia. rewrite Z.add_0_r. exact Hl. }
    destruct bs as [|b [|]]; try (cbn in Hlen; llia).
    eapply ts_lbu; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; cbn; llia] | exact Hrd |].
    rewrite bytes_le_single in Hval. rewrite Hval. change (2^(8*Z.of_nat 1)) with 256. exact Hk.
  Qed.
End StepsW.

End WithLayout.
