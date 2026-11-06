(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import
  ShapeAlgBase ShapeCfg NodesCfg LedgerCfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma width_bytes_le8 : forall n : N, (width_bytes n <= 8)%nat.
Proof.
  intros [| p]; [cbn; lia |].
  do 7 (destruct p as [p | p |]; try (cbn; lia)).
Qed.

(* [comment removed for export] *)
Inductive acc_at (a : word) : eff -> Prop :=
| aa_done : forall c, acc_at a (EDone c)
| aa_illegal : forall c, acc_at a (EIllegal c)
| aa_defined_illegal : forall c, acc_at a (EDefinedIllegal c)
| aa_ecall : forall c, acc_at a (EEcall c)
| aa_ebreak : forall c, acc_at a (EEbreak c)
| aa_fault : forall c, acc_at a (EFault c)
| aa_load : forall n k, (forall v, acc_at a (k v)) -> acc_at a (ELoad n a k)
| aa_store : forall n v k, acc_at a k -> acc_at a (EStore n a v k).

Ltac acc_at_tac :=
  repeat first
    [ apply aa_done | apply aa_illegal | apply aa_defined_illegal | apply aa_ecall
    | apply aa_ebreak | apply aa_fault
    | apply aa_load; intros ?
    | apply aa_store
    | match goal with
      | |- acc_at _ (if ?x then _ else _) => destruct x
      | |- acc_at _ (match ?x with _ => _ end) => destruct x
      | |- acc_at _ ((match ?x with _ => _ end) _) => destruct x
      | |- acc_at _ (?f (match ?x with _ => _ end)) => destruct x
      | |- acc_at _ (?f (match ?x with _ => _ end) _) => destruct x
      end ].

(* [comment removed for export] *)
Definition exec_addr (i : instr) (c : core) : word :=
  match i with
  | Load _ _ _ rs1 imm | FLoad _ _ rs1 imm => bv_add (rget c rs1) (sext 64 imm)
  | Store _ rs1 _ imm | FStore _ rs1 _ imm => bv_add (rget c rs1) (sext 64 imm)
  | Lr _ _ _ _ rs1 | Sc _ _ _ _ rs1 _ => rget c rs1
  | Amo _ _ _ _ _ rs1 _ => rget c rs1
  | _ => w0
  end.

Theorem exec_acc_at_addr : forall sz i c, acc_at (exec_addr i c) (exec sz i c).
Proof.
  intros sz i c.
  destruct i; cbn [exec exec_addr]; unfold load_val, store_val, exec_csr; cbv zeta; acc_at_tac.
Qed.

Theorem exec_acc_at : forall sz i c, exists a, acc_at a (exec sz i c).
Proof. intros sz i c. exists (exec_addr i c). apply exec_acc_at_addr. Qed.

(* [comment removed for export] *)
Definition lz_core (ms : machine_state) : core :=
  {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms;
     c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |}.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_acc_at : forall a t, acc_at a t -> forall m report,
  interp_eff_accesses segs t m = MachineOk report ->
  Forall (fun r : word * nat => fst r = a /\ (snd r <= 8)%nat) (@accessed_ranges _ report).
Proof.
  intros a t Ht. induction Ht as [c | c | c | c | c | c | n k Hk IH | n v k Hk IH];
    intros m report H; cbn [interp_eff_accesses] in H; try discriminate H.
  - inversion H; subst. constructor.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs |]; [| discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [accessed_ranges]. constructor.
    + split; [reflexivity | apply width_bytes_le8].
    + exact (IH _ m r0 E).
  - destruct (store_ok segs m a (width_bytes n)); [| discriminate H].
    destruct (interp_eff_accesses segs k
                (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [accessed_ranges]. constructor.
    + split; [reflexivity | apply width_bytes_le8].
    + exact (IH _ r0 E).
Qed.

Lemma decode_exec_accesses_addr : forall ms w i isz report,
  is_ecall w = false -> decode_any w = Some (i, isz) ->
  decode_exec_accesses segs ms w = MachineOk report ->
  Forall (fun r : word * nat => fst r = exec_addr i (lz_core ms) /\ (snd r <= 8)%nat)
         (@accessed_ranges _ report).
Proof.
  intros ms w i isz report He Hd H. unfold decode_exec_accesses in H. rewrite He, Hd in H.
  fold (lz_core ms) in H.
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 isz) i (lz_core ms)) (ms_mem ms))
    as [r0 | |] eqn:E; try discriminate H.
  pose proof (interp_acc_at _ _ (exec_acc_at_addr (Z_to_bv 64 isz) i (lz_core ms)) _ _ E) as HF.
  destruct (@access_value _ r0) as [c m']. inversion H; subst. cbn [accessed_ranges]. exact HF.
Qed.

(* [comment removed for export] *)
Theorem step_accesses_addr : forall ms w i isz report,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, isz) ->
  step_accesses segs ms = MachineOk report ->
  Forall (fun r : word * nat => fst r = exec_addr i (lz_core ms) /\ (snd r <= 8)%nat)
         (@accessed_ranges _ report).
Proof.
  intros ms w i isz report Hf He Hd H. unfold step_accesses in H. rewrite Hf in H.
  exact (decode_exec_accesses_addr ms w i isz report He Hd H).
Qed.

Lemma decode_exec_accesses_at : forall ms w report,
  decode_exec_accesses segs ms w = MachineOk report ->
  exists a, Forall (fun r : word * nat => fst r = a /\ (snd r <= 8)%nat) (@accessed_ranges _ report).
Proof.
  intros ms w report H. unfold decode_exec_accesses in H.
  destruct (is_ecall w).
  { inversion H; subst. exists w0. constructor. }
  destruct (decode_any w) as [[i isz] |]; [| destruct (is_defined_illegal w); discriminate H].
  match type of H with
  | match interp_eff_accesses segs ?t ?m with _ => _ end = _ =>
      destruct (interp_eff_accesses segs t m) as [r0 | |] eqn:E; try discriminate H;
      destruct (exec_acc_at (Z_to_bv 64 isz) i
                  {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms;
                     c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |}) as [a Ha];
      pose proof (interp_acc_at a _ Ha _ _ E) as HF
  end.
  destruct (@access_value _ r0) as [c m']. inversion H; subst. cbn [accessed_ranges].
  exists a. exact HF.
Qed.

(* [comment removed for export] *)
Theorem step_accesses_at : forall ms report,
  step_accesses segs ms = MachineOk report ->
  exists a, Forall (fun r : word * nat => fst r = a /\ (snd r <= 8)%nat) (@accessed_ranges _ report).
Proof.
  intros ms report H. unfold step_accesses in H.
  destruct (fetch_word segs (ms_pc ms)) as [w |]; [exact (decode_exec_accesses_at ms w report H) |].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w |];
    [exact (decode_exec_accesses_at ms w report H) |].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w |];
    [exact (decode_exec_accesses_at ms w report H) |].
  destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) as [st' | |]; try discriminate H.
  inversion H; subst. exists w0. constructor.
Qed.

End WithSegs.

(* [comment removed for export] *)

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> In p pages.
Proof.
  intros p pages. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hq & E). unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst q. exact Hq.
  - intros H. exists p. split; [exact H |]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma page_insert_spec : forall p pages,
  List.NoDup pages ->
  List.NoDup (page_insert p pages) /\ (forall q, In q (page_insert p pages) <-> q = p \/ In q pages).
Proof.
  intros p pages Hnd. unfold page_insert. destruct (page_mem p pages) eqn:E.
  - apply page_mem_In in E. split; [exact Hnd |]. intros q. split; [tauto |].
    intros [-> | H]; assumption.
  - assert (Hn : ~ In p pages) by (intros H; apply page_mem_In in H; congruence).
    split; [constructor; assumption |]. intros q. cbn [In]. split; intros [H | H]; auto.
Qed.

Lemma access_pages_acc_spec : forall n base pages,
  List.NoDup pages ->
  List.NoDup (access_pages_acc base n pages)
  /\ (forall q, In q (access_pages_acc base n pages) ->
        In q pages \/ exists i, 0 <= i < Z.of_nat n /\ q = page_base_of (base + i)).
Proof.
  induction n as [| n IH]; intros base pages Hnd; cbn [access_pages_acc].
  - split; [exact Hnd | intros q H; left; exact H].
  - destruct (page_insert_spec (page_base_of base) pages Hnd) as [Hnd1 Hin1].
    destruct (IH (base + 1) _ Hnd1) as [Hnd2 Hin2]. split; [exact Hnd2 |].
    intros q Hq. destruct (Hin2 q Hq) as [H | (i & Hi & ->)].
    + apply Hin1 in H as [-> | H]; [| left; exact H].
      right. exists 0. split; [lia |]. rewrite Z.add_0_r. reflexivity.
    + right. exists (i + 1). split; [lia |]. f_equal. lia.
Qed.

Lemma accesses_pages_spec : forall l pages,
  List.NoDup pages ->
  List.NoDup (accesses_pages l pages)
  /\ (forall q, In q (accesses_pages l pages) ->
        In q pages \/ exists r i, In r l /\ 0 <= i < Z.of_nat (snd r)
                                  /\ q = page_base_of (bv_unsigned (fst r) + i)).
Proof.
  induction l as [| [a n] l IH]; intros pages Hnd; cbn [accesses_pages].
  - split; [exact Hnd | intros q H; left; exact H].
  - destruct (access_pages_acc_spec n (bv_unsigned a) pages Hnd) as [Hnd1 Hin1].
    destruct (IH _ Hnd1) as [Hnd2 Hin2]. split; [exact Hnd2 |].
    intros q Hq. destruct (Hin2 q Hq) as [H | (r & i & Hr & Hi & ->)].
    + destruct (Hin1 q H) as [H' | (i & Hi & ->)]; [left; exact H' |].
      right. exists (a, n), i. cbn [fst snd In]. auto.
    + right. exists r, i. cbn [In]. auto.
Qed.

(* [comment removed for export] *)
Lemma page_base_of_near : forall A i, 0 <= i < 8 ->
  page_base_of (A + i) = page_base_of A \/ page_base_of (A + i) = page_base_of (A + 4096).
Proof.
  intros A i Hi. unfold page_base_of, page_size.
  assert (E : (A + i) / 4096 = A / 4096 \/ (A + i) / 4096 = (A + 4096) / 4096).
  { clear - Hi. Z.div_mod_to_equations. lia. }
  destruct E as [-> | ->]; [left | right]; reflexivity.
Qed.

Theorem accesses_pages_le2 : forall a (l : list (word * nat)),
  Forall (fun r => fst r = a /\ (snd r <= 8)%nat) l ->
  (length (accesses_pages l []) <= 2)%nat.
Proof.
  intros a l HF.
  destruct (accesses_pages_spec l [] (List.NoDup_nil _)) as [Hnd Hin].
  change 2%nat with (length [page_base_of (bv_unsigned a); page_base_of (bv_unsigned a + 4096)]).
  apply List.NoDup_incl_length; [exact Hnd |].
  intros q Hq. destruct (Hin q Hq) as [[] | (r & i & Hr & Hi & ->)].
  rewrite Forall_forall in HF. destruct (HF r Hr) as [-> Hw].
  destruct (page_base_of_near (bv_unsigned a) i ltac:(lia)) as [-> | ->]; cbn [In]; auto.
Qed.

Lemma filter_length_le' {A} (f : A -> bool) : forall l, (length (List.filter f l) <= length l)%nat.
Proof. induction l as [| x l IH]; cbn [List.filter length]; [lia |]. destruct (f x); cbn [length]; lia. Qed.

Theorem newly_le2 : forall lazy mat a (l : list (word * nat)),
  Forall (fun r => fst r = a /\ (snd r <= 8)%nat) l ->
  (length (newly_materialized_pages lazy mat l) <= 2)%nat.
Proof.
  intros lazy mat a l HF. unfold newly_materialized_pages.
  pose proof (filter_length_le' (fun p => page_in_ranges p lazy && negb (page_mem p mat))
                (accesses_pages l [])) as H1.
  pose proof (accesses_pages_le2 a l HF) as H2. lia.
Qed.

(* [comment removed for export] *)
Definition bytes_outside_lazy (lazy : list (word * word)) (l : list (word * nat)) : Prop :=
  forall r i, In r l -> 0 <= i < Z.of_nat (snd r) ->
    bv_unsigned (fst r) + i < 2 ^ 64
    /\ forall z, In z lazy -> ~ (e_lo z <= bv_unsigned (fst r) + i < e_hi z).

Lemma page_in_ranges_byte : forall p lazy,
  page_in_ranges p lazy = true ->
  exists z, In z lazy /\ e_lo z <= bv_unsigned p /\ bv_unsigned p + page_size <= e_hi z.
Proof.
  intros p lazy H. unfold page_in_ranges in H. apply existsb_exists in H as (z & Hz & E).
  cbv zeta in E. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2.
  exists z. split; [exact Hz |]. unfold e_hi, e_sz, e_lo. lia.
Qed.

Theorem newly_nil_outside : forall lazy mat l,
  bytes_outside_lazy lazy l -> newly_materialized_pages lazy mat l = [].
Proof.
  intros lazy mat l Hout. unfold newly_materialized_pages.
  destruct (accesses_pages_spec l [] (List.NoDup_nil _)) as [_ Hin].
  assert (Hall : forall q, In q (accesses_pages l []) -> page_in_ranges q lazy = false).
  { intros q Hq. destruct (Hin q Hq) as [[] | (r & i & Hr & Hi & ->)].
    destruct (Hout r i Hr Hi) as [Hlt Hno].
    destruct (page_in_ranges (page_base_of (bv_unsigned (fst r) + i)) lazy) eqn:E; [| reflexivity].
    exfalso. apply page_in_ranges_byte in E as (z & Hz & H1 & H2).
    apply (Hno z Hz). pose proof (u64_range (fst r)) as Ha.
    unfold page_base_of, page_size in H1, H2.
    set (B := bv_unsigned (fst r) + i) in *.
    assert (HB : 0 <= B / 4096 * 4096 <= B /\ B < B / 4096 * 4096 + 4096)
      by (clear - Ha Hi; subst B; Z.div_mod_to_equations; lia).
    rewrite u64_lit in H1, H2 by lia. lia. }
  clear Hin. induction (accesses_pages l []) as [| q qs IH]; [reflexivity |].
  cbn [List.filter]. rewrite (Hall q (or_introl eq_refl)). cbn [andb].
  apply IH. intros q' Hq'. apply Hall. right. exact Hq'.
Qed.

(* [comment removed for export] *)

Definition lazy_inv (U : Z) (m : Model) : Prop := vm_backing_used m <= U.

(* [comment removed for export] *)
Definition lazy_frame (m m' : Model) : Prop :=
  exists mat', m' = with_vm_backing (m_vm_lazy m) mat' m.

Lemma with_vm_backing_self : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma lazy_frame_refl : forall m, lazy_frame m m.
Proof. intros m. exists (m_vm_materialized m). symmetry. apply with_vm_backing_self. Qed.

Lemma lazy_frame_trans : forall m1 m2 m3, lazy_frame m1 m2 -> lazy_frame m2 m3 -> lazy_frame m1 m3.
Proof. intros m1 m2 m3 [a ->] [b ->]. exists b. reflexivity. Qed.

Lemma lazy_frame_facts : forall m m', lazy_frame m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m /\ m_lim m' = m_lim m
  /\ m_halted m' = m_halted m /\ m_creds m' = m_creds m.
Proof. intros m m' [mat' ->]. repeat split; reflexivity. Qed.

Lemma vm_backing_used_with_backing : forall mat' m,
  vm_backing_used (with_vm_backing (m_vm_lazy m) mat' m)
  = vm_backing_used m - Z.of_nat (length (m_vm_materialized m)) * page_size
    + Z.of_nat (length mat') * page_size.
Proof.
  intros mat' m. unfold vm_backing_used.
  change (m_vmmaps (with_vm_backing (m_vm_lazy m) mat' m)) with (m_vmmaps m).
  change (m_vm_lazy (with_vm_backing (m_vm_lazy m) mat' m)) with (m_vm_lazy m).
  change (m_vm_materialized (with_vm_backing (m_vm_lazy m) mat' m)) with mat'.
  lia.
Qed.

(* [comment removed for export] *)
Theorem materialize_exact : forall m l,
  let new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) l in
  vm_backing_used m + Z.of_nat (length new) * page_size <= vm_limit (m_vmmaps m) ->
  materialize_model_accesses m l
  = Some (with_vm_backing (m_vm_lazy m) (new ++ m_vm_materialized m) m).
Proof.
  intros m l new Hfit. unfold materialize_model_accesses, materialize_accesses. fold new.
  destruct new as [| p ps] eqn:En; [reflexivity |].
  apply Z.leb_le in Hfit. rewrite Hfit. reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m = eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
  existsb (fun iv => (fst iv <=? bv_unsigned p) && (bv_unsigned p + page_size <=? snd iv)) A.

Definition A_bytes (A : list (Z * Z)) : Z :=
  fold_right (fun iv acc => Z.max 0 (snd iv - fst iv) + acc) 0 A.

Lemma A_bytes_nonneg : forall A, 0 <= A_bytes A.
Proof. induction A as [| iv A IH]; cbn [A_bytes fold_right]; [lia |]. fold (A_bytes A). lia. Qed.

Definition page_aligned (p : word) : Prop := bv_unsigned p mod page_size = 0.

Lemma page_base_of_aligned : forall z, page_aligned (page_base_of z).
Proof.
  intros z. unfold page_aligned, page_base_of, page_size. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod_divide by (exists (2 ^ 52); reflexivity). apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma pages_in_interval_count : forall (pages : list word) lo hi,
  List.NoDup pages -> Forall page_aligned pages ->
  Forall (fun p => lo <= bv_unsigned p /\ bv_unsigned p + page_size <= hi) pages ->
  Z.of_nat (length pages) * page_size <= Z.max 0 (hi - lo).
Proof.
  intros pages lo hi Hnd Hal Hin. unfold page_aligned in *. unfold page_size in *.
  set (ks := map (fun p : word => bv_unsigned p / 4096) pages).
  assert (Hndk : List.NoDup ks).
  { unfold ks. clear Hin. induction pages as [| p ps IH]; cbn [map]; [constructor |].
    inversion Hnd as [| ? ? Hnp Hnd']; subst. inversion Hal as [| ? ? Hp Hal']; subst.
    constructor; [| exact (IH Hnd' Hal')].
    intros Hk. apply in_map_iff in Hk as (q & Eq & Hq). apply Hnp.
    rewrite Forall_forall in Hal'. pose proof (Hal' q Hq) as Hqa. cbv beta in Hqa.
    assert (E : bv_unsigned q = bv_unsigned p).
    { cbv beta in Hp. clear - Eq Hp Hqa. Z.div_mod_to_equations. lia. }
    apply bv_eq in E. subst q. exact Hq. }
  assert (Hr : forall k, In k ks -> (lo + 4095) / 4096 <= k <= hi / 4096 - 1).
  { intros k Hk. unfold ks in Hk. apply in_map_iff in Hk as (q & <- & Hq).
    rewrite Forall_forall in Hal, Hin. pose proof (Hal q Hq) as Ha. destruct (Hin q Hq) as [H1 H2].
    cbv beta in Ha. clear - Ha H1 H2. Z.div_mod_to_equations. lia. }
  pose proof (NoDup_interval_length ks _ _ Hndk Hr) as Hlen.
  unfold ks in Hlen. rewrite length_map in Hlen.
  clear - Hlen. Z.div_mod_to_equations. lia.
Qed.

Lemma filter_split_length {X} (f : X -> bool) : forall l,
  length l = (length (List.filter f l) + length (List.filter (fun x => negb (f x)) l))%nat.
Proof.
  induction l as [| x l IH]; cbn [List.filter length]; [reflexivity |].
  destruct (f x); cbn [negb length]; lia.
Qed.

(* [comment removed for export] *)
Theorem allowed_pages_count : forall A (pages : list word),
  List.NoDup pages -> Forall page_aligned pages ->
  Forall (fun p => page_allowedb A p = true) pages ->
  Z.of_nat (length pages) * page_size <= A_bytes A.
Proof.
  induction A as [| [lo hi] A IH]; intros pages Hnd Hal Hall.
  - destruct pages as [| p ps]; [cbn; lia |]. inversion Hall as [| ? ? Hp _]; subst. discriminate Hp.
  - set (f := fun p : word => (lo <=? bv_unsigned p) && (bv_unsigned p + page_size <=? hi)).
    rewrite (filter_split_length f pages), Nat2Z.inj_add, Z.mul_add_distr_r.
    cbn [A_bytes fold_right fst snd]. fold (A_bytes A).
    assert (H1 : Z.of_nat (length (List.filter f pages)) * page_size <= Z.max 0 (hi - lo)).
    { apply pages_in_interval_count.
      - apply List.NoDup_filter. exact Hnd.
      - rewrite Forall_forall in *. intros p Hp. apply List.filter_In in Hp as [Hp _]. exact (Hal p Hp).
      - rewrite Forall_forall. intros p Hp. apply List.filter_In in Hp as [_ Hp]. unfold f in Hp.
        apply andb_true_iff in Hp as [E1 E2]. apply Z.leb_le in E1, E2. split; assumption. }
    assert (H2 : Z.of_nat (length (List.filter (fun x => negb (f x)) pages)) * page_size <= A_bytes A).
    { apply IH.
      - apply List.NoDup_filter. exact Hnd.
      - rewrite Forall_forall in *. intros p Hp. apply List.filter_In in Hp as [Hp _]. exact (Hal p Hp).
      - rewrite Forall_forall in *. intros p Hp. apply List.filter_In in Hp as [Hp Hf].
        pose proof (Hall p Hp) as Ha. cbn [page_allowedb existsb fst snd] in Ha.
        fold (page_allowedb A p) in Ha. fold (f p) in Ha.
        apply negb_true_iff in Hf. rewrite Hf in Ha. exact Ha. }
    lia.
Qed.

(* [comment removed for export] *)
Record page_inv (A : list (Z * Z)) (m : Model) : Prop := mk_page_inv {
  pi_nodup   : List.NoDup (m_vm_materialized m);
  pi_aligned : Forall page_aligned (m_vm_materialized m);
  pi_allowed : Forall (fun p => page_allowedb A p = true) (m_vm_materialized m);
  pi_budget  : eager_used m + A_bytes A <= vm_limit (m_vmmaps m)
}.

Lemma page_inv_lazy_inv : forall A m, page_inv A m -> lazy_inv (eager_used m + A_bytes A) m.
Proof.
  intros A m [Hnd Hal Hall Hb]. unfold lazy_inv. rewrite vm_backing_used_split.
  pose proof (allowed_pages_count A _ Hnd Hal Hall). lia.
Qed.

(* [comment removed for export] *)
Definition touch_allowed (lazy : list (word * word)) (A : list (Z * Z)) (l : list (word * nat)) : Prop :=
  forall p, In p (accesses_pages l []) -> page_in_ranges p lazy = true -> page_allowedb A p = true.

(* [comment removed for export] *)
Lemma touch_allowed_of_addr : forall lazy A a (l : list (word * nat)),
  Forall (fun r => fst r = a /\ (snd r <= 8)%nat) l ->
  (page_in_ranges (page_base_of (bv_unsigned a)) lazy = true ->
   page_allowedb A (page_base_of (bv_unsigned a)) = true) ->
  (page_in_ranges (page_base_of (bv_unsigned a + 4096)) lazy = true ->
   page_allowedb A (page_base_of (bv_unsigned a + 4096)) = true) ->
  touch_allowed lazy A l.
Proof.
  intros lazy A a l HF H1 H2 p Hp Hlz.
  destruct (accesses_pages_spec l [] (List.NoDup_nil _)) as [_ Hin].
  destruct (Hin p Hp) as [[] | (r & i & Hr & Hi & ->)].
  rewrite Forall_forall in HF. destruct (HF r Hr) as [Ea Hw]. rewrite Ea in *.
  destruct (page_base_of_near (bv_unsigned a) i ltac:(lia)) as [E | E]; rewrite E in *; auto.
Qed.

Lemma lazy_inv_weaken : forall U U' m, lazy_inv U m -> U <= U' -> lazy_inv U' m.
Proof. unfold lazy_inv. intros. lia. Qed.

Theorem materialize_pages : forall A m l,
  page_inv A m -> touch_allowed (m_vm_lazy m) A l ->
  exists m', materialize_model_accesses m l = Some m' /\ lazy_frame m m' /\ page_inv A m'.
Proof.
  intros A m l Hinv Htouch. pose proof Hinv as [Hnd Hal Hall Hb].
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) l).
  destruct (accesses_pages_spec l [] (List.NoDup_nil _)) as [Hndp Hinp].
  assert (Hnew : forall p, In p new ->
            In p (accesses_pages l []) /\ page_in_ranges p (m_vm_lazy m) = true
            /\ ~ In p (m_vm_materialized m)).
  { intros p Hp. unfold new, newly_materialized_pages in Hp. apply List.filter_In in Hp as [Hp E].
    apply andb_true_iff in E as [E1 E2]. split; [exact Hp |]. split; [exact E1 |].
    intros Hc. apply page_mem_In in Hc. rewrite Hc in E2. discriminate E2. }
  assert (Hnd' : List.NoDup (new ++ m_vm_materialized m)).
  { apply List.NoDup_app.
    - unfold new, newly_materialized_pages. apply List.NoDup_filter. exact Hndp.
    - exact Hnd.
    - intros p Hp. exact (proj2 (proj2 (Hnew p Hp))). }
  assert (Hal' : Forall page_aligned (new ++ m_vm_materialized m)).
  { apply Forall_app. split; [| exact Hal]. rewrite Forall_forall. intros p Hp.
    destruct (Hnew p Hp) as (Hacc & _ & _).
    destruct (Hinp p Hacc) as [[] | (r & i & _ & _ & ->)]. apply page_base_of_aligned. }
  assert (Hall' : Forall (fun p => page_allowedb A p = true) (new ++ m_vm_materialized m)).
  { apply Forall_app. split; [| exact Hall]. rewrite Forall_forall. intros p Hp.
    destruct (Hnew p Hp) as (Hacc & Hlz & _). exact (Htouch p Hacc Hlz). }
  pose proof (allowed_pages_count A _ Hnd' Hal' Hall') as Hcount.
  rewrite length_app, Nat2Z.inj_add in Hcount.
  assert (Hfit : vm_backing_used m + Z.of_nat (length new) * page_size <= vm_limit (m_vmmaps m))
    by (rewrite vm_backing_used_split; lia).
  exists (with_vm_backing (m_vm_lazy m) (new ++ m_vm_materialized m) m).
  split; [exact (materialize_exact m l Hfit) |].
  split; [exists (new ++ m_vm_materialized m); reflexivity |].
  constructor; [exact Hnd' | exact Hal' | exact Hall' | exact Hb].
Qed.

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Theorem mi_account_step_exact : forall ms m report,
  step_accesses segs ms = MachineOk report ->
  let new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) (@accessed_ranges _ report) in
  vm_backing_used m + Z.of_nat (length new) * page_size <= vm_limit (m_vmmaps m) ->
  mi_account_step segs ms m
  = MachineOk (@access_value _ report, with_vm_backing (m_vm_lazy m) (new ++ m_vm_materialized m) m).
Proof.
  intros ms m report Hs new Hfit. unfold mi_account_step. rewrite Hs.
  rewrite (materialize_exact m (@accessed_ranges _ report) Hfit). reflexivity.
Qed.

Lemma step_report : forall ms ms',
  RiscvSemantics.step segs ms = MachineOk ms' ->
  exists report, step_accesses segs ms = MachineOk report /\ @access_value _ report = ms'.
Proof.
  intros ms ms' H. unfold RiscvSemantics.step, drop_access_report in H.
  destruct (step_accesses segs ms) as [report | |]; try discriminate H.
  exists report. split; [reflexivity |]. inversion H. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem mi_account_step_lazy : forall ms ms' m U,
  RiscvSemantics.step segs ms = MachineOk ms' ->
  lazy_inv U m ->
  U + 2 * page_size <= vm_limit (m_vmmaps m) ->
  exists m', mi_account_step segs ms m = MachineOk (ms', m')
             /\ lazy_frame m m' /\ lazy_inv (U + 2 * page_size) m'.
Proof.
  intros ms ms' m U Hstep Hinv Hfit.
  destruct (step_report ms ms' Hstep) as (report & Hs & <-).
  destruct (step_accesses_at segs ms report Hs) as (a & HF).
  pose proof (newly_le2 (m_vm_lazy m) (m_vm_materialized m) a _ HF) as H2.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) (@accessed_ranges _ report)) in *.
  unfold lazy_inv in *. unfold page_size in *.
  assert (Hfit' : vm_backing_used m + Z.of_nat (length new) * State.page_size <= vm_limit (m_vmmaps m))
    by (unfold State.page_size; lia).
  exists (with_vm_backing (m_vm_lazy m) (new ++ m_vm_materialized m) m).
  split; [exact (mi_account_step_exact ms m report Hs Hfit') |].
  split; [exists (new ++ m_vm_materialized m); reflexivity |].
  rewrite vm_backing_used_with_backing, length_app, Nat2Z.inj_add. unfold State.page_size. lia.
Qed.

(* [comment removed for export] *)
Theorem mi_account_step_free : forall ms ms' m,
  RiscvSemantics.step segs ms = MachineOk ms' ->
  (forall report, step_accesses segs ms = MachineOk report ->
                  bytes_outside_lazy (m_vm_lazy m) (@accessed_ranges _ report)) ->
  mi_account_step segs ms m = MachineOk (ms', m).
Proof.
  intros ms ms' m Hstep Hout.
  destruct (step_report ms ms' Hstep) as (report & Hs & <-).
  pose proof (newly_nil_outside (m_vm_lazy m) (m_vm_materialized m) _ (Hout report Hs)) as Hnil.
  unfold mi_account_step. rewrite Hs.
  unfold materialize_model_accesses, materialize_accesses. rewrite Hnil.
  rewrite with_vm_backing_self. reflexivity.
Qed.

(* [comment removed for export] *)

Theorem asteps_lazy : forall k ms ms' m U,
  rsteps segs k ms = MachineOk ms' ->
  lazy_inv U m ->
  U + Z.of_nat k * (2 * page_size) <= vm_limit (m_vmmaps m) ->
  exists m', asteps segs k (ms, m) = MachineOk (ms', m')
             /\ lazy_frame m m' /\ lazy_inv (U + Z.of_nat k * (2 * page_size)) m'.
Proof.
  induction k as [| k IH]; intros ms ms' m U Hr Hinv Hfit.
  - cbn [rsteps] in Hr. inversion Hr; subst. exists m. cbn [asteps].
    split; [reflexivity |]. split; [apply lazy_frame_refl |].
    unfold lazy_inv in *. change (Z.of_nat 0) with 0. lia.
  - cbn [rsteps] in Hr. cbn [asteps fst snd].
    assert (Hpos : 0 <= 2 * page_size) by (unfold page_size; lia).
    destruct (ms_svc_pending ms) as [x8 |].
    + inversion Hr; subst. exists m. split; [reflexivity |]. split; [apply lazy_frame_refl |].
      unfold lazy_inv in *. lia.
    + destruct (RiscvSemantics.step segs ms) as [ms1 | |] eqn:Hs; try discriminate Hr.
      rewrite Nat2Z.inj_succ in *.
      destruct (mi_account_step_lazy ms ms1 m U Hs Hinv ltac:(lia)) as (m1 & Ha & Hf1 & Hi1).
      rewrite Ha.
      destruct (lazy_frame_facts m m1 Hf1) as (_ & Hvm & _).
      destruct (IH ms1 ms' m1 (U + 2 * page_size) Hr Hi1 ltac:(rewrite Hvm; lia))
        as (m' & Ha' & Hf' & Hi').
      exists m'. split; [exact Ha' |]. split; [exact (lazy_frame_trans _ _ _ Hf1 Hf') |].
      unfold lazy_inv in *. lia.
Qed.

(* [comment removed for export] *)
Theorem rzc_rsteps_lazy : forall k ms ms' m U T,
  m_halted m = None ->
  rsteps segs k ms = MachineOk ms' ->
  lazy_inv U m ->
  U + Z.of_nat k * (2 * page_size) <= vm_limit (m_vmmaps m) ->
  (forall m', lazy_frame m m' -> lazy_inv (U + Z.of_nat k * (2 * page_size)) m' ->
              realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros k ms ms' m U T Hh Hr Hinv Hfit HT.
  destruct (asteps_lazy k ms ms' m U Hr Hinv Hfit) as (m' & Ha & Hf & Hi).
  exact (rzc_asteps cfg segs k ms m ms' m' T Hh Ha (HT m' Hf Hi)).
Qed.

(* [comment removed for export] *)
Theorem star_cfg_rsteps_lazy : forall k ms ms' m U,
  m_halted m = None ->
  rsteps segs k ms = MachineOk ms' ->
  lazy_inv U m ->
  U + Z.of_nat k * (2 * page_size) <= vm_limit (m_vmmaps m) ->
  exists m', lazy_frame m m' /\ lazy_inv (U + Z.of_nat k * (2 * page_size)) m'
             /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m').
Proof.
  intros k ms ms' m U Hh Hr Hinv Hfit.
  destruct (asteps_lazy k ms ms' m U Hr Hinv Hfit) as (m' & Ha & Hf & Hi).
  exists m'. split; [exact Hf |]. split; [exact Hi |].
  exact (asteps_star_cfg cfg segs k ms m ms' m' Hh Ha).
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition touch_ok (lazy : list (word * word)) (A : list (Z * Z)) (ms : machine_state) : Prop :=
  forall report, step_accesses segs ms = MachineOk report ->
    touch_allowed lazy A (@accessed_ranges _ report).

Theorem mi_account_step_pages : forall A ms ms' m,
  RiscvSemantics.step segs ms = MachineOk ms' ->
  page_inv A m -> touch_ok (m_vm_lazy m) A ms ->
  exists m', mi_account_step segs ms m = MachineOk (ms', m') /\ lazy_frame m m' /\ page_inv A m'.
Proof.
  intros A ms ms' m Hstep Hinv Htouch.
  destruct (step_report ms ms' Hstep) as (report & Hs & <-).
  destruct (materialize_pages A m _ Hinv (Htouch report Hs)) as (m' & Hm & Hf & Hi).
  exists m'. split; [| split; assumption].
  unfold mi_account_step. rewrite Hs, Hm. reflexivity.
Qed.

Theorem asteps_pages : forall A k ms ms' m,
  rsteps segs k ms = MachineOk ms' ->
  page_inv A m ->
  (forall j msj, (j < k)%nat -> rsteps segs j ms = MachineOk msj -> touch_ok (m_vm_lazy m) A msj) ->
  exists m', asteps segs k (ms, m) = MachineOk (ms', m') /\ lazy_frame m m' /\ page_inv A m'.
Proof.
  intros A. induction k as [| k IH]; intros ms ms' m Hr Hinv Htouch.
  - cbn [rsteps] in Hr. inversion Hr; subst. exists m. cbn [asteps].
    split; [reflexivity |]. split; [apply lazy_frame_refl | exact Hinv].
  - cbn [asteps fst snd]. pose proof Hr as Hr0. cbn [rsteps] in Hr.
    destruct (ms_svc_pending ms) as [x8 |] eqn:Hsvc.
    + inversion Hr; subst. exists m. split; [reflexivity |]. split; [apply lazy_frame_refl | exact Hinv].
    + destruct (RiscvSemantics.step segs ms) as [ms1 | |] eqn:Hs; try discriminate Hr.
      destruct (mi_account_step_pages A ms ms1 m Hs Hinv (Htouch 0%nat ms ltac:(lia) eq_refl))
        as (m1 & Ha & Hf1 & Hi1).
      rewrite Ha. destruct (lazy_frame_facts m m1 Hf1) as (_ & _ & Hlz & _).
      destruct (IH ms1 ms' m1 Hr Hi1) as (m' & Ha' & Hf' & Hi').
      { intros j msj Hj Hrj. rewrite Hlz. apply (Htouch (S j) msj ltac:(lia)).
        cbn [rsteps]. rewrite Hsvc, Hs. exact Hrj. }
      exists m'. split; [exact Ha' |]. split; [exact (lazy_frame_trans _ _ _ Hf1 Hf') | exact Hi'].
Qed.

Theorem rzc_rsteps_pages : forall A k ms ms' m T,
  m_halted m = None ->
  rsteps segs k ms = MachineOk ms' ->
  page_inv A m ->
  (forall j msj, (j < k)%nat -> rsteps segs j ms = MachineOk msj -> touch_ok (m_vm_lazy m) A msj) ->
  (forall m', lazy_frame m m' -> page_inv A m' -> realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros A k ms ms' m T Hh Hr Hinv Htouch HT.
  destruct (asteps_pages A k ms ms' m Hr Hinv Htouch) as (m' & Ha & Hf & Hi).
  exact (rzc_asteps cfg segs k ms m ms' m' T Hh Ha (HT m' Hf Hi)).
Qed.

Theorem star_cfg_rsteps_pages : forall A k ms ms' m,
  m_halted m = None ->
  rsteps segs k ms = MachineOk ms' ->
  page_inv A m ->
  (forall j msj, (j < k)%nat -> rsteps segs j ms = MachineOk msj -> touch_ok (m_vm_lazy m) A msj) ->
  exists m', lazy_frame m m' /\ page_inv A m' /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m').
Proof.
  intros A k ms ms' m Hh Hr Hinv Htouch.
  destruct (asteps_pages A k ms ms' m Hr Hinv Htouch) as (m' & Ha & Hf & Hi).
  exists m'. split; [exact Hf |]. split; [exact Hi |].
  exact (asteps_star_cfg cfg segs k ms m ms' m' Hh Ha).
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_no_accesses : forall m, materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses, newly_materialized_pages.
  cbn [accesses_pages List.filter]. rewrite with_vm_backing_self. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_svc_iff_noacc : forall ms m x8,
  m_halted m = None ->
  ms_svc_pending ms = Some x8 ->
  ~ syscall_spec (sys_input segs ms x8) m Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) m (Ok eff m' evs) ->
     m_halted m' = None /\ syscall_effect_accesses eff = []) ->
  forall e st,
    sstep_cfg segs cfg (mkCfg ms m) e st <->
    exists eff m',
      syscall_spec (sys_input segs ms x8) m (Ok eff m' e)
      /\ ~ spurious_refusal_cfg cfg (sys_input segs ms x8) m eff
      /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m').
Proof.
  intros ms m x8 Hh Hsvc Hnu Hout e st. split.
  - intros Hss.
    inversion Hss; subst; try congruence;
      try (exfalso; apply Hnu; assumption);
      match goal with H : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H; inversion H; subst end.
    + match goal with Hs : syscall_spec _ _ (Ok ?eff ?m' _) |- _ =>
        destruct (Hout _ _ _ Hs) as [_ Hl]; exists eff, m' end.
      split; [assumption |]. split; [assumption |].
      match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
        rewrite Hl, materialize_no_accesses in Hm; inversion Hm; subst end.
      reflexivity.
    + exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hm : materialize_model_accesses _ _ = None |- _ =>
        destruct (Hout _ _ _ Hs) as [_ Hl];
        rewrite Hl, materialize_no_accesses in Hm; discriminate Hm end.
    + exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hc : m_halted _ = Some _ |- _ =>
        destruct (Hout _ _ _ Hs) as [Hn _]; rewrite Hn in Hc; discriminate Hc end.
    + exfalso.
      match goal with Hs : syscall_spec _ _ (Ok _ _ _), Hk : m_killed _ = Some _ |- _ =>
        destruct (Hout _ _ _ Hs) as [Hn _];
        rewrite (m_killed_of_m_halted_none _ Hn) in Hk; discriminate Hk end.
  - intros (eff & m' & Hs & Hns & ->).
    destruct (Hout _ _ _ Hs) as [Hn Hl].
    eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact Hs | exact Hns | exact Hn |].
    rewrite Hl. apply materialize_no_accesses.
Qed.

End WithCfg.
