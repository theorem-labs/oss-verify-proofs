(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA LazyModel ITreeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition minvA (mo : Model) : Prop :=
  fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
  fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
  (forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
  (forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
  (forall k e, fd_lookup (m_fds mo) k = Some e ->
     match e with FdChannel _ | FdFile _ _ | FdDir => True | _ => False end) /\
  (forall t, m_tid mo = Some t -> 0 < bv_unsigned t < PID_MAX_ENVELOPE) /\
  alloc_top (m_vmmaps mo) = alloc_ceiling.   (* [comment removed for export] *)

Lemma minv_minvA : forall mo, minv mo -> minvA mo.
Proof. intros mo (M0 & M1 & M2 & MC & MF & MK & MT & ML & MA). unfold minvA. tauto. Qed.

Lemma minvA_alloc_top : forall mo, minvA mo -> alloc_top (m_vmmaps mo) = alloc_ceiling.
Proof. intros mo H. apply H. Qed.

Lemma minvA_init : forall reserved brk mbase sp lim inp,
  bv_unsigned sp = rc_sp -> (sp_window_lo <= rc_sp <= sp_window_hi)%Z ->
  minvA (init_model reserved brk mbase sp lim inp).
Proof. intros. apply minv_minvA. apply minv_init; assumption. Qed.

End RC__1.
Ltac minvA_open H := destruct H as (M0 & M1 & M2 & MC & MF & MK & MT & MA).

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma bvu64 : forall a : word, 0 <= bv_unsigned a < 2^64.
Proof. intros a. pose proof (bv_unsigned_in_range 64 a) as H. exact H. Qed.

(* [comment removed for export] *)
Lemma minvA_by_fields : forall mo mo',
  m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> m_tid mo' = m_tid mo ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) -> minvA mo -> minvA mo'.
Proof. intros mo mo' Hf Hs Ht Ha H. unfold minvA in *. rewrite Hf, Hs, Ht, Ha. exact H. Qed.

Lemma minvA_magree : forall mo mo', magree mo mo' -> minvA mo -> minvA mo'.
Proof.
  intros mo mo' Hag H. pose proof (magree_frame mo mo' Hag) as F.
  eapply minvA_by_fields; [| | | |exact H]; try tauto. rewrite (magree_vmmaps mo mo' Hag). reflexivity.
Qed.

Lemma minvA_with_vm_backing : forall l p mo, minvA mo -> minvA (with_vm_backing l p mo).
Proof. intros l p mo H. eapply minvA_by_fields; [| | | |exact H]; destruct mo; reflexivity. Qed.

Lemma minvA_with_vmmaps : forall h mo, alloc_top h = alloc_top (m_vmmaps mo) -> minvA mo -> minvA (with_vmmaps h mo).
Proof. intros h mo Ha H. eapply minvA_by_fields; [| | | exact Ha |exact H]; destruct mo; reflexivity. Qed.

Lemma minvA_vm_forget_range : forall lo hi mo, minvA mo -> minvA (vm_forget_range lo hi mo).
Proof. intros lo hi mo H. unfold vm_forget_range. apply minvA_with_vm_backing. exact H. Qed.

Lemma std_chanA : forall mo fd, minvA mo -> (fd = 1 \/ fd = 2) ->
  fd_lookup (m_fds mo) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd)) /\
  w_is0 (Z_to_bv 64 fd) = false.
Proof.
  intros mo fd (M0 & M1 & M2 & _) [-> | ->]; split; first [exact M1 | exact M2 | reflexivity].
Qed.

Lemma alloc_fd_rangeA : forall mo,
  minvA mo -> fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096.
Proof.
  intros mo (M0 & M1 & M2 & _) Hfree. pose proof (alloc_fd_le (m_fds mo)) as Hle.
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (H : forall z e, fd_lookup (m_fds mo) (Z_to_bv 64 z) = Some e -> 0 <= z < 2^64 -> bv_unsigned fd <> z).
  { intros z e Hz Hr E. rewrite <- (Z_to_bv_bv_unsigned fd), E in Hfree. congruence. }
  pose proof (H 0 _ M0 ltac:(lia)). pose proof (H 1 _ M1 ltac:(lia)). pose proof (H 2 _ M2 ltac:(lia)).
  pose proof (bv_unsigned_in_range 64 fd). lia.
Qed.

Lemma minvA_open_insert : forall mo ent,
  minvA mo ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
  minvA (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
  intros mo ent Hminv Hfree Hent. minvA_open Hminv. unfold minvA. macc.
  set (fd := alloc_fd (m_fds mo)) in *.
  assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
  { intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| exact MA]]]].
  - intros k c. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. destruct Hent.
    + apply MC.
  - intros k p off. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. exact Hent.
    + apply MF.
  - intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k).
    + intros H. inversion H; subst. destruct e; auto.
    + apply MK.
Qed.

Lemma minvA_update_file : forall mo k p off off',
  minvA mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
  minvA (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
  intros mo k p off off' Hminv Hk. minvA_open Hminv. unfold minvA. macc.
  assert (Hne : forall z c, fd_lookup (m_fds mo) (Z_to_bv 64 z) = Some (FdChannel c) -> bv_eqb k (Z_to_bv 64 z) = false).
  { intros z c Hz. destruct (bv_eqb k (Z_to_bv 64 z)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
  rewrite !fd_lookup_insert. rewrite (Hne 0 _ M0), (Hne 1 _ M1), (Hne 2 _ M2).
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| exact MA]]]].
  - intros k' c. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [intros H; discriminate| apply MC].
  - intros k' p' o'. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MF]. intros H; inversion H; subst. eapply MF; eauto.
  - intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MK]. intros H; inversion H; subst. exact I.
Qed.

Lemma minvA_remove : forall mo fd, minvA mo -> 3 <= fd < 2^32 ->
  minvA (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
  intros mo fd Hminv Hfd. minvA_open Hminv. unfold minvA. macc.
  rewrite !fd_lookup_remove.
  assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
  { intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  rewrite !Hne by lia.
  split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split; [|split; [|split; [exact MT| exact MA]]]].
  - intros k c. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MC].
  - intros k p off. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MF].
  - intros k e. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MK].
Qed.

Lemma minvA_with_tid : forall mo t, minvA mo -> 0 < bv_unsigned t < PID_MAX_ENVELOPE -> minvA (with_tid t mo).
Proof.
  intros mo t Hminv Ht. minvA_open Hminv. unfold minvA. macc.
  repeat split; try assumption; match goal with H : Some _ = Some _ |- _ => inversion H; subst; lia end.
Qed.

Lemma minvA_with_halted : forall mo c, minvA mo -> minvA (with_halted c mo).
Proof. intros mo c H. eapply minvA_by_fields; [| | | |exact H]; destruct mo; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ranges_cover (rs : list (Z * Z)) (accs : list acc) : Prop :=
  forall w k, In (w, k) accs ->
    exists lo hi, In (lo, hi) rs /\ lo <= bv_unsigned w /\ bv_unsigned w + Z.of_nat k <= hi.

Lemma ranges_cover_nil : forall rs, ranges_cover rs [].
Proof. intros rs w k []. Qed.

Lemma ranges_cover_app : forall rs a b, ranges_cover rs a -> ranges_cover rs b -> ranges_cover rs (a ++ b).
Proof. intros rs a b Ha Hb w k Hin. apply in_app_iff in Hin as [Hin|Hin]; eauto. Qed.

Lemma ranges_cover_one : forall rs (w : word) k lo hi,
  In (lo, hi) rs -> lo <= bv_unsigned w -> bv_unsigned w + Z.of_nat k <= hi -> ranges_cover rs [(w, k)].
Proof. intros rs w k lo hi Hin H1 H2 w' k' [E|[]]. inversion E; subst. eauto 6. Qed.

(* [comment removed for export] *)
Definition node_ranges (n : node) (ms : machine_state) : list (Z * Z) :=
  match n with
  | NWrite fd bs => [(bv_unsigned (areg ms 11), bv_unsigned (areg ms 11) + Z.of_nat (length bs))]
  | NWritev fd bufs =>
      (bv_unsigned (areg ms 11), bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs))
      :: []   (* [comment removed for export] *)
  | NOpen path => [(bv_unsigned (areg ms 11), bv_unsigned (areg ms 11) + Z.of_nat (length path) + 1)]
  | NRead fd buf count => [(buf, buf + count)]
  | _ => []
  end.

(* [comment removed for export] *)
Definition iov_ranges (iovs : list (word * word)) : list (Z * Z) :=
  map (fun iov => (bv_unsigned (fst iov), bv_unsigned (fst iov) + bv_unsigned (snd iov))) iovs.

(* [comment removed for export] *)
Definition node_policy (segs : list Segment) (P : acc -> Prop) (n : node) (ms : machine_state) : Prop :=
  (forall lo hi a k, In (lo, hi) (node_ranges n ms) -> lo <= a -> a + Z.of_nat k <= hi -> 0 <= a < 2^64 ->
     P (Z_to_bv 64 a, k))
  /\ match n with
     | NWritev fd bufs =>
         forall iovs, bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) ->
           Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                                  bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                                  bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs ->     (* [comment removed for export] *)
           forall lo hi a k, In (lo, hi) (iov_ranges iovs) -> lo <= a -> a + Z.of_nat k <= hi -> 0 <= a < 2^64 ->
             P (Z_to_bv 64 a, k)
     | _ => True
     end.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition at_nodeA (P : acc -> Prop) (n : node) (ms : machine_state) : Prop :=
  at_node segs n ms /\ node_policy segs P n ms.

Lemma at_nodeA_at_node : forall P n ms, at_nodeA P n ms -> at_node segs n ms.
Proof. intros P n ms [H _]; exact H. Qed.

Lemma at_nodeA_weaken : forall (P P' : acc -> Prop) n ms,
  (forall x, P x -> P' x) -> at_nodeA P n ms -> at_nodeA P' n ms.
Proof.
  intros P P' n ms HPP [Hat [H1 H2]]. split; [exact Hat|]. split.
  - intros; apply HPP; eauto.
  - destruct n; auto. intros iovs Hi Hb lo hi a k Hin Hlo Hhi Ha. apply HPP. eapply H2; eauto.
Qed.

(* [comment removed for export] *)
Lemma cover_policy : forall (P : acc -> Prop) rs accs,
  (forall lo hi a k, In (lo, hi) rs -> lo <= a -> a + Z.of_nat k <= hi -> 0 <= a < 2^64 -> P (Z_to_bv 64 a, k)) ->
  ranges_cover rs accs -> Forall P accs.
Proof.
  intros P rs accs HP HC. apply Forall_forall. intros [w k] Hin.
  destruct (HC w k Hin) as (lo & hi & Hr & H1 & H2).
  rewrite <- (Z_to_bv_bv_unsigned w). pose proof (bvu64 w) as Hw.
  apply (HP lo hi); auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KIA (S : word -> Prop) (N : nat) (EB : Z) (mo : Model) : Prop :=
  LI S N EB mo /\ minvA mo /\ m_halted mo = None.

Lemma KIA_magree : forall S N EB mo mo', KIA S N EB mo -> magree mo mo' -> LI S N EB mo' -> KIA S N EB mo'.
Proof.
  intros S N EB mo mo' (HL & HM & Hh) Hag HL'. split; [exact HL'|]. split.
  - eapply minvA_magree; eauto.
  - rewrite (magree_halted _ _ Hag). exact Hh.
Qed.

(* [comment removed for export] *)
Definition vm_same (mo mo' : Model) : Prop :=
  m_vm mo' = m_vm mo.

Lemma vm_same_refl : forall mo, vm_same mo mo. Proof. intros; reflexivity. Qed.
Lemma vm_same_with_fds : forall v mo, vm_same mo (with_fds v mo). Proof. intros; destruct mo; reflexivity. Qed.
Lemma vm_same_with_tid : forall v mo, vm_same mo (with_tid v mo). Proof. intros; destruct mo; reflexivity. Qed.
Lemma vm_same_with_halted : forall v mo, vm_same mo (with_halted v mo). Proof. intros; destruct mo; reflexivity. Qed.

Lemma LI_vm_same : forall S N EB mo mo', vm_same mo mo' -> LI S N EB mo -> LI S N EB mo'.
Proof.
  intros S N EB mo mo' Hv [HND HS HC HE HB].
  assert (E1 : m_vm_materialized mo' = m_vm_materialized mo) by (unfold m_vm_materialized; rewrite Hv; reflexivity).
  assert (E2 : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite Hv; reflexivity).
  assert (E3 : eager_used mo' = eager_used mo) by (unfold eager_used, m_vm_lazy; rewrite E2, Hv; reflexivity).
  constructor; rewrite ?E1, ?E2, ?E3; assumption.
Qed.

Lemma lazy_vm_same : forall mo mo', vm_same mo mo' -> m_vm_lazy mo' = m_vm_lazy mo.
Proof. intros mo mo' Hv. unfold m_vm_lazy. rewrite Hv. reflexivity. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PerNode.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_factsA (ms : machine_state) (mo : Model) (n : node) : Prop :=
  exists x8, ms_svc_pending ms = Some x8 /\
  (forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs ->
      nstep n mo (ceff eff) mo' evs /\ vm_same mo mo'
      /\ (forall P, node_policy segs P n ms -> Forall P (syscall_effect_accesses eff))) /\
  (forall eff mo' evs, nstep n mo eff mo' evs ->
     exists ci, check_syscall (sys_input segs ms x8) (with_ci ci eff) mo = CheckOk mo' evs) /\
  (forall eff, check_syscall (sys_input segs ms x8) eff mo <> CheckUnmodeled) /\
  (forall eff mo' evs, nstep n mo eff mo' evs -> m_halted mo' = None /\ minvA mo').

(* [comment removed for export] *)
Lemma access_ranges_eqb_eq' : forall a b, access_ranges_eqb a b = true -> a = b.
Proof. intros. apply access_ranges_eqb_eq. assumption. Qed.

Lemma syscall_effect_accesses_U : forall r ws zs us cs ci,
  syscall_effect_accesses (mkEffectU r ws zs us cs ci) = ci ++ write_accesses ws.
Proof. reflexivity. Qed.

Ltac dispatch K arm :=
  unfold check_syscall; rewrite in_sysno_si;
  change (bv_unsigned (Z_to_bv 64 K)) with K;
  replace (lookup_ca checked_table K) with (Some arm) by reflexivity;
  cbn [arm ca_check];
  rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma write_checkA : forall ms mo fd bs eff mo' evs,
  at_node segs (NWrite fd bs) ms -> minvA mo ->
  (check_syscall (sys_input segs ms (Z_to_bv 64 64)) eff mo = CheckOk mo' evs <->
   write_char (areg ms 11) fd bs mo eff mo' evs)
  /\ check_syscall (sys_input segs ms (Z_to_bv 64 64)) eff mo <> CheckUnmodeled.
Proof.
  intros ms mo fd bs eff mo' evs (Hsvc & Hfd & Ha0 & Ha2 & Hlen & Hrom & Hbs) Hminv.
  pose proof rw_bytes_max_small as HM.
  match goal with |- (?c = _ <-> _) /\ _ => cut (c = match eff with
     | mkEffectU ret [] [] [] [] ci =>
         if (1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length bs))
         then if access_ranges_eqb ci [(areg ms 11, Z.to_nat (bv_unsigned ret))]
              then CheckOk mo (map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat (bv_unsigned ret)) bs))
              else CheckReject
         else CheckReject
     | _ => CheckReject end) end.
  { intros E. rewrite E. split.
    - unfold write_char. destruct eff as [ret ws zs us cs ci]. split.
      + intros H. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
        destruct (1 <=? bv_unsigned ret) eqn:E1; [|discriminate].
        destruct (bv_unsigned ret <=? Z.of_nat (length bs)) eqn:E2; [|discriminate].
        cbn [andb] in H.
        destruct (access_ranges_eqb ci _) eqn:E3; [|discriminate]. inversion H; subst.
        apply Z.leb_le in E1. apply Z.leb_le in E2.
        exists (bv_unsigned ret), ci. rewrite Z_to_bv_bv_unsigned. repeat split; auto; lia.
      + intros (k & ci' & Hk & Heff & Hci & -> & ->). inversion Heff; subst.
        rewrite unsigned_lit by lia. rewrite Hci.
        replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia).
        replace (k <=? Z.of_nat (length bs)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - destruct eff as [ret [|? ?] [|? ?] [|? ?] [|? ?] ci]; try discriminate. destruct (_ && _); [destruct (access_ranges_eqb _ _)|]; discriminate. }
  dispatch 64 arm_write. unfold check_write. rewrite Ha0, Ha2, in_mem_si.
  destruct (std_chanA mo fd Hminv Hfd) as [-> Hw]. rewrite Hw.
  unfold modeled_rw_range, modeled_rw_count. rewrite unsigned_lit by lia.
  replace (Z.of_nat (length bs) <=? rw_bytes_max) with true by (symmetry; apply Z.leb_le; lia). cbn [negb orb].
  rewrite w_is0_lit by lia. replace (Z.of_nat (length bs) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv zeta.
  replace (write_source (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length bs)))) with bs.
  2:{ symmetry. unfold write_source. rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; unfold MAX_RW_COUNT, rw_bytes_max in *; lia).
      rewrite unsigned_lit by lia.
      rewrite <- (wa_unsigned_id (areg ms 11)). apply readable_bytes_bytes_in; [eapply bytes_at_in; eassumption| lia]. }
  replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

Lemma write_factsA : forall ms mo fd bs,
  at_node segs (NWrite fd bs) ms -> minvA mo -> m_halted mo = None -> node_factsA ms mo (NWrite fd bs).
Proof.
  intros ms mo fd bs Hat Hminv Hh. exists (Z_to_bv 64 64). split; [exact (proj1 Hat)|].
  split; [|split; [|split]].
  - intros eff mo' evs Hc. apply (proj1 (proj1 (write_checkA _ _ _ _ eff mo' evs Hat Hminv))) in Hc.
    destruct Hc as (k & ci & Hk & -> & Hci & -> & ->). split; [|split].
    + cbn [nstep chan_write ceff]. split; [reflexivity|]. right. exists k. repeat split; auto; lia.
    + apply vm_same_refl.
    + intros P [HP _]. apply access_ranges_eqb_eq' in Hci. subst ci.
      rewrite syscall_effect_accesses_U. cbn [write_accesses app].
      eapply cover_policy; [exact HP|]. cbn [node_ranges].
      eapply ranges_cover_one; [left; reflexivity| lia | lia].
  - intros eff mo' evs [-> [(Hbs & _) | (k & Hk & -> & ->)]].
    { exfalso. subst bs. cbn in Hat. lia. }
    exists [(areg ms 11, Z.to_nat k)]. apply (proj2 (proj1 (write_checkA _ _ _ _ _ _ _ Hat Hminv))).
    exists k, [(areg ms 11, Z.to_nat k)].
    split; [exact Hk|]. split; [reflexivity|]. split; [apply access_ranges_eqb_refl|]. split; reflexivity.
  - intros eff. exact (proj2 (write_checkA _ _ _ _ eff mo [] Hat Hminv)).
  - intros eff mo' evs [-> _]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma copy_iovecs_accesses_cover : forall n mp (a w : word) k,
  bv_unsigned a + 16 * Z.of_nat n <= 2^64 ->
  In (w, k) (copy_iovecs_accesses mp a n) ->
  bv_unsigned a <= bv_unsigned w /\ bv_unsigned w + Z.of_nat k <= bv_unsigned a + 16 * Z.of_nat n.
Proof.
  induction n as [|n IH]; intros mp a w k Hb Hin; cbn [copy_iovecs_accesses] in Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - inversion E; subst. cbn [Z.of_nat]. lia.
  - destruct (read_iovec_entry mp a) as [b l| |]; [|destruct Hin|destruct Hin].
    destruct n as [|n']. { cbn in Hin. destruct Hin. }
    assert (Ha16 : bv_unsigned (a + 16)%bv = bv_unsigned a + 16).
    { rewrite bv_add_unsigned. change (bv_unsigned (16%bv : word)) with 16. apply bv_wrap_small.
      pose proof (bvu64 a). change (bv_modulus 64) with (2^64). clear IH Hin. lia. }
    specialize (IH mp (a + 16)%bv w k). rewrite Ha16 in IH. destruct (IH ltac:(lia) Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma import_iovecs_accesses_cover : forall mp (a w : word) (n : nat) k,
  bv_unsigned a + 16 * Z.of_nat n <= 2^64 -> (n <= 1024)%nat ->
  In (w, k) (import_iovecs_accesses mp a (Z_to_bv 64 (Z.of_nat n))) ->
  bv_unsigned a <= bv_unsigned w /\ bv_unsigned w + Z.of_nat k <= bv_unsigned a + 16 * Z.of_nat n.
Proof.
  intros mp a w n k Hb Hn Hin. unfold import_iovecs_accesses in Hin.
  destruct (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !unsigned_lit in E1 by lia.
    destruct (negb (access_okb a 16)); [destruct Hin|]. destruct Hin as [E|[]]. inversion E; subst. cbn [Z.of_nat]. lia.
  - destruct (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 0)); [destruct Hin|].
    destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat n))); [destruct Hin|].
    destruct (negb (access_okb a (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat n))))); [destruct Hin|].
    rewrite word_to_nat_of_nat in Hin by lia. exact (copy_iovecs_accesses_cover _ _ _ _ _ Hb Hin).
Qed.

(* [comment removed for export] *)
Lemma iov_prefix_accesses_cover : forall iovs left (w : word) k,
  In (w, k) (iov_prefix_accesses iovs left) -> exists l, In (w, l) iovs /\ (k <= word_to_nat l)%nat.
Proof.
  induction iovs as [|[b l] iovs IH]; intros left w k Hin.
  - destruct left; cbn in Hin; destruct Hin.
  - destruct left as [|left']; [cbn in Hin; destruct Hin|].
    cbn [iov_prefix_accesses] in Hin. rewrite word_to_nat_bounded_eq_min in Hin.
    destruct (Nat.eqb (Nat.min (word_to_nat l) (S left')) 0) eqn:E.
    + destruct (IH _ _ _ Hin) as (l' & Hl' & Hk). exists l'. split; [right; exact Hl'| exact Hk].
    + destruct Hin as [E2|Hin].
      * inversion E2; subst. exists l. split; [left; reflexivity|]. apply Nat.le_min_l.
      * destruct (IH _ _ _ Hin) as (l' & Hl' & Hk). exists l'. split; [right; exact Hl'| exact Hk].
Qed.

Lemma cap_iovecs_id : forall mp iovs bufs,
  Forall2 (iov_ok mp) iovs bufs -> Z.of_nat (length (concat bufs)) <= MAX_RW_COUNT -> cap_iovecs iovs = iovs.
Proof. intros. unfold cap_iovecs. eapply cap_iovecs_aux_id; eauto. Qed.

Lemma writev_check_nfA : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minvA mo ->
  exists iovs,
    bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
    Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                           bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                           bv_unsigned (fst iov) + Z.of_nat (length bs) <= TASK_SIZE) iovs bufs /\
    forall eff,
    check_syscall (sys_input segs ms (Z_to_bv 64 66)) eff mo
    = writev_nf (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length bufs)))) (cap_iovecs iovs) fd bufs mo eff.
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Harr & iovs & Hiov & Hbufs) Hminv.
  pose proof writev_node_max_small as HM. pose proof writev_node_max_big as HM2.
  pose proof (iovs_ok_of_at segs _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (iovs_access_okb_of_at segs _ _ _ Hbufs ltac:(lia)) as Hacc.
  pose proof (Forall2_length Hbufs) as Hleq.
  pose proof (bv_unsigned_in_range 64 (areg ms 11)) as [Ha11 _].
  exists iovs. split; [exact Hiov|]. split; [exact Hbufs|].
  intros eff. unfold writev_nf.
  dispatch 66 arm_writev.
  unfold check_writev. rewrite Ha0, Ha2, in_mem_si.
  destruct (std_chanA mo fd Hminv Hfd) as [-> Hw]. rewrite Hw.
  unfold iovcnt32. rewrite abi_low32_small by lia.
  rewrite <- (wa_unsigned_id (areg ms 11)) at 1.
  rewrite (import_iovecs_bytes_in (ms_read_byte ms) (bv_unsigned (areg ms 11)) iovs bufs Hok Hacc ltac:(lia) Hcnt Harr Ha11)
    by (eapply bytes_at_in; eassumption).
  cbv zeta. rewrite iovs_total_cap, (iovs_total_ok _ _ _ Hok). rewrite Z.min_l by lia.
  assert (Hg : writev_gathered (ms_read_byte ms) iovs = concat bufs).
  { unfold writev_gathered, cap_iovecs. rewrite (cap_iovecs_aux_id _ _ _ _ Hok) by lia.
    apply gather_prefix_full. apply gather_iovecs_ok. exact Hok. }
  rewrite Hg.
  destruct (length (concat bufs) =? 0)%nat eqn:El.
  { apply Nat.eqb_eq in El. rewrite El. cbn [Z.of_nat Z.eqb]. reflexivity. }
  apply Nat.eqb_neq in El.
  replace (Z.of_nat (length (concat bufs)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold len_word. replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat (length (concat bufs))))) with false.
  2:{ symmetry. unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia. }
  reflexivity.
Qed.

Lemma cap_iovecs_In : forall mp iovs bufs x,
  Forall2 (iov_ok mp) iovs bufs -> Z.of_nat (length (concat bufs)) <= MAX_RW_COUNT -> In x (cap_iovecs iovs) -> In x iovs.
Proof. intros mp iovs bufs x Hok Hle. rewrite (cap_iovecs_id mp iovs bufs Hok Hle). exact (fun H => H). Qed.

Lemma iov_ranges_In : forall iovs (w l : word),
  In (w, l) iovs -> In (bv_unsigned w, bv_unsigned w + bv_unsigned l) (iov_ranges iovs).
Proof.
  intros iovs w l H. unfold iov_ranges. apply in_map_iff. exists (w, l). split; [reflexivity| exact H].
Qed.

Lemma Forall2_In_l : forall {A B} (R : A -> B -> Prop) l1 l2 x,
  Forall2 R l1 l2 -> In x l1 -> exists y, In y l2 /\ R x y.
Proof.
  intros A B R l1 l2 x H; induction H as [|a b la lb Hab H IH]; intros Hin; [destruct Hin|].
  destruct Hin as [->|Hin]; [exists b; split; [left; reflexivity| assumption]|].
  destruct (IH Hin) as (y' & Hy' & HR). exists y'. split; [right; exact Hy'| exact HR].
Qed.

Lemma in_concat_length : forall {A} (ls : list (list A)) l, In l ls -> (length l <= length (concat ls))%nat.
Proof.
  induction ls as [|x ls IH]; intros l Hin; [destruct Hin|]. cbn [concat]. rewrite length_app.
  destruct Hin as [->|Hin]; [lia|]. specialize (IH l Hin). lia.
Qed.

Lemma writev_factsA : forall ms mo fd bufs,
  at_node segs (NWritev fd bufs) ms -> minvA mo -> m_halted mo = None -> node_factsA ms mo (NWritev fd bufs).
Proof.
  intros ms mo fd bufs Hat Hminv Hh.
  destruct (writev_check_nfA _ _ _ _ Hat Hminv) as (iovs & Hiov & Hbufs & Hnf).
  assert (Htot : Z.of_nat (length (concat bufs)) <= writev_node_max) by (cbn in Hat; tauto).
  assert (Hcnt : (length bufs <= 1024)%nat) by (cbn in Hat; tauto).
  assert (Hrom : ms_rom ms = seg_rom segs) by (cbn in Hat; tauto).
  pose proof writev_node_max_small as HM. pose proof writev_node_max_big as HM2.
  pose proof (iovs_ok_of_at segs _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (bytes_at_bound _ _ _ _ Hiov) as Biov. rewrite length_iovec_bytes in Biov.
  pose proof (Forall2_length Hbufs) as Hleq.
  assert (HB16 : bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^64). { rewrite <- Hleq. clear -Biov. lia. }
  exists (Z_to_bv 64 66). split; [exact (proj1 Hat)|].
  split; [|split; [|split]].
  - intros eff mo' evs H. rewrite Hnf in H.
    assert (HC : nstep (NWritev fd bufs) mo (ceff eff) mo' evs /\ mo' = mo /\
                 (forall P, node_policy segs P (NWritev fd bufs) ms -> Forall P (syscall_effect_accesses eff))).
    2:{ destruct HC as (H1 & -> & H3). split; [exact H1|]. split; [apply vm_same_refl| exact H3]. }
    unfold writev_nf in H.
    (* [comment removed for export] *)
    assert (COV1 : forall P, node_policy segs P (NWritev fd bufs) ms ->
              Forall P (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length bufs))))).
    { intros P [HP _]. eapply cover_policy; [exact HP|]. intros w k Hin.
      pose proof (import_iovecs_accesses_cover _ _ _ _ _ HB16 Hcnt Hin) as [H1 H2].
      cbn [node_ranges]. eexists _, _. split; [left; reflexivity|]. lia. }
    assert (COV2 : forall P k, node_policy segs P (NWritev fd bufs) ms -> Forall P (iov_prefix_accesses (cap_iovecs iovs) k)).
    { intros P k [_ HP]. specialize (HP iovs Hiov Hbufs). eapply cover_policy; [exact HP|]. intros w j Hin.
      destruct (iov_prefix_accesses_cover _ _ _ _ Hin) as (l & Hl0 & Hj).
      pose proof (cap_iovecs_In _ _ _ _ Hok ltac:(lia) Hl0) as Hl.
      destruct (Forall2_In_l _ _ _ _ Hbufs Hl) as (bs & Hbs & (El & Hb & _)). cbn [fst snd] in El, Hb.
      pose proof (bytes_at_bound _ _ _ _ Hb) as Bb.
      assert (Hlen : Z.of_nat (length bs) <= writev_node_max).
      { pose proof (in_concat_length bufs bs Hbs). clear -H0 Htot. lia. }
      subst l. rewrite word_to_nat_of_nat in Hj by lia.
      eexists _, _. split; [apply iov_ranges_In; exact Hl|]. cbn [fst snd]. rewrite unsigned_lit by lia. lia. }
    destruct (length (concat bufs) =? 0)%nat eqn:E1.
    { apply check_ret_only_copyins_ok_iff in H as (-> & -> & ->). apply Nat.eqb_eq in E1.
      split; [|split; [reflexivity|]].
      - cbn [nstep chan_write ceff]. destruct (concat bufs); [|cbn in E1; lia]. split; [reflexivity|]. left. repeat split; reflexivity.
      - intros P HP. rewrite syscall_effect_accesses_U. cbn [write_accesses]. rewrite app_nil_r. apply COV1. exact HP. }
    destruct eff as [ret ws zs us cs ci].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    destruct (1 <=? bv_unsigned ret) eqn:E2; [|discriminate].
    destruct (bv_unsigned ret <=? Z.of_nat (length (concat bufs))) eqn:E3; [|discriminate].
    destruct (negb (addr_is_error_b ret)); [|discriminate]. cbn [andb] in H.
    destruct (access_ranges_eqb ci _) eqn:E4; [|discriminate]. inversion H; subst.
    apply Z.leb_le in E2. apply Z.leb_le in E3. apply access_ranges_eqb_eq' in E4. subst ci.
    split; [|split; [reflexivity|]].
    + cbn [nstep chan_write ceff]. split; [reflexivity|]. right. exists (bv_unsigned ret). rewrite Z_to_bv_bv_unsigned. repeat split; auto; lia.
    + intros P HP. rewrite syscall_effect_accesses_U. cbn [write_accesses]. rewrite app_nil_r.
      apply Forall_app. split; [apply COV1; exact HP| apply COV2; exact HP].
  - intros eff mo' evs [-> [(Hbs & -> & ->) | (k & Hk & -> & ->)]].
    + eexists. rewrite Hnf. unfold writev_nf. rewrite Hbs. cbn [length Nat.eqb].
      apply check_ret_only_copyins_ok_iff. repeat split; reflexivity.
    + destruct (length (concat bufs) =? 0)%nat eqn:E1.
      { exfalso. apply Nat.eqb_eq in E1. lia. }
      eexists (_ ++ iov_prefix_accesses (cap_iovecs iovs) (Z.to_nat k)). rewrite Hnf. unfold writev_nf. rewrite E1.
      cbn [with_ci eff0 eff_ret eff_writes eff_zeros eff_unmaps eff_copies].
      rewrite unsigned_lit by lia.
      replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia).
      replace (k <=? Z.of_nat (length (concat bufs))) with true by (symmetry; apply Z.leb_le; lia).
      rewrite addr_is_error_small_wv by lia. rewrite access_ranges_eqb_refl. reflexivity.
  - intros eff. rewrite Hnf. unfold writev_nf.
    destruct (length (concat bufs) =? 0)%nat; [apply check_ret_only_copyins_no_unmodeled|].
    destruct eff as [ret [|? ?] [|? ?] [|? ?] [|? ?] ci]; try discriminate. destruct (_ && _); [destruct (access_ranges_eqb _ _)|]; discriminate.
  - intros eff mo' evs [-> _]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cstr_access_len_aux_le : forall str fuel mp a,
  ~ In (Z_to_bv 8 0) str -> bytes_in mp a (str ++ [Z_to_bv 8 0]) ->
  (cstr_access_len_aux mp (wa a) fuel <= length str + 1)%nat.
Proof.
  induction str as [|b str IH]; intros fuel mp a Hnz H.
  - destruct fuel as [|fuel]; [cbn; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb _].
    cbn [cstr_access_len_aux]. rewrite Hb, bv_eqb_refl. cbn [length]. lia.
  - destruct fuel as [|fuel]; [cbn; lia|]. cbn [app] in H. apply bytes_in_cons in H as [Hb H].
    cbn [cstr_access_len_aux length]. rewrite Hb.
    destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. rewrite wa_succ.
    specialize (IH fuel mp (a + 1) ltac:(intro Hin; apply Hnz; right; exact Hin) H). lia.
Qed.

Lemma open_check_nfA : forall ms mo path,
  at_node segs (NOpen path) ms ->
  forall eff,
  check_syscall (sys_input segs ms (Z_to_bv 64 56)) eff mo
  = check_copyins_after [(areg ms 11, cstr_access_len_aux (ms_read_byte ms) (areg ms 11) path_max)] eff
      (open_check path (ceff eff) mo).
Proof.
  intros ms mo path (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hrom & Hp) eff.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  dispatch 56 arm_openat. unfold check_openat. rewrite in_mem_si.
  rewrite (modeled_open_flags_rd _ (ldiff_open_flags _ Hfl)). cbn [negb]. cbv zeta.
  rewrite clear_copyins_ceff. f_equal.
  unfold Open.check_openat_body, open_check. rewrite Ha0, in_mem_si.
  rewrite <- (wa_unsigned_id (areg ms 11)). unfold read_cstr.
  destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
  - rewrite (read_cstr_aux_toolong_bytes_in path_max path); [reflexivity|exact Hlong|exact Hnz|].
    apply bytes_in_app in Hin as [Hin _]. exact Hin.
  - rewrite (read_cstr_aux_bytes_in path path_max); [|lia|exact Hnz|exact Hin].
    destruct path as [|c path']; [reflexivity|].
    cbn [path_eqb]. change (bv_eqb (fd32 (Z_to_bv 64 (-100))) AT_FDCWD32) with true. cbn [negb].
    unfold Open.check_openat_resolved. rewrite Hsl. rewrite (ldiff_open_flags _ Hfl). cbn [Z.eqb].
    unfold Open.check_openat_read. reflexivity.
Qed.

Lemma open_presA : forall mo path eff mo' evs,
  minvA mo -> m_halted mo = None -> nstep (NOpen path) mo eff mo' evs -> m_halted mo' = None /\ minvA mo' /\ vm_same mo mo'.
Proof.
  intros mo path eff mo' evs Hminv Hh [_ H].
  assert (T : m_halted mo = None /\ minvA mo /\ vm_same mo mo) by (split; [exact Hh| split; [exact Hminv| apply vm_same_refl]]).
  assert (G : forall ent, match ent with FdFile p _ => fs_lookup (m_fs mo) p <> None | FdDir => True | _ => False end ->
            open_result mo ent eff mo' ->
            m_halted mo' = None /\ minvA mo' /\ vm_same mo mo').
  { intros ent Hent [(e & _ & _ & ->) | (Hfree & _ & ->)]; [exact T|].
    split; [macc; exact Hh|]. split; [apply minvA_open_insert; assumption| apply vm_same_with_fds]. }
  destruct (path_max <=? length path)%nat. { destruct H as [_ ->]. exact T. }
  destruct path as [|c path']. { destruct H as [_ ->]. exact T. }
  destruct (path_is_dirref (c :: path')). { apply (G FdDir); [exact I| exact H]. }
  destruct (fs_lookup (m_fs mo) _) eqn:E.
  - apply (G (FdFile (c :: path') (Z_to_bv 64 0))); [rewrite E; discriminate| exact H].
  - destruct H as [_ ->]. exact T.
Qed.

Lemma open_result_eff0 : forall mo ent eff mo', open_result mo ent eff mo' -> exists r, eff = eff0 r.
Proof. intros mo ent eff mo' [(e & _ & -> & _) | (_ & -> & _)]; eexists; reflexivity. Qed.

Lemma nstep_open_eff0 : forall path mo eff mo' evs, nstep (NOpen path) mo eff mo' evs -> exists r, eff = eff0 r.
Proof.
  intros path mo eff mo' evs [_ H].
  destruct (path_max <=? length path)%nat. { destruct H as [-> _]. eexists; reflexivity. }
  destruct path as [|c path']. { destruct H as [-> _]. eexists; reflexivity. }
  destruct (path_is_dirref (c :: path')). { eapply open_result_eff0; exact H. }
  destruct (fs_lookup (m_fs mo) _).
  - eapply open_result_eff0; exact H.
  - destruct H as [-> _]. eexists; reflexivity.
Qed.

Lemma open_factsA : forall ms mo path,
  at_node segs (NOpen path) ms -> minvA mo -> m_halted mo = None -> node_factsA ms mo (NOpen path).
Proof.
  intros ms mo path Hat Hminv Hh. pose proof (open_check_nfA _ mo _ Hat) as Hnf.
  pose proof Hat as (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hrom & Hp).
  pose proof (bytes_at_bound _ _ _ _ Hp) as Bp. rewrite length_app in Bp. cbn [length] in Bp.
  pose proof (cstr_access_len_aux_le path path_max _ _ Hnz (bytes_at_in _ _ _ _ Hrom Hp)) as Hcl.
  rewrite wa_unsigned_id in Hcl.
  exists (Z_to_bv 64 56). split; [exact Hsvc|]. split; [|split; [|split]].
  - intros eff mo' evs Hc. rewrite Hnf in Hc. apply check_copyins_after_ok_iff in Hc as [Hci Hc].
    apply open_check_ok_iff in Hc. split; [exact Hc|]. split; [exact (proj2 (proj2 (open_presA _ _ _ _ _ Hminv Hh Hc)))|].
    intros P [HP _].
    assert (Hw : eff_writes eff = []).
    { destruct (nstep_open_eff0 _ _ _ _ _ Hc) as [r Er]. destruct eff as [r0 ws zs us cs ci]. cbn in Er. unfold eff0 in Er. inversion Er. reflexivity. }
    unfold syscall_effect_accesses. rewrite Hci, Hw. cbn [write_accesses app].
    eapply cover_policy; [exact HP|]. cbn [node_ranges]. eapply ranges_cover_one; [left; reflexivity| lia | lia].
  - intros eff mo' evs HP. eexists. rewrite Hnf. apply (proj2 (check_copyins_after_ok_iff _ _ _ _ _)). split.
    + cbn [eff_copyins with_ci]. reflexivity.
    + apply open_check_ok_iff. rewrite ceff_with_ci.
      destruct (nstep_open_eff0 _ _ _ _ _ HP) as [r ->]. cbn [with_ci ceff eff0]. exact HP.
  - intros eff. rewrite Hnf. intros Hu. apply check_copyins_after_unmodeled in Hu. exact (open_check_no_unmodeled _ _ _ Hu).
  - intros eff mo' evs HP. pose proof (open_presA _ _ _ _ _ Hminv Hh HP). tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_check_specA : forall ms mo fd buf count eff,
  at_node segs (NRead fd buf count) ms -> minvA mo ->
  check_syscall (sys_input segs ms (Z_to_bv 64 63)) eff mo = read_check fd buf count eff mo.
Proof.
  intros ms mo fd buf count eff (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hb47 & Hwr) Hminv. minvA_open Hminv.
  pose proof (proj1 Hwr) as Hb0.
  assert (Hsure : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { unfold access_okb. rewrite !unsigned_lit by (unfold TASK_SIZE in *; lia). apply andb_true_intro; split; apply Z.leb_le; unfold TASK_SIZE in *; lia. }
  dispatch 63 arm_read. unfold check_read, read_check. rewrite Ha0, Ha1, Ha2, in_wmem_si.
  rewrite fd32_small by lia.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk; [|reflexivity].
  pose proof (MK _ _ Hlk) as HK. destruct e as [ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]; try contradiction.
  - exfalso. apply MC in Hlk. rewrite unsigned_lit in Hlk by lia. lia.
  - rewrite Hsure. cbn [negb].
    destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
    rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; unfold MAX_RW_COUNT; lia).
    rewrite unsigned_lit by lia.
    cbv zeta. set (bs := file_read data off (Z_to_bv 64 count)).
    assert (Hlen : Z.of_nat (length bs) <= count /\ Z.of_nat (length bs) < 2^64).
    { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. fold bs in L.
      unfold word_to_nat in L. rewrite unsigned_lit in L by lia. lia. }
    rewrite read_bytes_map_eq. unfold ms_writable_byte. unfold len_word at 1. rewrite word_to_nat_of_nat by lia.
    change (Z_to_bv 64 buf) with (wa buf) at 1.
    destruct (read_bytes_aux (wview segs (ms_mem ms)) (wa buf) (length bs)) eqn:E.
    2:{ exfalso. exact (read_bytes_aux_wr_at _ _ _ _ _ Hwr (proj1 Hlen) E). }
    destruct bs; reflexivity.
  - rewrite Hsure. reflexivity.
Qed.

Lemma read_check_ok_iffA : forall fd buf count eff mo mo' evs,
  minvA mo ->
  read_check fd buf count eff mo = CheckOk mo' evs <-> nstep (NRead fd buf count) mo eff mo' evs.
Proof.
  intros fd buf count eff mo mo' evs Hminv. minvA_open Hminv. unfold read_check. cbn [nstep].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  2:{ rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto. }
  destruct e as [ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]; try (split; [discriminate| tauto]).
  - destruct (fs_lookup (m_fs mo) p) as [data|]. 2:{ split; [discriminate|tauto]. }
    cbv zeta. destruct (file_read data off (Z_to_bv 64 count)) as [|b bs'] eqn:Ebs.
    + rewrite check_ret_only_ok_iff. cbn [delivered_writes]. change (len_word (@nil byte)) with (Z_to_bv 64 0). tauto.
    + cbn [delivered_writes]. destruct eff as [ret ws zs us cs ci]. split.
      * intros H. destruct ws as [|[a bs''] [|? ?]]; try discriminate. destruct zs; [|discriminate]. destruct us; [|discriminate].
        destruct cs; [|discriminate]. destruct ci; [|discriminate].
        destruct (bv_eqb a (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
        destruct (listN_eqb bs'' (b :: bs')) eqn:E2; [|discriminate].
        destruct (bv_eqb ret (len_word (b :: bs'))) eqn:E3; [|discriminate].
        cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3.
        subst. repeat split; reflexivity.
      * intros (-> & Heff & ->). inversion Heff; subst. rewrite !bv_eqb_refl, listN_eqb_refl. reflexivity.
  - rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
Qed.

(* [comment removed for export] *)
Lemma nstep_read_shape : forall fd buf count mo eff mo' evs,
  0 < count < 2^63 ->
  nstep (NRead fd buf count) mo eff mo' evs ->
  eff_copyins eff = [] /\
  (eff_writes eff = [] \/ exists bs, eff_writes eff = [(Z_to_bv 64 buf, bs)] /\ Z.of_nat (length bs) <= count) /\
  vm_same mo mo' /\ (mo' = mo \/ exists k p off off', fd_lookup (m_fds mo) k = Some (FdFile p off) /\
                                                    mo' = with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
  intros fd buf count mo eff mo' evs Hc [_ H].
  assert (T : vm_same mo mo /\ (mo = mo \/ exists k p off off', fd_lookup (m_fds mo) k = Some (FdFile p off) /\
                                                    mo = with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo)).
  { split; [apply vm_same_refl| left; reflexivity]. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  2:{ destruct H as [-> ->]. split; [reflexivity|]. split; [left; reflexivity| exact T]. }
  destruct e as [ch|p off|p off|p off|p off| |sk|id w|drd dwr| ]; try contradiction.
  - destruct (fs_lookup (m_fs mo) p) as [data|]; [|contradiction].
    destruct H as [-> ->]. cbn [delivered_writes eff_copyins eff_writes].
    pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. unfold word_to_nat in L. rewrite unsigned_lit in L by lia.
    split; [destruct (file_read data off (Z_to_bv 64 count)); reflexivity|]. split.
    + destruct (file_read data off (Z_to_bv 64 count)) eqn:E; [left; reflexivity| right]. eexists. split; [reflexivity|]. lia.
    + split; [apply vm_same_with_fds| right]. eexists _, _, _, _. split; [exact Hlk| reflexivity].
  - destruct H as [-> ->]. split; [reflexivity|]. split; [left; reflexivity| exact T].
Qed.

Lemma read_factsA : forall ms mo fd buf count,
  at_node segs (NRead fd buf count) ms -> minvA mo -> m_halted mo = None -> node_factsA ms mo (NRead fd buf count).
Proof.
  intros ms mo fd buf count Hat Hminv Hh. pose proof Hat as (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hb47 & Hwr).
  pose proof Hwr as (Hb0 & _ & _).
  unfold TASK_SIZE in Hb47. assert (HC63 : 0 < count < 2^63) by (clear -Hc Hb47 Hb0; lia).
  exists (Z_to_bv 64 63). split; [exact Hsvc|]. split; [|split; [|split]].
  - intros eff mo' evs H. rewrite (read_check_specA _ _ _ _ _ _ Hat Hminv) in H. apply (read_check_ok_iffA _ _ _ _ _ _ _ Hminv) in H.
    destruct (nstep_read_shape _ _ _ _ _ _ _ HC63 H) as (Hci & Hws & Hvm & _).
    split; [|split; [exact Hvm|]].
    + destruct eff as [r ws zs us cs ci]; cbn in Hci; subst ci. exact H.
    + intros P [HP _]. unfold syscall_effect_accesses. rewrite Hci. cbn [app].
      destruct Hws as [-> | (bs & -> & Hbs)]; [apply Forall_nil|]. cbn [write_accesses].
      eapply cover_policy; [exact HP|]. cbn [node_ranges].
      eapply ranges_cover_one; [left; reflexivity| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia].
  - intros eff mo' evs H. exists (@nil (word * nat)).
    rewrite (read_check_specA _ _ _ _ _ _ Hat Hminv). apply (read_check_ok_iffA _ _ _ _ _ _ _ Hminv).
    destruct (nstep_read_shape _ _ _ _ _ _ _ HC63 H) as (Hci & _).
    destruct eff as [r ws zs us cs ci]; cbn in Hci; subst ci. exact H.
  - intros eff. rewrite (read_check_specA _ _ _ _ _ _ Hat Hminv). apply read_check_no_unmodeled.
  - intros eff mo' evs H. destruct (nstep_read_shape _ _ _ _ _ _ _ HC63 H) as (_ & _ & _ & [-> | (k & p & off & off' & Hk & ->)]); [auto|].
    split; [macc; exact Hh|]. eapply minvA_update_file; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma factsA_ret_only : forall ms mo n x8 r mo1 evs0,
  ms_svc_pending ms = Some x8 -> m_halted mo1 = None -> minvA mo1 -> vm_same mo mo1 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff mo = check_ret_only eff r mo1 evs0) ->
  (forall eff mo' evs, nstep n mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo1 /\ evs = evs0)) ->
  node_factsA ms mo n.
Proof.
  intros ms mo n x8 r mo1 evs0 Hsvc Hh1 Hm1 Hv1 Hchk Hn. exists x8. split; [exact Hsvc|]. split; [|split; [|split]].
  - intros eff mo' evs H. rewrite Hchk, check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    split; [apply Hn; unfold eff0; auto|]. split; [exact Hv1|].
    intros P _. cbn. apply Forall_nil.
  - intros eff mo' evs H. apply Hn in H as (-> & -> & ->). exists (@nil (word * nat)). rewrite Hchk. apply check_ret_only_ok_iff. auto.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - intros eff mo' evs H. apply Hn in H as (_ & -> & _). auto.
Qed.

Lemma close_factsA : forall ms mo fd,
  at_node segs (NClose fd) ms -> minvA mo -> m_halted mo = None -> node_factsA ms mo (NClose fd).
Proof.
  intros ms mo fd (Hsvc & Hfd & Ha0) Hminv Hh.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms (Z_to_bv 64 57)) eff mo =
            match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
            | None => check_ret_only eff (errno_ret EBADF) mo []
            | Some _ => check_ret_only eff (Z_to_bv 64 0) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []
            end).
  { intros eff. dispatch 57 arm_close. unfold check_close. rewrite Ha0. rewrite fd32_small by lia. reflexivity. }
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk.
  - eapply (factsA_ret_only ms mo (NClose fd) _ (Z_to_bv 64 0)); [exact Hsvc| | | | exact Hchk|].
    + macc. exact Hh.
    + apply minvA_remove; assumption.
    + apply vm_same_with_fds.
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold eff0. tauto.
  - eapply (factsA_ret_only ms mo (NClose fd) _ (errno_ret EBADF) mo); [exact Hsvc| exact Hh| exact Hminv| apply vm_same_refl| exact Hchk|].
    intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
Qed.

Lemma ioctl_factsA : forall ms mo fd req,
  at_node segs (NIoctl fd req) ms -> minvA mo -> m_halted mo = None -> node_factsA ms mo (NIoctl fd req).
Proof.
  intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) Hminv Hh.
  eapply (factsA_ret_only ms mo (NIoctl fd req) _ (errno_ret ENOTTY) mo []); [exact Hsvc | exact Hh | exact Hminv | apply vm_same_refl | |].
  - intros eff. dispatch 29 arm_ioctl. unfold check_ioctl. rewrite Ha0, Ha1. subst req.
    unfold cmd32. rewrite fd32_small, abi_low32_small by lia.
    destruct Hminv as (M0 & M1 & M2 & _).
    assert (Hl : exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)).
    { assert (fd = 0 \/ fd = 1 \/ fd = 2) as [-> | [-> | ->]] by lia; eexists; eassumption. }
    destruct Hl as [c ->]. reflexivity.
  - intros eff mo' evs. cbn [nstep]. unfold efferr. tauto.
Qed.

Lemma set_tid_factsA : forall ms mo,
  at_node segs NSetTid ms -> minvA mo -> m_halted mo = None -> node_factsA ms mo NSetTid.
Proof.
  intros ms mo Hsvc Hminv Hh.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms (Z_to_bv 64 96)) eff mo = check_set_tid_address eff mo).
  { intros eff. dispatch 96 arm_set_tid_address. reflexivity. }
  assert (SHAPE : forall eff mo' evs, nstep NSetTid mo eff mo' evs -> exists t, eff = eff0 t /\ (mo' = mo \/ (mo' = with_tid t mo /\ 0 < bv_unsigned t < PID_MAX_ENVELOPE))).
  { intros eff mo' evs (_ & t & -> & Ht). exists t. split; [reflexivity|]. destruct (m_tid mo); [destruct Ht as [_ ->]; auto| destruct Ht as [Hr ->]; auto]. }
  exists (Z_to_bv 64 96). split; [exact Hsvc|]. split; [|split; [|split]].
  - intros [ret ws zs us cs ci] mo' evs. rewrite Hchk. unfold check_set_tid_address. cbn [nstep ceff]. unfold eff0. intros H.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    assert (R : evs = [] /\ exists t : word, mkEffectU ret [] [] [] [] [] = {| eff_ret := t; eff_writes := []; eff_zeros := []; eff_unmaps := []; eff_copies := []; eff_copyins := [] |}
             /\ match m_tid mo with Some t0 => t = t0 /\ mo' = mo | None => 0 < bv_unsigned t < PID_MAX_ENVELOPE /\ mo' = with_tid t mo end).
    { destruct (m_tid mo) as [t0|].
      * destruct (bv_eqb ret t0) eqn:E; [|discriminate]. apply bv_eqb_eq in E. inversion H; subst.
        split; [reflexivity|]. exists t0. auto.
      * destruct ((0 <? bv_unsigned ret) && (bv_unsigned ret <? PID_MAX_ENVELOPE)) eqn:E; [|discriminate].
        inversion H; subst. apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
        split; [reflexivity|]. exists ret. auto. }
    split; [exact R|]. split.
    + destruct R as (_ & t & _ & Ht). destruct (m_tid mo); [destruct Ht as [_ ->]; apply vm_same_refl| destruct Ht as [_ ->]; apply vm_same_with_tid].
    + intros P _. cbn. apply Forall_nil.
  - intros eff mo' evs HP. exists (@nil (word * nat)). rewrite Hchk. unfold check_set_tid_address.
    destruct HP as (-> & t & -> & Ht). unfold with_ci, eff0. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
    destruct (m_tid mo) as [t0|].
    + destruct Ht as [-> ->]. rewrite bv_eqb_refl. reflexivity.
    + destruct Ht as [[H1 H2] ->]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
  - intros [ret ws zs us cs ci]. rewrite Hchk. unfold check_set_tid_address.
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (m_tid mo); [destruct (bv_eqb _ _); discriminate| destruct (_ && _); discriminate].
  - intros eff mo' evs HP. destruct (SHAPE _ _ _ HP) as (t & _ & [-> | [-> Ht]]); [auto|].
    split; [macc; exact Hh|]. apply minvA_with_tid; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End PerNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Kit.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_svc_invA : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> sstep segs (mkCfg ms mo) evs X ->
  (exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\ m_halted mo' = None /\
        materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\ X = SNext (mkCfg (nret ms eff) mo''))
  \/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = None /\
        materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\ evs = [] /\ X = SError)
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
        m_killed mo' = None /\
        evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
        evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))      (* [comment removed for export] *)
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. split; [eassumption|]. split; [eassumption|]. split; [eassumption| reflexivity].
  - right; left. eexists _, _, _. split; [eassumption|]. split; [eassumption|]. split; [eassumption| split; reflexivity].
  - right; right; left. eexists _, _, _, _. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; reflexivity.
  - right; right; right; left. eexists _, _, _, _. split; [eassumption|]. split; [eassumption|]. split; reflexivity.
  - right; right; right; right. auto.
Qed.

(* [comment removed for export] *)
Section WithLI.
Variables (S : word -> Prop) (N : nat) (EB : Z).
Theorem neutral_kit : forall (P : acc -> Prop) n ms mo,
  node_factsA segs ms mo n -> node_policy segs P n ms ->
  (forall x, P x -> acc_ok (m_vm_lazy mo) S x) ->
  KIA S N EB mo ->
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     exists eff mo' mo'', X = SNext (mkCfg (nret ms eff) mo'') /\ nstep n mo eff mo' evs /\ magree mo' mo'' /\ KIA S N EB mo'')
  /\ (forall eff mo' evs, nstep n mo eff mo' evs ->
     exists mo'', magree mo' mo'' /\ KIA S N EB mo'' /\ sstep segs (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo'')))
  /\ (exists eff mo' evs, nstep n mo eff mo' evs).
Proof.
  intros P n ms mo (x8 & Hsvc & Hcmp & Hsnd & Hnu & Hpres) Hpol HPS (HLI & Hmi & Hh).
  (* [comment removed for export] *)
  assert (MAT : forall eff mo' evs, check_syscall (sys_input segs ms x8) eff mo = CheckOk mo' evs ->
            nstep n mo (ceff eff) mo' evs /\
            exists M', materialize_model_accesses mo' (syscall_effect_accesses eff) = Some (with_vm_backing (m_vm_lazy mo') M' mo')
                       /\ KIA S N EB (with_vm_backing (m_vm_lazy mo') M' mo')).
  { intros eff mo' evs Hc. destruct (Hcmp _ _ _ Hc) as (Hn & Hvm & Hacc). split; [exact Hn|].
    destruct (Hpres _ _ _ Hn) as [Hh' Hmi'].
    assert (HLI' : LI S N EB mo') by (eapply LI_vm_same; eauto).
    assert (Hrs : Forall (acc_ok (m_vm_lazy mo') S) (syscall_effect_accesses eff)).
    { rewrite (lazy_vm_same _ _ Hvm). eapply Forall_impl; [exact HPS|]. apply Hacc. exact Hpol. }
    destruct (materialize_ok S N EB mo' _ HLI' Hrs) as (M' & Hm & HLI'').
    exists M'. split; [exact Hm|]. split; [exact HLI''|]. split.
    - apply minvA_with_vm_backing. exact Hmi'.
    - destruct mo' as [fd [maps lazy mat] io fs proc lim tm]. exact Hh'. }
  split; [|split].
  - intros evs X Hst. destruct (sstep_svc_invA _ _ _ _ _ Hsvc Hst)
      as [(eff & mo' & mo'' & Hs & Hh' & Hm & ->) | [(eff & mo' & evs0 & Hs & Hh' & Hm & -> & ->) | [(eff & mo' & evs0 & code & Hs & Hh' & Hk' & -> & ->) | [(eff & mo' & evs0 & sig & Hs & Hk' & -> & ->) | (Hs & -> & ->)]]]].
    + apply check_syscall_ok_iff in Hs. destruct (MAT _ _ _ Hs) as (Hn & M' & Hm' & HK).
      rewrite Hm' in Hm. inversion Hm; subst.
      exists (ceff eff), mo', (with_vm_backing (m_vm_lazy mo') M' mo'). rewrite nret_ceff.
      split; [reflexivity|]. split; [exact Hn|]. split; [exists M'; reflexivity| exact HK].
    + exfalso. apply check_syscall_ok_iff in Hs. destruct (MAT _ _ _ Hs) as (_ & M' & Hm' & _). rewrite Hm' in Hm. discriminate.
    + exfalso. apply check_syscall_ok_iff in Hs. destruct (MAT _ _ _ Hs) as (Hn & _). apply Hpres in Hn. destruct Hn; congruence.
    + exfalso. apply check_syscall_ok_iff in Hs. destruct (MAT _ _ _ Hs) as (Hn & _). apply Hpres in Hn. destruct Hn as [Hh0 _].
      rewrite (m_killed_of_m_halted_none _ Hh0) in Hk'. discriminate Hk'.
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. exact (Hnu _ Hs).
  - intros eff mo' evs HP. destruct (Hsnd _ _ _ HP) as [ci Hc].
    destruct (MAT _ _ _ Hc) as (_ & M' & Hm & HK).
    exists (with_vm_backing (m_vm_lazy mo') M' mo'). split; [exists M'; reflexivity|]. split; [exact HK|].
    rewrite <- (nret_with_ci ms ci eff). unfold nret.
    eapply sstep_syscall; [exact Hh|exact Hsvc| | exact (proj1 (Hpres _ _ _ HP)) | exact Hm].
    apply check_syscall_ok_iff. exact Hc.
  - pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
    + exists (ceff eff), mo', evs. apply (proj1 (Hcmp _ _ _ ltac:(apply check_syscall_ok_iff; exact Hr))).
    + exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. exact (Hnu _ Hr).
Qed.
End WithLI.

(* [comment removed for export] *)
Definition neutral_node (n : node) : Prop :=
  match n with
  | NWrite _ _ | NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ | NSetTid => True
  | _ => False
  end.

Lemma neutral_factsA : forall n ms mo,
  neutral_node n -> at_node segs n ms -> minvA mo -> m_halted mo = None -> node_factsA segs ms mo n.
Proof.
  intros n ms mo Hn Hat Hmi Hh. destruct n; try contradiction.
  - apply write_factsA; assumption.
  - apply writev_factsA; assumption.
  - apply open_factsA; assumption.
  - apply read_factsA; assumption.
  - apply close_factsA; assumption.
  - apply ioctl_factsA; assumption.
  - apply set_tid_factsA; assumption.
Qed.

(* [comment removed for export] *)
Lemma exit_kitA : forall ms mo c x8,
  at_node segs (NExit c) ms -> ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  let code := bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) in
  (forall evs X, sstep segs (mkCfg ms mo) evs X ->
     X = SNext (mkCfg ms (with_halted code mo)) /\ evs = [ExitEv code (m_fs mo)])
  /\ sstep segs (mkCfg ms mo) [ExitEv code (m_fs mo)] (SNext (mkCfg ms (with_halted code mo))).
Proof.
  intros ms mo c x8 Hat Hsvc Hh. apply (exit_kit segs ms mo x8); [exact Hsvc| exact Hh| |].
  - intros eff mo' evs. rewrite (exit_check segs ms mo c x8 eff Hat Hsvc). rewrite check_ret_only_ok_iff. unfold eff0. tauto.
  - intros eff. rewrite (exit_check segs ms mo c x8 eff Hat Hsvc). apply check_ret_only_no_unmodeled.
Qed.

End Kit.
End RC__2.
