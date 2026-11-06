(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app : forall o1 o2 K, t_eq (t_emit (o1 ++ o2) K) (t_emit o1 (t_emit o2 K)).
Proof.
  intros o1 o2 K tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HK)].
    + destruct (is_prefix_app_split o1 o2 tr Hp) as [Hp1 | (b' & -> & Hp2)]; [left; exact Hp1|].
      right. exists b'. split; [reflexivity|]. left. exact Hp2.
    + right. exists (o2 ++ tr'). split; [rewrite app_assoc; reflexivity|]. right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp2 | (tr'' & -> & HK)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. clear K. revert o2 tr' Hp2. induction o1 as [|x o1 IH]; intros o2 tr' Hp2; cbn; [exact Hp2|]. split; [reflexivity| apply IH; exact Hp2].
    + right. exists tr''. split; [rewrite app_assoc; reflexivity| exact HK].
Qed.

Lemma t_eq_emit : forall o K K', t_eq K K' -> t_eq (t_emit o K) (t_emit o K').
Proof.
  intros o K K' H tr. unfold t_emit. split; intros [Hp | (tr' & -> & HK)]; try (left; exact Hp); right; exists tr'; split; auto; apply H; exact HK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Local Notation impl := (ITree.impl segs (at_node segs)).

Lemma impl_bind_inv : forall {A B} (t : itree node A) (f : A -> itree node B) Q ms,
  impl (ITree.bind node t f) Q ms -> impl t (fun r ms' => impl (f r) Q ms') ms.
Proof.
  intros A B t. induction t as [r | n k IH]; intros f Q ms H; cbn [ITree.bind] in H; cbn.
  - apply evt_done. exact H.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rzt {A} (t : itree node (exc A)) (mo : Model) (out : list event) (R : A -> Prop) : Prop :=
  forall (Q : A -> machine_state -> Prop) (ms : machine_state) (K : TSet),
    MOK mo ->
    impl t (epost Q) ms ->
    K [] ->
    (forall a ms', Q a ms' -> R a -> realizes segs (mkCfg ms' mo) K) ->
    realizes segs (mkCfg ms mo) (t_emit out K).

Lemma rz_emit_nil : forall c K, realizes segs c K -> realizes segs c (t_emit [] K).
Proof.
  intros c K H. eapply rz_conseq; [exact H|]. apply t_eq_sym. apply t_emit_nil_eq. exact (realizes_nonempty _ _ _ H).
Qed.

Lemma rzt_ret : forall {A} (a : A) mo (R : A -> Prop), R a -> rzt (ITree.Ret (Ok a)) mo [] R.
Proof.
  intros A a mo R Ha Q ms K HM Hi HK Hc. cbn in Hi. apply rz_emit_nil.
  eapply rz_evt; [exact HM| exact Hi|]. intros ms' HQ. apply (Hc a ms'); [exact HQ| exact Ha].
Qed.

Lemma rzt_mono : forall {A} (t : itree node (exc A)) mo out (R R' : A -> Prop),
  rzt t mo out R -> (forall a, R a -> R' a) -> rzt t mo out R'.
Proof. intros A t mo out R R' H HR Q ms K HM Hi HK Hc. apply (H Q ms K HM Hi HK). intros a ms' HQ Ha. apply (Hc a ms'); auto. Qed.

Lemma rzt_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo o1 o2 (R1 : A -> Prop) (R2 : B -> Prop),
  rzt t mo o1 R1 -> (forall a, R1 a -> rzt (f a) mo o2 R2) -> rzt (ebind t f) mo (o1 ++ o2) R2.
Proof.
  intros A B t f mo o1 o2 R1 R2 Ht Hf Q ms K HM Hi HK Hc.
  eapply rz_conseq; [| apply t_eq_sym; apply t_emit_app].
  unfold ebind in Hi. apply impl_bind_inv in Hi.
  apply (Ht (fun a ms' => impl (f a) (epost Q) ms') ms (t_emit o2 K) HM).
  - eapply impl_mono; [exact Hi|]. intros [|a] ms'; cbn; [intros _; exact I| intros H; exact H].
  - apply t_emit_has_nil.
  - intros a ms' Hfa Ha. apply (Hf a Ha Q ms' K HM Hfa HK Hc).
Qed.

(* [comment removed for export] *)
Lemma rzt_mbind : forall {St A B} (m : M St A) (f : A -> M St B) (s : St) mo o1 o2 (R1 : A * St -> Prop) (R2 : B * St -> Prop),
  rzt (m s) mo o1 R1 -> (forall a s', R1 (a, s') -> rzt (f a s') mo o2 R2) -> rzt (mbind m f s) mo (o1 ++ o2) R2.
Proof.
  intros St A B m f s mo o1 o2 R1 R2 Hm Hf. unfold mbind. eapply rzt_ebind; [exact Hm|]. intros [a s'] H. apply Hf. exact H.
Qed.

Lemma rzt_mbind_nil_l : forall {St A B} (m : M St A) (f : A -> M St B) (s : St) mo o (R1 : A * St -> Prop) (R2 : B * St -> Prop),
  rzt (m s) mo [] R1 -> (forall a s', R1 (a, s') -> rzt (f a s') mo o R2) -> rzt (mbind m f s) mo o R2.
Proof. intros. change o with ([] ++ o). eapply rzt_mbind; eauto. Qed.

Lemma rzt_mbind_nil_r : forall {St A B} (m : M St A) (f : A -> M St B) (s : St) mo o (R1 : A * St -> Prop) (R2 : B * St -> Prop),
  rzt (m s) mo o R1 -> (forall a s', R1 (a, s') -> rzt (f a s') mo [] R2) -> rzt (mbind m f s) mo o R2.
Proof. intros. rewrite <- (app_nil_r o). eapply rzt_mbind; eauto. Qed.

Lemma rzt_mret : forall {St A} (a : A) (s : St) mo (R : A * St -> Prop), R (a, s) -> rzt (mret a s) mo [] R.
Proof. intros. unfold mret. apply rzt_ret. exact H. Qed.

Lemma rzt_mupd : forall {St} (f : St -> St) (s : St) mo (R : unit * St -> Prop), R (tt, f s) -> rzt (mupd f s) mo [] R.
Proof. intros. unfold mupd. apply rzt_ret. exact H. Qed.

Lemma rzt_mget : forall {St} (s : St) mo (R : St * St -> Prop), R (s, s) -> rzt (mget s) mo [] R.
Proof. intros. unfold mget. apply rzt_ret. exact H. Qed.

(* [comment removed for export] *)
Lemma rzt_unr_false : forall {A} mo out (R : A -> Prop), False -> rzt (ITree.Ret Unr) mo out R.
Proof. intros A mo out R []. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_at_ioctl : forall ms mo (fd req : Z) e K,
  at_node segs (NIoctl fd req) ms -> MOK mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  e <> FdUrandom ->
  realizes segs (mkCfg (nret ms (efferr ENOTTY)) mo) K ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros ms mo fd req e K Hat [Hh Hl] Hlk Hnd HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & -> & H10 & H11).
  eapply rz_det_silent; [exact Hh | exact Hsvc | | | | exact HK]; [| exact Hh | exact Hl].
  intros o. rewrite (syscall_spec_29 _ mo o) by (rewrite in_sysno_pending; reflexivity).
  rewrite in_a0_si, in_a1_si, H10, H11, fd32_id by (rewrite u64_lit; lia).
  apply (ioctl_tty_outcome (Z_to_bv 64 fd) _ _ mo e o Hlk Hnd). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma at_node_writev_facts : forall ms (fd : Z) bufs,
  at_node segs (NWritev fd bufs) ms ->
  ms_svc_pending ms = Some (Z_to_bv 64 66) /\ (fd = 1 \/ fd = 2) /\ areg ms 10 = Z_to_bv 64 fd
  /\ areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\ (length bufs <= 1024)%nat /\ Z.of_nat (length (concat bufs)) < 2^63
  /\ exists iovs, bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE   (* [comment removed for export] *)
                  /\ Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs
                  /\ bytes_in (ms_read_byte ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs)
                  /\ Forall2 (iov_ok (ms_read_byte ms)) iovs bufs.
Proof.
  intros ms fd bufs Hat. cbn [at_node] in Hat.
  destruct Hat as (Hsvc & Hfd & H10 & H12 & Hcnt & Hlen & Hrom & iovs & Htask & Hbtask & Harr & Hbufs).
  repeat (split; [assumption|]). exists iovs. split; [exact Htask|]. split; [exact Hbtask|]. split.
  - apply (bytes_at_in segs); [exact Hrom| exact Harr].
  - clear Harr H12 Hcnt Htask Hbtask. revert Hlen. induction Hbufs as [| iov bs iovs' bss' [Hl Hb] _ IH]; intros Hlen; [constructor|].
    cbn [concat] in Hlen. rewrite length_app in Hlen.
    constructor; [| apply IH; lia].
    split; [exact Hl|]. split; [lia|]. apply (bytes_at_in segs); [exact Hrom| exact Hb].
Qed.

Lemma rz_at_writev_wall : forall ms mo (fd : Z) bufs K,
  at_node segs (NWritev fd bufs) ms -> MOK mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (1 <= length bufs)%nat ->
  let bs := concat bufs in
  1 <= Z.of_nat (length bs) <= 67108864 ->   (* [comment removed for export] *)
  K [] ->
  (forall k, (1 <= k <= length bs)%nat ->
     realizes segs (mkCfg (nret ms (eff0 (Z_to_bv 64 (Z.of_nat k)))) mo) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K)) ->
  realizes segs (mkCfg ms mo) (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs) K).
Proof.
  intros ms mo fd bufs K Hat [Hh Hl] Hlk Hlen bs Hb HK0 HK.
  destruct (at_node_writev_facts _ _ _ Hat) as (Hsvc & Hfd & H10 & H12 & Hcnt & Hlen63 & iovs & Htask & Hbtask & Harr & Hbufs).
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose proof (Forall2_length Hbufs) as Hleneq.
  unshelve epose proof (writev_outcome_i (sys_input segs ms (Z_to_bv 64 66)) mo fd (areg ms 11) iovs bufs _ _ _ Hlk _ _ _ _ _ _ _ _ _) as Hiff.
  { rewrite in_sysno_pending; apply u64_lit; lia. }
  { rewrite in_a0_si; exact H10. }
  { lia. }
  { rewrite in_a1_si; reflexivity. }
  { rewrite in_a2_si, Hleneq; exact H12. }
  { lia. }
  { rewrite in_mem_si; exact Harr. }
  { rewrite in_mem_si; exact Hbufs. }
  { rewrite Hleneq; exact Htask. }
  { exact Hbtask. }
  { subst bs; lia. }
  { subst bs; lia. }
  cbv zeta in Hiff. fold bs in Hiff.
  set (CA := copy_iovecs_accesses _ _ _) in Hiff.
  eapply rz_conseq.
  - apply (rz_outcomes segs ms mo (Z_to_bv 64 66) (wr_index bs)
             (fun i => mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig i)))
             (fun _ => mo)
             (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
             (fun i => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn (proj1_sig i) bs)) K) (wr_full bs Hnb) Hh Hsvc eq_refl).
    + intros o. rewrite Hiff. split.
      * intros (k & Hk & ->). exists (exist _ k Hk). reflexivity.
      * intros [[k Hk] ->]. exists k. split; [exact Hk | reflexivity].
    + intros _; exact Hh.
    + intros _; exact Hl.
    + intros [k Hk]. cbn [proj1_sig]. apply (HK k Hk).
  - apply t_alt_wall; [exact HK0 | lia].
Qed.

Lemma rz_at_writev_zero : forall ms mo (fd : Z) bufs K,
  at_node segs (NWritev fd bufs) ms -> MOK mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (1 <= length bufs)%nat ->
  concat bufs = [] ->
  realizes segs (mkCfg (nret ms (eff0 (Z_to_bv 64 0))) mo) K ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros ms mo fd bufs K Hat [Hh Hl] Hlk Hlen Hnil HK.
  destruct (at_node_writev_facts _ _ _ Hat) as (Hsvc & Hfd & H10 & H12 & Hcnt & Hlen63 & iovs & Htask & Hbtask & Harr & Hbufs).
  pose proof (Forall2_length Hbufs) as Hleneq. rewrite <- Hleneq in H12, Hlen, Hcnt, Htask.
  pose proof (iovs_total_ok _ _ _ Hbufs) as Htot. rewrite Hnil in Htot. cbn in Htot.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
  apply (rz_det_silent segs ms mo (Z_to_bv 64 66)
           (with_copyins (copy_iovecs_accesses (in_mem (sys_input segs ms (Z_to_bv 64 66))) (areg ms 11)
                            (word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs)))))
                         (mkEffect (Z_to_bv 64 0) [] [])) mo); [exact Hh | exact Hsvc | | exact Hh | exact Hl | exact HK].
  intros o. rewrite (syscall_spec_66 _ mo o) by (rewrite in_sysno_pending; apply u64_lit; lia).
  rewrite in_a0_si, in_a1_si, in_a2_si, H10, H12, fd32_id by (rewrite u64_lit; lia).
  apply (writev_chan_zero_outcome _ _ _ _ mo o (Z_to_bv 64 fd) iovs Hlk).
  - apply w_is0_pos. rewrite u64_lit; lia.
  - unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity.
  - apply w_is0_pos. rewrite u64_lit; lia.
  - unfold IOV_MAX. rewrite u64_lit; lia.
  - rewrite Hwn, in_mem_si. rewrite <- (wa_unsigned_id (areg ms 11)). apply copy_iovecs_aux_bytes_in; [exact Harr|].
    eapply Forall_impl; [|exact (Forall2_iov_ok_lens _ _ _ Hbufs)]. intros [b l] Hb. cbn [snd] in *. rewrite Hnil in Hb. cbn in Hb. lia.
  - apply access_okb_intro_Z; rewrite u64_lit by lia; lia.
  - unfold iovs_access_okb. apply forallb_forall. intros [b l] Hin.
    rewrite Forall_forall in Hbtask. specialize (Hbtask _ Hin). cbn [fst snd] in *.
    apply access_okb_intro. exact Hbtask.
  - exact Htot.
  - vm_compute. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rzt_ioctl : forall {St} (st : St) mo (fd : Z) e (R : sret * St -> Prop),
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  e <> FdUrandom ->
  (forall err, R (SErr err, st)) ->
  rzt (msys (NIoctl fd TIOCGWINSZ) dec_ioctl st) mo [] R.
Proof.
  intros St st mo fd e R Hlk Hnd HR Q ms K HM Hi HK Hc. unfold msys, enode in Hi. cbn [ITree.impl] in Hi.
  apply rz_emit_nil. eapply rz_evt; [exact HM| exact Hi|]. intros ms1 [Hat Hk].
  eapply rz_at_ioctl; [exact Hat| exact HM| exact Hlk| exact Hnd|].
  specialize (Hk (efferr ENOTTY)). unfold dec_ioctl in Hk. rewrite dec_plain_err in Hk by (unfold ENOTTY; lia).
  cbn [ITree.impl epost] in Hk.
  eapply rz_evt; [exact HM| exact Hk|]. intros ms2 HQ. apply (Hc _ _ HQ). apply HR.
Qed.

Lemma to_bytes_concat : forall (iov : list (list Z)), concat (map to_bytes iov) = to_bytes (concat iov).
Proof. intros iov. unfold to_bytes. rewrite concat_map. reflexivity. Qed.

Lemma to_bytes_skipn : forall n (l : list Z), to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.

Lemma to_bytes_length' : forall (l : list Z), length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

(* [comment removed for export] *)
Lemma rzt_wv_loop : forall {St} (st : St) mo (fd : Z) (fuel : nat) (iov : list (list Z)),
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (length iov = 1%nat \/ length iov = 2%nat) ->
  wv_total iov < Z.of_nat fuel -> wv_total iov <= 67108864 ->   (* [comment removed for export] *)
  rzt (mloop fuel (wv_body fd) iov st) mo (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (concat iov))) (fun p => snd p = st).
Proof.
  intros St st mo fd fuel. induction fuel as [|fuel IH]; intros iov Hlk Hsh Hfuel Hmax.
  { pose proof (wv_total_nonneg iov). lia. }
  intros Q ms K HM Hi HK Hc.
  cbn [mloop] in Hi. cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hi.
  eapply rz_evt; [exact HM| exact Hi|]. intros ms1 [Hat Hk].
  assert (Hlen : (1 <= length (map to_bytes iov))%nat) by (rewrite length_map; lia).
  pose proof (wv_total_nonneg iov) as T0.
  assert (TOT : Z.of_nat (length (concat (map to_bytes iov))) = wv_total iov).
  { rewrite to_bytes_concat, to_bytes_length'. reflexivity. }
  destruct (Z.eq_dec (wv_total iov) 0) as [Z0|NZ].
  - (* [comment removed for export] *)
    eapply rz_at_writev_zero; [exact Hat| exact HM| exact Hlk| exact Hlen| |].
    { apply length_zero_iff_nil. lia. }
    specialize (Hk (eff0 (Z_to_bv 64 0))). rewrite (dec_wv_val (wv_total iov) 0) in Hk by lia.
    rewrite Z0 in Hk. cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hk.
    replace (concat iov) with (@nil Z).
    2:{ symmetry. apply length_zero_iff_nil. unfold wv_total, zlength in Z0. lia. }
    cbn [to_bytes map]. apply rz_emit_nil.
    eapply rz_evt; [exact HM| exact Hk|]. intros ms2 HQ. apply (Hc _ _ HQ). reflexivity.
  - rewrite <- to_bytes_concat.
    eapply rz_at_writev_wall; [exact Hat| exact HM| exact Hlk| exact Hlen| lia| exact HK|].
    intros k Hk1. assert (K1 : 1 <= Z.of_nat k <= wv_total iov) by lia.
    specialize (Hk (eff0 (Z_to_bv 64 (Z.of_nat k)))). rewrite (dec_wv_val (wv_total iov) (Z.of_nat k)) in Hk by lia.
    cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hk.
    destruct (Z.eq_dec (Z.of_nat k) (wv_total iov)) as [E|NE];
      [rewrite (proj2 (Z.eqb_eq _ _) E) in Hk | rewrite (proj2 (Z.eqb_neq _ _) NE) in Hk];
      cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hk.
    + (* [comment removed for export] *)
      replace (skipn k (concat (map to_bytes iov))) with (@nil byte).
      2:{ symmetry. apply skipn_all2. lia. }
      cbn [map]. apply rz_emit_nil.
      eapply rz_evt; [exact HM| exact Hk|]. intros ms2 HQ. apply (Hc _ _ HQ). reflexivity.
    + (* [comment removed for export] *)
      rewrite to_bytes_concat, <- to_bytes_skipn.
      replace (skipn k (concat iov)) with (concat (wv_advance iov (Z.of_nat k))).
      2:{ rewrite wv_advance_concat by lia. f_equal. lia. }
      apply (IH (wv_advance iov (Z.of_nat k)) Hlk (wv_advance_shape _ _ Hsh)
               ltac:(rewrite wv_advance_total by lia; lia) ltac:(rewrite wv_advance_total by lia; lia) Q _ K HM Hk HK Hc).
Qed.

(* [comment removed for export] *)
Lemma rzt_stdio_writev : forall {St} (st : St) mo (fd : Z) (buf s : list Z),
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  zlength buf + zlength s <= 67108864 ->   (* [comment removed for export] *)
  rzt (stdio_writev fd buf s st) mo (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))) (fun p => snd p = st).
Proof.
  intros St st mo fd buf s Hlk Hmax. unfold stdio_writev.
  replace (buf ++ s) with (concat (wv_init buf s)) by (unfold wv_init; destruct buf; cbn; rewrite ?app_nil_r; reflexivity).
  apply rzt_wv_loop; [exact Hlk| apply wv_init_shape| rewrite wv_total_init; unfold zlength; lia| rewrite wv_total_init; exact Hmax].
Qed.
End WithSegs.
