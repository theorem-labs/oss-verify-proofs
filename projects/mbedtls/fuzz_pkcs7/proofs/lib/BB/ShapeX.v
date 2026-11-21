(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (node_ok's third conjunct, sys_rob, on the write, exit, munmap, mmap and channel-write nodes, with Vdso, RomBase and RomWrite imported; the access_okb premise on node_write1, rz_write1, node_write_ch and rz_write_ch; rz_munmap takes munmap's refusal branch through the new rz_silent_all; the place_declined_b premise on rz_mmap; the using attribute dropped on three lemmas). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatSim MmapSim AllocSim WallSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require Import RomBase.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import RomWrite.

Import ListNotations.
Open Scope bv_scope.

Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T. Proof. reflexivity. Qed.

Lemma t_writes_pick_cons : forall buf bufs T,
  t_writes_pick (buf :: bufs) T = t_write_ch (Z_to_bv 64 1) buf (t_writes_pick bufs T).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
  T [] -> (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
  intros ch rest T HT Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

Section WithSegs.
Variable segs : list Segment.
Local Notation node_ok := (Shape.node_ok segs) (only parsing).
Local Notation realizes := (Shape.realizes segs) (only parsing).
Local Notation realizes_nonempty := (Shape.realizes_nonempty segs) (only parsing).
Local Notation realizes_pclosed := (Shape.realizes_pclosed segs) (only parsing).
Local Notation rz_silent1 := (Shape.rz_silent1 segs) (only parsing).
Local Notation rz_emit1 := (Shape.rz_emit1 segs) (only parsing).
Local Notation rz_alt2 := (Shape.rz_alt2 segs) (only parsing).
Local Notation node_instr := (Shape.node_instr segs) (only parsing).
Local Notation rz_step := (Shape.rz_step segs) (only parsing).
Local Notation rz_msteps := (Shape.rz_msteps segs) (only parsing).
Local Notation msteps := (Shape.msteps segs) (only parsing).
Local Notation rz_node := (@Shape.rz_node segs) (only parsing).
Local Notation rz_halt := (@Shape.rz_halt segs) (only parsing).
Local Notation rz_conseq := (@Shape.rz_conseq segs) (only parsing).

(* [comment removed for export] *)
Lemma rz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok c I (fun _ => []) nx ->
  (forall i, realizes (nx i) T) ->
  realizes c T.
Proof.
  intros c I nx T i0 Hnode HT.
  assert (HT0 : T []) by (eapply realizes_nonempty; apply (HT i0)).
  apply (rz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

Lemma node_write1 : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb. split; [|split].
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_inv segs ms model x8 buf e st
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
  - exact (write1_rob segs ms model x8 buf Hfd Hsvc Hno Hg Hr Hbm).
Qed.

Lemma rz_write1 : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1 ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split; [|split].
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
    + apply (sys_rob_exit segs ms model x8 Hsvc). exact Hx8.
  - apply rz_halt. split; [exists (ms_gpr ms 0); reflexivity | apply m_killed_with_halted].
Qed.

(* [comment removed for export] *)
Lemma rz_munmap : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  (forall e, In e munmap_errnos ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) T) ->
  realizes (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs HA HB.
  apply (rz_silent_all (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
           (fun i => match i with
              | inl (exist _ e _) =>
                  mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
              | inr _ =>
                  mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
              end) T (inr tt)).
  - split; [|split].
    + intros [[e He] | []]; cbn.
      * rewrite <- (apply_effect_no_write ms (errno_ret e)).
        apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
                 model model []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply munmap_fail_ok; assumption.
        -- exact Hh.
        -- apply materialize_model_accesses_no_lazy. exact Hlazy.
      * apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                 (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                 (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply munmap_ok; assumption.
        -- rewrite munmap_model_halted; exact Hh.
        -- apply materialize_model_accesses_no_lazy.
           exact (munmap_model_no_lazy _ _ _ Hlazy).
    + intros e st Hss.
      destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
        as [-> [(er & Her & ->) | ->]].
      * exists (inl (exist _ er Her)). split; reflexivity.
      * exists (inr tt). split; reflexivity.
    + apply (sys_rob_memfree segs ms model x8 Hsvc). rewrite Hno. exact memfree_215.
  - intros [[e He] | []]; cbn; [exact (HA e He) | exact HB].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mmap : forall ms model x8 A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  (forall e, In e mmap_errnos ->
     realizes (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
     realizes (mkCfg (advance_past_svc
                       (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
                     (mmap_model a (page_round_up (ms_gpr ms 1)) model)) B) ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  realizes (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs Hdecl HA HB Hex.
  set (n := page_round_up (ms_gpr ms 1)).
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
  destruct Hex as [a0 Ha0].
  pose (IA := {e : Z | In e mmap_errnos}).
  pose (IB := {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}).
  pose (nx := fun (i : IA + IB) =>
    match i with
    | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
    | inr (exist _ a _) =>
        mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)])))
              (mmap_model a n model)
    end).
  apply (rz_alt2 (mkCfg ms model) IA IB nx A B
           (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - split; [|split].
    + intros [[e He] | [a Ha]]; cbn.
      * rewrite <- (apply_effect_no_write ms (errno_ret e)).
        apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
                 model model []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply mmap_fail_ok; assumption.
        -- exact Hh.
        -- apply materialize_model_accesses_no_lazy. exact Hlazy.
      * apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
                 (mmap_model a n model) (mmap_model a n model) []).
        -- exact Hh.
        -- exact Hsvc.
        -- apply mmap_succ_ok; assumption.
        -- rewrite mmap_model_halted; exact Hh.
        -- apply materialize_model_accesses_no_lazy.
           exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
    + intros e st Hss.
      destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hdecl Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      * exists (inl (exist _ er Her)). split; reflexivity.
      * exists (inr (exist _ a Ha)). split; reflexivity.
    + apply (sys_rob_memfree segs ms model x8 Hsvc). rewrite Hno. exact memfree_222.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

End WithSegs.

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.

Lemma t_writes_ch_pick_cons : forall ch buf bufs T,
  t_writes_ch_pick ch (buf :: bufs) T = t_write_ch ch buf (t_writes_ch_pick ch bufs T).
Proof. reflexivity. Qed.

Lemma node_write_ch : forall segs ms model fd ch x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok segs (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb. split; [|split].
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
    rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
                  [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model
             model (map (WriteEv ch) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + eapply write_ch_ok_n; eassumption.
    + exact Hh.
    + apply materialize_model_accesses_no_lazy. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_write_ch_inv segs fd ch H32 ms model x8 buf e st
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
  - exact (write_ch_rob segs ms model x8 fd ch buf Hfdc H32 Hsvc Hno Hg Hr Hbm).
Qed.

Lemma rz_write_ch : forall segs ms model fd ch x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model -> fd32 fd = fd ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes segs
       (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes segs (mkCfg ms model) (t_write_ch ch buf T).
Proof.
  intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node segs (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - eapply node_write_ch; eassumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

