(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/HaltsKitB.v, with its module paths changed; the walk lemma and the halting corollary take srealizes (YK18.v) where cgif's take realizes, because fuzz_knock's realizes (YK15.v) has a cut at a budget refusal. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/HaltsKitB.v at origin/ossv/recipes 4b6f0df50aa7 (fuzz_knock's released ASan tree); module paths changed to libdiginet/fuzz_codec. *)
(* Modified by Theorem Labs, 2026-11: copied from projects/libdiginet/fuzz_codec/proofs/lib/Reusable/HaltsKitB.v at commit 874e3397a35, its definitions ev_ok, trace_ok and shape_ok, its lemmas trace_ok_app, trace_ok_prefix and trace_ok_writes, and its walk lemma srealizes_must_exit_in, restated for libpcap/fuzz_pcap's SpinAlg.srealizes and ShapeAlg.CFG; its other lemmas and its halting corollary are left out, and the lemmas shape_ok_branch, nstep_trace_ok, texit_trace_ok, plain_traces_ok, must_exit_forced_of_srz and plain_entry are new. *)
(** Halting of a sanitizer build from the srealizes fact of its equivalence
    proof.

    [SpinAlg.srealizes] has no spinning leaf (its [srz_spin] constructor takes
    a proof of False), so an srealizes derivation is a finite tree of steps
    that covers every step of the run under [ShapeAlg.CFG] and ends in halted
    configurations.  When every trace of the realized set is [trace_ok] --
    every exit status in the allowed list and no death by a signal -- the
    configuration must exit with an allowed status ([srealizes_must_exit_in]).

    The sanitizer build's srealizes fact realizes the plain build's trace set,
    and every trace of the plain build is [trace_ok] for the statuses 0 and 2,
    because the plain build's program tree exits only with those
    ([plain_traces_ok]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.libpcap.fuzz_pcap Require Images.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common SpinAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require HaltsAdq HaltsFinal.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import Final_ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Final_asan__EquivA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SA := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.

(** The statuses the halting statements allow. *)
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

(** An event a halting run may emit: an exit with an allowed status, or any
    input or output; never a death by a signal. *)
Definition ev_ok (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv k _ => In k S
  | KillEv _ _ => False
  | _ => True
  end.

Definition trace_ok (S : list word) (tr : list event) : Prop := Forall (ev_ok S) tr.

Definition shape_ok (S : list word) (T : SA.TSet) : Prop := forall tr, T tr -> trace_ok S tr.

Lemma trace_ok_app : forall S a b, trace_ok S (a ++ b) <-> trace_ok S a /\ trace_ok S b.
Proof. intros S a b. unfold trace_ok. apply Forall_app. Qed.

Lemma trace_ok_prefix : forall S tr tr', is_prefix tr tr' -> trace_ok S tr' -> trace_ok S tr.
Proof.
  intros S tr; induction tr as [|e tr IH]; intros tr' Hp Hok.
  - constructor.
  - destruct tr' as [|e' tr']; cbn in Hp; [destruct Hp|]. destruct Hp as [<- Hp].
    inversion Hok; subst. constructor; [assumption|]. eapply IH; eauto.
Qed.

Lemma trace_ok_writes : forall S ch bs, trace_ok S (map (WriteEv ch) bs).
Proof.
  intros S ch bs. unfold trace_ok. apply Forall_forall. intros e He.
  apply in_map_iff in He as (b & <- & _). exact I.
Qed.

(** ** From an srealizes fact to [must_exit_in_at_cfg] *)

Section Srz.
Variable segs : list Segment.

Lemma shape_ok_branch : forall S (I : Type) (evs : I -> list event) (T : I -> SA.TSet) i,
  T i [] ->
  shape_ok S (SA.t_alt (fun j => SA.t_emit (evs j) (T j))) ->
  trace_ok S (evs i) /\ shape_ok S (T i).
Proof.
  intros S I evs T i H0 H. unfold shape_ok, SA.t_alt, SA.t_emit in *. split.
  - apply (H (evs i)). exists i. right. exists []. rewrite app_nil_r. split; [reflexivity | exact H0].
  - intros tr Htr. assert (Hc : trace_ok S (evs i ++ tr)).
    { apply H. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
    apply trace_ok_app in Hc. tauto.
Qed.

Theorem srealizes_must_exit_in : forall c T,
  SpinAlg.srealizes segs c T ->
  forall S, m_halted (cfg_model c) = None -> shape_ok S T ->
  must_exit_in_at_cfg SA.CFG segs S c.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq];
    intros S Hnone Hx.
  - destruct Hnode as [Hsound Hinv].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + eexists _, _. exact (Hsound i0).
    + intros e Herr. destruct (Hinv e SError Herr) as (i & _ & Habs). discriminate Habs.
    + intros e c' Hs.
      destruct (Hinv e (SNext c') Hs) as (i & -> & Hc'). injection Hc' as ->.
      destruct (shape_ok_branch S I evs T i (SpinAlg.srealizes_nonempty segs _ _ (Hcont i)) Hx) as [Hevs HTi].
      destruct (sstep_cfg_next_halts_by_exit segs SA.CFG c (evs i) (nx i) Hs)
        as [Hn | [(evs0 & code & Hevs' & Hh & Hk) | (evs0 & sig & Hevs' & Hk)]].
      * apply IH; assumption.
      * apply (must_exit_in_at_cfg_halted SA.CFG segs S (nx i) code Hh); [|exact Hk].
        rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. exact (Forall_inv Hev).
      * exfalso. rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. exact (Forall_inv Hev).
  - exfalso. apply Hh. exact Hnone.
  - destruct Hspin as [[] _].
  - apply IH; [exact Hnone|]. intros tr Htr. apply Hx. exact (proj1 (Heq tr) Htr).
Qed.

End Srz.

(** ** Every trace of the plain build is [trace_ok] for 0 and 2 *)

(** A node step emits only output bytes. *)
Lemma nstep_trace_ok : forall S n mo rsp mo' evs, nstep n mo rsp mo' evs -> trace_ok S evs.
Proof.
  intros S n mo rsp mo' evs H.
  destruct n; cbn [nstep] in H;
    first [ solve [contradiction]
          | solve [unfold write_result in H; destruct H as (_ & k & _ & _ & ->); apply trace_ok_writes]
          | solve [destruct H as (_ & -> & _); constructor]
          | solve [destruct H as [-> _]; constructor] ].
Qed.

Lemma texit_trace_ok : forall S {R} (t : itree node R) mo full,
  texit nstep nexit t mo full ->
  HaltsAdq.exits_in nstep nexit t mo (fun c => In c S) ->
  trace_ok S full.
Proof.
  intros S R t. induction t as [r|n k IH]; intros mo full Ht Hx; cbn in Ht, Hx.
  - destruct Ht.
  - destruct Hx as [HxK Hxk].
    destruct Ht as [(code & mo' & Hex & ->) | (rsp & mo' & evs & tr' & Hst & Ht' & ->)].
    + constructor; [cbn; exact (HxK code mo' Hex) | constructor].
    + apply trace_ok_app. split.
      * exact (nstep_trace_ok S n mo rsp mo' evs Hst).
      * exact (IH rsp mo' tr' Ht' (Hxk rsp mo' evs Hst)).
Qed.

Notation IMG_S := (mkImage ssegs SRCM.init_pc SRCM.phdrs) (only parsing).

(** The plain build's traces, at any budget its tree is proved at. *)
Theorem plain_traces_ok : forall limS,
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink.BLIVE
  + OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink.RMAX <= limS ->
  forall enS inp, valid_entry IMG_S enS inp -> valid_input inp ->
  shape_ok codes02 (fun tr => bh_traces (run_scfg CFG IMG_S limS enS inp) tr).
Proof.
  intros limS LIMS enS inp HvS Hvi.
  destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.Final_asan__EquivA.Final_asan.tree_ok_S limS LIMS) as [QS HS].
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (run_of_tree ssegs SRCM.init_pc SRCM.phdrs limS _ QS enS inp HimplS HleavesS HsafeS Hvi)
    as (HsoundS & _ & _).
  intros tr Htr.
  destruct (tree_traces_exits _ _ _ HleavesS (HsoundS tr Htr)) as (full & Hfull & Hp).
  apply (trace_ok_prefix codes02 tr full Hp).
  apply (texit_trace_ok codes02 _ _ full Hfull).
  exact (HaltsFinal.ptree_exits_in ssegs tbS stkS sec inp enS _).
Qed.

(** ** The assembly: srealizes at the large budget, then the forced-only
    configuration *)

Theorem must_exit_forced_of_srz : forall segs pc ph lim en inp T,
  SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) T ->
  shape_ok codes02 T ->
  must_exit_in_scfg forced_only_cfg codes02 (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim [sp brk mb rnd] inp T Hsrz Hok. cbn [must_exit_in_scfg en_sp en_brk en_mmap_base en_draw] in *.
  apply (HaltsAdq.must_exit_in_at_cfg_down forced_only_cfg SA.CFG segs codes02 _ (forced_only_cfg_least SA.CFG)).
  apply (srealizes_must_exit_in segs _ T Hsrz codes02); [reflexivity | exact Hok].
Qed.

(** Some entry of the plain build is valid on every valid input. *)
Lemma plain_entry : forall inp, valid_input inp -> exists enS, valid_entry IMG_S enS inp.
Proof.
  intros inp Hi. apply (image_brk_satisfiable_entry IMG_S inp Hi).
  exact (proj2 (proj2 OSSVerify.libpcap.fuzz_pcap.Images.plain_wf)).
Qed.
