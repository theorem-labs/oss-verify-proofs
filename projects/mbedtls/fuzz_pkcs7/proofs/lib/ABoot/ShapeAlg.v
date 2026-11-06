(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ShapeAlg () : Init.string Init.list := ["t_alt"; "wr_index"; "t_emit"; "Corelib.Lists.ListDef.map"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Specif.proj1_sig"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.and"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.list"; "TSet"; "Corelib.Init.Logic.eq"; "t_writes_pick"; "Corelib.Init.Datatypes.cons"; "t_write_ch"; "stdpp.bitvector.definitions.Z_to_bv"; "t_writes"; "t_writes_ch"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "Corelib.Init.Logic.iff"; "t_exit"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.ABoot.CatSim.wevents_ch"; "LinuxProcessSemantics.LinuxProcessSem.State.ExitEv"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.ABoot.CatSim.wevents"; "t_eq"; "Corelib.Lists.ListDef.skipn"; "Corelib.Lists.ListDef.Forall"; "Stdlib.Lists.List.fold_right"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.ABoot.CatSim.wpick"; "t_alt2"; "OSSVerify.KrLib.ABoot.MmapSim.two_traces"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "WithSegs.node_ok"; "Corelib.Init.Datatypes.unit"; "WithSegs.realizes"; "Corelib.Init.Datatypes.sum"; "Corelib.Init.Datatypes.inl"; "Corelib.Init.Datatypes.inr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "OSSVerify.KrLib.ABoot.CatSim.fd1chan"; "Corelib.Init.Datatypes.Some"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes"; "OSSVerify.KrLib.ABoot.CatSim.buf_modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "OSSVerify.KrLib.ABoot.ExitSim.is_exit_no"; "stdpp.bitvector.definitions.bv_and"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_args_ok"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_eff"; "OSSVerify.KrLib.ABoot.MmapSim.munmap_model"; "OSSVerify.KrLib.ABoot.MmapSim.page_round_up"; "OSSVerify.KrLib.ABoot.MmapSim.mmap_args_ok"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.ABoot.MmapSim.grant_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "OSSVerify.KrLib.ABoot.MmapSim.mmap_model"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_corun"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.outcome"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.is_error"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_cosafe"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_trace_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_equiv"; "LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.target_alloc_limit"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"; "OSSVerify.KrLib.ABoot.CatSim.to_wexit"; "OSSVerify.KrLib.ABoot.CatSim.bufs_modeled"; "OSSVerify.KrLib.ABoot.WallSim.to_wall"; "OSSVerify.KrLib.ABoot.WallSim.to_wall_tail"; "OSSVerify.KrLib.ABoot.WallSim.to_wallexit"; "OSSVerify.KrLib.ABoot.MmapSim.twm"; "OSSVerify.KrLib.ABoot.MmapSim.twm_pend"; "OSSVerify.KrLib.ABoot.MmapSim.twm_tail"; "OSSVerify.KrLib.ABoot.MmapSim.tmw"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "OSSVerify.KrLib.ABoot.AllocSim.to_outcomes"; "t_outcomes"; "OSSVerify.KrLib.ABoot.AllocSim2.two_outcomes"; "t_writes_ch_pick"; "OSSVerify.KrLib.ABoot.CatSim.fdchan"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.fd32"; "node_ok"; "OSSVerify.KrLib.ABoot.CatSim.to_wexit_ch"].


(* [comment removed for export] *)

Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
  induction l as [|x l IH]; intros m a H.
  - destruct a; [apply is_prefix_nil | cbn in H; contradiction].
  - destruct a as [|y a]; cbn in *; [exact I|].
    destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
  induction l as [|x l IH]; intros a b H.
  - right. exists b. split; [reflexivity | exact H].
  - destruct b as [|y b]; cbn in H; [left; exact I|].
    destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
    + left. cbn. split; [reflexivity | exact Hp].
    + right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T. Proof. firstorder. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T. Proof. firstorder. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof. firstorder. Qed.

(* [comment removed for export] *)
Definition t_nil : TSet := fun tr => tr = [].

(* [comment removed for export] *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.

(* [comment removed for export] *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(* [comment removed for export] *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(* [comment removed for export] *)
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet := ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "(0.(1.O2.)Li,(1.O2.)(2.(3.(4.&8.)$5.(6.O3.)(7.(4.&8.)(8.$9.Ln,$9.(:.(;.#1.R1.)(;.R1.(<.(4.&8.)O2.)))R1.)O2.))O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition t_writes_pick (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch (Z_to_bv 64 1)) T bufs.

(* [comment removed for export] *)
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

Lemma t_writes_pick_nil : forall T, t_writes_pick [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_pick_cons : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pbuf,(=.(4.&8.))Pbufs,(=.(=.(4.&8.)))PT,$>.(?.$>.(10.(11.(=.(4.&8.))R3.R2.)R1.)(12.(13.&40.+1.)R3.(10.R2.R1.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Definition t_writes (bufs : list (list byte)) (T : TSet) : TSet :=
  t_writes_ch (Z_to_bv 64 1) bufs T.

Lemma t_writes_nil : forall T, t_writes [] T = T. Proof. reflexivity. Qed.
Lemma t_writes_cons : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pbuf,(=.(4.&8.))Pbufs,(=.(=.(4.&8.)))PT,$>.(?.$>.(14.(11.(=.(4.&8.))R3.R2.)R1.)(2.(3.(4.&8.)$5.(6.(13.&40.+1.))R3.)(14.R2.R1.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.
Lemma t_writes_ch_cons : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pch,(4.&40.)Pbuf,(=.(4.&8.))Pbufs,(=.(=.(4.&8.)))PT,$>.(?.$>.(15.R4.(11.(=.(4.&8.))R3.R2.)R1.)(2.(3.(4.&8.)$5.(6.R4.)R3.)(15.R4.R2.R1.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_writes_ch_exit_has_nil : forall ch bufs code fs,
  t_writes_ch ch bufs (t_exit code fs) [].
Proof.
  intros ch [|b bs] code fs; cbn [t_writes_ch fold_right];
    apply t_emit_has_nil.
Qed.

(* [comment removed for export] *)
Lemma t_writes_ch_exit_iff : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pch,(4.&40.)Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pfs,$16.Ptr,(=.$5.)(17.(15.R5.R4.(18.R3.R2.)R1.)(19.$5.R1.(1:.$5.(1;.R5.R4.)(11.$5.(1<.R3.R2.)(1=.$5.)))))")
(* [comment removed for export] *).
Proof.
  intros ch bufs; induction bufs as [|buf bufs IH]; intros code fs tr.
  - cbn [wevents_ch app]. unfold t_writes_ch, fold_right, t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)]; [exact H | rewrite app_nil_r; apply is_prefix_refl].
    + intro H. left. exact H.
  - rewrite t_writes_ch_cons. cbn [wevents_ch]. rewrite <- app_assoc.
    unfold t_emit at 1. split.
    + intros [H | (tr' & -> & Hc)].
      * apply is_prefix_app_r; exact H.
      * apply is_prefix_app_mono. apply IH. exact Hc.
    + intro H. apply is_prefix_app_split in H as [H | (tr' & -> & H)].
      * left; exact H.
      * right. exists tr'. split; [reflexivity | apply IH; exact H].
Qed.

Lemma t_writes_exit_iff : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pfs,$16.Ptr,(=.$5.)(17.(14.R4.(18.R3.R2.)R1.)(19.$5.R1.(1:.$5.(1>.R4.)(11.$5.(1<.R3.R2.)(1=.$5.)))))")
(* [comment removed for export] *).
Proof.
  intros bufs code fs tr. unfold t_writes.
  rewrite t_writes_ch_exit_iff, wevents_ch_fd1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma t_alt_wall : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pch,(4.&40.)Prest,(=.(4.&8.))PT,$>.P,A1.R1.(1=.$5.)P,(;.#1.(<.(4.&8.)R3.))(1?.(0.(1.R4.)Li,(1.R4.)(2.(3.(4.&8.)$5.(6.R6.)(7.(4.&8.)(8.$9.Ln,$9.(:.(;.#1.R1.)(;.R1.(<.(4.&8.)R6.)))R1.)R5.))(2.(3.(4.&8.)$5.(6.R6.)(20.(4.&8.)(8.$9.Ln,$9.(:.(;.#1.R1.)(;.R1.(<.(4.&8.)R6.)))R1.)R5.))R4.)))(2.(3.(4.&8.)$5.(6.R5.)R4.)R3.))")
(* [comment removed for export] *).
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

(* [comment removed for export] *)
Lemma t_writes_ch_pick_exit_iff : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pch,(4.&40.)Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pfs,$16.Ptr,(=.$5.)P,(21.(=.(4.&8.))Lb,(=.(4.&8.))(;.#1.(<.(4.&8.)R1.))R4.)(17.(22.$>.(=.(4.&8.))(12.R6.)(18.R4.R3.)R5.R2.)(23.(=.$5.)Lfull,(=.$5.)(:.(24.R7.R6.R1.)(19.$5.R3.(1:.$5.R1.(11.$5.(1<.R5.R4.)(1=.$5.)))))))")
(* [comment removed for export] *).
Proof.
  intros ch bufs code fs tr Hall; revert tr;
    induction Hall as [|buf bufs Hnb Hall IH]; intros tr.
  - cbn [fold_right]. unfold t_exit, t_emit, t_nil.
    split.
    + intros [H | (tr' & -> & ->)].
      * exists []. split; [apply wp_nil | exact H].
      * exists []. split; [apply wp_nil|].
        rewrite app_nil_r. cbn [app]. apply is_prefix_refl.
    + intros (full & Hw & Hp). inversion Hw; subst full.
      left. exact Hp.
  - cbn [fold_right]. unfold t_write_ch at 1, t_alt at 1.
    split.
    + intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
      destruct Hi as [H | (tr' & -> & Hc)].
      * exists (map (WriteEv ch) (firstn n buf) ++ wevents_ch ch bufs).
        split; [apply wp_cons; [exact Hn1 | exact Hn2 | apply wpick_wevents; exact Hall]|].
        rewrite <- app_assoc.
        eapply is_prefix_trans; [exact H | apply is_prefix_app_r; apply is_prefix_refl].
      * apply IH in Hc. destruct Hc as (full & Hw & Hp).
        exists (map (WriteEv ch) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption|].
        rewrite <- app_assoc. apply is_prefix_app_mono. exact Hp.
    + intros (full & Hw & Hp).
      inversion Hw as [|buf' bufs' n tr0 Hn1 Hn2 Hw0]; subst.
      rewrite <- app_assoc in Hp.
      apply is_prefix_app_split in Hp as [Hp | (tr' & -> & Hp)].
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. left. exact Hp.
      * exists (exist _ n (conj Hn1 Hn2)). cbn [proj1_sig]. right.
        exists tr'. split; [reflexivity|].
        apply IH. exists tr0. split; assumption.
Qed.

Lemma t_writes_pick_exit_iff : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pfs,$16.Ptr,(=.$5.)P,(21.(=.(4.&8.))Lb,(=.(4.&8.))(;.#1.(<.(4.&8.)R1.))R4.)(17.(10.R5.(18.R4.R3.)R2.)(23.(=.$5.)Lfull,(=.$5.)(:.(24.(13.&40.+1.)R6.R1.)(19.$5.R3.(1:.$5.R1.(11.$5.(1<.R5.R4.)(1=.$5.)))))))")
(* [comment removed for export] *).
Proof. intros. apply t_writes_ch_pick_exit_iff. assumption. Qed.

(* [comment removed for export] *)
Lemma two_traces_t_alt2 : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)Pfs,$16.Ptr,(=.$5.)(17.(25.(14.R6.(18.R5.R2.))(14.R4.(18.R3.R2.))R1.)(26.R6.R5.R4.R3.R2.R1.))")
(* [comment removed for export] *).
Proof.
  intros. unfold t_alt2, MmapSim.two_traces.
  rewrite !t_writes_exit_iff. reflexivity.
Qed.

(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop := ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "(:.Pi,O3.(27.Vsegs,O4.A1.O2.R1.(28.A1.O1.R1.))Pe,(=.$5.)Pst,$29.P,(27.Vsegs,O4.R2.R1.)(23.O3.Li,O3.(:.(?.(=.$5.)R4.A1.O2.R1.)(?.$29.R3.(28.A1.O1.R1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* [comment removed for export] *)

#[using="Type"] Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

#[using="Type"] Lemma realizes_pclosed : forall c T, realizes c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma realizes_star_only : forall c T, realizes c T ->
  forall tr c', star segs c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_halted_nil segs c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma realizes_admits : forall c T, realizes c T ->
  forall tr, T tr -> obs_trace segs c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem realizes_obs_iff : forall c T, realizes c T ->
  forall tr, obs_trace segs c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma sstep_halted_none : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

#[using="Type"] Lemma realizes_step : forall c T e c',
  realizes c T -> sstep segs c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

#[using="Type"] Lemma realizes_no_sserror : forall c T e,
  realizes c T -> ~ sstep segs c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path (c : config) : Prop := exists T, realizes c T.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_cosafe : forall c T, realizes c T -> cosafe segs c T.
Proof.
  intros c T H. apply star_cosafe.
  intros tr c' Hstar. exact (realizes_star_only c T H tr c' Hstar).
Qed.

#[using="Type"] Theorem realizes_coexec : forall c T, realizes c T ->
  OmniRun.coexec segs c (fun tr o => T tr /\ ~ is_error o).
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - apply coexec_step.
    + destruct Hnode as [Hcomp _]. eapply sstep_halted_none. apply (Hcomp i0).
    + intros e Hss. exfalso. destruct Hnode as [_ Hsound].
      destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss. destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c') Hss) as (i & -> & Heq2).
      inversion Heq2; subst c'.
      eapply coexec_conseq; [exact (IH i) |].
      intros tr o (HT & Hno). split; [| exact Hno].
      exists i. right. exists tr. split; [reflexivity | exact HT].
  - apply coexec_halt; [exact Hh | split; [reflexivity | exact (fun h => h)]].
  - eapply coexec_conseq; [exact IH |].
    intros tr o (HT & Hno). split; [apply Heq; exact HT | exact Hno].
Qed.

#[using="Type"] Theorem realizes_no_error : forall c T, realizes c T -> ~ reaches_error segs c.
Proof.
  intros c T H. apply coexec_no_error.
  eapply coexec_conseq; [exact (realizes_coexec c T H) |].
  intros tr o (_ & Hno). exact Hno.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_not_errors : forall c T, realizes c T -> ~ OmniRun.exec segs c errors.
Proof.
  intros c T H Hex.
  destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
  exact (proj2 (coexec_sound _ _ _ _ Hm _ (realizes_coexec c T H)) Herr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_refutes_excluding : forall c T tr,
  realizes c T -> T tr -> ~ cosafe segs c (fun tr' => ~ is_prefix tr tr').
Proof.
  intros c T tr H HT Hc.
  destruct (realizes_admits c T H tr HT) as (tr' & c' & Hstar & Hp).
  exact (cosafe_star _ _ _ _ _ Hc Hstar Hp).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_silent1 : forall c c' T,
  node_ok c unit (fun _ => []) (fun _ => c') ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_emit1 : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pc,$2:.Pc',$2:.Pe,(=.$5.)PT,$>.P,(2;.R4.$2<.L,$2<.R3.L,$2<.R4.)P,(2=.R4.R2.)(2=.R6.(2.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros c c' e T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_alt2 : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pc,$2:.PIA,StPIB,StPnx,P,(2>.R2.R1.)$2:.PA,$>.PB,$>.Pa0,R5.Pb0,R5.P,(2;.R8.(2>.R7.R6.)L,(2>.R7.R6.)(1=.$5.)R5.)P,Pi,R8.(2=.A1.R7.(2?.R9.R8.R1.)R6.)P,Pi,R8.(2=.A1.R8.(30.R:.R9.R1.)R6.)(2=.R;.(25.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma node_instr : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pmodel,$32.Pms',$31.P,(?.(33.(4.&40.))(34.R2.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R3.)(1=.(36.(4.&40.)(4.&40.))))P,(?.(33.(4.&40.))(38.R5.)(35.(4.&40.)))P,(?.(39.$31.)(3:.Vsegs,R6.)(3;.$31.R4.))(2;.(3<.R7.R6.)$2<.L,$2<.(1=.$5.)L,$2<.(3<.R6.R7.))")
(* [comment removed for export] *).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep. split.
  - intros []. apply (sstep_instr segs ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_step : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pmodel,$32.Pms',$31.PT,$>.P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))P,(?.(33.(4.&40.))(38.R6.)(35.(4.&40.)))P,(?.(39.$31.)(3:.Vsegs,R7.)(3;.$31.R5.))P,(2=.(3<.R6.R7.)R5.)(2=.(3<.R9.R8.)R6.)")
(* [comment removed for export] *).
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma rz_msteps : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pms',$31.Pmodel,$32.PT,$>.P,(?.(33.(4.&40.))(34.R2.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R3.)(1=.(36.(4.&40.)(4.&40.))))P,(3=.Vsegs,R6.R5.)P,(2=.(3<.R6.R5.)R4.)(2=.(3<.R8.R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_write1 : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pmodel,$32.Px8,(4.&40.)Pbuf,(=.(4.&8.))P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R5.)P,(?.(33.(4.&40.))(38.R7.)(3?.(4.&40.)R5.))P,(?.$40.(41.&40.R6.)+40.)P,(?.(4.&40.)(42.R9.#0.)(13.&40.+1.))P,(?.(33.(=.(4.&8.)))(43.R:.(42.R:.#1.)(42.R:.#2.))(3?.(=.(4.&8.))R7.))P,(44.R8.)P,(;.#1.(<.(4.&8.)R9.))(2;.(3<.R=.R<.)(1.R:.)Li,(1.R:.)(3.(4.&8.)$5.(6.(13.&40.+1.))(7.(4.&8.)(8.$9.Ln,$9.(:.(;.#1.R1.)(;.R1.(<.(4.&8.)R<.)))R1.)R;.))Li,(1.R:.)(3<.(45.(46.R>.(47.(4.&8.)(7.(4.&8.)(8.$9.Ln,$9.(:.(;.#1.R1.)(;.R1.(<.(4.&8.)R<.)))R1.)R;.))))R=.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb. split.
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
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

#[using="Type"] Lemma rz_write1 : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pmodel,$32.Px8,(4.&40.)Pbuf,(=.(4.&8.))PT,$>.P,(?.(33.(4.&40.))(34.R4.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R5.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R6.)P,(?.(33.(4.&40.))(38.R8.)(3?.(4.&40.)R6.))P,(?.$40.(41.&40.R7.)+40.)P,(?.(4.&40.)(42.R:.#0.)(13.&40.+1.))P,(?.(33.(=.(4.&8.)))(43.R;.(42.R;.#1.)(42.R;.#2.))(3?.(=.(4.&8.))R8.))P,(44.R9.)P,(;.#1.(<.(4.&8.)R:.))P,Pn,$9.P,(;.#1.R1.)P,(;.R2.(<.(4.&8.)R=.))(2=.(3<.(45.(46.R11.(47.(4.&8.)(7.(4.&8.)R3.R>.))))R10.)R=.)(2=.(3<.R?.R>.)(12.(13.&40.+1.)R<.R;.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
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
#[using="Type"] Lemma rz_exit : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pmodel,$32.Px8,(4.&40.)P,(?.(33.(4.&40.))(34.R2.)(35.(4.&40.)))P,(?.(33.(4.&40.))(38.R4.)(3?.(4.&40.)R2.))P,(48.R3.)(2=.(3<.R6.R5.)(18.(49.&40.(42.R6.#0.)(13.&40.+??.))(4:.R5.)))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
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
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_munmap : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pmodel,$32.Px8,(4.&40.)PT,$>.P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))P,(?.(33.(4.&40.))(38.R6.)(3?.(4.&40.)R4.))P,(?.$40.(41.&40.R5.)+=7.)P,(4;.R8.R7.)P,(2=.(3<.(45.(4<.R9.(4=.R9.)))(4>.(42.R9.#0.)(4?.(42.R9.#1.))R8.))R6.)(2=.(3<.R:.R9.)R7.)")
(* [comment removed for export] *).
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply rz_silent1; [| exact Hc]. split.
  - intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rz_mmap : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pms,$31.Pmodel,$32.Px8,(4.&40.)PA,$>.PB,$>.P,(?.(33.(4.&40.))(34.R4.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R5.)(1=.(36.(4.&40.)(4.&40.))))P,(?.(33.(4.&40.))(38.R7.)(3?.(4.&40.)R5.))P,(?.$40.(41.&40.R6.)+=>.)P,(50.R9.)P,Pe,$40.P,(51.$40.R1.$52.)(2=.(3<.(45.(46.R<.(53.R2.)))R;.)R9.)P,Pa,(4.&40.)P,(?.$54.(55.(42.R<.#0.)R;.R1.(56.(41.&40.(42.R<.#1.))))$57.)(2=.(3<.(45.(4<.R=.(58.R2.(1=.(36.(4.&40.)(=.(4.&8.))))(11.(36.(4.&40.)(4.&40.))(59.(4.&40.)(4.&40.)R2.(4?.(42.R=.#1.)))(1=.(36.(4.&40.)(4.&40.))))(1=.(36.(4.&40.)(4.&40.)))(1=.$5:.)(1=.(36.(4.&40.)$9.)))))(5;.R2.(4?.(42.R=.#1.))R<.))R9.)P,(23.(4.&40.)La,(4.&40.)(?.$54.(55.(42.R=.#0.)R<.R1.(56.(41.&40.(42.R=.#1.))))$57.))(2=.(3<.R=.R<.)(25.R:.R9.))")
(* [comment removed for export] *).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs HA HB Hex.
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
  - split.
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
      destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      * exists (inl (exist _ er Her)). split; reflexivity.
      * exists (inr (exist _ a Ha)). split; reflexivity.
  - intros [e He]; cbn. apply HA; exact He.
  - intros [a Ha]; cbn. apply HB; exact Ha.
Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shape_omni_corun : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Ppc,$5=.Pph,$5>.Psp,(4.&40.)Pbrk0,(4.&40.)Pmb,(4.&40.)Prnd,$5?.Plim,$40.PT,$>.Pinp,$60.P,(61.R:.(62.R:.R9.R8.R7.R6.R5.R4.R3.R1.)R2.)(63.(64.R;.R:.R9.)R4.(65.R8.R7.R6.R5.)R2.Ltr,(=.$5.)Lo,$66.(:.A1.R5.R2.(67.(68.R1.))))")
(* [comment removed for export] *).
Proof. intros. cbn [omni_corun]. apply realizes_coexec; assumption. Qed.

Lemma shape_omni_cosafe : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Ppc,$5=.Pph,$5>.Psp,(4.&40.)Pbrk0,(4.&40.)Pmb,(4.&40.)Prnd,$5?.Plim,$40.PT,$>.Pinp,$60.P,(61.R:.(62.R:.R9.R8.R7.R6.R5.R4.R3.R1.)R2.)(69.(64.R;.R:.R9.)R4.(65.R8.R7.R6.R5.)R2.R3.)")
(* [comment removed for export] *).
Proof. intros. cbn [omni_cosafe]. apply realizes_cosafe; assumption. Qed.

(* [comment removed for export] *)
Lemma shape_omni_trace_equiv : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.PT,$>.Pinp,$60.P,(61.R12.(62.R12.R11.R10.R?.R>.R=.R<.R;.R1.)R2.)P,(61.R;.(62.R;.R:.R9.R8.R7.R6.R5.R4.R2.)R3.)(6:.(64.R14.R13.R12.)R=.(65.R11.R10.R?.R>.)(64.R<.R;.R:.)R5.(65.R9.R8.R7.R6.)R3.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  apply omni_trace_equiv_refinement. cbn [run bh_traces omni_cosafe]. split.
  - apply (cosafe_obs_iff _ _ _ (obs_trace_is_prefix_closed _ _)).
    intros tr Hobs. apply (realizes_obs_iff _ _ _ Htarget).
    apply (realizes_obs_iff _ _ _ Hsource). exact Hobs.
  - apply (cosafe_obs_iff _ _ _ (obs_trace_is_prefix_closed _ _)).
    intros tr Hobs. apply (realizes_obs_iff _ _ _ Hsource).
    apply (realizes_obs_iff _ _ _ Htarget). exact Hobs.
Qed.

Lemma shape_omni_equiv : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.PT,$>.Pinp,$60.P,(61.R12.(62.R12.R11.R10.R?.R>.R=.R<.R;.R1.)R2.)P,(61.R;.(62.R;.R:.R9.R8.R7.R6.R5.R4.R2.)R3.)(6;.(64.R14.R13.R12.)R=.(65.R11.R10.R?.R>.)(64.R<.R;.R:.)R5.(65.R9.R8.R7.R6.)R3.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  right. split.
  - eapply shape_omni_trace_equiv; eassumption.
  - eapply coexec_conseq; [apply (shape_omni_corun _ _ _ _ _ _ _ _ _ _ Htarget) |].
    intros tr o (_ & Hno). exact Hno.
Qed.

(* [comment removed for export] *)
Theorem shape_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.PT,$>.Pinp,$60.P,(61.R10.(62.R10.R?.R>.R=.R<.R;.R:.$6<.R1.)R2.)P,(61.R:.(62.R:.R9.R8.R7.R6.R5.R4.$6=.R2.)R3.)(6>.(64.R12.R11.R10.)(64.R;.R:.R9.)(65.R?.R>.R=.R<.)(65.R8.R7.R6.R5.)R3.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd T inp
    Hsource Htarget.
  split.
  - cbn [img_segments].
    eapply coexec_conseq; [apply (shape_omni_corun _ _ _ _ _ _ _ _ _ _ Hsource) |].
    intros tr o (_ & Hno). exact (never_errors_covered _ _ _ Hno).
  - eapply shape_omni_equiv; eassumption.
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.PT,$>.Pinp,$60.P,(61.R12.(62.R12.R11.R10.R?.R>.R=.R<.R;.R1.)R2.)P,(61.R;.(62.R;.R:.R9.R8.R7.R6.R5.R4.R2.)R3.)(:.(6?.(70.(64.R14.R13.R12.)R=.(65.R11.R10.R?.R>.)R3.))(71.(70.(64.R14.R13.R12.)R=.(65.R11.R10.R?.R>.)R3.)(70.(64.R<.R;.R:.)R5.(65.R9.R8.R7.R6.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split.
  - apply modeled_iff. cbn [img_segments].
    eapply coexec_conseq; [apply (shape_omni_corun _ _ _ _ _ _ _ _ _ _ Hsource) |].
    intros tr o (_ & Hno). exact (never_errors_covered _ _ _ Hno).
  - apply equiv_iff. eapply shape_omni_equiv; eassumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cat_realizes : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pmodel,$32.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R5.)P,(72.R8.R7.R5.R4.)P,(73.R6.)(61.R:.(3<.R9.R8.)(10.R7.(18.R6.(4:.R8.))))")
(* [comment removed for export] *).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hte. revert model Hh Hlazy Hfd.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - rewrite t_writes_pick_nil. eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_pick_cons. eapply rz_write1; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exitline_realizes_aux : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pmodel,$32.P,(72.R5.R4.R3.R2.)P,(?.(=.(=.(4.&8.)))R4.(1=.(=.(4.&8.))))P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))(61.R9.(3<.R8.R5.)(18.R6.(4:.R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms bufs code model Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intros Hbufs Hh;
    [| discriminate Hbufs |]; intro Hlazy.
  - eapply rz_exit; eassumption.
  - eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep |].
    apply IH; [solve [assumption | reflexivity] | exact Hh | exact Hlazy].
Qed.

Lemma exitline_realizes : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pcode,(4.&40.)Pmodel,$32.P,(72.R4.R3.(1=.(=.(4.&8.)))R2.)P,(?.(33.(4.&40.))(34.R2.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R3.)(1=.(36.(4.&40.)(4.&40.))))(61.R7.(3<.R6.R4.)(18.R5.(4:.R4.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms code model Hte Hh Hlazy.
  exact (exitline_realizes_aux segs ms [] code model Hte eq_refl Hh Hlazy).
Qed.

Lemma rz_wall1_mut : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pmodel,$32.P,(?.(33.(4.&40.))(34.R1.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R2.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R3.)(:.Pms,$31.Prest,(=.(4.&8.))Pk,P,$31.SpP,(74.R8.(13.&40.+1.)R3.R2.R1.)P,(44.R3.)PT,$>.P,A1.R1.(1=.$5.)P,Pms',$31.P,A1.R6.R1.(61.R>.(3<.R2.R=.)R4.)(61.R=.(3<.R8.R<.)(2.(3.(4.&8.)$5.(6.(13.&40.+1.))R7.)R3.))Pms,$31.Prest,(=.(4.&8.))Pk,P,$31.SpP,(75.R8.(13.&40.+1.)R3.R2.R1.)P,(44.R3.)PT,$>.P,A1.R1.(1=.$5.)P,Pms',$31.P,A1.R6.R1.(61.R>.(3<.R2.R=.)R4.)(61.R=.(3<.R8.R<.)(2.(3.(4.&8.)$5.(6.(13.&40.+1.))R7.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs model Hh Hlazy Hfd.
  apply (to_wall_mutind segs (Z_to_bv 64 1)
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))
    (fun ms rest k => buf_modeled rest -> forall T : TSet, T [] ->
       (forall ms', k ms' -> realizes segs (mkCfg ms' model) T) ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest) T))).
  - (* [comment removed for export] *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm T HT Hk.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest)) T)
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) T HT Hk). }
    apply t_alt_wall; [exact HT | exact Hnb].
  - (* [comment removed for export] *)
    intros ms k Hk Hbm T HT Hcont.
    eapply rz_conseq; [apply Hcont; exact Hk|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT.
  - (* [comment removed for export] *)
    intros ms rest k Hnb Hw IH Hbm T HT Hk. exact (IH Hbm T HT Hk).
  - (* [comment removed for export] *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm T HT Hk.
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | exact (IH Hbm T HT Hk)].
Qed.

(* [comment removed for export] *)
Lemma wall_realizes : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pmodel,$32.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R5.)P,(76.R8.(13.&40.+1.)R5.R4.R7.)P,(73.R6.)(61.R:.(3<.R9.R8.)(14.R7.(18.R6.(4:.R8.))))")
(* [comment removed for export] *).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hw Hbm. revert ms Hw Hbm.
  induction bufs as [|buf rest IH]; intros ms Hw Hbm.
  - exact (exitline_realizes segs ms code model Hw Hh Hlazy).
  - destruct Hw as [Hnb Ht]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons.
    eapply (proj2 (rz_wall1_mut segs model Hh Hlazy Hfd)).
    + exact Ht.
    + exact Hb.
    + unfold t_writes. apply t_writes_ch_exit_has_nil.
    + intros ms' Hk. apply IH; [exact Hk | exact Hbs].
Qed.

(* [comment removed for export] *)
Lemma twm_realizes_mut : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)(:.Pms,$31.Pmodel,$32.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)P,(77.R5.R4.R3.R2.R1.)P,(?.(33.(4.&40.))(34.R4.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R5.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R6.)P,(73.R6.)(61.R:.(3<.R9.R8.)(14.R7.(18.R6.(4:.R8.))))(:.Pms,$31.Pmodel,$32.Prest,(=.(4.&8.))Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)P,(78.R6.R5.R4.R3.R2.R1.)P,(?.(33.(4.&40.))(34.R5.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R6.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R7.)P,(44.R7.)P,(73.R7.)(61.R<.(3<.R;.R:.)(2.(3.(4.&8.)$5.(6.(13.&40.+1.))R9.)(14.R8.(18.R7.(4:.R:.)))))Pms,$31.Pmodel,$32.Prest,(=.(4.&8.))Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)P,(79.R6.R5.R4.R3.R2.R1.)P,(?.(33.(4.&40.))(34.R5.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R6.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R7.)P,(44.R7.)P,(73.R7.)(61.R<.(3<.R;.R:.)(2.(3.(4.&8.)$5.(6.(13.&40.+1.))R9.)(14.R8.(18.R7.(4:.R:.)))))))")
(* [comment removed for export] *).
Proof.
  intros segs.
  apply (MmapSim.twm_mutind segs
    (fun ms model bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model) (t_writes bufs (t_exit code (m_fs model))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))
    (fun ms model rest bufs code =>
       m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
       buf_modeled rest -> bufs_modeled bufs ->
       realizes segs (mkCfg ms model)
         (t_emit (map (WriteEv (Z_to_bv 64 1)) rest)
                 (t_writes bufs (t_exit code (m_fs model)))))).
  - (* [comment removed for export] *)
    intros ms model x8 Hsvc Hx8 Hh Hlazy Hfd Hbm. eapply rz_exit; eassumption.
  - (* [comment removed for export] *)
    intros ms model buf bufs code Hnb Hp IH Hh Hlazy Hfd Hbm.
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_cons. exact (IH Hh Hlazy Hfd Hb Hbs).
  - (* [comment removed for export] *)
    intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_munmap; try eassumption.
    rewrite <- (munmap_model_fs (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).
    apply IH; [rewrite munmap_model_halted; exact Hh
              | exact (munmap_model_no_lazy _ _ _ Hlazy)
              | apply munmap_model_fd1chan; exact Hfd | exact Hbm].
  - (* [comment removed for export] *)
    intros ms ms' model bufs code Hsvc Hstep Hte IH Hh Hlazy Hfd Hbm.
    eapply rz_step; try eassumption. apply IH; assumption.
  - (* [comment removed for export] *)
    intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (wr_index rest)
        (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) rest))
        (fun i => mkCfg (advance_past_svc
                           (set_gpr0 ms (len_word (firstn (proj1_sig i) rest))))
                        model)
        (fun i => t_emit (map (WriteEv (Z_to_bv 64 1))
                              (skipn (proj1_sig i) rest))
                         (t_writes bufs (t_exit code (m_fs model))))
        (wr_full rest Hnb)).
      - apply (node_write1 segs ms model x8 rest); assumption.
      - intros [n [Hn1 Hn2]]. cbn [proj1_sig].
        apply (IH n Hn1 Hn2 Hh Hlazy Hfd (buf_modeled_skipn n rest Hbr) Hbm). }
    apply t_alt_wall;
      [unfold t_writes; apply t_writes_ch_exit_has_nil | exact Hnb].
  - (* [comment removed for export] *)
    intros ms model bufs code Hte IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_conseq; [apply IH; assumption|].
    cbn [map]. apply t_eq_sym. apply t_emit_nil_eq.
    unfold t_writes. apply t_writes_ch_exit_has_nil.
  - (* [comment removed for export] *)
    intros ms model rest bufs code Hnb Hp IH Hh Hlazy Hfd Hbr Hbm.
    exact (IH Hh Hlazy Hfd Hbr Hbm).
  - (* [comment removed for export] *)
    intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hh Hlazy Hfd Hbr Hbm.
    eapply rz_step; try eassumption. exact (IH Hh Hlazy Hfd Hbr Hbm).
Qed.

Lemma twm_realizes : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pmodel,$32.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R5.)P,(77.R8.R7.R6.R5.R4.)P,(73.R6.)(61.R:.(3<.R9.R8.)(14.R7.(18.R6.(4:.R8.))))")
(* [comment removed for export] *).
Proof.
  intros segs ms model bufs code Hh Hlazy Hfd Hte.
  exact (proj1 (twm_realizes_mut segs) ms model bufs code Hte Hh Hlazy Hfd).
Qed.

(* [comment removed for export] *)
Lemma tmw_realizes : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pmodel,$32.Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)P,(?.(33.(4.&40.))(34.R5.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R6.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R7.)P,(7:.R:.R9.R8.R7.R6.R5.R4.)P,(73.R8.)P,(73.R7.)(61.R=.(3<.R<.R;.)(25.(14.R:.(18.R9.(4:.R;.)))(14.R8.(18.R7.(4:.R;.)))))")
(* [comment removed for export] *).
Proof.
  intros segs ms model bf cf bs cs Hh Hlazy Hfd Hte. revert Hh Hlazy Hfd.
  induction Hte as
    [ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
    | ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hh Hlazy Hfd Hbf Hbs.
  - eapply rz_mmap; try eassumption.
    + intros e He. apply twm_realizes;
        [exact Hh | exact Hlazy | exact Hfd | apply Hfail; exact He | exact Hbf].
    + intros a Ha.
      rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
      apply twm_realizes;
        [rewrite mmap_model_halted; exact Hh
        | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
        | apply mmap_model_fd1chan; exact Hfd
        | apply Hsucc; exact Ha | exact Hbs].
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.


(* [comment removed for export] *)
Theorem cat_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pinp,$60.P,(72.R13.(7;.R13.R12.R11.R10.R=.(7<.R1.)(7=.R1.)(7>.R1.)(7?.R1.))R3.R2.)P,(72.R<.(7;.R<.R;.R:.R9.R6.(7<.R2.)(7=.R2.)(7>.R2.)(7?.R2.))R4.R3.)P,(73.R5.)(:.(6?.(70.(64.R16.R15.R14.)R?.(65.R13.R12.R11.R10.)R4.))(71.(70.(64.R16.R15.R14.)R?.(65.R13.R12.R11.R10.)R4.)(70.(64.R>.R=.R<.)R7.(65.R;.R:.R9.R8.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    bufs code inp Hs Ht Hbm.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_writes_pick bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes source_segs
             (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
             bufs code eq_refl eq_refl eq_refl Hs Hbm).
  - unfold init_config.
    apply (cat_realizes target_segs
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp alim inp)
             bufs code eq_refl eq_refl eq_refl Ht Hbm).
Qed.

(* [comment removed for export] *)
Theorem cat_omni_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pinp,$60.P,(72.R11.(7;.R11.R10.R?.R>.R;.(7<.R1.)(7=.R1.)(7>.R1.)(7?.R1.))R3.R2.)P,(72.R;.(7;.R;.R:.R9.R8.R5.(7<.R2.)(7=.R2.)(7>.R2.)(7?.R2.))R4.R3.)P,(73.R5.)(6>.(64.R14.R13.R12.)(64.R=.R<.R;.)(65.R11.R10.R?.R>.)(65.R:.R9.R8.R7.)R4.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    bufs code inp Hs Ht Hbm.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_writes_pick bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes source_segs
             (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
             bufs code eq_refl eq_refl eq_refl Hs Hbm).
  - unfold init_config.
    apply (cat_realizes target_segs
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
             bufs code eq_refl eq_refl eq_refl Ht Hbm).
Qed.

(* [comment removed for export] *)
Theorem mmap_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)Pinp,$60.P,(7:.R15.(7;.R15.R14.R13.R12.R?.(7<.R1.)(7=.R1.)(7>.R1.)(7?.R1.))(80.(81.R15.)R11.R10.R12.R>.R1.)R5.R4.R3.R2.)P,(7:.R>.(7;.R>.R=.R<.R;.R8.(7<.R2.)(7=.R2.)(7>.R2.)(7?.R2.))(80.(81.R>.)R:.R9.R;.R7.R2.)R6.R5.R4.R3.)P,(73.R7.)P,(73.R6.)(:.(6?.(70.(64.R19.R18.R17.)R12.(65.R16.R15.R14.R13.)R5.))(71.(70.(64.R19.R18.R17.)R12.(65.R16.R15.R14.R13.)R5.)(70.(64.R11.R10.R?.)R:.(65.R>.R=.R<.R;.)R5.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    bf cf bs cs inp Hs Ht Hbf Hbs.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    apply (tmw_realizes source_segs
             (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
             bf cf bs cs eq_refl eq_refl eq_refl Hs Hbf Hbs).
  - unfold init_config.
    apply (tmw_realizes target_segs
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp alim inp)
             bf cf bs cs eq_refl eq_refl eq_refl Ht Hbf Hbs).
Qed.

(* [comment removed for export] *)
Theorem mmap_omni_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)Pinp,$60.P,(7:.R13.(7;.R13.R12.R11.R10.R=.(7<.R1.)(7=.R1.)(7>.R1.)(7?.R1.))(80.(81.R13.)R?.R>.R10.$6<.R1.)R5.R4.R3.R2.)P,(7:.R=.(7;.R=.R<.R;.R:.R7.(7<.R2.)(7=.R2.)(7>.R2.)(7?.R2.))(80.(81.R=.)R9.R8.R:.$6=.R2.)R6.R5.R4.R3.)P,(73.R7.)P,(73.R6.)(6>.(64.R17.R16.R15.)(64.R10.R?.R>.)(65.R14.R13.R12.R11.)(65.R=.R<.R;.R:.)R5.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    bf cf bs cs inp Hs Ht Hbf Hbs.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    apply (tmw_realizes source_segs
             (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
             bf cf bs cs eq_refl eq_refl eq_refl Hs Hbf Hbs).
  - unfold init_config.
    apply (tmw_realizes target_segs
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
             bf cf bs cs eq_refl eq_refl eq_refl Ht Hbf Hbs).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Corollary rz_alloc_writes : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms0,$31.Pms,$31.Pmodel,$32.Px8,(4.&40.)Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)P,(?.(33.(4.&40.))(34.R6.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R7.)(1=.(36.(4.&40.)(4.&40.))))P,(3>.R8.)P,(3=.R<.R;.R:.)P,(?.(33.(4.&40.))(38.R;.)(3?.(4.&40.)R9.))P,(?.$40.(41.&40.R:.)+=>.)P,(50.R=.)P,Pe,$40.P,(51.$40.R1.$52.)(72.R12.(45.(46.R10.(53.R2.)))R=.R<.)P,Pa,(4.&40.)P,(?.$54.(55.(42.R10.#0.)R?.R1.(56.(41.&40.(42.R10.#1.))))$57.)(77.R13.(45.(4<.R11.(58.R2.(1=.(36.(4.&40.)(=.(4.&8.))))(11.(36.(4.&40.)(4.&40.))(59.(4.&40.)(4.&40.)R2.(4?.(42.R11.#1.)))(1=.(36.(4.&40.)(4.&40.))))(1=.(36.(4.&40.)(4.&40.)))(1=.$5:.)(1=.(36.(4.&40.)$9.)))))(5;.R2.(4?.(42.R11.#1.))R10.)R<.R;.)P,(23.(4.&40.)La,(4.&40.)(?.$54.(55.(42.R11.#0.)R10.R1.(56.(41.&40.(42.R11.#1.))))$57.))P,(73.R>.)P,(73.R=.)(61.R15.(3<.R14.R12.)(25.(10.R10.(18.R?.(4:.R12.)))(14.R>.(18.R=.(4:.R12.)))))")
(* [comment removed for export] *).
Proof.
  intros segs ms0 ms model x8 bf cf bs cs Hh Hlazy Hfd Hms Hsvc Hno Hargs Hfail Hsucc Hex
    Hbf Hbs.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  eapply rz_mmap; try eassumption.
  - intros e He. apply cat_realizes;
      [exact Hh | exact Hlazy | exact Hfd | apply Hfail; exact He | exact Hbf].
  - intros a Ha.
    rewrite <- (mmap_model_fs a (page_round_up (ms_gpr ms 1)) model).
    apply twm_realizes;
      [rewrite mmap_model_halted; exact Hh
      | exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)
      | apply mmap_model_fd1chan; exact Hfd
      | apply Hsucc; exact Ha | exact Hbs].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_outcomes (fs : Fs.Fs)
    (U : (list (list byte) * word) -> Prop) : TSet :=
  fun tr => exists o, U o /\ is_prefix tr (AllocSim.outcome_trace fs o).

Lemma t_alt_emit_nil : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "PI,StPf,P,R1.$>.P,Pi,R2.A2.R2.R1.(1=.$5.)(1?.(0.R3.Li,R3.(2.(1=.$5.)A1.R3.R1.))(0.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros I f H tr. split.
  - intros [i Hi]. exists i. exact (proj1 (t_emit_nil_eq (f i) (H i) tr) Hi).
  - intros [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (f i) (H i) tr) Hi).
Qed.

(* [comment removed for export] *)
Lemma outcomes_realizes : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pmodel,$32.PU,P,(36.(=.(=.(4.&8.)))(4.&40.))SpP,(82.R4.R3.R2.R1.)P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))(61.R7.(3<.R6.R5.)(83.(4:.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros segs ms model U Hto.
  induction Hto as
    [ ms model bufs code U Hfd Hte Hbm HU
    | ms ms' model U Hsvc Hstep Hto IH
    | ms model x8 T U Hsvc Hno Hcont IH HU ];
    intros Hh Hlazy.
  - (* [comment removed for export] *)
    eapply rz_conseq;
      [apply (wall_realizes segs ms model bufs code Hh Hlazy Hfd Hte Hbm)|].
    intro tr. rewrite t_writes_exit_iff.
    unfold t_outcomes, AllocSim.outcome_trace. split.
    + intro Hp. exists (bufs, code). split; [apply HU; reflexivity | exact Hp].
    + intros (o & Ho & Hp). apply HU in Ho. subst o. exact Hp.
  - (* [comment removed for export] *)
    eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                    | apply IH; assumption].
  - (* [comment removed for export] *)
    pose (P := fun p : SyscallEffect * Model =>
                 syscall_spec (sys_input segs ms x8) model (Ok (fst p) (snd p) [])).
    pose (nx := fun (i : sig P) =>
                  mkCfg (advance_past_svc (apply_effect ms (fst (proj1_sig i))))
                        (snd (proj1_sig i))).
    pose (Ti := fun (i : sig P) =>
                  t_outcomes (m_fs model) (T (fst (proj1_sig i)) (snd (proj1_sig i)))).
    destruct (AllocSim.brk_receptive segs ms x8 model Hno)
      as (eff0 & model0 & Hspec0).
    assert (Hcont' : forall i : sig P, realizes segs (nx i) (Ti i)).
    { intros [[eff model'] Hspec]. cbn in Hspec. unfold nx, Ti; cbn.
      destruct (AllocSim.brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec)
        as (_ & Hh' & Hfs & _ & Hlazy').
      rewrite <- Hfs. apply (IH eff model' []);
        [exact Hspec | exact Hh' | exact (eq_trans Hlazy' Hlazy)]. }
    eapply rz_conseq.
    { apply (rz_node segs (mkCfg ms model) (sig P) (fun _ => []) nx Ti
               (exist P (eff0, model0) Hspec0)); [| exact Hcont'].
      split.
      - intros [[eff model'] Hspec]. cbn in Hspec. unfold nx; cbn.
        destruct (AllocSim.brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec)
          as (_ & Hh' & _ & _ & Hlazy').
        apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
        apply materialize_model_accesses_no_lazy. exact (eq_trans Hlazy' Hlazy).
      - intros e st Hss.
        destruct (AllocSim.sstep_brk_inv segs ms model x8 e st
                    Hh Hlazy Hsvc Hno Hss)
          as (eff & model' & Hspec & -> & ->).
        exists (exist P (eff, model') Hspec). split; reflexivity. }
    eapply t_eq_trans;
      [apply t_alt_emit_nil; intro i; eapply realizes_nonempty; apply Hcont'|].
    intro tr. unfold t_alt, Ti, t_outcomes; cbn. split.
    + intros ([[eff model'] Hspec] & o & Ho & Hp). cbn in Ho, Hspec.
      exists o. split; [apply HU; exists eff, model', []; auto | exact Hp].
    + intros (o & Ho & Hp). apply HU in Ho.
      destruct Ho as (eff & model' & evs & Hspec & Ht).
      destruct (AllocSim.brk_step_shape segs ms x8 model eff model' evs Hh Hlazy Hno Hspec)
        as (-> & _ & _ & _).
      exists (exist P (eff, model') Hspec). cbn.
      exists o. split; [exact Ht | exact Hp].
Qed.

(* [comment removed for export] *)
Lemma t_outcomes_two_alt2 : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pfs,$16.Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)(1?.(83.R5.(84.R4.R3.R2.R1.))(25.(14.R4.(18.R3.R5.))(14.R2.(18.R1.R5.))))")
(* [comment removed for export] *).
Proof.
  intros fs bf cf bs cs tr.
  unfold t_outcomes, AllocSim2.two_outcomes, AllocSim.outcome_trace, t_alt2.
  rewrite !t_writes_exit_iff. split.
  - intros (o & [-> | ->] & Hp); cbn [fst snd] in Hp; [left | right]; exact Hp.
  - intros [Hp | Hp]; [exists (bf, cf) | exists (bs, cs)]; cbn [fst snd]; auto.
Qed.

(* [comment removed for export] *)
Theorem alloc_mmap_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)Pinp,$60.P,(82.R15.(7;.R15.R14.R13.R12.R?.(7<.R1.)(7=.R1.)(7>.R1.)(7?.R1.))(80.(81.R15.)R11.R10.R12.R>.R1.)(84.R5.R4.R3.R2.))P,(7:.R>.(7;.R>.R=.R<.R;.R8.(7<.R2.)(7=.R2.)(7>.R2.)(7?.R2.))(80.(81.R>.)R:.R9.R;.R7.R2.)R6.R5.R4.R3.)P,(73.R7.)P,(73.R6.)(:.(6?.(70.(64.R19.R18.R17.)R12.(65.R16.R15.R14.R13.)R5.))(71.(70.(64.R19.R18.R17.)R12.(65.R16.R15.R14.R13.)R5.)(70.(64.R11.R10.R?.)R:.(65.R>.R=.R<.R;.)R5.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    bf cf bs cs inp Hs Ht Hbf Hbs.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    eapply rz_conseq;
      [apply outcomes_realizes; [exact Hs | reflexivity | reflexivity]|].
    apply t_outcomes_two_alt2.
  - unfold init_config.
    apply (tmw_realizes target_segs
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp alim inp)
             bf cf bs cs eq_refl eq_refl eq_refl Ht Hbf Hbs).
Qed.

(* [comment removed for export] *)
Theorem alloc_mmap_omni_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Pbf,(=.(=.(4.&8.)))Pcf,(4.&40.)Pbs,(=.(=.(4.&8.)))Pcs,(4.&40.)Pinp,$60.P,(82.R13.(7;.R13.R12.R11.R10.R=.(7<.R1.)(7=.R1.)(7>.R1.)(7?.R1.))(80.(81.R13.)R?.R>.R10.$6<.R1.)(84.R5.R4.R3.R2.))P,(7:.R=.(7;.R=.R<.R;.R:.R7.(7<.R2.)(7=.R2.)(7>.R2.)(7?.R2.))(80.(81.R=.)R9.R8.R:.$6=.R2.)R6.R5.R4.R3.)P,(73.R7.)P,(73.R6.)(6>.(64.R17.R16.R15.)(64.R10.R?.R>.)(65.R14.R13.R12.R11.)(65.R=.R<.R;.R:.)R5.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    bf cf bs cs inp Hs Ht Hbf Hbs.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_alt2 (t_writes bf (t_exit cf (in_fs inp))) (t_writes bs (t_exit cs (in_fs inp))))
           inp).
  - unfold init_config.
    eapply rz_conseq;
      [apply outcomes_realizes; [exact Hs | reflexivity | reflexivity]|].
    apply t_outcomes_two_alt2.
  - unfold init_config.
    apply (tmw_realizes target_segs
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
             bf cf bs cs eq_refl eq_refl eq_refl Ht Hbf Hbs).
Qed.


(* [comment removed for export] *)

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

Lemma t_writes_ch_pick_1 : forall bufs T, t_writes_ch_pick (Z_to_bv 64 1) bufs T = t_writes_pick bufs T.
Proof. reflexivity. Qed.

Lemma t_writes_ch_pick_cons : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Pch,(4.&40.)Pbuf,(=.(4.&8.))Pbufs,(=.(=.(4.&8.)))PT,$>.(?.$>.(85.R4.(11.(=.(4.&8.))R3.R2.)R1.)(12.R4.R3.(85.R4.R2.R1.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma node_write_ch : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pmodel,$32.Pfd,(4.&40.)Pch,(4.&40.)Px8,(4.&40.)Pbuf,(=.(4.&8.))P,(?.(33.(4.&40.))(34.R5.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R6.)(1=.(36.(4.&40.)(4.&40.))))P,(86.R6.R5.R7.)P,(?.(4.&40.)(87.R7.)R7.)P,(?.(33.(4.&40.))(38.R:.)(3?.(4.&40.)R6.))P,(?.$40.(41.&40.R7.)+40.)P,(?.(4.&40.)(42.R<.#0.)R:.)P,(?.(33.(=.(4.&8.)))(43.R=.(42.R=.#1.)(42.R=.#2.))(3?.(=.(4.&8.))R8.))P,(44.R9.)P,(;.#1.(<.(4.&8.)R:.))(88.R11.(3<.R10.R?.)(1.R;.)Li,(1.R;.)(3.(4.&8.)$5.(6.R>.)(7.(4.&8.)(8.$9.Ln,$9.(:.(;.#1.R1.)(;.R1.(<.(4.&8.)R=.)))R1.)R<.))Li,(1.R;.)(3<.(45.(46.R11.(47.(4.&8.)(7.(4.&8.)(8.$9.Ln,$9.(:.(;.#1.R1.)(;.R1.(<.(4.&8.)R=.)))R1.)R<.))))R10.))")
(* [comment removed for export] *).
Proof.
  intros segs ms model fd ch x8 buf Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb. split.
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
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss)
      as (n & Hn1 & Hn2 & -> & ->).
    exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.

Lemma rz_write_ch : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pms,$31.Pmodel,$32.Pfd,(4.&40.)Pch,(4.&40.)Px8,(4.&40.)Pbuf,(=.(4.&8.))PT,$>.P,(?.(33.(4.&40.))(34.R6.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R7.)(1=.(36.(4.&40.)(4.&40.))))P,(86.R7.R6.R8.)P,(?.(4.&40.)(87.R8.)R8.)P,(?.(33.(4.&40.))(38.R;.)(3?.(4.&40.)R7.))P,(?.$40.(41.&40.R8.)+40.)P,(?.(4.&40.)(42.R=.#0.)R;.)P,(?.(33.(=.(4.&8.)))(43.R>.(42.R>.#1.)(42.R>.#2.))(3?.(=.(4.&8.))R9.))P,(44.R:.)P,(;.#1.(<.(4.&8.)R;.))P,Pn,$9.P,(;.#1.R1.)P,(;.R2.(<.(4.&8.)R>.))(61.R15.(3<.(45.(46.R14.(47.(4.&8.)(7.(4.&8.)R3.R?.))))R13.)R>.)(61.R13.(3<.R12.R11.)(12.R?.R=.R<.))")
(* [comment removed for export] *).
Proof.
  intros segs ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb Hc.
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

Lemma cat_realizes_ch : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psegs,(=.$5<.)Pfd,(4.&40.)Pch,(4.&40.)Pms,$31.Pmodel,$32.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)P,(?.(33.(4.&40.))(34.R3.)(35.(4.&40.)))P,(?.(=.(36.(4.&40.)(4.&40.)))(37.R4.)(1=.(36.(4.&40.)(4.&40.))))P,(86.R8.R7.R5.)P,(?.(4.&40.)(87.R9.)R9.)P,(89.R;.R:.R8.R6.R5.)P,(73.R7.)(61.R=.(3<.R:.R9.)(85.R;.R8.(18.R7.(4:.R9.))))")
(* [comment removed for export] *).
Proof.
  intros segs fd ch ms model bufs code Hh Hlazy Hfdc H32 Hte.
  revert model Hh Hlazy Hfdc.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfdc Hbm.
  - eapply rz_exit; eassumption.
  - apply Forall_cons_iff in Hbm as [Hb Hbs].
    rewrite t_writes_ch_pick_cons. eapply rz_write_ch; try eassumption.
    intros n Hn1 Hn2. apply IH; assumption.
  - eapply rz_step; try eassumption. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Theorem cat_ch_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.Pfd,(4.&40.)Pch,(4.&40.)Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pinp,$60.P,(?.(4.&40.)(87.R5.)R5.)P,Preserved,(=.(36.(4.&40.)(4.&40.)))Pbrk0,(4.&40.)Pmb1,(4.&40.)Psp1,(4.&40.)Plim1,$40.Pinp1,$60.(86.R<.R;.(80.R6.R5.R4.R3.R2.R1.))P,(89.R17.R7.(7;.R17.R16.R15.R14.R11.(7<.R3.)(7=.R3.)(7>.R3.)(7?.R3.))R5.R4.)P,(89.R10.R8.(7;.R10.R?.R>.R=.R:.(7<.R4.)(7=.R4.)(7>.R4.)(7?.R4.))R6.R5.)P,(73.R7.)(:.(6?.(70.(64.R1:.R19.R18.)R13.(65.R17.R16.R15.R14.)R6.))(71.(70.(64.R1:.R19.R18.)R13.(65.R17.R16.R15.R14.)R6.)(70.(64.R12.R11.R10.)R;.(65.R?.R>.R=.R<.)R6.)))")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    fd ch bufs code inp H32 Hinit Hs Ht Hbm.
  apply (shape_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd rlim
           target_segs apc aph asp abrk amb arnd alim
           (t_writes_ch_pick ch bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes_ch source_segs fd ch
             (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp)
             bufs code eq_refl eq_refl (Hinit _ _ _ _ _ _) H32 Hs Hbm).
  - unfold init_config.
    apply (cat_realizes_ch target_segs fd ch
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp alim inp)
             bufs code eq_refl eq_refl (Hinit _ _ _ _ _ _) H32 Ht Hbm).
Qed.

(* [comment removed for export] *)
Theorem cat_ch_omni_strong_equiv_alg : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Pfd,(4.&40.)Pch,(4.&40.)Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pinp,$60.P,(?.(4.&40.)(87.R5.)R5.)P,Preserved,(=.(36.(4.&40.)(4.&40.)))Pbrk0,(4.&40.)Pmb1,(4.&40.)Psp1,(4.&40.)Plim1,$40.Pinp1,$60.(86.R<.R;.(80.R6.R5.R4.R3.R2.R1.))P,(89.R15.R7.(7;.R15.R14.R13.R12.R?.(7<.R3.)(7=.R3.)(7>.R3.)(7?.R3.))R5.R4.)P,(89.R?.R8.(7;.R?.R>.R=.R<.R9.(7<.R4.)(7=.R4.)(7>.R4.)(7?.R4.))R6.R5.)P,(73.R7.)(6>.(64.R18.R17.R16.)(64.R11.R10.R?.)(65.R15.R14.R13.R12.)(65.R>.R=.R<.R;.)R6.)")
(* [comment removed for export] *).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd
    fd ch bufs code inp H32 Hinit Hs Ht Hbm.
  apply (shape_omni_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd
           target_segs apc aph asp abrk amb arnd
           (t_writes_ch_pick ch bufs (t_exit code (in_fs inp))) inp).
  - unfold init_config.
    apply (cat_realizes_ch source_segs fd ch
             (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp)
             bufs code eq_refl eq_refl (Hinit _ _ _ _ _ _) H32 Hs Hbm).
  - unfold init_config.
    apply (cat_realizes_ch target_segs fd ch
             (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
             (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp)
             bufs code eq_refl eq_refl (Hinit _ _ _ _ _ _) H32 Ht Hbm).
Qed.

(* [comment removed for export] *)
Corollary cat_strong_equiv_alg_via_ch : ltac2:(CDefT.buildp (gd_tbl_ShapeAlg ()) "Psource_segs,(=.$5<.)Prpc,$5=.Prph,$5>.Prsp,(4.&40.)Prbrk,(4.&40.)Prmb,(4.&40.)Prrnd,$5?.Prlim,$40.Ptarget_segs,(=.$5<.)Papc,$5=.Paph,$5>.Pasp,(4.&40.)Pabrk,(4.&40.)Pamb,(4.&40.)Parnd,$5?.Palim,$40.Pbufs,(=.(=.(4.&8.)))Pcode,(4.&40.)Pinp,$60.P,(72.R13.(7;.R13.R12.R11.R10.R=.(7<.R1.)(7=.R1.)(7>.R1.)(7?.R1.))R3.R2.)P,(72.R<.(7;.R<.R;.R:.R9.R6.(7<.R2.)(7=.R2.)(7>.R2.)(7?.R2.))R4.R3.)P,(73.R5.)(:.(6?.(70.(64.R16.R15.R14.)R?.(65.R13.R12.R11.R10.)R4.))(71.(70.(64.R16.R15.R14.)R?.(65.R13.R12.R11.R10.)R4.)(70.(64.R>.R=.R<.)R7.(65.R;.R:.R9.R8.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros. eapply (cat_ch_strong_equiv_alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (Z_to_bv 64 1) (Z_to_bv 64 1));
    [ reflexivity
    | intros; apply fd1chan_fdchan; apply init_model_fd1chan
    | apply to_wexit_ch_1; eassumption
    | apply to_wexit_ch_1; eassumption
    | eassumption ].
Qed.
