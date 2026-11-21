(* [accepts_all] of the release classifier image (sha256 ..., its elf-snapshot X.v), on
   linux-process-semantics .  The walk (Cls/ClsStartup.cls_startup_spec) is a node tree with one
   set_tid_address node and then the exit_group(0) node; Lib/ITreeFO.impl_run_must_exit2_cfg turns it into
   halting with exit code 0 under the zlib configuration [alloc_forced_cfg] (the node relation is sound there,
   Lib/Nodes.nodes_sound_fo), over the node relations restricted to the code-0 exit node; MustExit's
   monotonicity (with FO/FOCore's classical decision of the filter, Classical_Prop.classic) carries it down to
   [forced_only_cfg], and the singleton form is [must_exit_with_scfg ... verdict_accept]. *)
From Stdlib Require Import ZArith NArith QArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Vdso Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv FP InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Lib Require Import ITreeFO RegsEquivFO Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Cls Require Import CImg TopLevelG ClsStartup AcceptAllGeneric.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.OSSV Require Import Images Shapes ClassifierShapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(** The classifier image, as lps's [Image]. *)
Definition cls_image : Image := mkImage X.M.loaded_segments X.M.init_pc X.M.phdrs.

(** It is well formed (lps's three checks), so its valid entries are not vacuous. *)
Lemma cls_image_wf : image_wf cls_image.
Proof. check_image_wf. Qed.

(** ** The node relations restricted to the code-0 exit node *)
Definition at_node0 (segs : list Segment) (n : node) (ms : machine_state) : Prop :=
  at_node segs n ms /\ match n with NExit c => c = 0%Z | _ => True end.
Definition nexit0 (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
  nexit n mo code mo' /\ match n with NExit c => c = 0%Z | _ => True end.

Lemma nodes_sound_fo0 : forall segs,
  node_sound_cfg alloc_forced_cfg node segs (at_node0 segs) nstep nexit0 minv nsafe.
Proof.
  intros segs. destruct (nodes_sound_fo segs) as [H1 H2 H3 H4 H5 H6]. constructor.
  - exact H1.
  - intros n ms [Hat _]. exact (H2 n ms Hat).
  - intros n ms mo evs X [Hat Hc] Hh Hinv Hsf Hss.
    destruct (H3 n ms mo evs X Hat Hh Hinv Hsf Hss) as [Hl | (code & mo' & E & Hx & Hevs)].
    + left. exact Hl.
    + right. exists code, mo'. split; [exact E|]. split; [split; [exact Hx | exact Hc] | exact Hevs].
  - intros n ms mo rsp mo' evs [Hat _] Hh Hinv Hsf Hst. exact (H4 n ms mo rsp mo' evs Hat Hh Hinv Hsf Hst).
  - intros n ms mo code mo' [Hat _] Hh Hinv Hsf [Hx _]. exact (H5 n ms mo code mo' Hat Hh Hinv Hsf Hx).
  - intros n ms mo [Hat Hc] Hh Hinv Hsf.
    destruct (H6 n ms mo Hat Hh Hinv Hsf) as [Hl | (code & mo' & Hx)].
    + left. exact Hl.
    + right. exists code, mo'. split; [exact Hx | exact Hc].
Qed.

Lemma nexit0_code : forall n mo1 code mo2, nexit0 n mo1 code mo2 -> In code [verdict_accept].
Proof.
  intros n mo1 code mo2 [Hx Hc]. destruct n; cbn [nexit] in Hx; try contradiction.
  destruct Hx as [-> _]. cbn in Hc. subst. left. apply bv_eq. vm_compute. reflexivity.
Qed.

(** ** The tree: set_tid_address, then exit_group(0) *)
Definition cls_tree : itree node (exc unit) :=
  ebind (enode NSetTid dec_set_tid) (fun _ : Z => enode (NExit 0) (fun _ : resp => @None unit)).

Lemma cls_tree_impl : forall sp0 brk0 mbase inp draw,
  valid_sp sp0 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase draw) inp ->
  impl psegs (at_node psegs) cls_tree (epost (fun (_ : unit) (_ : machine_state) => True))
       (init_ms psegs p_init_pc p_phdrs sp0 mbase draw inp).
Proof.
  intros sp0 brk0 mbase inp draw VSP VARGV VENVP VLAUNCH LOK. unfold cls_tree.
  eapply impl_ebind; [eapply cls_startup_spec; eassumption |].
  intros a ms' Hat. apply impl_enode. apply evt_done. split; [exact Hat | intros rsp b E; discriminate E].
Qed.

Lemma impl_cls_tree_at0 : forall segs Q ms,
  impl segs (at_node segs) cls_tree Q ms -> impl segs (at_node0 segs) cls_tree Q ms.
Proof.
  intros segs Q ms H. unfold cls_tree, ebind, enode in *. cbn [bind impl] in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [split; [exact Hat | exact I]|].
  intros rsp. specialize (Hk rsp). destruct (dec_set_tid rsp); cbn [bind impl] in *; [| exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 [Hat2 Hk2]. split; [split; [exact Hat2 | reflexivity] | exact Hk2].
Qed.

Lemma cls_tree_leaves : forall mo, minv mo -> leaves_unreachable_m nstep cls_tree mo.
Proof.
  intros mo Hinv tr r mo' Hp. unfold cls_tree in Hp.
  apply tpath_ebind in Hp. destruct Hp as [[Hp _] | (tr1 & a & mo1 & tr2 & H1 & H2 & _)].
  - apply tpath_enode in Hp. destruct Hp as (rsp & Hst & Hr).
    destruct (nstep_dec_set_tid mo rsp mo' tr Hinv Hst) as (_ & t & Hd & _). rewrite Hd in Hr. discriminate Hr.
  - apply tpath_enode in H2. destruct H2 as (rsp & Hst & _). exact Hst.
Qed.

Lemma cls_tree_safe : forall mo, tsafe nstep nsafe cls_tree mo.
Proof.
  intros mo. unfold cls_tree. apply tsafe_ebind. split.
  - apply tsafe_enode. exact I.
  - intros tr a mo' _. apply tsafe_enode. exact I.
Qed.

(** ** The result: on every valid input, from every valid entry, every run of the classifier exits 0 *)
Theorem cls_accepts_all : accepts_all cls_image.
Proof.
  intros f Hf en Hen.
  set (inp := to_proc_input f) in *.
  pose proof (valid_input_either_of_valid_input inp Hf) as VI.
  change cls_image with (mkImage psegs p_init_pc p_phdrs) in *.
  apply (proj1 (must_exit_in_scfg_singleton forced_only_cfg verdict_accept _ _ en inp)).
  apply (must_exit_in_scfg_mono forced_only_cfg alloc_forced_cfg); [apply forced_only_cfg_least | apply run_decided_classic |].
  destruct en as [sp0 brk mb draw].
  pose proof (mo0_minv psegs p_init_pc p_phdrs classifier_alloc_limit (mkEntry sp0 brk mb draw) inp Hen
                (valid_input_either_va_size inp VI) (valid_input_either_reader inp VI)) as Hminv.
  pose proof Hen as VE.
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ VI) in VE.
  destruct VE as (VSP & _ & _ & _ & LOK).
  pose proof (valid_input_either_launch inp VI) as VLAUNCH.
  pose proof VI as VI'. destruct VI' as (VARGV & VENVP & _).
  pose proof (cls_tree_impl sp0 brk mb inp draw VSP VARGV VENVP VLAUNCH LOK) as Himpl.
  set (V := vdso_segments (in_kernel inp) sp0 mb).
  pose proof (impl_lift psegs V cls_tree _ _ (vdso_nonexec _ _ _) Himpl) as Himpl'.
  change (set_rom (seg_rom (psegs ++ V)) (init_ms psegs p_init_pc p_phdrs sp0 mb draw inp))
    with (init_ms (psegs ++ V) p_init_pc p_phdrs sp0 mb draw inp) in Himpl'.
  apply impl_cls_tree_at0 in Himpl'.
  cbn [must_exit_in_scfg]. cbv zeta. unfold run_segments. fold V.
  change (init_config (psegs ++ V) p_init_pc p_phdrs sp0 brk mb draw classifier_alloc_limit inp)
    with (mkCfg (init_machine_state (psegs ++ V) p_init_pc p_phdrs sp0 mb draw inp)
                (mo0 (psegs ++ V) classifier_alloc_limit (mkEntry sp0 brk mb draw) inp)).
  assert (SR : segments_reserved (psegs ++ V) = segments_reserved psegs)
    by exact (run_segments_reserved psegs inp sp0 mb).
  assert (EM : mo0 (psegs ++ V) classifier_alloc_limit (mkEntry sp0 brk mb draw) inp
               = mo0 psegs classifier_alloc_limit (mkEntry sp0 brk mb draw) inp).
  { unfold mo0. cbn [en_sp en_brk en_mmap_base en_draw]. rewrite SR. reflexivity. }
  rewrite EM.
  apply must_exit_in_at_cfg_init_ms.
  apply (impl_run_must_exit2_cfg alloc_forced_cfg node (psegs ++ V) (at_node0 (psegs ++ V)) nstep nexit0 minv nsafe
           (nodes_sound_fo0 (psegs ++ V)) [verdict_accept] cls_tree _ _ _ Himpl').
  - exact (cls_tree_leaves _ Hminv).
  - apply mo0_not_halted.
  - exact Hminv.
  - exact (cls_tree_safe _).
  - exact nexit0_code.
Qed.

(** ** Every classifier row shape for this image *)
Corollary cls_total3 : classifier_total3 cls_image.
Proof. exact (total3_of_accepts_all cls_image cls_accepts_all). Qed.

Corollary cls_rejects_at_most_zero : forall w M, classifier_rejects_at_most cls_image w M 0%Q.
Proof. intros w M. exact (rejects_at_most_zero_of_accepts_all cls_image w M cls_accepts_all). Qed.

Corollary cls_maybe_at_most_zero : forall w M, maybe_at_most cls_image w M 0%Q.
Proof. intros w M. exact (maybe_at_most_zero_of_accepts_all cls_image w M cls_accepts_all). Qed.

(** Planted negative: the theorem is the accept verdict, not the reject one. *)
Fail Check (cls_accepts_all : rejects_all cls_image).

Print Assumptions cls_accepts_all.
Print Assumptions cls_total3.
Print Assumptions cls_rejects_at_most_zero.
Print Assumptions cls_maybe_at_most_zero.
