(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Frame Exec Cfg ITree Nodes RegsEquiv FP.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require SpinAlg ShapeAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_TopLevelGen () := "c59OSSVerify5KrLib4LibA;TopLevelGen4tfamC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List2hdI47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run8run_scfgC4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgC4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgI4ELinuxProcessSemantics?LinuxProcessSem3RunDall_traces_error_cfg00C4ELinuxProcessSemantics?LinuxProcessSem3RunEreaches_unmodeled_cfgK4ELinuxProcessSemantics?LinuxProcessSem3Run8behavior01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem3Run8behavior00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C49OSSVerify5KrLib8TopLevel9prog_treeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel;tree_tracesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevelCtree_traces_no_killC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA;TopLevelGen<tfam_no_killC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C49OSSVerify5KrLib8TopLevel7tree_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel;run_of_treeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3ms0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC49OSSVerify5KrLib8TopLevelJvalid_input_either_va_sizeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<bh_unmodeledC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence>dies_by_signalC47Corelib4Init5Logic3notK47Corelib4Init5Logic3and01c59OSSVerify5KrLib4LibA;TopLevelGen7side_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I59OSSVerify5KrLib2AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgAsrealizes_obs_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SpinAlgBsrealizes_no_errorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA;TopLevelGen?run_init_configC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS7SpinAlg9srealizes03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA;TopLevelGenDside_ok_of_srealizesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tfam : Type := ProcInput -> ExecEntry -> list event -> Prop.

Definition side_ok (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) (T : tfam) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim en inp)) (T inp en)
    /\ ~ bh_errors (run_scfg ACFG (mkImage segs pc ph) lim en inp).

(* [comment removed for export] *)
Lemma run_init_config : forall segs pc ph lim en inp,
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  run_scfg ACFG (mkImage segs pc ph) lim en inp =
  {| bh_traces := obs_trace_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_errors := reaches_error_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_all_errors := all_traces_error_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp);
     bh_unmodeled := reaches_unmodeled_cfg segs ACFG (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) |}.
Proof. intros segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

(* [comment removed for export] *)
Definition tfam_no_kill (T : tfam) : Prop :=
  forall inp en tr, T inp en tr -> forall sig fs, ~ In (KillEv sig fs) tr.

Lemma tfam_no_kill_tree : forall {R : Type} segs lim (t : prog_tree R),
  tfam_no_kill (fun inp en => tree_traces (t inp en) (mo0 segs lim en inp)).
Proof.
ltac2:(KReplay.run1 (kr_t_TopLevelGen ()) [] "h02enh13inph21Hh31Rh43limh54segsh61th72trp;1p;4p;5p;3p200R0g00HiR1p4p710p8P0g00I`R2p4p710p8P0g00JYR3p4p710p8g002Mj11TP1j16Tg00KZj40TP2j42j34TP3j55Tg00LKj13Tg00@o#1g00CLf2R3#6g00DbR2g00CjR1g00MM#1f6R4f3R5P3f1R6O2f5R7f4R8P6P3C0f0R9C2f7P8P5P3O2P4P7P3P5C0P6P9D5W2W7W0W1P3P6P9O2P8P5P9P6C0547X01X12#3eW6W4W5X30o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma side_ok_of_tree_ok : forall {R : Type} segs pc ph lim (t : prog_tree R) (Q : R -> machine_state -> Prop),
  tree_ok segs pc ph lim t Q ->
  side_ok segs pc ph lim (fun inp en => tree_traces (t inp en) (mo0 segs lim en inp)).
Proof.
  intros R segs pc ph lim t Q HT en inp Hv Hi.
  destruct (HT en inp Hv Hi) as (Himpl & Hleaves & Hsafe).
  destruct (run_of_tree segs pc ph lim (t inp en) Q en inp Hv (valid_input_either_va_size _ Hi) Himpl Hleaves Hsafe) as (Htr & Herr & _).
  split; [exact Htr| exact Herr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma side_ok_of_srealizes : forall segs pc ph lim (T : tfam),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
      SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T inp en)) ->
  side_ok segs pc ph lim T.
Proof.
  intros segs pc ph lim T H en inp Hv Hi. specialize (H en inp Hv Hi).
  rewrite run_init_config. cbn [bh_traces bh_errors]. split.
  - intros tr. apply SpinAlg.srealizes_obs_iff. exact H.
  - eapply SpinAlg.srealizes_no_error. exact H.
Qed.

(* [comment removed for export] *)
Lemma side_ok_of_srealizes_eq : forall segs pc ph lim (T T' : tfam),
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
      SpinAlg.srealizes segs (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) (T' inp en)
      /\ ShapeAlg.t_eq (T' inp en) (T inp en)) ->
  side_ok segs pc ph lim T.
Proof.
  intros segs pc ph lim T T' H. apply side_ok_of_srealizes.
  intros en inp Hv Hi. destruct (H en inp Hv Hi) as [Hs Heq].
  eapply SpinAlg.srz_conseq; [exact Hs| exact Heq].
Qed.
