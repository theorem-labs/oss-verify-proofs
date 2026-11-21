(* pair 52 (example_large UBSan) with UNPATCHED originals (a worker note
). The frozen method (S/a worker/freeze-r1,
   FREEZE.md5 ) in SOURCE form, the shape of a worker's R47U.v (): each build's run is error-free and its
   traces are the canonical trace set of the harness spec, from that build's OWN walk facts (impl_*_of_zlib,
   zlib_closed_all, prog_model_ok_*, run_of_tree, prog_det / prog_det_U). The unpatched builds take every fact from the
   closure UnpW (the walk renaming of the unpatched texts). prog_det's right side names no image: its canonical trace set
   is Spec/Canon's definitions over the SHARED model Z/ZApiInstL (closure of 21 texts, no image, every text byte-equal in
   the two trees); Spec/Canon and Spec/ZInstL are copied under UnpW only because their Require closure reaches proof texts
   that differ. canonT_UP states the two copies equal; only definitions are unfolded, no lemma of either copy is used.
   x1_srco_tgt, x2_src_tgto: the two cross agreements. ca_iff, cb_iff: the accept-all rows of the pair at its unpatched
   originals; their statements and those of x1 / x2 are R29U.v's with only the pair names changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ITree.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Image.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Stage.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.TopLevel.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Obligations.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Prog.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ZInstL.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ModelInv.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgNoEnomem.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgDet.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zlib_closed.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Impl_closed.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U.Zlib_closed.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U.Impl_closed.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Image.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Stage.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.TopLevel.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Obligations.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Prog.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ZInstL.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ModelInv.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgNoEnomem.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgDet.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zlib_closed.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Impl_closed.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U.Zlib_closed.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U.Impl_closed.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.AgreeCross.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* -- bridge: begin -- *)
(* The canonical trace set of the closure UnpW is the published one: both are the definitions of Spec/Canon.v over
   the same shared model (Z/ZApiInstL.zinstL); only the definitions are unfolded (no lemma of either copy is used). *)
#[local] Transparent OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ZInstL.the_zapiL.
#[local] Transparent OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ZInstL.the_zapiL.

Lemma ct_events_UP : forall (argv : list (list Z)) (fs : Fs) (ok : bool),
  OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.ct_events fs
    (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.ctrace_of argv fs ok)
  = OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.ct_events fs
      (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.ctrace_of argv fs ok).
Proof.
  intros argv fs ok.
  unfold OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.ctrace_of, OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.ctrace_of,
    OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.open_class, OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.open_class,
    OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.file_trace, OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.file_trace,
    OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.cfg_len, OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.cfg_len.
  cbv zeta.
  repeat (match goal with
          | |- context [if ?c then _ else _] => destruct c
          | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
          | |- context [match ?x with nil => _ | cons _ _ => _ end] => destruct x
          end; cbv beta iota).
  all: reflexivity.
Qed.

Lemma canonT_UP : forall (argv : list (list Z)) (fs : Fs) tr,
  OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.canonT argv fs tr
  <-> OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT argv fs tr.
Proof.
  intros argv fs tr.
  unfold OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.canonT, OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT,
    OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.canon_traces, OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canon_traces.
  split; intros (ct & Hin & Hp); destruct Hin as [Hc|[Hc|[]]]; subst ct.
  - exists (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.ctrace_of argv fs false).
    split; [exact (or_introl eq_refl)|]. rewrite <- ct_events_UP. exact Hp.
  - exists (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.ctrace_of argv fs true).
    split; [exact (or_intror (or_introl eq_refl))|]. rewrite <- ct_events_UP. exact Hp.
  - exists (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.ctrace_of argv fs false).
    split; [exact (or_introl eq_refl)|]. rewrite ct_events_UP. exact Hp.
  - exists (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.Canon.ctrace_of argv fs true).
    split; [exact (or_intror (or_introl eq_refl))|]. rewrite ct_events_UP. exact Hp.
Qed.
(* -- bridge: end -- *)

(* the published source build: its own walk facts *)
Lemma side_src : forall (en : ExecEntry) (inp : ProcInput),
  valid_entry (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs) en inp ->
  valid_input inp ->
  ~ bh_errors (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs) source_alloc_limit en inp)
  /\ trace_equiv (bh_traces (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs) source_alloc_limit en inp))
       (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Prog.argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp Hv Hvi.
  pose proof (valid_input_channel_reader inp Hvi) as Hrdr.
  pose proof (valid_input_either_of_valid_input inp Hvi) as Hve.
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Impl_closed.impl_P_of_zlib (fun CE => @OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zlib_closed.zR CE) OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Zlib_closed.zlib_closed_all
                en inp Hv Hvi) as Hi.
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ModelInv.prog_model_ok_P (CE__ := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Obligations.run_ceiling en) en inp Hv Hve
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgDet.run_ceiling_eq _ _ _ _ _ (valid_input_va_size _ Hvi) Hv)) as [Hl Hs].
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.TopLevel.run_of_tree OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Image.psegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs source_alloc_limit
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Obligations.the_prog OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Image.psegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Stage.pstage inp en)
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ITree.epost OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Obligations.the_post)
              en inp Hrdr Hi Hl Hs) as (Htr & Herr & _).
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgDet.prog_det OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgNoEnomem.prog_no_enomem_P en inp Hv Hve) as Hd.
  split; [exact Herr|].
  intro tr. split; intro H.
  - exact (proj1 (Hd tr) (proj1 (Htr tr) H)).
  - exact (proj2 (Htr tr) (proj2 (Hd tr) H)).
Qed.

(* the UNPATCHED source build: every fact from UnpW, then canonT_UP *)
Lemma side_srco : forall (en : ExecEntry) (inp : ProcInput),
  valid_entry (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs) en inp ->
  valid_input inp ->
  ~ bh_errors (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs) source_alloc_limit en inp)
  /\ trace_equiv (bh_traces (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs) source_alloc_limit en inp))
       (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Prog.argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp Hv Hvi.
  pose proof (valid_input_channel_reader inp Hvi) as Hrdr.
  pose proof (valid_input_either_of_valid_input inp Hvi) as Hve.
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Impl_closed.impl_P_of_zlib (fun CE => @OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zlib_closed.zR CE) OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P.Zlib_closed.zlib_closed_all
                en inp Hv Hvi) as Hi.
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ModelInv.prog_model_ok_P (CE__ := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Obligations.run_ceiling en) en inp Hv Hve
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgDet.run_ceiling_eq _ _ _ _ _ (valid_input_va_size _ Hvi) Hv)) as [Hl Hs].
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.TopLevel.run_of_tree OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Image.psegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs source_alloc_limit
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Obligations.the_prog OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Image.psegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Stage.pstage inp en)
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ITree.epost OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Obligations.the_post)
              en inp Hrdr Hi Hl Hs) as (Htr & Herr & _).
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgDet.prog_det OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgNoEnomem.prog_no_enomem_P en inp Hv Hve) as Hd.
  split; [exact Herr|].
  intro tr. split; intro H.
  - exact (proj1 (canonT_UP _ _ tr) (proj1 (Hd tr) (proj1 (Htr tr) H))).
  - exact (proj2 (Htr tr) (proj2 (Hd tr) (proj2 (canonT_UP _ _ tr) H))).
Qed.

(* the published target build: its own walk facts *)
Lemma side_tgt : forall (en : ExecEntry) (inp : ProcInput),
  valid_entry (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs) en inp ->
  valid_input inp ->
  ~ bh_errors (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs) target_alloc_limit en inp)
  /\ trace_equiv (bh_traces (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs) target_alloc_limit en inp))
       (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Prog.argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp Hv Hvi.
  pose proof (valid_input_channel_reader inp Hvi) as Hrdr.
  pose proof (valid_input_either_of_valid_input inp Hvi) as Hve.
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U.Impl_closed.impl_U_of_zlib (fun CE => @OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U.Zlib_closed.zR CE) OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U.Zlib_closed.zlib_closed_all
                en inp Hv Hvi) as Hi.
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ModelInv.prog_model_ok_U (CE__ := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Obligations.run_ceiling en) en inp Hv Hve
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgDet.run_ceiling_eq _ _ _ _ _ (valid_input_va_size _ Hvi) Hv)) as [Hl Hs].
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.TopLevel.run_of_tree OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Image.usegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs target_alloc_limit
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Obligations.the_prog OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Image.usegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Stage.ustage inp en)
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ITree.epost OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Obligations.the_post)
              en inp Hrdr Hi Hl Hs) as (Htr & Herr & _).
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgDet.prog_det_U OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.ProgNoEnomem.prog_no_enomem_U en inp Hv Hve) as Hd.
  split; [exact Herr|].
  intro tr. split; intro H.
  - exact (proj1 (Hd tr) (proj1 (Htr tr) H)).
  - exact (proj2 (Htr tr) (proj2 (Hd tr) H)).
Qed.

(* the UNPATCHED target build: every fact from UnpW, then canonT_UP *)
Lemma side_tgto : forall (en : ExecEntry) (inp : ProcInput),
  valid_entry (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs) en inp ->
  valid_input inp ->
  ~ bh_errors (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs) target_alloc_limit en inp)
  /\ trace_equiv (bh_traces (run_scfg alloc_forced_cfg (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs) target_alloc_limit en inp))
       (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Prog.argv_Z (in_argv inp)) (in_fs inp)).
Proof.
  intros en inp Hv Hvi.
  pose proof (valid_input_channel_reader inp Hvi) as Hrdr.
  pose proof (valid_input_either_of_valid_input inp Hvi) as Hve.
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U.Impl_closed.impl_U_of_zlib (fun CE => @OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U.Zlib_closed.zR CE) OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U.Zlib_closed.zlib_closed_all
                en inp Hv Hvi) as Hi.
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ModelInv.prog_model_ok_U (CE__ := OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Obligations.run_ceiling en) en inp Hv Hve
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgDet.run_ceiling_eq _ _ _ _ _ (valid_input_va_size _ Hvi) Hv)) as [Hl Hs].
  destruct (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.TopLevel.run_of_tree OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Image.usegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs target_alloc_limit
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Obligations.the_prog OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Image.usegs OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib.Stage.ustage inp en)
              (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.ITree.epost OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Obligations.the_post)
              en inp Hrdr Hi Hl Hs) as (Htr & Herr & _).
  pose proof (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgDet.prog_det_U OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec.ProgNoEnomem.prog_no_enomem_U en inp Hv Hve) as Hd.
  split; [exact Herr|].
  intro tr. split; intro H.
  - exact (proj1 (canonT_UP _ _ tr) (proj1 (Hd tr) (proj1 (Htr tr) H))).
  - exact (proj2 (Htr tr) (proj2 (Hd tr) (proj2 (canonT_UP _ _ tr) H))).
Qed.

(* Two sides that each run error-free with the canonical trace set agree, error-free (generic in the images). *)
Lemma xcombine : forall imgS imgT,
  (forall (en : ExecEntry) (inp : ProcInput), valid_entry imgS en inp -> valid_input inp ->
     ~ bh_errors (run_scfg alloc_forced_cfg imgS source_alloc_limit en inp)
     /\ trace_equiv (bh_traces (run_scfg alloc_forced_cfg imgS source_alloc_limit en inp))
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT
             (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Prog.argv_Z (in_argv inp)) (in_fs inp))) ->
  (forall (en : ExecEntry) (inp : ProcInput), valid_entry imgT en inp -> valid_input inp ->
     ~ bh_errors (run_scfg alloc_forced_cfg imgT target_alloc_limit en inp)
     /\ trace_equiv (bh_traces (run_scfg alloc_forced_cfg imgT target_alloc_limit en inp))
          (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Canon.canonT
             (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.Prog.argv_Z (in_argv inp)) (in_fs inp))) ->
  strong_universal_error_free_T_scfg alloc_forced_cfg imgS imgT.
Proof.
  intros imgS imgT HS HT enS enT inp HvS HvT Hvi.
  destruct (HS enS inp HvS Hvi) as [HeS HtS]. destruct (HT enT inp HvT Hvi) as [HeT HtT].
  split; [exact HeS|]. split; [exact HeT|].
  intro tr. split; intro H.
  - exact (proj2 (HtT tr) (proj1 (HtS tr) H)).
  - exact (proj2 (HtS tr) (proj1 (HtT tr) H)).
Qed.

Theorem x1_srco_tgt :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs).
Proof. exact (xcombine _ _ side_srco side_tgt). Qed.

Theorem x2_src_tgto :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs).
Proof. exact (xcombine _ _ side_src side_tgto). Qed.

Lemma ca_iff : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs) ->
  LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifies_good_inputs_T_s cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  intros cfg T.
  exact (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.classifies_of_accepts_all cfg _ _ _ T
           OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_example_large_fuzzer_ubsan.cla_accepts_all).
Qed.

Lemma cb_iff : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs) ->
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs) ->
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs) ->
  LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifies_patch_diff_T_s cfg
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  intros cfg X1 B X2.
  exact (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.AgreeCross.cb_iff_of_cross cfg _ _ _ _ _ X1 B X2
           OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_example_large_fuzzer_ubsan.src_brk
           OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_example_large_fuzzer_ubsan.tgt_brk
           OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_example_large_fuzzer_ubsan.clb_accepts_all).
Qed.
