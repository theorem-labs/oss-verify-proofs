(** a worker (JOB 1 PART B): the six classifier rows of example_large_fuzzer / ubsan from cls_accepts_all.

    World of record: zlib-85kb-rcp-c0dd-r2-clf (a worker; MANIFEST ): every Cla_ / Clb_ module there is the
    snapshot of the release classifier ELF sha256 , and every SrcO_ / TgtO_ module there has the same image
    as its Src_ / Tgt_ module (the originals ARE the #1390 builds: D2, a worker).  Each image equality
    below is decided by vm_compute; nothing else here computes.

    The two iff rows take the pair agreement [strong_universal_error_free_T_scfg cfg Src Tgt] as a hypothesis (the
    package's base theorem, NOT the budgets row of record); the other four rows need nothing.
    No axiom, no parameter, no unfinished proof. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput Classifier Measure.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.W_aefw2_zlib_example_large_fuzzer.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.
Require OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.RowsCommon.

(** ** The image equalities (one per world module) *)

Lemma cla_is_cls_image : (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.phdrs) = OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_image.
Proof. vm_compute. reflexivity. Qed.

Lemma clb_is_cls_image : (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.phdrs) = OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_image.
Proof. vm_compute. reflexivity. Qed.

Lemma src_brk : LinuxProcessSemantics.EquivalenceDefinition.Equivalence.image_brk_satisfiable
  (LinuxProcessSemantics.LinuxProcessSem.MemImageType.img_segments (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tgt_brk : LinuxProcessSemantics.EquivalenceDefinition.Equivalence.image_brk_satisfiable
  (LinuxProcessSemantics.LinuxProcessSem.MemImageType.img_segments (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** accepts_all of both classifier modules *)

Lemma cla_accepts_all : OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.accepts_all (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.phdrs).
Proof. rewrite cla_is_cls_image. exact OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_accepts_all. Qed.

Lemma clb_accepts_all : OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.accepts_all (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.phdrs).
Proof. rewrite clb_is_cls_image. exact OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_accepts_all. Qed.

(** ** The six rows *)

Lemma ca_total : LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifier_total_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.phdrs).
Proof. exact (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.total_of_accepts_all _ cla_accepts_all). Qed.

Lemma cb_total : LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifier_total_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.phdrs).
Proof. exact (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.total_of_accepts_all _ clb_accepts_all). Qed.

Lemma bound_good : forall b : Q, Qle_bool 0 (b * OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.W_aefw2_zlib_example_large_fuzzer.M) = true ->
  LinuxProcessSemantics.EquivalenceDefinition.Measure.weight_bound_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_example_large_fuzzer_ubsan.M.phdrs) OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.W_aefw2_zlib_example_large_fuzzer.w OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.W_aefw2_zlib_example_large_fuzzer.M b.
Proof.
  intros b Hb.
  exact (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.RowsCommon.weight_bound_of_accepts_all _ _ _ _ cla_accepts_all
           (Qle_bool_imp_le _ _ Hb)).
Qed.

Lemma bound_diff : forall b : Q, Qle_bool 0 (b * OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.W_aefw2_zlib_example_large_fuzzer.M) = true ->
  LinuxProcessSemantics.EquivalenceDefinition.Measure.weight_bound_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.loaded_segments OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.init_pc OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_example_large_fuzzer_ubsan.M.phdrs) OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.W_aefw2_zlib_example_large_fuzzer.w OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.W_aefw2_zlib_example_large_fuzzer.M b.
Proof.
  intros b Hb.
  exact (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.RowsCommon.weight_bound_of_accepts_all _ _ _ _ clb_accepts_all
           (Qle_bool_imp_le _ _ Hb)).
Qed.
