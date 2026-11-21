(** a worker: the classifier rows of zlib_uncompress3_fuzzer / asan from cls_accepts_all that name no original: the two totality
    rows and the two bound rows.  No iff row here (4-row form, rule 5).

    World: zlib-85kb-rcp-c0dd-r2-clf: every Cla_ / Clb_ module there is the snapshot of
    the release classifier ELF sha256 .  This text Requires only the Cla_ / Clb_ / W_ modules, so it compiles
    whatever the SrcO_ / TgtO_ originals hold (under rule 5 they are the UNPATCHED builds; the iff rows that name them
    are not in this text).  Each image equality below is decided by vm_compute; nothing else here computes.
    No axiom, no parameter, no unfinished proof. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput Classifier Measure.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.W_aefw2_zlib_zlib_uncompress3_fuzzer.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.RowsCommon.

(** ** The classifier image equalities *)

Lemma cla_is_cls_image : (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.phdrs) = OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_image.
Proof. vm_compute. reflexivity. Qed.

Lemma clb_is_cls_image : (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.phdrs) = OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_image.
Proof. vm_compute. reflexivity. Qed.

(** ** accepts_all of both classifier modules *)

Lemma cla_accepts_all : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.accepts_all (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof. rewrite cla_is_cls_image. exact OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_accepts_all. Qed.

Lemma clb_accepts_all : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.accepts_all (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof. rewrite clb_is_cls_image. exact OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.ClsAccept.cls_accepts_all. Qed.

(** ** The four rows *)

Lemma ca_total : LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifier_total_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof. exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.total_of_accepts_all _ cla_accepts_all). Qed.

Lemma cb_total : LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifier_total_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof. exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.total_of_accepts_all _ clb_accepts_all). Qed.

Lemma bound_good : forall b : Q, Qle_bool 0 (b * OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.W_aefw2_zlib_zlib_uncompress3_fuzzer.M) = true ->
  LinuxProcessSemantics.EquivalenceDefinition.Measure.weight_bound_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.phdrs) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.W_aefw2_zlib_zlib_uncompress3_fuzzer.w OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.W_aefw2_zlib_zlib_uncompress3_fuzzer.M b.
Proof.
  intros b Hb.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.RowsCommon.weight_bound_of_accepts_all _ _ _ _ cla_accepts_all
           (Qle_bool_imp_le _ _ Hb)).
Qed.

Lemma bound_diff : forall b : Q, Qle_bool 0 (b * OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.W_aefw2_zlib_zlib_uncompress3_fuzzer.M) = true ->
  LinuxProcessSemantics.EquivalenceDefinition.Measure.weight_bound_T_fo (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.phdrs) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.W_aefw2_zlib_zlib_uncompress3_fuzzer.w OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.W_aefw2_zlib_zlib_uncompress3_fuzzer.M b.
Proof.
  intros b Hb.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.RowsCommon.weight_bound_of_accepts_all _ _ _ _ clb_accepts_all
           (Qle_bool_imp_le _ _ Hb)).
Qed.

(* p2425-w u119: the 2 brk lemmas R24U's cb_iff names, cls-rows-w's o1 text (exact lines 39-45). *)
Lemma src_brk : LinuxProcessSemantics.EquivalenceDefinition.Equivalence.image_brk_satisfiable
  (LinuxProcessSemantics.LinuxProcessSem.MemImageType.img_segments (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tgt_brk : LinuxProcessSemantics.EquivalenceDefinition.Equivalence.image_brk_satisfiable
  (LinuxProcessSemantics.LinuxProcessSem.MemImageType.img_segments (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.init_pc OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.phdrs)) = true.
Proof. vm_compute. reflexivity. Qed.
