(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OssFuzzTheorems.openssl.hashtable.images Require Import Plain.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ShapeAlg Spec SpecGen ClaVerdict HTHgTop.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ShapeCfg ConeCfg AsanInit H0Lim H0Full H0FiTail HBFullDefs HtHaltsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition X0 : Image := mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Lemma p_lim_san : (H0Lim.LIM <= SanitizerBudgets.lim_source)%Z.   Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma p_lim_src : (H0Lim.LIM <= source_alloc_limit)%Z.             Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma p_lim_shp : (H0Lim.LIM <= ShippedBudgets.lim_source)%Z.     Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma x_lim_san : (AsanInit.LIMIT <= SanitizerBudgets.lim_target)%Z.  Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma x_lim_tgt : (AsanInit.LIMIT <= target_alloc_limit)%Z.           Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma x_lim_shp : (AsanInit.LIMIT <= ShippedBudgets.lim_source)%Z.    Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.

Section Pair.
  Variable KT : list byte -> Fs.Fs -> TSet.
  Hypothesis LP : H0FiTail.leaf_tail_stmt KT.        (* [comment removed for export] *)
  Hypothesis FX : HBFullDefs.ha_full_stmt KT.       (* [comment removed for export] *)

  Lemma h0_full_all : H0Full.h0_full_stmt KT.
  Proof. exact (H0Full.h0_full KT (H0FiTail.tail_of_leaves KT LP)). Qed.

  (* [comment removed for export] *)
  Lemma hf_shapes_at : forall ls lt, (H0Lim.LIM <= ls)%Z -> (AsanInit.LIMIT <= lt)%Z ->
    forall inp, valid_input inp -> forall en1 en2, valid_entry P0 en1 inp -> valid_entry X0 en2 inp ->
    exists T : TSet,
      ShapeCfg.realizes_cfg ConeCfg.CFG (img_segments P0) (ShapeCfg.init_cfg P0 ls en1 inp) T
      /\ ShapeCfg.realizes_cfg ConeCfg.CFG (img_segments X0) (ShapeCfg.init_cfg X0 lt en2 inp) T.
  Proof.
    intros ls lt Hls Hlt inp Hv [ssp sbrk smb srnd] [tsp tbrk tmb trnd] Hens Hent.
    pose proof (valid_input_va_size _ Hv) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as (Hssp & Hsbrk & Hsmb & Hsfit). destruct Hent as (Htsp & Htbrk & Htmb & Htfit).
    exists (spec_g KT (in_argv inp) (in_fs inp)). split.
    - apply (h0_full_all ls Hls); assumption.
    - exact (FX lt Hlt tsp tbrk tmb trnd inp Htsp Htbrk Htmb Htfit Hv).
  Qed.

  (* [comment removed for export] *)
  Theorem hf_base : strong_universal_error_free_T_scfg_budgets ConeCfg.CFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target P0 X0.
  Proof. apply ShapeCfg.shape_cfg_universal. intros en_s en_t inp Hs Ht Hv _. exact (hf_shapes_at _ _ p_lim_san x_lim_san inp Hv en_s en_t Hs Ht). Qed.

  (* [comment removed for export] *)
  Theorem hf_base_shipped : strong_universal_error_free_T_scfg_budgets ConeCfg.CFG source_alloc_limit target_alloc_limit P0 X0.
  Proof. apply ShapeCfg.shape_cfg_universal. intros en_s en_t inp Hs Ht Hv _. exact (hf_shapes_at _ _ p_lim_src x_lim_tgt inp Hv en_s en_t Hs Ht). Qed.

  Theorem hf_good : forall f, valid_fin_input f -> good_input_s ConeCfg.CFG P0 X0 (to_proc_input f).
  Proof. intros f Hv. apply ShapeCfg.shape_cfg_good_input_s. intros en1 en2 H1 H2. exact (hf_shapes_at _ _ p_lim_src x_lim_tgt (to_proc_input f) Hv en1 en2 H1 H2). Qed.

  Theorem hf_agree : forall f, valid_fin_input f ->
    agree_s ConeCfg.CFG P0 P0 source_alloc_limit (to_proc_input f) /\ agree_s ConeCfg.CFG X0 X0 target_alloc_limit (to_proc_input f).
  Proof.
    intros f Hv. pose proof Hv as Hvi. pose proof (valid_input_va_size _ Hvi) as Hsv48.
    split.
    - apply (ShapeCfg.shape_cfg_agree_s_self ConeCfg.CFG P0 source_alloc_limit (to_proc_input f) (spec_g KT (in_argv (to_proc_input f)) (in_fs (to_proc_input f)))).
      intros [sp brk mb rnd] Hen. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as (H1 & H2 & H3 & H4).
      apply (h0_full_all source_alloc_limit p_lim_src); assumption.
    - apply (ShapeCfg.shape_cfg_agree_s_self ConeCfg.CFG X0 target_alloc_limit (to_proc_input f) (spec_g KT (in_argv (to_proc_input f)) (in_fs (to_proc_input f)))).
      intros [sp brk mb rnd] Hen. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as (H1 & H2 & H3 & H4).
      exact (FX target_alloc_limit x_lim_tgt sp brk mb rnd (to_proc_input f) H1 H2 H3 H4 Hvi).
  Qed.

  (* [comment removed for export] *)
  Theorem full_p16 : HtHaltsLib.full_stmt ConeCfg.CFG P0 ShippedBudgets.lim_source KT.
  Proof. exact (h0_full_all ShippedBudgets.lim_source p_lim_shp). Qed.
  Theorem full_x16 : HtHaltsLib.full_stmt ConeCfg.CFG X0 ShippedBudgets.lim_source KT.
  Proof. exact (FX ShippedBudgets.lim_source x_lim_shp). Qed.
End Pair.
