(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require ShapeAlg Spec SpecNoKill.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import ProgP ModelOK EquivZP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SPEC : list (list byte) -> Fs.Fs -> list event -> Prop := Common.Spec.spec.
Definition TSU : tfam := fun inp _ => SPEC (in_argv inp) (in_fs inp).

Lemma SPEC_nil : forall argv fs, SPEC argv fs [].
Proof.
  intros argv fs. unfold SPEC, Common.Spec.spec.
  assert (D : forall msg f, Common.Spec.t_die msg f []) by (intros; apply Common.ShapeAlg.t_emit_has_nil).
  assert (A2 : forall (A B : Common.ShapeAlg.TSet), A [] -> Common.ShapeAlg.t_alt2 A B []).
  { intros A B HA. left. exact HA. }
  destruct argv as [|a0 [|path [|x l]]]; try apply D.
  destruct (4096 <=? length path)%nat; [apply D|].
  destruct (Common.Spec.list_byte_eqb path []); [apply D|].
  destruct (Common.Spec.list_byte_eqb path Common.Spec.dot_path); [apply A2, D|].
  destruct (fs_lookup fs path); [apply A2, D | apply D].
Qed.

Lemma NOKILL : tfam_no_kill TSU.
Proof.
  intros inp en tr H sig fs Hin.
  pose proof (Common.SpecNoKill.spec_nokill (in_argv inp) (in_fs inp) tr H) as HF.
  rewrite Forall_forall in HF. exact (HF _ Hin).
Qed.

(* [comment removed for export] *)
Definition pimpl_stmt (segs : list Segment) (pc : N) (ph : PhdrInfo) (rs : Z) : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    impl segs (at_node segs) (ProgP.prog segs rs inp en) (epost (fun (_ : unit) (_ : machine_state) => True)) (ms0 segs pc ph en inp).

(* [comment removed for export] *)
Theorem plain_side_ok : pimpl_stmt psegs p_init_pc p_phdrs PREAD_STAGE ->
  side_ok psegs p_init_pc p_phdrs source_alloc_limit TSU.
Proof.
  intros PIMPL en inp Hv Hi.
  assert (TOK : tree_ok psegs p_init_pc p_phdrs source_alloc_limit (ProgP.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True))).
  { intros en' inp' Hv' Hi'. split; [exact (PIMPL en' inp' Hv' Hi')| exact (prog_model_ok_plain PREAD_STAGE en' inp' Hv' Hi')]. }
  destruct (side_ok_of_tree_ok _ _ _ _ _ _ TOK en inp Hv Hi) as [Htr Herr].
  split; [| exact Herr].
  eapply trace_equiv_trans; [exact Htr|]. intros tr. exact (tfam_plain PREAD_STAGE en inp Hv Hi tr).
Qed.

(* [comment removed for export] *)
Theorem plain_side_ok_lim : forall lim, 2^31 <= lim -> pimpl_stmt psegs p_init_pc p_phdrs PREAD_STAGE ->
  side_ok psegs p_init_pc p_phdrs lim TSU.
Proof.
  intros lim Hlim PIMPL en inp Hv Hi.
  assert (TOK : tree_ok psegs p_init_pc p_phdrs lim (ProgP.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True))).
  { intros en' inp' Hv' Hi'. split; [exact (PIMPL en' inp' Hv' Hi')| exact (prog_model_ok_plain_lim lim Hlim PREAD_STAGE en' inp' Hv' Hi')]. }
  destruct (side_ok_of_tree_ok _ _ _ _ _ _ TOK en inp Hv Hi) as [Htr Herr].
  split; [| exact Herr].
  eapply trace_equiv_trans; [exact Htr|]. intros tr. exact (tfam_plain_lim lim Hlim PREAD_STAGE en inp Hv Hi tr).
Qed.

Theorem plain_side_ok_san : pimpl_stmt psegs p_init_pc p_phdrs PREAD_STAGE ->
  side_ok psegs p_init_pc p_phdrs SanitizerBudgets.lim_source TSU.
Proof. intros PIMPL. apply (plain_side_ok_lim SanitizerBudgets.lim_source); [vm_compute; discriminate| exact PIMPL]. Qed.

(* [comment removed for export] *)
Theorem side_ok_equiv_budgets_abort_lim :
  forall (limS limT : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS limS TS ->
    side_ok segsT pcT phT limT TT ->
    tfam_no_kill TS ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets_abort ACFG limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros limS limT segsS pcS phS segsT pcT phT TS TT HS HT HNK HEQ.
  intros enS enT inp HvS HvT Hvi0 _.
  pose proof (valid_input_either_of_valid_input_abort _ Hvi0) as Hvi.
  destruct (HS enS inp HvS Hvi) as [HtrS HerrS].
  destruct (HT enT inp HvT Hvi) as [HtrT HerrT].
  pose proof (HEQ enS enT inp HvS HvT Hvi) as Hst.
  split; [| split].
  - split; [exact HerrS|]. intros (tr & sig & fs & Hb & Hin).
    apply (proj1 (HtrS tr)) in Hb. exact (HNK _ _ _ Hb sig fs Hin).
  - split; [exact HerrT|]. intros (tr & sig & fs & Hb & Hin).
    apply (proj1 (HtrT tr)) in Hb. apply (proj2 (Hst tr)) in Hb. exact (HNK _ _ _ Hb sig fs Hin).
  - eapply trace_equiv_trans; [exact HtrS|].
    eapply trace_equiv_trans; [exact Hst|].
    apply trace_equiv_sym. exact HtrT.
Qed.

(* [comment removed for export] *)
Theorem ubsan_side_ok : pimpl_stmt usegs u_init_pc u_phdrs UREAD_STAGE ->
  side_ok usegs u_init_pc u_phdrs target_alloc_limit TSU.
Proof.
  intros UIMPL en inp Hv Hi.
  assert (TOK : tree_ok usegs u_init_pc u_phdrs target_alloc_limit (ProgP.prog usegs UREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True))).
  { intros en' inp' Hv' Hi'. split; [exact (UIMPL en' inp' Hv' Hi')| exact (prog_model_ok_ubsan UREAD_STAGE en' inp' Hv' Hi')]. }
  destruct (side_ok_of_tree_ok _ _ _ _ _ _ TOK en inp Hv Hi) as [Htr Herr].
  split; [| exact Herr].
  eapply trace_equiv_trans; [exact Htr|]. intros tr. exact (tfam_ubsan UREAD_STAGE en inp Hv Hi tr).
Qed.

(* [comment removed for export] *)
Section Pair.
  Hypothesis PIMPL : pimpl_stmt psegs p_init_pc p_phdrs PREAD_STAGE.
  Hypothesis UIMPL : pimpl_stmt usegs u_init_pc u_phdrs UREAD_STAGE.

  (* [comment removed for export] *)
  Theorem base_ubsan :
    strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs) (mkImage usegs u_init_pc u_phdrs).
  Proof.
    eapply (side_ok_equiv_budgets_abort _ _ _ _ _ _ TSU TSU); [exact (plain_side_ok PIMPL) | exact (ubsan_side_ok UIMPL) | exact NOKILL |].
    intros enS enT inp HvS HvT Hi tr. reflexivity.
  Qed.

  (* [comment removed for export] *)
End Pair.
