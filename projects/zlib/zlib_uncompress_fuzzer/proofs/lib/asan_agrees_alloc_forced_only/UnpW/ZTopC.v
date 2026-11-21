(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import Classical IndefiniteDescription.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import TopLevel. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW Require Import ZTop.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Monad CMonad Prog ProgC ModelInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Spec Require Import ModelOKC EquivPA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
(* allowed-axiom cure (a worker, edition r2, 2026-11-17; a worker and a worker): the informative excluded middle and functional
   choice, proved from Stdlib.Logic.Classical_Prop.classic and
   Stdlib.Logic.IndefiniteDescription.constructive_indefinite_description only (the repository's allowlist), in place of
   ClassicalDescription / ClassicalChoice. Local: no importer sees these names. The same block, byte for byte, in every text. *)
Local Lemma excluded_middle_informative : forall P : Prop, {P} + {~ P}.
Proof.
  intro P.
  assert (E : exists b : bool, if b then P else ~ P).
  { destruct (classic P) as [p|np]; [exists true; exact p | exists false; exact np]. }
  destruct (constructive_indefinite_description _ E) as [[|] H].
  - left; exact H.
  - right; exact H.
Qed.
Local Lemma choice : forall {A B : Type} (R : A -> B -> Prop),
  (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).
Proof.
  intros A B R H.
  exists (fun x => proj1_sig (constructive_indefinite_description _ (H x))).
  intro x. exact (proj2_sig (constructive_indefinite_description _ (H x))).
Qed.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition plain_implC_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
    implC psegs (at_node psegs) (progC_tree psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
          (ms0 psegs p_init_pc p_phdrs en inp).

(* [comment removed for export] *)
Definition D0 : hist -> bool := fun _ => false.
(* [comment removed for export] *)
Definition TPC (lim : Z) : tfam := fun inp en => tree_traces (progD D0 psegs PREAD_STAGE inp en) (mo0 psegs lim en inp).
Definition TAC (lim : Z) : tfam := fun inp en => tree_traces (progD D0 psegs PREAD_STAGE inp (toP en)) (mo0 psegs lim (toP en) inp).

Definition asan_sideC_stmt (segsX : list Segment) (pcX : N) (phX : PhdrInfo) : Prop :=
  forall lim, 2^31 <= lim -> side_ok segsX pcX phX target_alloc_limit (TAC lim).

(* [comment removed for export] *)
Definition oracle_of (P : (hist -> bool) -> Prop) : hist -> bool :=
  match excluded_middle_informative (exists D, P D) with
  | left E => proj1_sig (constructive_indefinite_description P E)
  | right _ => D0
  end.
Lemma oracle_of_ok : forall P, (exists D, P D) -> P (oracle_of P).
Proof.
  intros P E. unfold oracle_of. destruct (excluded_middle_informative (exists D, P D)) as [E'|N]; [| contradiction].
  exact (proj2_sig (constructive_indefinite_description P E')).
Qed.

Section Plain.
  Hypothesis plain_implC : plain_implC_stmt.

  Definition DP (inp : ProcInput) (en : ExecEntry) : hist -> bool :=
    oracle_of (fun D => impl psegs (at_node psegs) (progD D psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
                             (ms0 psegs p_init_pc p_phdrs en inp)).
  Definition tP : prog_tree (exc unit) := fun inp en => progD (DP inp en) psegs PREAD_STAGE inp en.

  Lemma plain_tree_okC : forall lim, 2^31 <= lim ->
    tree_ok psegs p_init_pc p_phdrs lim tP (epost (fun (_ : unit) (_ : machine_state) => True)).
  Proof.
    intros lim Hlim en inp Hen Hinp. unfold tP. split.
    - unfold DP. apply (oracle_of_ok (fun D => impl psegs (at_node psegs) (progD D psegs PREAD_STAGE inp en) _ _)).
      destruct (implC_res node psegs (at_node psegs) _ _ _ (plain_implC en inp Hen Hinp)) as [D HD].
      exists D. rewrite res_progC_tree in HD. exact HD.
    - exact (prog_model_ok_plain_DL lim (DP inp en) PREAD_STAGE en inp Hlim Hen Hinp).
  Qed.

  Lemma plain_side_okC : forall lim, 2^31 <= lim -> side_ok psegs p_init_pc p_phdrs lim
                                 (fun inp en => tree_traces (tP inp en) (mo0 psegs lim en inp)).
  Proof. intros lim Hlim. exact (side_ok_of_tree_ok _ _ _ _ _ _ (plain_tree_okC lim Hlim)). Qed.

  (* [comment removed for export] *)
  Section AsanSide.
    Variables (segsX : list Segment) (pcX : N) (phX : PhdrInfo).
    Hypothesis asan_side : asan_sideC_stmt segsX pcX phX.

    Lemma middleC : forall lim, 2^31 <= lim -> forall enS enT inp,
      valid_entry (mkImage psegs p_init_pc p_phdrs) enS inp -> valid_entry (mkImage segsX pcX phX) enT inp -> valid_input_either inp ->
      trace_equiv (tree_traces (tP inp enS) (mo0 psegs lim enS inp)) (TAC lim inp enT).
    Proof.
      intros lim Hlim enS enT inp HvS HvT Hi. unfold tP, TAC.
      apply (equiv_PP_D lim Hlim); [exact HvS | exact (toP_valid _ _ _ enT inp HvT) | exact Hi].
    Qed.

    Theorem zc_base_asan_plain :
      strong_universal_error_free_T_scfg alloc_forced_cfg (mkImage psegs p_init_pc p_phdrs) (mkImage segsX pcX phX).
    Proof. exact (side_ok_equiv _ _ _ _ _ _ _ (TAC source_alloc_limit) (plain_side_okC _ ImgFacts.lim_p) (asan_side _ ImgFacts.lim_p) (middleC _ ImgFacts.lim_p)). Qed.

    (* [comment removed for export] *)
    Theorem zc_base_asan :
      strong_universal_error_free_T_scfg_budgets alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
        (mkImage psegs p_init_pc p_phdrs) (mkImage segsX pcX phX).
    Proof.
      exact (side_ok_equiv_budgets sanitizer_source_limit target_alloc_limit _ _ _ _ _ _ _ (TAC sanitizer_source_limit)
               (plain_side_okC _ ImgFacts.lim_s) (asan_side _ ImgFacts.lim_s) (middleC _ ImgFacts.lim_s)).
    Qed.
  End AsanSide.
End Plain.
