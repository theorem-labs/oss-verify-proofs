(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith List Lia.
From Stdlib Require Import Classical IndefiniteDescription.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Monad CMonad Prog ProgC ModelInv ModelInvC ModelOKC EquivPA.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PlainU0 Require Import UImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
(* the informative excluded middle and functional
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



Section Top.
Variable FM : flush_model.
Variable FK : fkit.

Definition plain_implC_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
    implC psegs (at_node psegs) (progC_tree FM psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
          (ms0 psegs p_init_pc p_phdrs en inp).

Definition ubsan_implC_stmt : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
    implC usegs (at_node usegs) (progC_tree FM usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
          (ms0 usegs u_init_pc u_phdrs en inp).

Definition D0 : hist -> bool := fun _ => false.
Definition TPC (lim : Z) : tfam := fun inp en => tree_traces (progD FM D0 psegs PREAD_STAGE inp en) (mo0 psegs lim en inp).
Definition TAC (lim : Z) : tfam := fun inp en => tree_traces (progD FM D0 psegs PREAD_STAGE inp (toP en)) (mo0 psegs lim (toP en) inp).

Definition asan_sideC_stmt (segsX : list Segment) (pcX : N) (phX : PhdrInfo) : Prop :=
  forall lim, 2^31 <= lim -> side_ok segsX pcX phX target_alloc_limit (TAC lim).

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
    oracle_of (fun D => impl psegs (at_node psegs) (progD FM D psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
                             (ms0 psegs p_init_pc p_phdrs en inp)).
  Definition tP : prog_tree (exc unit) := fun inp en => progD FM (DP inp en) psegs PREAD_STAGE inp en.

  Lemma plain_tree_okC : forall lim, 2^31 <= lim ->
    tree_ok psegs p_init_pc p_phdrs lim tP (epost (fun (_ : unit) (_ : machine_state) => True)).
  Proof.
    intros lim Hlim en inp Hen Hinp. unfold tP. split.
    - unfold DP. apply (oracle_of_ok (fun D => impl psegs (at_node psegs) (progD FM D psegs PREAD_STAGE inp en) _ _)).
      destruct (implC_res node psegs (at_node psegs) _ _ _ (plain_implC en inp Hen Hinp)) as [D HD].
      exists D. rewrite res_progC_tree in HD. exact HD.
    - exact (prog_model_ok_plain_DL FM FK lim (DP inp en) PREAD_STAGE en inp Hlim Hen Hinp).
  Qed.


  Section Ubsan.
    Hypothesis ubsan_implC : ubsan_implC_stmt.

    Definition DU (inp : ProcInput) (en : ExecEntry) : hist -> bool :=
      oracle_of (fun D => impl usegs (at_node usegs) (progD FM D usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
                               (ms0 usegs u_init_pc u_phdrs en inp)).
    Definition tU : prog_tree (exc unit) := fun inp en => progD FM (DU inp en) usegs UREAD_STAGE inp en.

    Lemma ubsan_tree_okC :
      tree_ok usegs u_init_pc u_phdrs target_alloc_limit tU (epost (fun (_ : unit) (_ : machine_state) => True)).
    Proof.
      intros en inp Hen Hinp. unfold tU. split.
      - unfold DU. apply (oracle_of_ok (fun D => impl usegs (at_node usegs) (progD FM D usegs UREAD_STAGE inp en) _ _)).
        destruct (implC_res node usegs (at_node usegs) _ _ _ (ubsan_implC en inp Hen Hinp)) as [D HD].
        exists D. rewrite res_progC_tree in HD. exact HD.
      - exact (prog_model_ok_ubsan_D FM FK (DU inp en) UREAD_STAGE en inp Hen Hinp).
    Qed.

    Lemma ubsan_tree_okC_L : forall lim, 2^31 <= lim ->
      tree_ok usegs u_init_pc u_phdrs lim tU (epost (fun (_ : unit) (_ : machine_state) => True)).
    Proof.
      intros lim Hlim en inp Hen Hinp. unfold tU. split.
      - unfold DU. apply (oracle_of_ok (fun D => impl usegs (at_node usegs) (progD FM D usegs UREAD_STAGE inp en) _ _)).
        destruct (implC_res node usegs (at_node usegs) _ _ _ (ubsan_implC en inp Hen Hinp)) as [D HD].
        exists D. rewrite res_progC_tree in HD. exact HD.
      - exact (prog_model_ok_ubsan_DL FM FK lim (DU inp en) UREAD_STAGE en inp Hlim Hen Hinp).
    Qed.

    Lemma trees_equivC : trees_equiv psegs p_init_pc p_phdrs usegs u_init_pc u_phdrs tP tU.
    Proof. intros enS enT inp HS HT Hi. unfold tP, tU. apply (equiv_PU_D FM FK); assumption. Qed.

    (* forced-only port: the trees now give the equivalence over the filtered run. *)
    Theorem zc_base_ubsan_plain :
      strong_universal_error_free_T_scfg alloc_forced_cfg
        (mkImage psegs p_init_pc p_phdrs) (mkImage usegs u_init_pc u_phdrs).
    Proof.
      exact (strong_universal_error_free_from_trees_gen psegs p_init_pc p_phdrs usegs u_init_pc u_phdrs
               tP tU _ _ (plain_tree_okC source_alloc_limit ImgFacts.lim_p) ubsan_tree_okC trees_equivC).
    Qed.

    Theorem zc_base_ubsan :
      strong_universal_error_free_T_scfg_budgets alloc_forced_cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
        (mkImage psegs p_init_pc p_phdrs) (mkImage usegs u_init_pc u_phdrs).
    Proof.
      cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
      apply strong_universal_error_free_T_scfg_budgets_of_scfg. exact zc_base_ubsan_plain.
    Qed.
  End Ubsan.

  Section AsanSide.
    Variables (segsX : list Segment) (pcX : N) (phX : PhdrInfo).
    Hypothesis asan_side : asan_sideC_stmt segsX pcX phX.



  End AsanSide.
End Plain.
End Top.
