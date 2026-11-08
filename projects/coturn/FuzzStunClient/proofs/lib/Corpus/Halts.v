(* The halting theorems of this fuzz target's plain and UBSan builds.

   Both builds realize the driver specification [Spec.spec]: [RefMain.ref_realizes_spec] at [source_alloc_limit] and
   [UbMain.ub_realizes_spec] at [target_alloc_limit].  [ShapeAlg.realizes] is an inductive with three constructors and
   no silent-loop case, so a realized trace set whose every exit is in [codes02] gives
   [must_exit_in_at_cfg forced_only_cfg] by one induction ([Corpus.HaltsFO.fo_of_realizes]), and
   [Corpus.SpecShape.shape_ok_spec] is that fact about the specification.

   The plain build is realized at the budget the statement names, so its theorem is immediate.  The UBSan build is
   realized at 512 GiB and the statement asks for 16 GiB, so its theorem goes through
   [Corpus.LimSimSys.must_exit_in_scfg_relim_closed], which lowers the limit on the statement's own budget premise.

   The two AddressSanitizer builds are not here.  Their closures are built with [SpinAlg.srealizes], whose [srz_spin]
   constructor admits a silent infinite loop and is used at [Common/NoReserve.v:518] and [:737] for a refused mmap and
   at [Asan/AsanPlanSound.v:6993] for the plan's [PSpin] node, so [srealizes] does not imply halting and no induction
   here can make it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.RefMain.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.UbMain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require Import HaltsFO SpecShape LimSimSys.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma source_le_target : (Budgets.Standard.lim_source <= target_alloc_limit)%Z.
Proof. apply Z.leb_le. reflexivity. Qed.

Theorem coturn_fuzzstunclient_plain_halts :
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
  rewrite halts_within_budget_is_lps.
  apply halts_allowed_T_scfg_budgets_of_scfg.
  intros [sp brk mb rnd] inp Hen Hinp.
  cbn [must_exit_in_scfg].
  apply (fo_exits_must_exit Plain.M.loaded_segments Exits.ok_or_refused _
           (spec (in_argv inp) (in_fs inp))).
  - apply fo_of_realizes.
    exact (OSSVerify.Proofs.coturn.FuzzStunClient.lib.RefMain.ref_realizes_spec
             sp brk mb rnd inp Hen Hinp).
  - exact (shape_ok_spec (in_argv inp) (in_fs inp)).
  - reflexivity.
Qed.

Theorem coturn_fuzzstunclient_ubsan_halts :
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  rewrite halts_within_budget_is_lps.
  intros [sp brk mb rnd] inp Hen Hinp Hbud.
  apply (must_exit_in_scfg_relim_closed forced_only_cfg Exits.ok_or_refused
           (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs)
           target_alloc_limit Budgets.Standard.lim_source (mkEntry sp brk mb rnd) inp
           source_le_target Hbud).
  cbn [must_exit_in_scfg].
  apply (fo_exits_must_exit Ubsan.M.loaded_segments Exits.ok_or_refused _
           (spec (in_argv inp) (in_fs inp))).
  - apply fo_of_realizes.
    exact (OSSVerify.Proofs.coturn.FuzzStunClient.lib.UbMain.ub_realizes_spec
             sp brk mb rnd inp Hen Hinp).
  - exact (shape_ok_spec (in_argv inp) (in_fs inp)).
  - reflexivity.
Qed.
