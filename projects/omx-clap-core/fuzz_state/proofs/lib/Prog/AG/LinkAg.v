From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import StatementHalts Link
  AG.StatementHaltsAg AG.LLVMFuzzerTestOneInputAg.
Import ListNotations.
Local Open Scope Z_scope.

(* The plain slot at the agreement room, closed. The callee contracts of entry_fn do not read the lib shape: from
   frame_facts_plain_ag, frame_facts_plain holds at ls_no_room LS (LS with an empty lib_room), and Link.v's proof of
   slot_callees_plain at that shape gives them. *)

Definition ls_no_room (LS : lib_shape) : lib_shape :=
  {| LIBK := @LIBK LS; LIBK_ext := @LIBK_ext LS; lib_delta := @lib_delta LS; lib_room := fun _ _ => False |}.

Lemma frame_facts_plain_of_ag : forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (empty : Z),
  frame_facts_plain_ag B API LS SH SK empty -> frame_facts_plain B API (ls_no_room LS) SH SK empty.
Proof.
  intros B API LS SH SK empty FF.
  destruct FF as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
    H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & _ & H32).
  unfold frame_facts_plain.
  do 30 (split; [assumption|]).
  split; [intros b n HF; exact (False_ind _ HF) | exact H32].
Qed.

Theorem slot_callees_plain_ag_holds : slot_callees_plain_ag.
Proof.
  intros B API LS SH SK empty FF.
  exact (slot_callees_plain_of (check_round_trip_plain_of parse_items_step_plain_holds) B API (ls_no_room LS) SH SK
    empty (frame_facts_plain_of_ag B API LS SH SK empty FF)).
Qed.

Theorem slot_premise_plain_ag_holds : slot_premise_plain_ag.
Proof. exact (LLVMFuzzerTestOneInput_ag_holds slot_callees_plain_ag_holds). Qed.
