(* The wild-trace room that link's ASan entry contract carries (a Theorem Labs lane's route (a) for ACej, 2026-10-30).
   Measured on fuzz_link.asan (sha256 059dae63e07c):
   - the only allocation site whose stack trace holds a word the input decides is the malloc in text_of (0x87fec);
     text_of has three call sites, all in LLVMFuzzerTestOneInput: op_decide 0x82e24 and 0x82e34, op_write 0x837d8, so one
     op calls it at most twice; the op loop runs at most OPS_MAX = 48 ops (fuzz_link.c:75, :777). One call of the target
     therefore puts at most 96 wild traces into the depot (LINK_WILD_PER_CALL).
   - target_run (0x81ffc) calls LLVMFuzzerTestOneInput in a loop (0x820b4 .. 0x820e8) s5 times, with
     s5 = (first input byte & 3) + 1 (0x82048 .. 0x82050), or 1 for an empty input: at most 4 calls (LINK_CALLS_MAX).
   The pre-condition conjunct of one target call is link_wild_room; its post-condition conjunct is link_wild_call over
   the call's run of depot puts (YGwildCount.depot_run). link_wild_room_calls is the driver's sum over the calls. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01 YGwildCount.
Import ListNotations.

Definition LINK_WILD_PER_CALL : nat := 96.
Definition LINK_CALLS_MAX : nat := 4.

(* pre: room for one call's wild traces *)
Definition link_wild_room (U : Univ) (s : astate) : Prop :=
  (length (wild_part U (st_depot s)) + LINK_WILD_PER_CALL <= u_wmax U)%nat.

(* post: the call's run of puts holds at most LINK_WILD_PER_CALL wild traces *)
Definition link_wild_call (U : Univ) (trs : list (list Z)) : Prop :=
  (length (wild_part U trs) <= LINK_WILD_PER_CALL)%nat.

(* the wild traces of two runs, one after the other *)
Lemma link_wild_call_app : forall U trs1 trs2,
  (length (wild_part U (trs1 ++ trs2)) = length (wild_part U trs1) + length (wild_part U trs2))%nat.
Proof. intros U trs1 trs2. unfold wild_part. rewrite filter_app, length_app. reflexivity. Qed.

(* the driver's sum: from a depot with no wild trace, after runs that put at most i * 96 wild traces, with i < 4 and
   room for 4 * 96, the next call has its room *)
Lemma link_wild_room_calls : forall U d0 trs d i,
  depot_run trs d0 d -> length (wild_part U d0) = 0%nat ->
  (length (wild_part U trs) <= i * LINK_WILD_PER_CALL)%nat -> (i < LINK_CALLS_MAX)%nat ->
  (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax U)%nat ->
  (length (wild_part U d) + LINK_WILD_PER_CALL <= u_wmax U)%nat.
Proof.
  intros U d0 trs d i Hrun H0 Hw Hi Hroom.
  pose proof (depot_run_wild U trs d0 d Hrun) as Hd.
  unfold LINK_CALLS_MAX, LINK_WILD_PER_CALL in *. nia.
Qed.

(* the same in states: the start-up depot is empty (YG01.depot_fits_nil's st_depot = []) *)
Lemma link_wild_room_state : forall U s0 s trs i,
  st_depot s0 = [] -> depot_run trs (st_depot s0) (st_depot s) ->
  (length (wild_part U trs) <= i * LINK_WILD_PER_CALL)%nat -> (i < LINK_CALLS_MAX)%nat ->
  (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax U)%nat -> link_wild_room U s.
Proof.
  intros U s0 s trs i H0 Hrun Hw Hi Hroom. unfold link_wild_room.
  apply (link_wild_room_calls U (st_depot s0) trs (st_depot s) i); auto.
  rewrite H0. reflexivity.
Qed.

(* the room link's universe has: u_wmax = DEPOT_MAX - |u_fix| (YG01.univ_of) with 32 fixed traces is 4064 >= 4 * 96 *)
Lemma link_wild_room_fits : forall U,
  length (u_fix U) = 32%nat -> u_wmax U = (Z.to_nat DEPOT_MAX - length (u_fix U))%nat ->
  (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax U)%nat.
Proof.
  intros U Hf Hw. rewrite Hw, Hf. unfold DEPOT_MAX, LINK_CALLS_MAX, LINK_WILD_PER_CALL. cbn. lia.
Qed.
