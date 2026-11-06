From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

(** slots_of of fuzz_qdisc.c:63-70, which is also what reac_qdisc_etf_catchup_slots computes, over the
    integers: the lead past the qdisc's 300 microsecond delta, in slots at fps, rounded down, then at least 1
    and at most 1000000; a frame rate of 0 or less gives 1. [lead] is the u16 the harness reads. *)
Definition slots_spec (lead fps : Z) : Z :=
  if fps <=? 0 then 1 else
  let n := Z.max 0 (lead - 300) * fps / 1000000 in
  if n <? 1 then 1 else if 1000000 <? n then 1000000 else n.

(** The harness's frame-rate table LLVMFuzzerTestOneInput.fps (fuzz_qdisc.c:95; 24 bytes of .rodata at
    0x103e8 in the plain and the ubsan image). *)
Definition fps_table : list Z := [8000; 4000; 0; -1; 96000; 2147483647].

Lemma slots_spec_range : forall lead fps, 1 <= slots_spec lead fps <= 1000000.
Proof.
  intros lead fps. unfold slots_spec.
  destruct (fps <=? 0); [lia|].
  set (n := Z.max 0 (lead - 300) * fps / 1000000).
  destruct (n <? 1) eqn:E1; [lia|]. destruct (1000000 <? n) eqn:E2; [lia|].
  apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. lia.
Qed.
