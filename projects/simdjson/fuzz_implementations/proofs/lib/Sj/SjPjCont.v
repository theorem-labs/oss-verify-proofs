(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjTape SjTapeInv SjTapeList SjTapeTile SjPjSer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition ae_u (t : Z) : Z := Z.land (t + -91) 18446744073709551615.
Definition ae_num (t : Z) : Z := Z.land (Z.land (Z.shiftr 67240448 (Z.land (ae_u t) 63)) 18446744073709551615) 1.
Definition ae_cont (t : Z) : Z := Z.land (Z.land (Z.shiftr 4294967297 (Z.land (ae_u t) 63)) 18446744073709551615) 1.

Definition ae_next (w x x' : Z) : Prop :=
  let t := ttype w in
  (32 < ae_u t /\ x' = x + 1)
  \/ (ae_u t <= 32 /\ ae_num t = 0 /\ ae_cont t = 0 /\ x' = x + 1)
  \/ (ae_u t <= 32 /\ ae_num t <> 0 /\ x' = x + 2)
  \/ (ae_u t <= 32 /\ ae_num t = 0 /\ ae_cont t <> 0 /\ x' = Z.land w 4294967295).

Lemma land_low32 : forall w, Z.land w 4294967295 = tnext w.
Proof. intros w. unfold tnext. change 4294967295 with (Z.ones 32). apply Z.land_ones. lia. Qed.

Section After.
  Variable T : Z -> Z.
  Variable S : Z -> Z.
  Variable sn : Z.
  Hypothesis Hsn : 0 <= sn < 2^56.

  Lemma elemS_word : forall d x x' c c1, elemS T S sn ck_any d x x' c c1 -> 0 <= x -> x' < 2^32 -> 0 <= T x < 2^64.
  Proof.
    intros d x x' c c1 H Hx Hx'.
    destruct (ser_view_of T S sn Hsn _ _ _ _ _ H Hx Hx') as [Hw _ _|Hw _ _|l Hw _ _ _ _|d' e' n' _ Hw _ _ _ _|d' e' n' _ Hw _ _ _ _];
      try (destruct Hw as [Hw|[Hw|Hw]]); (eapply ttype_range; [exact Hw|]);
      unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj; lia.
  Qed.

  Lemma elemS_after : forall d x x' c c1, elemS T S sn ck_any d x x' c c1 -> 0 <= x -> x' < 2^32 -> ae_next (T x) x x'.
  Proof.
    intros d x x' c c1 H Hx Hx'. unfold ae_next.
    destruct (ser_view_of T S sn Hsn _ _ _ _ _ H Hx Hx') as [Hw Ej Ec|Hw Ej Ec|l Hw Hv Ej Hs Ec|d' e' n' Ed Hw Ej Hn He Ht|d' e' n' Ed Hw Ej Hn He Ht];
      unfold SjTape.ty in Hw.
    - right; left. destruct Hw as [Hw|[Hw|Hw]]; rewrite Hw;
        (split; [apply Z.leb_le; vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity| exact Ej]).
    - right; right; left. destruct Hw as [Hw|[Hw|Hw]]; rewrite Hw;
        (split; [apply Z.leb_le; vm_compute; reflexivity|]); (split; [vm_compute; discriminate| exact Ej]).
    - left. rewrite Hw. split; [apply Z.ltb_lt; vm_compute; reflexivity| exact Ej].
    - right; right; right. rewrite Hw. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [vm_compute; discriminate|]. rewrite land_low32. lia.
    - right; right; right. rewrite Hw. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
      split; [vm_compute; discriminate|]. rewrite land_low32. lia.
  Qed.
End After.
