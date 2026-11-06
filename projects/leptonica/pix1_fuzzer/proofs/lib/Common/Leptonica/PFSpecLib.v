(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require Import PFLib.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Context {fx : FPState}.   (* [comment removed for export] *)
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Fixpoint img_cstr (a : Z) (fuel : nat) : option (list Z) :=
    match fuel with
    | O => None
    | S f =>
        match seg_rom segs (Z_to_bv 64 a) with
        | Some b => if bv_unsigned b =? 0 then Some [0]
                    else option_map (cons (bv_unsigned b)) (img_cstr (a + 1) f)
        | None => None
        end
    end.

  Lemma img_cstr_sound : forall fuel a bs, img_cstr a fuel = Some bs ->
    (forall i, 0 <= i < Z.of_nat (length bs) ->
       seg_rom segs (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) bs 0)))
    /\ (forall i, 0 <= i < Z.of_nat (length bs) -> 0 <= nth (Z.to_nat i) bs 0 <= 255).
  Proof.
    induction fuel as [|f IH]; intros a bs H; cbn [img_cstr] in H; [discriminate|].
    destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:R; [|discriminate].
    pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
    assert (Rb : seg_rom segs (Z_to_bv 64 (a + 0)) = Some (Z_to_bv 8 (bv_unsigned b))).
    { rewrite Z.add_0_r, R. f_equal. symmetry. apply Z_to_bv_bv_unsigned. }
    destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|NE].
    - inversion H; subst. split.
      + intros i Hi. cbn [length Z.of_nat Pos.of_succ_nat] in Hi. replace i with 0 by lia.
        change (nth (Z.to_nat 0) [0] 0) with 0. rewrite Rb, E. reflexivity.
      + intros i Hi. cbn [length Z.of_nat Pos.of_succ_nat] in Hi. replace i with 0 by lia.
        change (nth (Z.to_nat 0) [0] 0) with 0. lia.
    - destruct (img_cstr (a + 1) f) as [bs'|] eqn:R'; [|discriminate]. cbn [option_map] in H. inversion H; subst.
      destruct (IH _ _ R') as [A B]. split.
      + intros i Hi. cbn [length] in Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
        * exact Rb.
        * replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
          change (nth (S (Z.to_nat (i - 1))) (bv_unsigned b :: bs') 0) with (nth (Z.to_nat (i - 1)) bs' 0).
          replace (a + i) with (a + 1 + (i - 1)) by lia. apply A. lia.
      + intros i Hi. cbn [length] in Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
        * change (nth (Z.to_nat 0) (bv_unsigned b :: bs') 0) with (bv_unsigned b). lia.
        * replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
          change (nth (S (Z.to_nat (i - 1))) (bv_unsigned b :: bs') 0) with (nth (Z.to_nat (i - 1)) bs' 0).
          apply B. lia.
  Qed.

  Fixpoint list_eqbZ (l1 l2 : list Z) : bool :=
    match l1, l2 with
    | [], [] => true
    | x :: r1, y :: r2 => (x =? y) && list_eqbZ r1 r2
    | _, _ => false
    end.
  Lemma list_eqbZ_eq : forall l1 l2, list_eqbZ l1 l2 = true -> l1 = l2.
  Proof.
    induction l1 as [|x r1 IH]; intros [|y r2] H; cbn in H; try discriminate; [reflexivity|].
    apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst. f_equal. apply IH. exact H2.
  Qed.

  (* [comment removed for export] *)
  Definition fmt_check (nS : nat) (lo hi rlo rhi fa : Z) : bool :=
    match img_cstr fa 300 with
    | Some fbs =>
        match fmt_parse fbs with
        | Some its =>
            list_eqbZ (flat its) fbs && wf_items its && class_ok nS (convs its)
            && Nat.leb (length (convs its)) 7
            && (lit_total its + 256 * Z.of_nat (length (convs its)) + 56 <=? 2147483647)
            && (lo <=? fa) && (fa + Z.of_nat (length fbs) <=? hi)
            && (rlo <=? fa) && (fa + Z.of_nat (length fbs) <=? rhi)
        | None => false
        end
    | None => false
    end.

  Lemma fmt_check_sound : forall nS lo hi rlo rhi fa, fmt_check nS lo hi rlo rhi fa = true ->
    exists fbs its,
      (forall i, 0 <= i < Z.of_nat (length fbs) ->
         seg_rom segs (Z_to_bv 64 (fa + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) fbs 0)))
      /\ (forall i, 0 <= i < Z.of_nat (length fbs) -> 0 <= nth (Z.to_nat i) fbs 0 <= 255)
      /\ lo <= fa /\ fa + Z.of_nat (length fbs) <= hi
      /\ rlo <= fa /\ fa + Z.of_nat (length fbs) <= rhi
      /\ flat its = fbs /\ wf_items its = true /\ class_ok nS (convs its) = true
      /\ Z.of_nat (length (convs its)) <= 7
      /\ lit_total its + 256 * Z.of_nat (length (convs its)) + 56 <= 2147483647.
  Proof.
    intros nS lo hi rlo rhi fa H. unfold fmt_check in H.
    destruct (img_cstr fa 300) as [fbs|] eqn:IC; [|discriminate].
    destruct (fmt_parse fbs) as [its|] eqn:FP; [|discriminate].
    apply andb_prop in H as [H R4]. apply andb_prop in H as [H R3]. apply andb_prop in H as [H R2].
    apply andb_prop in H as [H R1]. apply andb_prop in H as [H LT]. apply andb_prop in H as [H N7].
    apply andb_prop in H as [H CL]. apply andb_prop in H as [EQ WFI].
    destruct (img_cstr_sound _ _ _ IC) as [A B].
    exists fbs, its. apply list_eqbZ_eq in EQ. apply Nat.leb_le in N7.
    apply Z.leb_le in R1. apply Z.leb_le in R2. apply Z.leb_le in R3. apply Z.leb_le in R4. apply Z.leb_le in LT.
    split; [exact A|]. split; [exact B|]. repeat split; try assumption; lia.
  Qed.
End WithSegs.
