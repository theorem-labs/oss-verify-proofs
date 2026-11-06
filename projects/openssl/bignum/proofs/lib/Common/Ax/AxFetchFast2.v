(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import AxFetchFast AxDecInt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition wf32 (z : Z) : bool := ((0 <=? z) && (z <? 4294967296))%bool.

Lemma wf32_wf (z : Z) : wf32 z = true -> BvWf 32 z.
Proof. intros H. apply bv_wf_in_range. unfold wf32 in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. change (bv_modulus 32) with 4294967296. lia. Qed.

Definition mkbv32 (z : Z) : bv 32 :=
  match Bool.bool_dec (wf32 z) true with
  | left H => @BV 32 z (wf32_wf z H)
  | right _ => Z_to_bv 32 z
  end.

Lemma mkbv32_eq (z : Z) (b : bv 32) : bv_unsigned b = z -> mkbv32 z = b.
Proof.
  intros <-. apply bv_eq. unfold mkbv32. destruct (Bool.bool_dec (wf32 (bv_unsigned b)) true) as [H|H]; [reflexivity|].
  exfalso. apply H. pose proof (bv_unsigned_in_range 32 b) as R. change (bv_modulus 32) with 4294967296 in R.
  unfold wf32. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Definition fetch_fast2 (segs : list Segment) (pc : w64) : option (bv 32) :=
  if wh pc then fetch_word segs (wbv pc) else
  if PrimInt63.eqb (PrimInt63.mod (wl pc) 2) 0 then
    let a := Uint63.to_Z (wl pc) in
    match find_segment segs a 4 with
    | Some seg =>
        if (seg_executable seg && negb (seg_writable seg))%bool then
          match seg_bytes seg with
          | [c] =>
              let j := Uint63.of_Z (2 * (a - Z.of_N (seg_base seg))) in
              if (2 * (a - Z.of_N (seg_base seg)) + 8 <? 4611686018427387904)%Z && PrimInt63.ltb (PrimInt63.add j 7) (PrimString.length c) then
                match hbyte c j, hbyte c (PrimInt63.add j 2), hbyte c (PrimInt63.add j 4), hbyte c (PrimInt63.add j 6) with
                | Some b0, Some b1, Some b2, Some b3 =>
                    Some (mkbv32 (Uint63.to_Z
                            (PrimInt63.add b0 (PrimInt63.mul 256 (PrimInt63.add b1 (PrimInt63.mul 256
                               (PrimInt63.add b2 (PrimInt63.mul 256 b3))))))))
                | _, _, _, _ => fetch_word segs (wbv pc)
                end
              else fetch_word segs (wbv pc)
          | _ => fetch_word segs (wbv pc)
          end
        else fetch_word segs (wbv pc)
    | None => fetch_word segs (wbv pc)
    end
  else fetch_word segs (wbv pc).

Lemma hbyte_lt (c : PrimString.string) (j v : int) : hbyte c j = Some v -> Uint63.to_Z v < 256.
Proof.
  unfold hbyte. set (h := nyb (PrimString.get c j)). set (l := nyb (PrimString.get c (PrimInt63.add j 1))).
  destruct (PrimInt63.ltb h 16 && PrimInt63.ltb l 16)%bool eqn:E; [|discriminate]. intros H. injection H as <-.
  apply andb_true_iff in E as [E1 E2]. apply Uint63Axioms.ltb_spec in E1. apply Uint63Axioms.ltb_spec in E2.
  change (Uint63Axioms.to_Z 16) with 16 in E1, E2. change Uint63Axioms.to_Z with Uint63.to_Z in E1, E2.
  pose proof (Uint63.to_Z_bounded h). pose proof (Uint63.to_Z_bounded l).
  rewrite tz_add; rewrite ?tz_mul; change (Uint63.to_Z 16) with 16; lia.
Qed.

Theorem fetch_fast2_fast (segs : list Segment) (pc : w64) : fetch_fast2 segs pc = fetch_fast segs pc.
Proof.
  unfold fetch_fast2, fetch_fast. destruct (wh pc); [reflexivity|].
  destruct (PrimInt63.eqb (PrimInt63.mod (wl pc) 2) 0); [|reflexivity]. cbv zeta.
  destruct (find_segment segs (Uint63.to_Z (wl pc)) 4) as [seg|] eqn:Ef; [|reflexivity].
  unfold fetch_fast_b. rewrite Ef.
  destruct (seg_executable seg && negb (seg_writable seg))%bool; [|reflexivity].
  destruct (seg_bytes seg) as [|c [|c' rest]]; try reflexivity.
  change (2 ^ 62) with 4611686018427387904.
  destruct ((2 * (Uint63.to_Z (wl pc) - Z.of_N (seg_base seg)) + 8 <? 4611686018427387904)
            && PrimInt63.ltb (PrimInt63.add (Uint63.of_Z (2 * (Uint63.to_Z (wl pc) - Z.of_N (seg_base seg)))) 7) (PrimString.length c))%bool; [|reflexivity].
  set (j := Uint63.of_Z (2 * (Uint63.to_Z (wl pc) - Z.of_N (seg_base seg)))).
  destruct (hbyte c j) as [b0|] eqn:B0; [|reflexivity].
  destruct (hbyte c (PrimInt63.add j 2)) as [b1|] eqn:B1; [|reflexivity].
  destruct (hbyte c (PrimInt63.add j 4)) as [b2|] eqn:B2; [|reflexivity].
  destruct (hbyte c (PrimInt63.add j 6)) as [b3|] eqn:B3; [|reflexivity].
  f_equal. apply mkbv32_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (hbyte_lt _ _ _ B0). pose proof (hbyte_lt _ _ _ B1). pose proof (hbyte_lt _ _ _ B2). pose proof (hbyte_lt _ _ _ B3).
  pose proof (Uint63.to_Z_bounded b0). pose proof (Uint63.to_Z_bounded b1). pose proof (Uint63.to_Z_bounded b2). pose proof (Uint63.to_Z_bounded b3).
  assert (T3 : Uint63.to_Z (PrimInt63.mul 256 b3) = 256 * Uint63.to_Z b3) by (rewrite tz_mul; change (Uint63.to_Z 256) with 256; lia).
  assert (T2 : Uint63.to_Z (PrimInt63.add b2 (PrimInt63.mul 256 b3)) = Uint63.to_Z b2 + 256 * Uint63.to_Z b3) by (rewrite tz_add; rewrite T3; lia).
  assert (T2' : Uint63.to_Z (PrimInt63.mul 256 (PrimInt63.add b2 (PrimInt63.mul 256 b3))) = 256 * (Uint63.to_Z b2 + 256 * Uint63.to_Z b3))
    by (rewrite tz_mul; change (Uint63.to_Z 256) with 256; rewrite T2; lia).
  assert (T1 : Uint63.to_Z (PrimInt63.add b1 (PrimInt63.mul 256 (PrimInt63.add b2 (PrimInt63.mul 256 b3))))
               = Uint63.to_Z b1 + 256 * (Uint63.to_Z b2 + 256 * Uint63.to_Z b3)) by (rewrite tz_add; rewrite T2'; lia).
  assert (T1' : Uint63.to_Z (PrimInt63.mul 256 (PrimInt63.add b1 (PrimInt63.mul 256 (PrimInt63.add b2 (PrimInt63.mul 256 b3)))))
               = 256 * (Uint63.to_Z b1 + 256 * (Uint63.to_Z b2 + 256 * Uint63.to_Z b3))) by (rewrite tz_mul; change (Uint63.to_Z 256) with 256; rewrite T1; lia).
  rewrite tz_add; rewrite T1'; change (bv_modulus 32) with 4294967296; lia.
Qed.

Theorem fetch_fast2_eq (segs : list Segment) (pc : w64) : fetch_fast2 segs pc = fetch_word segs (wbv pc).
Proof. rewrite fetch_fast2_fast. apply fetch_fast_eq. Qed.

Definition is_ecall_fast (w : bv 32) : bool := (bv_unsigned w =? 115)%Z.

Lemma is_ecall_fast_eq (w : bv 32) : is_ecall_fast w = is_ecall w.
Proof. reflexivity. Qed.
