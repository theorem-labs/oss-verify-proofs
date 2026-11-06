(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxFetchFast AxDecInt AxFetchFast2 AsanWBase AsanSRipA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition seg_lo (sg : Segment) : Z := Z.of_N (seg_base sg).
Definition seg_hi (sg : Segment) : Z := Z.of_N (seg_base sg) + Z.of_N (seg_size sg).

Definition disj_from (sg : Segment) (l : list Segment) : bool :=
  forallb (fun s' => (seg_hi sg <=? seg_lo s') || (seg_hi s' <=? seg_lo sg)) l.

Fixpoint segs_disj (l : list Segment) : bool :=
  match l with
  | [] => true
  | sg :: r => disj_from sg r && segs_disj r
  end.

Lemma find_segment_In (segs : list Segment) (a n : Z) (sg : Segment) : find_segment segs a n = Some sg -> In sg segs.
Proof.
  induction segs as [|s0 r IH]; cbn [find_segment]; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - intros H. injection H as <-. left. reflexivity.
  - intros H. right. exact (IH H).
Qed.

Lemma find_segment_unique (segs : list Segment) (a n : Z) (sg : Segment) :
  segs_disj segs = true -> In sg segs -> 0 < n -> seg_lo sg <= a -> a + n <= seg_hi sg -> find_segment segs a n = Some sg.
Proof.
  unfold seg_lo, seg_hi. induction segs as [|s0 r IH]; intros Hd Hin Hn H1 H2; [destruct Hin|].
  cbn [segs_disj] in Hd. apply andb_true_iff in Hd as [Hd0 Hdr]. cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool eqn:E.
  - destruct Hin as [->|Hin]; [reflexivity|]. exfalso.
    apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    unfold disj_from in Hd0. rewrite forallb_forall in Hd0. specialize (Hd0 sg Hin). unfold seg_lo, seg_hi in Hd0.
    apply orb_true_iff in Hd0 as [X|X]; apply Z.leb_le in X; lia.
  - destruct Hin as [->|Hin].
    + exfalso. apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.leb_gt in E]; lia.
    + exact (IH Hdr Hin Hn H1 H2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition word_at (c : PrimString.string) (j : int) : option int :=
  match hbyte c j, hbyte c (PrimInt63.add j 2), hbyte c (PrimInt63.add j 4), hbyte c (PrimInt63.add j 6) with
  | Some b0, Some b1, Some b2, Some b3 =>
      Some (PrimInt63.add b0 (PrimInt63.mul 256 (PrimInt63.add b1 (PrimInt63.mul 256 (PrimInt63.add b2 (PrimInt63.mul 256 b3))))))
  | _, _, _, _ => None
  end.

Lemma word_at_lt (c : PrimString.string) (j x : int) : word_at c j = Some x -> Uint63.to_Z x < 4294967296.
Proof.
  unfold word_at.
  destruct (hbyte c j) as [b0|] eqn:B0; [|discriminate].
  destruct (hbyte c (PrimInt63.add j 2)) as [b1|] eqn:B1; [|discriminate].
  destruct (hbyte c (PrimInt63.add j 4)) as [b2|] eqn:B2; [|discriminate].
  destruct (hbyte c (PrimInt63.add j 6)) as [b3|] eqn:B3; [|discriminate].
  intros H. injection H as <-.
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
  rewrite tz_add; rewrite T1'; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mkbv32_unsigned (z : Z) : 0 <= z < 4294967296 -> bv_unsigned (mkbv32 z) = z.
Proof.
  intros Hz. rewrite (mkbv32_eq z (Z_to_bv 32 z)); rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 32) with 4294967296; exact Hz.
Qed.

(* [comment removed for export] *)
Definition word_ok_i (c : PrimString.string) (bi lo hi : int) (ow : Z * Z) : bool :=
  let o := fst ow in let w := snd ow in
  if ((0 <=? o) && (o <? 4294967296) && (0 <=? w) && (w <? 4294967296))%bool then
    let a := PrimInt63.add bi (Uint63.of_Z o) in
    if (PrimInt63.leb lo a && PrimInt63.leb (PrimInt63.add a 4) hi && PrimInt63.eqb (PrimInt63.mod a 2) 0)%bool then
      let j := PrimInt63.mul 2 (PrimInt63.sub a lo) in
      if PrimInt63.ltb (PrimInt63.add j 7) (PrimString.length c) then
        match word_at c j with
        | Some x => PrimInt63.eqb x (Uint63.of_Z w)
        | None => false
        end
      else false
    else false
  else false.

Definition words_ok_i (segs : list Segment) (base : Z) (ws : list (Z * Z)) : bool :=
  match ws with
  | [] => true
  | ow0 :: _ =>
      match find_segment segs (base + fst ow0) 4 with
      | Some seg =>
          if (seg_executable seg && negb (seg_writable seg) && segs_disj segs
              && (0 <=? base) && (base <? 1152921504606846976) && (seg_hi seg <? 1152921504606846976))%bool then
            match seg_bytes seg with
            | [c] => forallb (word_ok_i c (Uint63.of_Z base) (Uint63.of_Z (seg_lo seg)) (Uint63.of_Z (seg_hi seg))) ws
            | _ => false
            end
          else false
      | None => false
      end
  end.

Lemma tz_of_small (z : Z) : 0 <= z < 2 ^ 62 -> Uint63.to_Z (Uint63.of_Z z) = z.
Proof. intros H. apply tz_small. lia. Qed.

Lemma word_ok_i_sound (segs : list Segment) (seg : Segment) (c : PrimString.string) (base : Z) (ow : Z * Z) :
  segs_disj segs = true -> In seg segs -> (seg_executable seg && negb (seg_writable seg))%bool = true -> seg_bytes seg = [c] ->
  0 <= base < 1152921504606846976 -> seg_hi seg < 1152921504606846976 ->
  word_ok_i c (Uint63.of_Z base) (Uint63.of_Z (seg_lo seg)) (Uint63.of_Z (seg_hi seg)) ow = true ->
  match fetch_word segs (Z_to_bv 64 (base + fst ow)) with Some x => Z.eqb (bv_unsigned x) (snd ow) | None => false end = true.
Proof.
  intros Hd Hin Hx Hc Hb Hhi H. destruct ow as [o w]. unfold word_ok_i in H. cbn [fst snd] in *.
  destruct ((0 <=? o) && (o <? 4294967296) && (0 <=? w) && (w <? 4294967296))%bool eqn:Er; [|discriminate].
  apply andb_true_iff in Er as [Er W2]. apply andb_true_iff in Er as [Er W1]. apply andb_true_iff in Er as [O1 O2].
  apply Z.leb_le in O1. apply Z.ltb_lt in O2. apply Z.leb_le in W1. apply Z.ltb_lt in W2.
  assert (Hlo0 : 0 <= seg_lo seg) by (unfold seg_lo; lia).
  assert (Hlh : seg_lo seg <= seg_hi seg) by (unfold seg_lo, seg_hi; lia).
  set (bi := Uint63.of_Z base) in *. set (lo := Uint63.of_Z (seg_lo seg)) in *. set (hi := Uint63.of_Z (seg_hi seg)) in *.
  assert (Tb : Uint63.to_Z bi = base) by (apply tz_of_small; lia).
  assert (Tl : Uint63.to_Z lo = seg_lo seg) by (apply tz_of_small; lia).
  assert (Th : Uint63.to_Z hi = seg_hi seg) by (apply tz_of_small; lia).
  assert (To : Uint63.to_Z (Uint63.of_Z o) = o) by (apply tz_of_small; lia).
  set (a := PrimInt63.add bi (Uint63.of_Z o)) in *.
  assert (Ta : Uint63.to_Z a = base + o) by (unfold a; rewrite tz_add; rewrite Tb, To; lia).
  destruct (PrimInt63.leb lo a && PrimInt63.leb (PrimInt63.add a 4) hi && PrimInt63.eqb (PrimInt63.mod a 2) 0)%bool eqn:Ec; [|discriminate].
  apply andb_true_iff in Ec as [Ec Eal]. apply andb_true_iff in Ec as [C1 C2].
  apply Uint63Axioms.leb_spec in C1. apply Uint63Axioms.leb_spec in C2. change Uint63Axioms.to_Z with Uint63.to_Z in C1, C2.
  rewrite tz_add in C2 by (rewrite Ta; change (Uint63.to_Z 4) with 4; lia). change (Uint63.to_Z 4) with 4 in C2.
  rewrite Tl, Ta in C1. rewrite Ta, Th in C2.
  set (j := PrimInt63.mul 2 (PrimInt63.sub a lo)) in *.
  assert (Ts : Uint63.to_Z (PrimInt63.sub a lo) = base + o - seg_lo seg) by (rewrite tz_sub; rewrite Ta, Tl; lia).
  assert (Tj : Uint63.to_Z j = 2 * (base + o - seg_lo seg)) by (unfold j; rewrite tz_mul; rewrite Ts; change (Uint63.to_Z 2) with 2; lia).
  destruct (PrimInt63.ltb (PrimInt63.add j 7) (PrimString.length c)) eqn:El; [|discriminate].
  destruct (word_at c j) as [x|] eqn:Ew; [|discriminate].
  pose proof (word_at_lt c j x Ew) as Hlt. pose proof (Uint63.to_Z_bounded x) as Hxb.
  apply Uint63.eqb_spec in H.
  (* [comment removed for export] *)
  assert (Epc : Z_to_bv 64 (base + o) = wbv (W false a)).
  { unfold wbv, wZ. cbn [wh wl]. rewrite Ta. f_equal. }
  rewrite Epc, <- fetch_fast2_eq. unfold fetch_fast2. cbn [wh wl]. rewrite Eal. cbv zeta. rewrite Ta.
  rewrite (find_segment_unique segs (base + o) 4 seg Hd Hin ltac:(lia) C1 C2), Hx, Hc.
  assert (Ej : Uint63.of_Z (2 * (base + o - Z.of_N (seg_base seg))) = j).
  { apply Uint63.to_Z_inj. rewrite Tj. unfold seg_lo. apply tz_of_small. unfold seg_lo in *. lia. }
  rewrite Ej, El.
  replace (2 * (base + o - Z.of_N (seg_base seg)) + 8 <? 4611686018427387904) with true
    by (symmetry; apply Z.ltb_lt; unfold seg_lo in *; lia).
  cbn [andb]. unfold word_at in Ew.
  destruct (hbyte c j) as [b0|]; [|discriminate]. destruct (hbyte c (PrimInt63.add j 2)) as [b1|]; [|discriminate].
  destruct (hbyte c (PrimInt63.add j 4)) as [b2|]; [|discriminate]. destruct (hbyte c (PrimInt63.add j 6)) as [b3|]; [|discriminate].
  injection Ew as Ew. rewrite Ew. apply Z.eqb_eq.
  rewrite mkbv32_unsigned by lia. rewrite H. apply tz_of_small. lia.
Qed.

Theorem words_ok_i_ok (segs : list Segment) (base : Z) (ws : list (Z * Z)) : words_ok_i segs base ws = true -> words_ok segs base ws = true.
Proof.
  unfold words_ok_i, words_ok. destruct ws as [|ow0 r]; [reflexivity|].
  destruct (find_segment segs (base + fst ow0) 4) as [seg|] eqn:Ef; [|discriminate].
  destruct (seg_executable seg && negb (seg_writable seg) && segs_disj segs
            && (0 <=? base) && (base <? 1152921504606846976) && (seg_hi seg <? 1152921504606846976))%bool eqn:Ec; [|discriminate].
  apply andb_true_iff in Ec as [Ec H3]. apply andb_true_iff in Ec as [Ec H2]. apply andb_true_iff in Ec as [Ec H1].
  apply andb_true_iff in Ec as [Hx Hd]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  destruct (seg_bytes seg) as [|c [|c' rest]] eqn:Eb; try discriminate.
  intros H. rewrite forallb_forall in *. intros ow Hin.
  exact (word_ok_i_sound segs seg c base ow Hd (find_segment_In _ _ _ _ Ef) Hx Eb ltac:(lia) H3 (H ow Hin)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pair_ok_f (segs : list Segment) (base o : Z) (rd rd2 : reg) (g : Z) : bool :=
  match fetch_fast2 segs (wofZ (base + o)), fetch_fast2 segs (wofZ (base + (o + 4))) with
  | Some wa, Some wl =>
      match fdecode wa, fdecode wl with
      | Some (Auipc rd' ia, isa), Some (Load SZ8 true rd2' rs il, isl) =>
          Z.eqb isa 4 && Z.eqb isl 4 && bv_eqb rd' rd && bv_eqb rd2' rd2 && bv_eqb rs rd &&
          negb (is_ecall_fast wa) && negb (is_ecall_fast wl) &&
          Z.eqb (bv_unsigned (pcw base (o + bv_signed (bv_concat 32 ia (Z_to_bv 12 0))) + sext 64 il)) g
      | _, _ => false
      end
  | _, _ => false
  end.

Lemma wbv_wofZ64 (z : Z) : wbv (wofZ z) = Z_to_bv 64 z.
Proof.
  unfold wbv. rewrite wZ_wofZ. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with FastWord.two64.
  rewrite Z.mod_mod by (unfold FastWord.two64; lia). reflexivity.
Qed.

Theorem pair_ok_f_eq (segs : list Segment) (base o : Z) (rd rd2 : reg) (g : Z) : pair_ok_f segs base o rd rd2 g = pair_ok segs base o rd rd2 g.
Proof.
  unfold pair_ok_f, pair_ok. rewrite !fetch_fast2_eq, !wbv_wofZ64.
  destruct (fetch_word segs (Z_to_bv 64 (base + o))) as [wa|]; [|reflexivity].
  destruct (fetch_word segs (Z_to_bv 64 (base + (o + 4)))) as [wl|]; [|reflexivity].
  rewrite !fdecode_eq, !is_ecall_fast_eq. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition jal_ok_f (segs : list Segment) (base o : Z) (rd : reg) (tgt : Z) : bool :=
  match fetch_fast2 segs (wofZ (base + o)) with
  | Some w =>
      match fdecode w with
      | Some (Jal rd' imm, isz) => Z.eqb isz 4 && bv_eqb rd' rd && negb (is_ecall_fast w) && Z.eqb (base + o + bv_signed imm) tgt
      | _ => false
      end
  | None => false
  end.

Theorem jal_ok_f_eq (segs : list Segment) (base o : Z) (rd : reg) (tgt : Z) : jal_ok_f segs base o rd tgt = jal_ok segs base o rd tgt.
Proof.
  unfold jal_ok_f, jal_ok. rewrite fetch_fast2_eq, wbv_wofZ64.
  destruct (fetch_word segs (Z_to_bv 64 (base + o))) as [w|]; [|reflexivity].
  rewrite fdecode_eq, is_ecall_fast_eq. reflexivity.
Qed.
