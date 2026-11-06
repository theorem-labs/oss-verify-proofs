(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require FrmKeep FrmKeepC.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMF.

Lemma expand_c_safe (c : cinstr) : FrmKeep.FRM.instr_frm_safe (expand_c c) = true.
Proof. destruct c; reflexivity. Qed.

Ltac dcrush1 :=
  match goal with
  | H : ?o <> ?o |- _ => exfalso; exact (H eq_refl)
  | |- ?l = ?l => reflexivity
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end;
      first [ is_var x; destruct x | destruct x ]; cbv beta iota
  end.
Ltac dcrush := repeat dcrush1.

Lemma decode_safe (w : bv 32) :
  bv_unsigned (bits 0 7 w) <> 115 ->
  match decode w with Some i => FrmKeep.FRM.instr_frm_safe i | None => true end = true.
Proof.
  intros NE. cbv beta zeta delta [decode].
  remember (bv_unsigned (bits 0 7 w)) as o eqn:Ho. clear Ho.
  dcrush; reflexivity.
Qed.

Lemma low7_bits (w : bv 32) : bv_unsigned (bits 0 7 w) = bv_unsigned w mod 128.
Proof. unfold bits. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.

Theorem safe_unless_system (w : bv 32) : bv_unsigned w mod 128 <> 115 -> FrmKeep.FRM.word_frm_safe w = true.
Proof.
  intros NE. unfold FrmKeep.FRM.word_frm_safe, decode_any.
  destruct (decide _) as [E3|N3].
  - pose proof (decode_safe w ltac:(rewrite low7_bits; exact NE)) as D.
    destruct (decode w) as [i|]; [exact D| reflexivity].
  - destruct (decode16 _) as [c|]; [apply expand_c_safe| reflexivity].
Qed.
Corollary safe_unless_systemC (w : bv 32) : bv_unsigned w mod 128 <> 115 -> FrmKeepC.FRMC.word_frm_safe w = true.
Proof. intros NE. apply FrmKeepC.FRMC.safe_of_coarse, safe_unless_system, NE. Qed.

Lemma low7_concat (X : bv 16) (b1 b0 : bv 8) :
  bv_unsigned (bv_concat 32 X (bv_concat 16 b1 b0)) mod 128 = bv_unsigned b0 mod 128.
Proof.
  rewrite !bv_concat_unsigned'. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 16) with (2 ^ 16).
  change 128 with (2 ^ 7).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 7) as [LT|GE].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (n - Z.of_N 16)) by (cbn; lia). cbn [orb].
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (n - Z.of_N 8)) by (cbn; lia). reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma low7_le4 b3 b2 b1 b0 : bv_unsigned (le4 b3 b2 b1 b0) mod 128 = bv_unsigned b0 mod 128.
Proof. unfold le4, le2. apply low7_concat. Qed.

Section Fast.
Variable wsafe : bv 32 -> bool.
Hypothesis wsafe_sys : forall w, bv_unsigned w mod 128 <> 115 -> wsafe w = true.
Variable segs : list Segment.

Definition okP (a : Z) : bool :=
  (match fetch_word segs (Z_to_bv 64 a) with Some w => wsafe w | None => true end)
  && (match fetch_tail segs (Z_to_bv 64 a) with Some w => wsafe w | None => true end).

Definition fposB (base : Z) (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with
  | Some b => if bv_unsigned b mod 128 =? 115 then okP (base + Z.of_N off) else true
  | None => true
  end.

Definition fpos (base : Z) (s : PrimString.string) (off : N) : bool :=
  match hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) with
  | 7%N | 15%N => fposB base s off
  | _ => true
  end.
Fixpoint fscan1 (base : Z) (s : PrimString.string) (f : nat) (off : N) : bool :=
  match f with O => true | S f' => fpos base s off && fscan1 base s f' (off + 2)%N end.
Fixpoint fscan2 (base : Z) (s : PrimString.string) (g f : nat) (off : N) : bool :=
  match g with O => true | S g' => fscan1 base s f off && fscan2 base s g' f (off + 2 * N.of_nat f)%N end.

Definition fseg (g f : nat) (seg : Segment) : bool :=
  if seg_executable seg then
    match seg_bytes seg with
    | [chunk] => if (Z.of_N (seg_size seg) <=? 2 * Z.of_nat f * Z.of_nat g) && (Z.of_N (seg_base seg) mod 2 =? 0)
                 then fscan2 (Z.of_N (seg_base seg)) chunk g f 0 else false
    | _ => false
    end
  else true.

Lemma fscan1_sound base s : forall f o0, fscan1 base s f o0 = true ->
  forall o, (o0 <= o < o0 + 2 * N.of_nat f)%N -> (exists k, o = o0 + 2 * k)%N -> fpos base s o = true.
Proof.
  induction f as [|f IH]; intros o0 H o Ho [k Hk]; [cbn [N.of_nat] in Ho; lia|].
  cbn [fscan1] in H. apply andb_true_iff in H as [H0 H1].
  destruct (N.eq_dec o o0) as [->|NE]; [exact H0|].
  apply (IH (o0 + 2)%N H1); [lia|]. exists (k - 1)%N. lia.
Qed.
Lemma fscan2_sound base s : forall g f o0, fscan2 base s g f o0 = true ->
  forall o, (o0 <= o < o0 + 2 * N.of_nat f * N.of_nat g)%N -> (exists k, o = o0 + 2 * k)%N -> fpos base s o = true.
Proof.
  induction g as [|g IH]; intros f o0 H o Ho [k Hk]; [cbn [N.of_nat] in Ho; lia|].
  cbn [fscan2] in H. apply andb_true_iff in H as [H0 H1].
  destruct (N.ltb_spec o (o0 + 2 * N.of_nat f)) as [LT|GE].
  - apply (fscan1_sound base s f o0 H0 o ltac:(lia)). exists k; exact Hk.
  - apply (IH f (o0 + 2 * N.of_nat f)%N H1); [lia|]. exists (k - N.of_nat f)%N. lia.
Qed.

Lemma hex_byte_sys_hi s off b : hex_byte_at s off = Some b -> bv_unsigned b mod 128 = 115 ->
  hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) = 7%N \/ hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off)))) = 15%N.
Proof.
  unfold hex_byte_at. cbv zeta.
  set (h := hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off))))).
  set (l := hex_nybble (PrimString.get s (Uint63.of_Z (Z.of_N (2 * off + 1))))).
  destruct (_ || _)%bool; [|discriminate].
  destruct (N.ltb_spec h 16) as [Hh|]; cbn [andb]; [|discriminate].
  destruct (N.ltb_spec l 16) as [Hl|]; [|discriminate].
  intros E. injection E as <-. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite (Z.mod_small _ 256) by lia. intros M.
  pose proof (Z_div_mod_eq_full (Z.of_N (h * 16 + l)) 128) as D. rewrite M in D.
  assert (Q : Z.of_N (h * 16 + l) / 128 = 0 \/ Z.of_N (h * 16 + l) / 128 = 1).
  { assert (0 <= Z.of_N (h * 16 + l) / 128 < 2); [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

Lemma code_read_first a n b0 rest : code_read segs a n = Some (b0 :: rest) ->
  exists seg, In seg segs /\ seg_executable seg = true
    /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + Z.of_N n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg)
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) = Some b0.
Proof.
  unfold code_read. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|discriminate].
  destruct (seg_executable seg) eqn:X; cbn [andb]; [|discriminate].
  destruct (negb (seg_writable seg)); [|discriminate].
  intros R. exists seg. split; [exact (FrmKeep.FRM.find_segment_In _ _ _ _ E)|]. split; [exact X|].
  destruct (FrmKeep.FRM.find_segment_range _ _ _ _ E) as [R1 R2]. split; [exact R1|]. split; [exact R2|].
  destruct (N.to_nat n) as [|n']; cbn [segment_read_bytes] in R; [discriminate|].
  destruct (segment_byte_at (seg_bytes seg) _) as [b|]; [|discriminate].
  destruct (segment_read_bytes _ _ n') as [r|]; [|discriminate]. injection R as -> _. reflexivity.
Qed.

Definition fetched_at (a : word) (w : bv 32) : Prop :=
  bv_unsigned a mod 2 = 0 /\ exists seg b0, In seg segs /\ seg_executable seg = true
    /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 2 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg)
    /\ segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) = Some b0
    /\ bv_unsigned w mod 128 = bv_unsigned b0 mod 128.
Lemma fetch_word_at a w : fetch_word segs a = Some w -> fetched_at a w.
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  destruct (code_read segs a 4) as [[|b0 [|b1 [|b2 [|b3 [|? ?]]]]]|] eqn:C; try discriminate. intros H. injection H as <-.
  split; [exact E|]. destruct (code_read_first a 4 b0 _ C) as (seg & IN & X & R1 & R2 & SB).
  exists seg, b0. split; [exact IN|]. split; [exact X|]. split; [exact R1|]. split; [change (Z.of_N 4) with 4 in R2; lia|]. split; [exact SB|]. apply low7_le4.
Qed.
Lemma fetch_tail_at a w : fetch_tail segs a = Some w -> fetched_at a w.
Proof.
  unfold fetch_tail. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  unfold fetch_half at 1.
  destruct (code_read segs a 2) as [[|b0 [|b1 [|? ?]]]|] eqn:C; try discriminate. intros H.
  split; [exact E|]. destruct (code_read_first a 2 b0 _ C) as (seg & IN & X & R1 & R2 & SB).
  exists seg, b0. split; [exact IN|]. split; [exact X|]. split; [exact R1|]. split; [exact R2|]. split; [exact SB|].
  destruct (_ =? 3); [destruct (fetch_half segs (a + 2)) as [h1|]; [|discriminate]|]; injection H as <-; unfold le2; apply low7_concat.
Qed.

Theorem fetch_safe_of_fscan (g f : nat) :
  forallb (fseg g f) segs = true ->
  forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> wsafe w = true.
Proof.
  intros SC a w H.
  destruct (Z.eq_dec (bv_unsigned w mod 128) 115) as [SYS|NSYS]; [|exact (wsafe_sys w NSYS)].
  assert (FA : fetched_at a w) by (destruct H as [H|H]; [exact (fetch_word_at a w H)| exact (fetch_tail_at a w H)]).
  destruct FA as (EA & seg & b0 & IN & X & R1 & R2 & SB & LB).
  pose proof (proj1 (forallb_forall _ _) SC seg IN) as FS. unfold fseg in FS. rewrite X in FS.
  destruct (seg_bytes seg) as [|chunk [|? ?]]; try discriminate.
  destruct (_ && _) eqn:FS0 in FS; [|discriminate]. rename FS into F2. apply andb_true_iff in FS0 as [COV EB].
  apply Z.leb_le in COV. apply Z.eqb_eq in EB.
  set (base := Z.of_N (seg_base seg)) in *. set (off := Z.to_N (bv_unsigned a - base)) in *.
  assert (HB : hex_byte_at chunk off = Some b0).
  { cbn [segment_byte_at] in SB. destruct (_ <? _)%N; [exact SB| discriminate]. }
  assert (EO : Z.of_N off = bv_unsigned a - base) by (unfold off; lia).
  assert (FP : fpos base chunk off = true).
  { apply (fscan2_sound base chunk g f 0%N F2); [lia|].
    exists (Z.to_N ((bv_unsigned a - base) / 2)).
    assert (M : (bv_unsigned a - base) mod 2 = 0) by (rewrite Zminus_mod, EA, EB; reflexivity).
    pose proof (Z_div_mod_eq_full (bv_unsigned a - base) 2) as D. lia. }
  assert (FPB : fposB base chunk off = true).
  { unfold fpos in FP. destruct (hex_byte_sys_hi chunk off b0 HB ltac:(rewrite <- LB; exact SYS)) as [HN|HN]; rewrite HN in FP; exact FP. }
  unfold fposB in FPB. rewrite HB in FPB. rewrite <- LB, SYS in FPB. cbn [Z.eqb Pos.eqb] in FPB. rename FPB into FP'.
  clear FP. rename FP' into FP.
  replace (base + Z.of_N off) with (bv_unsigned a) in FP by lia.
  unfold okP in FP. rewrite Z_to_bv_bv_unsigned in FP. apply andb_true_iff in FP as [O1 O2].
  destruct H as [H|H]; [rewrite H in O1; exact O1| rewrite H in O2; exact O2].
Qed.
End Fast.

Definition fetch_safe_of_fscan_FRM (segs : list Segment) (g f : nat) :=
  fetch_safe_of_fscan FrmKeep.FRM.word_frm_safe safe_unless_system segs g f.
Definition fetch_safe_of_fscan_FRMC (segs : list Segment) (g f : nat) :=
  fetch_safe_of_fscan FrmKeepC.FRMC.word_frm_safe safe_unless_systemC segs g f.
End FRMF.
