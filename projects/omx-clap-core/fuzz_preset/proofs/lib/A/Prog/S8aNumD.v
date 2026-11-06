(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, twin bff8519b), ex_value piece 5 (ev_number), sub-piece
   D of S8aNumCut.v: CR (+0x924, strtod's return site) -> CT (+0x9f4) | CC (+0x958), over WalkS8a's interface
   S8aIface.v. The code (the internal file ex_value.fuzz_preset.asan.s, offsets from ex_value's entry):
     +0x924 ld a0,0(s11)       a0 := *(&end) = scr + cn
     +0x928 ld a1,112(s1)      a1 := fr + 64 (&num)
     +0x92c fsd fa0,0(a1)      num := bits                       (hand step: YK0o.v fp_step_fsd)
     +0x930 .. +0x93c          the 1-byte shadow check of end, slow arm +0xc0c andi / +0xc10 blt back to +0x940
     +0x940 lbu a0,0(a0)       the byte at end; non-zero -> +0x9f4 (CT, r = -1)   (+0x944 bnez)
     +0x948 fclass.d a0,fa0    (hand step: fp_step_fclass_d below, from LPS Sem.v:651-652 and Fpu.v:586-598)
     +0x94c andi a0,a0,897     the infinities and NaNs; +0x950 snez; +0x954 bnez -> +0x9f4 (CT, r = -1); else CC.
   Every step is taken by hand (YA0n.v SRr_step with YK11.v's / YK0o.v's single-step lemmas): 15 listing
   instructions. The pure model: S8aModel.v's prhex_V_cons / prhex_V_num (cited) give jr_number's reading; the scan's
   stop is span's split (evD_span).
   MEMNORM: CR's MID ends with the memory normal form `YAkMemnorm.memnorm segs mem` (a state fact; S8aIface.v ev_mid's
   last conjunct). The one memory write, the fsd at +0x92c, takes it across by lib/Reusable/YSRrMemnorm.v's
   SRr_step_inv at P := YAkMemnorm.memnorm SEGS (its laws srr_inv_laws_memnorm_k; YAkMemnorm.memnorm is the same body,
   by conversion), and lane M's ev_mid_keep gets it as its memnorm premise. The other steps keep the memory.
   Section hypotheses: the image fact Hent (ex_value's listing offset, PRW_pj_write.v's form; at PI_prog_A it is
   A_entry_ex_value) and lane M's ev_mid_keep_stmt. No memnorm hypothesis.
   Numerals: 0x924 0x928 0x92c 0x930 0x934 0x938 0x93c 0x940 0x944 0x948 0x94c 0x950 0x954 0x958 0x9f4 0xc0c 0xc10
   (LENGTH: offsets into ex_value, measured from the listing); 7364 (DERIVED: slot 1841 * 4, PAImg_prog
   A_entry_ex_value); 32 64 72 96 104 112 120 128 (LENGTH: the frame's `end` / `num` slots, the s1 spills, the
   class-1 frame's bytes fs_frame_bytes 1); 256 272 (LENGTH: the prologue's frame, ev_img_ok's bound); 4 (LENGTH: an
   instruction); 8 (LENGTH: the num slot; the shadow granule); 3 7 897 (WORD: the srli / andi immediates);
   10 11 12 0 9 21 22 23 24 27 (WORD: register numbers); 45 48 34 91 123 102 110 116 (WORD: bytes of the grammar);
   2 ^ 47 2 ^ 64 1024 256 128 (LENGTH: address and value ranges; 1024 = 2 ^ 10, one past fclass's top bit);
   52 11 2047 10 (LENGTH / WORD: binary64's mantissa width, exponent width, its all-ones value, Z.log2 2047).
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04
YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YP0a YPsym YC4aP FCiface YGcallMx YC1fP YK0u YN01 YK1b YFclsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbn YK00 YA03 YC80x YSRrMemnorm YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut S8aNumPure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes strtod_c.
Import ListNotations.
Local Open Scope Z_scope.
(* lia over / and mod (the shadow map, the 32-aligned sp): this import set turns the euclidean equations off *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ======== pure: the number arm's reading at the scan's stop ======== *)

Lemma evD_skipn_cons : forall (x : list Z) (a : nat), (a < length x)%nat -> skipn a x = nth a x 0 :: skipn (S a) x.
Proof.
  induction x as [|b x IH]; intros a Ha; cbn [length] in Ha; [lia|].
  destruct a as [|a]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma evD_skipn_skipn : forall (x : list Z) (a b : nat), skipn a (skipn b x) = skipn (b + a) x.
Proof.
  intros x a b. revert x. induction b as [|b IH]; intros x; [reflexivity|].
  destruct x as [|h x]; cbn [skipn Nat.add].
  - destruct a; reflexivity.
  - apply IH.
Qed.

Lemma evD_skipn_nil : forall (x : list Z) (a : nat), (length x <= a)%nat -> skipn a x = [].
Proof.
  induction x as [|b x IH]; intros a Ha; [destruct a; reflexivity|].
  cbn [length] in Ha. destruct a as [|a]; [lia|]. cbn [skipn]. apply IH. lia.
Qed.

Lemma evD_nth_skipn : forall (x : list Z) (a n : nat), nth n (skipn a x) 0 = nth (a + n) x 0.
Proof.
  intros x a n. revert x. induction a as [|a IH]; intros x; [reflexivity|].
  destruct x as [|h x]; cbn [skipn Nat.add nth].
  - destruct n; reflexivity.
  - apply IH.
Qed.

Lemma evD_firstn_add : forall (l : list Z) (n m : nat), firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  intros l n m. revert l. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|h l]; cbn [firstn skipn Nat.add app].
  - destruct m; reflexivity.
  - f_equal. apply IH.
Qed.

Lemma evD_sub_cons : forall (x : list Z) (a z : nat), (a < z)%nat -> (a < length x)%nat ->
  ev_sub x a z = nth a x 0 :: ev_sub x (S a) z.
Proof.
  intros x a z Haz Hax. unfold ev_sub. rewrite (evD_skipn_cons x a Hax).
  replace (z - a)%nat with (S (z - S a)) by lia. reflexivity.
Qed.

Lemma evD_sub_split : forall (x : list Z) (a b z : nat), (a <= b <= z)%nat ->
  ev_sub x a z = ev_sub x a b ++ ev_sub x b z.
Proof.
  intros x a b z H. unfold ev_sub.
  replace (z - a)%nat with ((b - a) + (z - b))%nat by lia.
  rewrite evD_firstn_add, evD_skipn_skipn.
  replace (a + (b - a))%nat with b by lia. reflexivity.
Qed.

(* the scan's stop: span numch splits the text exactly at the first non-number byte *)
Lemma evD_span : forall (y : list Z) (n : nat),
  (n <= length y)%nat -> Forall (fun z => PjGrammar.numch z = true) (firstn n y) ->
  (n = length y \/ PjGrammar.numch (nth n y 0) = false) ->
  PjGrammar.span PjGrammar.numch y = (firstn n y, skipn n y).
Proof.
  induction y as [|b y IH]; intros n Hn Hall Hstop.
  - destruct n; [reflexivity | cbn [length] in Hn; lia].
  - destruct n as [|n].
    + destruct Hstop as [Hs|Hs]; [cbn [length] in Hs; lia|].
      cbn [nth] in Hs. exact (S8aNumPure.span_numch_cons_false b y Hs).
    + cbn [firstn] in Hall.
      rewrite (S8aNumPure.span_numch_cons_true b y (Forall_inv Hall)).
      rewrite (IH n); [reflexivity | cbn [length] in Hn; lia | exact (Forall_inv_tail Hall) |].
      destruct Hstop as [Hs|Hs]; [left; cbn [length] in Hs; lia | right; exact Hs].
Qed.

(* jr_number's reading (S8aModel.v prhex_V_cons, prhex_V_num) once its dispatch byte, lead digit, leading-zero test
   and span are known *)
Lemma evD_jr_number : forall (c : Z) (y' : list Z) (c' : Z) (z a r : list Z),
  PjGrammar.ws c = false -> c <> 123 -> c <> 91 -> c <> 34 -> c <> 116 -> c <> 102 -> c <> 110 ->
  skipn (ev_sg c) (c :: y') = c' :: z ->
  PjGrammar.digit c' = true ->
  ((c' =? 48) && match z with c1 :: _ => PjGrammar.digit c1 | [] => false end) = false ->
  PjGrammar.span PjGrammar.numch z = (a, r) ->
  ev_N (c :: y') =
    if PjGrammar.whole ReaderRes.jr_strtod (firstn (ev_sg c) (c :: y') ++ c' :: a)
    then Some (PjTree.JNum (firstn (ev_sg c) (c :: y') ++ c' :: a)
                 (snd (ReaderRes.jr_strtod (firstn (ev_sg c) (c :: y') ++ c' :: a))), r)
    else None.
Proof.
  intros c y' c' z a r Hw H1 H2 H3 H4 H5 H6 Hsk Hd Hnz Hspan.
  assert (E : ev_N (c :: y') = prhex_V 0 (c :: y')).
  { rewrite (S8aModel.prhex_V_cons 0 c y' Hw).
    rewrite (proj2 (Z.eqb_neq c 123) H1), (proj2 (Z.eqb_neq c 91) H2), (proj2 (Z.eqb_neq c 34) H3),
      (proj2 (Z.eqb_neq c 116) H4), (proj2 (Z.eqb_neq c 102) H5), (proj2 (Z.eqb_neq c 110) H6).
    reflexivity. }
  rewrite E, (S8aModel.prhex_V_num 0 c y' Hw H1 H2 H3 H4 H5 H6). cbv zeta. fold (ev_sg c).
  rewrite Hsk. cbv beta iota. rewrite Hd. cbv beta iota delta [negb].
  rewrite Hnz. cbv beta iota. rewrite Hspan. cbv beta iota zeta. reflexivity.
Qed.

(* the reading of x from i1 when the scan stopped at j and strtod read (bits, cn) from x[i1, j) *)
Lemma evD_N : forall (x : list Z) (i1 j : nat) (c bits cn : Z),
  nth i1 x 0 = c -> PjGrammar.ws c = false ->
  c <> 34 -> c <> 91 -> c <> 123 -> c <> 102 -> c <> 110 -> c <> 116 ->
  ev_lead_ok x (i1 + ev_sg c) ->
  Forall (fun z => PjGrammar.numch z = true) (ev_sub x (i1 + ev_sg c) j) ->
  (i1 + ev_sg c < j <= length x)%nat ->
  (j = length x \/ PjGrammar.numch (nth j x 0) = false) ->
  strtod_c.strtod_model (ev_sub x i1 j) = Some (bits, cn) ->
  ev_N (skipn i1 x) =
    if (cn =? Z.of_nat (length (ev_sub x i1 j))) && PjGrammar.finite bits
    then Some (PjTree.JNum (ev_sub x i1 j) bits, skipn j x) else None.
Proof.
  intros x i1 j c bits cn Hc Hws H34 H91 H123 H102 H110 H116. remember (i1 + ev_sg c)%nat as j0 eqn:Hj0.
  intros Hlead Hall Hj Hstop Hsm.
  destruct Hlead as [Hl0 [Hd Hnz]].
  assert (Hi1 : (i1 < length x)%nat) by lia.
  assert (H1 : skipn i1 x = c :: skipn (S i1) x) by (rewrite <- Hc; apply evD_skipn_cons; exact Hi1).
  assert (H2 : skipn (ev_sg c) (c :: skipn (S i1) x) = nth j0 x 0 :: skipn (S j0) x).
  { rewrite <- H1, evD_skipn_skipn, <- Hj0. apply evD_skipn_cons. lia. }
  assert (Hnz' : ((nth j0 x 0 =? 48) && match skipn (S j0) x with c1 :: _ => PjGrammar.digit c1 | [] => false end)
                 = false).
  { destruct (Z.eqb_spec (nth j0 x 0) 48) as [E|NE]; [|reflexivity].
    cbn [andb].
    destruct (Nat.lt_ge_cases (S j0) (length x)) as [Hlt|Hge].
    - rewrite (evD_skipn_cons x (S j0) Hlt). cbv beta iota.
      destruct (PjGrammar.digit (nth (S j0) x 0)) eqn:Ed; [|reflexivity].
      exfalso. apply Hnz. split; [exact E|]. split; [exact Hlt | reflexivity].
    - rewrite (evD_skipn_nil x (S j0) Hge). reflexivity. }
  assert (Hrest : Forall (fun z => PjGrammar.numch z = true) (ev_sub x (S j0) j)).
  { rewrite (evD_sub_cons x j0 j) in Hall by lia. exact (Forall_inv_tail Hall). }
  assert (Hspan : PjGrammar.span PjGrammar.numch (skipn (S j0) x) = (ev_sub x (S j0) j, skipn j x)).
  { rewrite (evD_span (skipn (S j0) x) (j - S j0)).
    - unfold ev_sub. rewrite evD_skipn_skipn. replace (S j0 + (j - S j0))%nat with j by lia. reflexivity.
    - rewrite length_skipn. lia.
    - exact Hrest.
    - destruct Hstop as [Hs|Hs]; [left; rewrite length_skipn; lia|].
      right. rewrite evD_nth_skipn. replace (S j0 + (j - S j0))%nat with j by lia. exact Hs. }
  assert (Htxt : firstn (ev_sg c) (c :: skipn (S i1) x) ++ nth j0 x 0 :: ev_sub x (S j0) j = ev_sub x i1 j).
  { rewrite <- H1. rewrite (evD_sub_split x i1 j0 j) by lia. rewrite (evD_sub_cons x j0 j) by lia.
    f_equal. unfold ev_sub. f_equal. lia. }
  rewrite H1.
  rewrite (evD_jr_number c (skipn (S i1) x) (nth j0 x 0) (skipn (S j0) x) (ev_sub x (S j0) j) (skipn j x)
             Hws H123 H91 H34 H116 H102 H110 H2 Hd Hnz' Hspan).
  rewrite Htxt.
  unfold PjGrammar.whole, ReaderRes.jr_strtod. rewrite Hsm. reflexivity.
Qed.

(* the text is all number characters (the sign byte is '-' when ev_sg c = 1) *)
Lemma evD_txt_numch : forall (x : list Z) (i1 j : nat) (c : Z),
  nth i1 x 0 = c -> (i1 + ev_sg c <= j <= length x)%nat ->
  Forall (fun z => PjGrammar.numch z = true) (ev_sub x (i1 + ev_sg c) j) ->
  Forall (fun z => PjGrammar.numch z = true) (ev_sub x i1 j).
Proof.
  intros x i1 j c Hc Hj Hall. unfold ev_sg in Hj, Hall. revert Hj Hall.
  destruct (Z.eqb_spec c 45) as [E|NE]; intros Hj Hall.
  - rewrite (evD_sub_cons x i1 j) by lia. constructor.
    + rewrite Hc, E. reflexivity.
    + replace (S i1) with (i1 + 1)%nat by lia. exact Hall.
  - rewrite Nat.add_0_r in Hall. exact Hall.
Qed.

(* the byte at end = scr + cn of txt ++ [0] is zero iff strtod consumed the whole text *)
Lemma evD_end_byte : forall (txt : list Z) (cn : Z),
  Forall (fun z => PjGrammar.numch z = true) txt -> 0 <= cn <= Z.of_nat (length txt) ->
  (nth (Z.to_nat cn) (txt ++ [0]) 0 =? 0) = (cn =? Z.of_nat (length txt)).
Proof.
  intros txt cn Hall Hcn.
  destruct (Z.eqb_spec cn (Z.of_nat (length txt))) as [E|NE].
  - rewrite E, Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by lia.
    assert (Hin : In (nth (Z.to_nat cn) txt 0) txt) by (apply nth_In; lia).
    rewrite Forall_forall in Hall. specialize (Hall _ Hin). cbv beta in Hall.
    destruct (Z.eqb_spec (nth (Z.to_nat cn) txt 0) 0) as [E0|NE0]; [|reflexivity].
    rewrite E0 in Hall. vm_compute in Hall. discriminate Hall.
Qed.

(* the fclass.d mask 0x381 (bit 0 -inf, 7 +inf, 8 sNaN, 9 qNaN) is zero iff the bits are finite; the register holds
   bits mod 2 ^ 64 *)
Lemma evD_exp_mod : forall bits : Z,
  Z.land (Z.shiftr (bits mod 2 ^ 64) 52) 2047 = Z.land (Z.shiftr bits 52) 2047.
Proof.
  intros bits. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases n 11) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - assert (H2047 : Z.testbit 2047 n = false).
    { apply Z.bits_above_log2; [lia|]. change (Z.log2 2047) with 10. lia. }
    rewrite H2047, !andb_false_r. reflexivity.
Qed.

Lemma evD_fclass : forall bits : Z,
  (Z.land (fp_class fmt_double (bits mod 2 ^ 64)) 897 =? 0) = PjGrammar.finite bits.
Proof.
  intros bits. unfold fp_class, PjGrammar.finite. cbv zeta.
  unfold fp_exp_field.
  change (fp_mw fmt_double) with 52. change (Z.ones (fp_ew fmt_double)) with 2047.
  rewrite evD_exp_mod.
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 2047);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma evD_fclass_range : forall a : Z, 0 <= fp_class fmt_double a < 1024.
Proof.
  intros a. unfold fp_class. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  vm_compute; split; congruence.
Qed.

(* the fclass.d single step fp_step_fclass_d is now lib/Reusable/YFclsStep.v (the shared one copy, h-hpreset-7's
   ruling 04:33Z); this file Requires it instead of defining a second. *)

(* ======== memory: one store of bs at A through the restricted view ======== *)
Section m.
Variable segs : list Segment.

Lemma evD_store_ok : forall (m : word -> option byte) (n : nat) (a : Z),
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (a + i)) <> None) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros m n. induction n as [|n IH]; intros a Hp Ha Hn; [reflexivity|].
  cbn [store_ok]. unfold wview.
  destruct (m (Z_to_bv 64 a)) eqn:E.
  - rewrite Z_to_bv64_add1. apply IH; [| lia | lia].
    intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hp. lia.
  - exfalso. apply (Hp 0); [lia|]. rewrite Z.add_0_r. exact E.
Qed.

Lemma evD_wb_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (x : word),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  (bv_unsigned x < A \/ A + Z.of_nat (length bs) <= bv_unsigned x) ->
  mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) x = mrestrict H mem x.
Proof.
  intros H mem A bs x HA HAn Hx. unfold munrestrict, mrestrict.
  destruct (H x) eqn:Hh; [reflexivity|].
  rewrite wbytes_outside; [cbv beta; rewrite Hh; reflexivity | rewrite YK00.u64_lit by lia; lia |].
  rewrite YK00.u64_lit by lia. exact Hx.
Qed.

Lemma evD_wb_hid : forall (H : word -> bool) (mem m' : word -> option byte) (x : word),
  H x = true -> munrestrict H mem m' x = mem x.
Proof. intros H mem m' x Hh. unfold munrestrict. rewrite Hh. reflexivity. Qed.

Lemma evD_wb_grow : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  mem_grows (mrestrict H mem) (mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs))).
Proof.
  intros H mem A bs HA HAn x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Hl|Hl]; [rewrite evD_wb_out by lia; exact Hx|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Hu|Hu];
    [|rewrite evD_wb_out by lia; exact Hx].
  unfold mrestrict in *. unfold munrestrict. destruct (H x) eqn:Hh; [exact Hx|].
  rewrite wbytes_inside; [discriminate | rewrite YK00.u64_lit by lia; lia | rewrite YK00.u64_lit by lia; lia].
Qed.

Lemma evD_wb_in : forall (H : word -> bool) (mem : word -> option byte) (A v : Z) (k : nat),
  0 <= A -> A + 8 <= 2 ^ 64 -> (k < 8)%nat -> H (Z_to_bv 64 (A + Z.of_nat k)) = false ->
  mbyte segs (mrestrict H (munrestrict H mem
      (wbytes (mrestrict H mem) (Z_to_bv 64 A) (word_to_le_bytes 8 (Z_to_bv 64 v))))) (A + Z.of_nat k)
  = Some (Z_to_bv 8 (le_byte v 8 k)).
Proof.
  intros H mem A v k HA HA8 Hk Hh.
  assert (Hlen : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 v))) = 8)
    by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
  assert (E : nth_error (word_to_le_bytes 8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (le_byte v 8 k))).
  { unfold word_to_le_bytes. rewrite nth_error_Z_to_le_bytes by lia. f_equal.
    rewrite le_byte_bv by lia. rewrite Z_to_bv_unsigned. reflexivity. }
  unfold mbyte, munrestrict, mrestrict. rewrite Hh.
  rewrite wbytes_inside; [| rewrite YK00.u64_lit by lia; lia | rewrite !YK00.u64_lit by lia; lia].
  rewrite !YK00.u64_lit by lia. replace (A + Z.of_nat k - A) with (Z.of_nat k) by lia. rewrite Nat2Z.id.
  f_equal. apply nth_error_nth. exact E.
Qed.

Lemma evD_aview_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (z : Z),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  (z < A \/ A + Z.of_nat (length bs) <= z) ->
  aview segs H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) z = aview segs H mem z.
Proof.
  intros H mem A bs z HA HAn Hz Hout. apply aview_eq_of. apply evD_wb_out; [lia | lia |].
  rewrite YK00.u64_lit by lia. exact Hout.
Qed.

Lemma evD_vm_keep : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (a : Z) (n : nat) (v : Z),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= A \/ A + Z.of_nat (length bs) <= a) ->
  val_mem segs (mrestrict H mem) a n v ->
  val_mem segs (mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs))) a n v.
Proof.
  intros H mem A bs a n v HA HAn Ha Han Hd Hv. eapply val_mem_kept; [|exact Hv].
  intros kk Hkk. apply evD_aview_out; lia.
Qed.

Lemma evD_garr_keep : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (b : Z) (l : list Z),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length l) <= 2 ^ 64 ->
  (b + Z.of_nat (length l) <= A \/ A + Z.of_nat (length bs) <= b) ->
  garr8 segs (mrestrict H mem) b l ->
  garr8 segs (mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs))) b l.
Proof.
  intros H mem A bs b l HA HAn Hb Hbl Hd Hg jj Hjj. destruct (Hg jj Hjj) as [Hv Hr]. split; [|exact Hr].
  eapply evD_vm_keep; [| | | | |exact Hv]; lia.
Qed.

Lemma evD_byte : forall e, 0 <= e < 256 -> bv_unsigned (Z_to_bv 8 (le_byte e 1 0)) = e.
Proof.
  intros e He. rewrite Z_to_bv_unsigned. unfold le_byte.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
  rewrite Z.shiftr_0_r, !(Z.mod_small e 256) by lia.
  replace (bv_wrap 8 e) with (e mod 256) by reflexivity. apply Z.mod_small. lia.
Qed.
End m.

(* the registers a step sequence leaves alone: all but a0, a1, a2 *)
Definition evD_frame (R regs : bvmap 5 word) : Prop :=
  forall r : Prelude.reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr R r = getr regs r.

Lemma evD_frame_refl : forall regs, evD_frame regs regs.
Proof. intros regs r _ _ _. reflexivity. Qed.

Lemma evD_frame_upd : forall R regs (d : Prelude.reg) v, (d = 10%bv \/ d = 11%bv \/ d = 12%bv) ->
  evD_frame R regs -> evD_frame (YK11.regupd R d v) regs.
Proof.
  intros R regs d v Hd HF r H10 H11 H12. rewrite getr_other; [apply HF; assumption|].
  destruct Hd as [ Hd | [ Hd | Hd ] ]; rewrite Hd; assumption.
Qed.

(* bv_signed of a literal immediate, computed *)
Ltac evD_bvs := repeat match goal with |- context [bv_signed ?i] =>
  let v := eval vm_compute in (bv_signed i) in
  lazymatch v with
  | Z0 => change (bv_signed i) with 0
  | Zpos ?p => change (bv_signed i) with (Zpos p)
  | Zneg ?p => change (bv_signed i) with (Zneg p)
  end end.

(* ======== the walk ======== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
Local Notation SEGS := (@pa_segs _ A_prog_listing PA).
Local Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* image fact of the instance, discharged at PI_prog_A by A_entry_ex_value (slot 1841) *)
Hypothesis Hent : @pa_sigma _ A_prog_listing PA AS_ex_value = BASE + 7364.
(* lane M *)
Hypothesis MIDK : forall a, ev_mid_keep_stmt B ARx SK a.

Lemma evD_fetch : forall off w, plookup (@pl_tpi _ PL_prog_A) (7364 + off) = Some (PW w) ->
  fetch_word SEGS (Z_to_bv 64 (@ev_pc _ _ PA off)) = Some (Z_to_bv 32 w).
Proof.
  intros off w H. unfold ev_pc. rewrite Hent.
  replace (BASE + 7364 + off) with (BASE + (7364 + off)) by lia.
  exact (@pa_fetch_pw _ _ PL_prog_A PA _ _ H).
Qed.

Lemma evD_next : forall off k, YK11.v_addi (Z_to_bv 64 (@ev_pc _ _ PA off)) k = Z_to_bv 64 (@ev_pc _ _ PA (off + k)).
Proof. intros off k. rewrite YCbn.v_addi_lit. unfold ev_pc. f_equal. lia. Qed.

Lemma evD_btgt : forall off k, YK11.btgt (Z_to_bv 64 (@ev_pc _ _ PA off)) k = Z_to_bv 64 (@ev_pc _ _ PA (off + k)).
Proof. intros off k. unfold YK11.btgt. apply evD_next. Qed.

(* one hand step at a cut-free pc: registers and pc change, memory does not *)
Lemma evD_step : forall (W : world SEGS) (fxc : YK11.FPState) regs off mem md0 md Q regs' off',
  same_but_materialized md0 md ->
  RiscvSemantics.step SEGS (@YK11.mkst fxc regs (Z_to_bv 64 (@ev_pc _ _ PA off)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxc regs' (Z_to_bv 64 (@ev_pc _ _ PA off')) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall md', same_but_materialized md0 md' -> SRr SEGS W (@ev_cfg _ _ PA fxc regs' off' mem md') Q) ->
  SRr SEGS W (@ev_cfg _ _ PA fxc regs off mem md) Q.
Proof.
  intros W fxc regs off mem md0 md Q regs' off' Hs0 Hst HK. unfold ev_cfg.
  eapply (SRr_step SEGS (@pa_wx _ _ PA) W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
  intros md' Hs. cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  apply HK. eapply same_but_materialized_trans; eassumption.
Qed.

(* one hand step that also writes memory: the new memory is the restricted write put back under the hidden part; the
   memory normal form crosses the step (YSRrMemnorm.v SRr_step_inv) *)
Lemma evD_step_m : forall (W : world SEGS) (fxc : YK11.FPState) regs off mem md0 md Q regs' off' m',
  same_but_materialized md0 md ->
  YAkMemnorm.memnorm SEGS mem ->
  RiscvSemantics.step SEGS (@YK11.mkst fxc regs (Z_to_bv 64 (@ev_pc _ _ PA off)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxc regs' (Z_to_bv 64 (@ev_pc _ _ PA off')) m' (YK11.seg_rom SEGS)) ->
  (forall md', same_but_materialized md0 md' -> YAkMemnorm.memnorm SEGS (munrestrict (w_H W) mem m') ->
     SRr SEGS W (@ev_cfg _ _ PA fxc regs' off' (munrestrict (w_H W) mem m') md') Q) ->
  SRr SEGS W (@ev_cfg _ _ PA fxc regs off mem md) Q.
Proof.
  intros W fxc regs off mem md0 md Q regs' off' m' Hs0 HPm Hst HK. unfold ev_cfg.
  eapply (YC80x.SRr_step_inv SEGS (@pa_wx _ _ PA) (YAkMemnorm.memnorm SEGS)
    (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) W);
    [reflexivity | rewrite restrict_mkst_fx; exact Hst | exact HPm |].
  intros md' Hs HPm'. exact (HK md' (same_but_materialized_trans _ _ _ Hs0 Hs) HPm').
Qed.

(* the listing word at the offset, and its decoding at the registers and immediates the proof names: the decoder
   builds its bv fields with Z_to_bv's opaque well-formedness proof, so the two forms are equal only by bv_eq *)
Ltac evD_fetch off instr :=
  let k := eval vm_compute in (7364 + off) in
  let e := eval vm_compute in (plookup (@pl_tpi _ PL_prog_A) k) in
  lazymatch e with
  | Some (PW ?w) =>
    pose proof (evD_fetch off w ltac:(vm_compute; reflexivity)) as Hf;
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (instr, 4%Z))
      by (vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]);
    assert (He : is_ecall (Z_to_bv 32 w) = false) by (vm_compute; reflexivity)
  end.

Lemma evD_base_regs : forall a (W : world SEGS) regs R mem i1 c,
  ev_base a W regs mem i1 c -> evD_frame R regs -> ev_base a W R mem i1 c.
Proof.
  intros a W regs R mem i1 c HB HF. unfold evD_frame in HF. unfold ev_base, ev_regs in *.
  rewrite !HF by discriminate. exact HB.
Qed.

Lemma evD_base_mem : forall a (W : world SEGS) regs mem mem' i1 c,
  ev_base a W regs mem i1 c -> val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 104) 8 (ea_v a) ->
  ev_base a W regs mem' i1 c.
Proof.
  intros a W regs mem mem' i1 c (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & h11 & h12 & _) H.
  exact (conj h1 (conj h2 (conj h3 (conj h4 (conj h5 (conj h6 (conj h7 (conj h8 (conj h9 (conj h10
    (conj h11 (conj h12 H)))))))))))).
Qed.

Lemma evD_mid_sbm : forall a ly S Hp (W : world SEGS) mem md md' k p dep dl,
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl -> same_but_materialized md md' ->
  ev_mid B ARx SK a ly S Hp W mem md' k p dep dl.
Proof.
  intros a ly S Hp W mem md md' k p dep dl (HJ & HR) Hs. split; [|exact HR].
  apply (ajournal_x_exec (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem md' (fun _ => False) HJ);
  [intros; reflexivity | apply mem_grows_refl | intros; reflexivity | exact Hs | intros z []].
Qed.

(* the frame of the activation, its slots apart from the s1 spills and from the scratch's block *)
Lemma evD_sep : forall a ly S Hp (W : world SEGS) mem md k p dep dl,
  ev_img_ok -> ev_pre B ARx a -> ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ARx ly S Hp W mem md /\ frame_addr ly 1 (ea_pos a) = ea_fr a /\ In (1, ea_pos a) (frames S) /\
  4096 <= ea_fr a /\ ea_fr a + 128 <= alloc_ceiling /\
  (forall z, ea_fr a <= z < ea_fr a + 128 -> apresent (w_H W) mem z) /\
  ea_fr a + 128 <= ea_S1 a /\ ea_S1 a + 256 <= 2 ^ 47 /\
  (forall i, 0 <= i <= 8 -> 0 <= shadow_addr (ea_fr a) + i < 2 ^ 64 /\
     (shadow_addr (ea_fr a) + i < ea_fr a + 64 \/ ea_fr a + 72 <= shadow_addr (ea_fr a) + i)) /\
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= ea_scr a /\ ea_scr a + ea_len a + 1 <= b + req_size m /\
     4096 <= b /\ b + req_size m <= alloc_ceiling /\ (b + req_size m <= ea_fr a \/ ea_fr a + 128 <= b)).
Proof.
  intros a ly S Hp W mem md k p dep dl HIMG HPRE HMID.
  destruct HMID as (HJ & _ & _ & Hbl & _).
  destruct HJ as (HARc & Hlyle & _ & _ & _ & Hfrs & _).
  destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIB & _).
  destruct HFP as ((HARe & _ & _ & _ & _ & HSTK & _) & _).
  pose proof (alx_layout SEGS B ARx LAWS _ _ _ _ _ _ ly HARe Hlyle) as (_ & Hfa & _).
  assert (Hin : In (1, ea_pos a) (frames S)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfa1 : frame_addr ly 1 (ea_pos a) = ea_fr a) by (rewrite Hfa; reflexivity).
  pose proof (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 (ea_pos a) HARc Hin) as (Hf1 & Hf2 & Happ).
  rewrite Hfa1 in Hf1, Hf2, Happ. change (fs_frame_bytes 1) with 128 in Hf2, Happ.
  pose proof (alx_frames SEGS B ARx LAWS ly S Hp W mem md 1 (ea_pos a) HARc Hin) as (_ & _ & Hpres & _).
  destruct HSTK as (Hsp16 & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
  assert (HSTKv : 272 <= ea_STK a).
  { unfold ea_STK, STK_ex_value. unfold ev_img_ok in HIMG.
    assert (Hz : 0 <= zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws])
      by (unfold zmaxl; cbn [fold_right]; lia).
    nia. }
  assert (HS1lo : ea_sp0 a - 272 <= ea_S1 a /\ ea_S1 a <= ea_sp0 a - 256).
  { unfold ea_S1, ea_SA, ea_sp0.
    pose proof (Z.div_mod (spZ (ea_regs a)) 16 ltac:(lia)) as E16. rewrite Hsp16 in E16.
    pose proof (Z.div_mod (spZ (ea_regs a) - 256) 32 ltac:(lia)) as E32.
    pose proof (Z.mod_pos_bound (spZ (ea_regs a) - 256) 32 ltac:(lia)) as B32.
    lia. }
  destruct HIB as (b & m & Hbm & Hb1 & Hb2 & _).
  rewrite <- Hbl in Hbm.
  pose proof (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HARc Hbm) as (_ & Hb4 & Hbc & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md b m 1 (ea_pos a) HARc Hbm Hin) as Hsep.
  rewrite Hfa1 in Hsep. change (fs_frame_bytes 1) with 128 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  assert (Hlen0 : 0 <= ea_len a) by (unfold ea_len; lia).
  assert (Hm : m <= req_size m) by (apply (proj2 (req_size_pos m ltac:(lia)))).
  unfold ea_sp0 in *.
  split; [exact HARc|]. split; [exact Hfa1|]. split; [exact Hin|]. split; [lia|]. split; [lia|].
  split; [intros z Hz; apply (Hpres z); rewrite Hfa1; change (fs_frame_bytes 1) with 128; lia|].
  split; [lia|]. split; [lia|].
  split.
  { intros i Hi. unfold shadow_addr, SHADOW_OFF.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    pose proof asan_consts as (Hac & _ & _ & _ & _).
    split; [lia|]. destruct Happ as (_ & [Hlow | [Hhigh Hceil2]]); [right | left]; lia. }
  exists b, m. split; [exact Hbm|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

Lemma ev_D : ev_D_stmt B ARx SK.
Proof.
  intros HIMG a KTa KCa. unfold KR.
  intros fxc W regs mem md ly S Hp k i1 c j bits cn HPRE HFX HCR.
  unfold ev_CR in HCR. cbv zeta in HCR.
  destruct HCR as (HMID & HBASE & R27 & M112 & R21 & M120 & M96 & HSPAN & HJB & HSTOP & R22 & HSCR & HSTR & HCN
    & M32 & FA0 & FSH).
  pose proof HBASE as (HREGS & R23 & Hi1 & Hc & Hws & Hskip & Hc34 & Hc91 & Hc123 & Hc102 & Hc110 & Hc116 & M104).
  pose proof HREGS as (R2r & R3r & R4r & R8r & R9r & R18r & R19r & R24r & R25r & R26r).
  pose proof (evD_sep a ly S Hp W mem md k _ _ _ HIMG HPRE HMID)
    as (HARc & Hfa & Hin1 & Hfr4 & Hfrc & Hfrp & HS1 & HS1h & Hfsh & bk & mk & Hbm & Hb1 & Hb2 & Hb4 & Hbc & Hbfr).
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdl & _).
  pose proof asan_consts as (Hacl & _ & _ & _ & _).
  pose proof HSPAN as (HLEAD & HNUM).
  (* MID's last conjunct, the memory normal form, as the hand step's invariant P := YAkMemnorm.memnorm SEGS *)
  pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
  assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN. clear HMN.
  assert (Htxtn : Forall (fun z => PjGrammar.numch z = true) (ev_sub (ea_x a) i1 j))
    by (apply (evD_txt_numch _ i1 j c Hc); [lia | exact HNUM]).
  pose proof (evD_N (ea_x a) i1 j c bits cn Hc Hws Hc34 Hc91 Hc123 Hc102 Hc110 Hc116 HLEAD HNUM HJB HSTOP HSTR) as HN.
  assert (Hltxt : length (ev_sub (ea_x a) i1 j) = (j - i1)%nat)
    by (unfold ev_sub; rewrite length_firstn, length_skipn; lia).
  assert (Hlenx : ea_len a = Z.of_nat (length (ea_x a))) by reflexivity.
  assert (FA0' : reg_get (@YK11.fp_regs fxc) 10%bv = Z_to_bv 64 bits)
    by (rewrite <- FA0; f_equal; apply bv_eq; reflexivity).
  (* +0x924 ld a0,0(s11) *)
  destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) (ea_fr a + 32) (ea_scr a + cn)
    (proj1 (val_mem_word_mem _ _ _ _) M32) ltac:(lia) ltac:(lia)) as (bs1 & Hrd1 & Hbs1).
  set (R1 := YK11.regupd regs 10%bv (w64 (ea_scr a + cn))).
  evD_fetch 0x924 (Load SZ8 true 10%bv 27%bv 0%bv).
  apply (evD_step W fxc regs 0x924 mem md md _ R1 0x928 (same_but_materialized_refl md)).
  { rewrite (step_ld _ _ _ _ _ _ _ _ _ bs1 (w64 (ea_scr a + cn)) Hf He Hd); [rewrite evD_next; reflexivity | | exact Hbs1].
    rewrite R27. unfold w64. rewrite YCbn.v_addi_lit. evD_bvs. rewrite Z.add_0_r. exact Hrd1. }
  clear Hf He Hd. intros md1 Hsm1.
  assert (A1 : getr R1 10%bv = w64 (ea_scr a + cn)) by (unfold R1; apply getr_same; discriminate).
  assert (HF1 : evD_frame R1 regs) by (unfold R1; apply evD_frame_upd; [left; reflexivity | apply evD_frame_refl]).
  clearbody R1.
  (* +0x928 ld a1,112(s1) *)
  destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) (ea_S1 a + 112) (ea_fr a + 64)
    (proj1 (val_mem_word_mem _ _ _ _) M112) ltac:(lia) ltac:(lia)) as (bs2 & Hrd2 & Hbs2).
  set (R2 := YK11.regupd R1 11%bv (w64 (ea_fr a + 64))).
  evD_fetch 0x928 (Load SZ8 true 11%bv 9%bv 112%bv).
  apply (evD_step W fxc R1 0x928 mem md md1 _ R2 0x92c Hsm1).
  { rewrite (step_ld _ _ _ _ _ _ _ _ _ bs2 (w64 (ea_fr a + 64)) Hf He Hd); [rewrite evD_next; reflexivity | | exact Hbs2].
    rewrite (HF1 9%bv) by discriminate. rewrite R9r. unfold w64. rewrite YCbn.v_addi_lit. evD_bvs. exact Hrd2. }
  clear Hf He Hd. intros md2 Hsm2.
  assert (A2_10 : getr R2 10%bv = w64 (ea_scr a + cn)) by (unfold R2; rewrite getr_other by discriminate; exact A1).
  assert (A2_11 : getr R2 11%bv = w64 (ea_fr a + 64)) by (unfold R2; apply getr_same; discriminate).
  assert (HF2 : evD_frame R2 regs) by (unfold R2; apply evD_frame_upd; [right; left; reflexivity | exact HF1]).
  clearbody R2.
  (* +0x92c fsd fa0,0(a1) *)
  evD_fetch 0x92c (FStore FMT_D 11%bv 10%bv 0%bv).
  apply (evD_step_m W fxc R2 0x92c mem md md2 _ R2 0x930
    (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 (ea_fr a + 64)) (word_to_le_bytes 8 (Z_to_bv 64 bits))) Hsm2 HPM).
  { rewrite (fp_step_fsd fxc _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (ea_fr a + 64)) Hf He Hd).
    - rewrite FA0', evD_next. reflexivity.
    - rewrite A2_11. unfold w64. rewrite YCbn.v_addi_lit. evD_bvs. rewrite Z.add_0_r. reflexivity.
    - apply evD_store_ok; [| lia | lia]. intros i Hi.
      destruct (Hfrp (ea_fr a + 64 + i) ltac:(lia)) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. discriminate. }
  clear Hf He Hd. intros md3 Hsm3 HPM1.
  set (mem1 := munrestrict (w_H W) mem
    (wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 (ea_fr a + 64)) (word_to_le_bytes 8 (Z_to_bv 64 bits)))).
  assert (Hbl8 : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 bits))) = 8)
    by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
  assert (AV1 : forall z, 0 <= z < 2 ^ 64 -> (z < ea_fr a + 64 \/ ea_fr a + 72 <= z) ->
                  aview SEGS (w_H W) mem1 z = aview SEGS (w_H W) mem z).
  { intros z Hz Hout. unfold mem1. apply evD_aview_out; rewrite ?Hbl8; lia. }
  pose proof HMID as (HJ & _).
  assert (AJ1 : ajournal_x (SK := SK) SEGS B prh_pst ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
      (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem1 md3 k).
  { apply (ajournal_x_exec (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem1 md3 (fun z => ea_fr a + 64 <= z < ea_fr a + 72) HJ).
    - intros x Hx. unfold mem1. apply evD_wb_out; rewrite ?Hbl8; lia.
    - unfold mem1. apply evD_wb_grow; rewrite ?Hbl8; lia.
    - intros x Hx. unfold mem1. apply evD_wb_hid. exact Hx.
    - exact Hsm3.
    - intros z Hz. right; right; right. exists 1, (ea_pos a). split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes 1) with 128. lia. }
  assert (MID1 : ev_mid B ARx SK a ly S Hp W mem1 md3 k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a)).
  { apply (MIDK a ly S Hp W mem md k _ _ _ mem1 md3 k HPRE HMID AJ1); [|exact HPM1].
    intros z Hz Hwz. apply AV1; [exact Hz|].
    destruct (Z_lt_le_dec z (ea_fr a + 64)) as [Hz1|Hz1]; [left; exact Hz1|].
    destruct (Z_lt_le_dec z (ea_fr a + 72)) as [Hz2|Hz2]; [|right; exact Hz2].
    exfalso. apply Hwz. unfold ev_wz. right; right; left. lia. }
  assert (M104' : val_mem SEGS (mrestrict (w_H W) mem1) (ea_S1 a + 104) 8 (ea_v a))
    by (unfold mem1; apply evD_vm_keep; rewrite ?Hbl8; try lia; exact M104).
  assert (M112' : val_mem SEGS (mrestrict (w_H W) mem1) (ea_S1 a + 112) 8 (ea_fr a + 64))
    by (unfold mem1; apply evD_vm_keep; rewrite ?Hbl8; try lia; exact M112).
  assert (M120' : val_mem SEGS (mrestrict (w_H W) mem1) (ea_S1 a + 120) 8 (ea_q a + 24))
    by (unfold mem1; apply evD_vm_keep; rewrite ?Hbl8; try lia; exact M120).
  assert (M96' : val_mem SEGS (mrestrict (w_H W) mem1) (ea_S1 a + 96) 8 (shadow_addr (ea_q a + 24)))
    by (unfold mem1; apply evD_vm_keep; rewrite ?Hbl8; try lia; exact M96).
  assert (HSCR' : garr8 SEGS (mrestrict (w_H W) mem1) (ea_scr a) (ev_sub (ea_x a) i1 j ++ [0])).
  { unfold mem1. apply evD_garr_keep; rewrite ?Hbl8, ?length_app, ?Hltxt; cbn [length];
    [lia | lia | lia | lia | lia | exact HSCR]. }
  assert (MFR : val_mem SEGS (mrestrict (w_H W) mem1) (ea_fr a + 64) 8 bits).
  { intros kk Hkk. unfold mem1. apply evD_wb_in; [lia | lia | exact Hkk |].
    destruct (Hfrp (ea_fr a + 64 + Z.of_nat kk) ltac:(lia)) as [Hh _]. exact Hh. }
  assert (FSH1 : ev_fsh a W mem1).
  { destruct FSH as [F4 F8]. split.
    - rewrite <- F4. apply AV1; [exact (proj1 (Hfsh 4 ltac:(lia))) | exact (proj2 (Hfsh 4 ltac:(lia)))].
    - rewrite <- F8. apply AV1; [exact (proj1 (Hfsh 8 ltac:(lia))) | exact (proj2 (Hfsh 8 ltac:(lia)))]. }
  assert (HBASE1 : ev_base a W regs mem1 i1 c) by exact (evD_base_mem a W regs mem mem1 i1 c HBASE M104').
  (* the tail from +0x940, reached with a0 = end by both sides of the shadow check *)
  lazymatch goal with |- SRr _ _ _ ?Q =>
  assert (TAIL : forall R md', same_but_materialized md3 md' -> evD_frame R regs ->
            getr R 10%bv = w64 (ea_scr a + cn) -> SRr SEGS W (@ev_cfg _ _ PA fxc R 0x940 mem1 md') Q) end.
  { intros R md' Hsm' HFR A10.
    (* +0x940 lbu a0,0(a0) *)
    set (e := nth (Z.to_nat cn) (ev_sub (ea_x a) i1 j ++ [0]) 0).
    destruct (HSCR' (Z.to_nat cn) ltac:(rewrite length_app; cbn [length]; lia)) as [Hve Hre].
    fold e in Hve, Hre. rewrite Z2Nat.id in Hve by lia.
    assert (Hrd8 : rdn SEGS (mrestrict (w_H W) mem1) (Z_to_bv 64 (ea_scr a + cn)) 1 = Some [Z_to_bv 8 (le_byte e 1 0)]).
    { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
      rewrite (Hve 0%nat ltac:(lia)). reflexivity. }
    set (R8 := YK11.regupd R 10%bv (w64 e)).
    evD_fetch 0x940 (Load SZ1 false 10%bv 10%bv 0%bv).
    apply (evD_step W fxc R 0x940 mem1 md3 md' _ R8 0x944 Hsm').
    { rewrite (step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 (le_byte e 1 0)) Hf He Hd).
      - rewrite evD_byte by exact Hre. rewrite evD_next. reflexivity.
      - rewrite A10. unfold w64. rewrite YCbn.v_addi_lit. evD_bvs. rewrite Z.add_0_r. exact Hrd8. }
    clear Hf He Hd. intros md8 Hsm8.
    assert (A8 : getr R8 10%bv = w64 e) by (unfold R8; apply getr_same; discriminate).
    assert (HF8 : evD_frame R8 regs) by (unfold R8; apply evD_frame_upd; [left; reflexivity | exact HFR]).
    clearbody R8.
    pose proof (evD_end_byte _ cn Htxtn HCN) as HEB. fold e in HEB.
    (* +0x944 bnez a0 *)
    evD_fetch 0x944 (Branch BC_NE 10%bv 0%bv 176%bv).
    destruct (Z.eqb_spec cn (Z.of_nat (length (ev_sub (ea_x a) i1 j)))) as [Ecn | Ecn].
    2: {
      apply (evD_step W fxc R8 0x944 mem1 md3 md8 _ R8 0x9f4 Hsm8).
      { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite evD_btgt; reflexivity|].
        rewrite A8, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. exact HEB. }
      intros md9 Hsm9.
      apply (KTa fxc W R8 mem1 md9 ly S Hp k i1 c HPRE HFX).
      unfold ev_CT. split; [exact (evD_base_regs a W regs R8 mem1 i1 c HBASE1 HF8)|].
      exists (-1), (Z.of_nat i1), (ea_dl a).
      split; [rewrite (HF8 21%bv) by discriminate; exact R21|].
      split; [exact (evD_mid_sbm _ _ _ _ _ _ _ _ _ _ _ _ MID1 Hsm9)|].
      split; [exact Hdl|].
      rewrite HN. cbn [andb]. auto. }
    apply (evD_step W fxc R8 0x944 mem1 md3 md8 _ R8 0x948 Hsm8).
    { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite evD_next; reflexivity|].
      rewrite A8, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. exact HEB. }
    clear Hf He Hd. intros md9 Hsm9.
    (* +0x948 fclass.d a0,fa0 *)
    set (K := fp_class fmt_double (bits mod 2 ^ 64)).
    pose proof (evD_fclass_range (bits mod 2 ^ 64)) as HKr. fold K in HKr.
    set (R10 := YK11.regupd R8 10%bv (w64 K)).
    evD_fetch 0x948 (Fclass FMT_D 10%bv 10%bv).
    apply (evD_step W fxc R8 0x948 mem1 md3 md9 _ R10 0x94c Hsm9).
    { rewrite (fp_step_fclass_d fxc _ _ _ _ _ _ _ _ Hf He Hd). rewrite FA0', Z_to_bv_unsigned, evD_next. reflexivity. }
    clear Hf He Hd. intros md10 Hsm10.
    assert (A10' : getr R10 10%bv = w64 K) by (unfold R10; apply getr_same; discriminate).
    assert (HF10 : evD_frame R10 regs) by (unfold R10; apply evD_frame_upd; [left; reflexivity | exact HF8]).
    clearbody R10.
    (* +0x94c andi a0,a0,897 *)
    set (R11 := YK11.regupd R10 10%bv (w64 (Z.land K 897))).
    evD_fetch 0x94c (OpImm ALU_AND 10%bv 10%bv 897%bv).
    apply (evD_step W fxc R10 0x94c mem1 md3 md10 _ R11 0x950 Hsm10).
    { rewrite (step_andi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A10'. evD_bvs. unfold YK11.v_andi, w64.
      rewrite YK00.u64_lit by lia. rewrite evD_next. reflexivity. }
    clear Hf He Hd. intros md11 Hsm11.
    assert (A11 : getr R11 10%bv = w64 (Z.land K 897)) by (unfold R11; apply getr_same; discriminate).
    assert (HF11 : evD_frame R11 regs) by (unfold R11; apply evD_frame_upd; [left; reflexivity | exact HF10]).
    clearbody R11.
    assert (HM : 0 <= Z.land K 897 < 2 ^ 64) by (apply Z_land_range; lia).
    (* +0x950 snez a0,a0 *)
    set (s12 := if 0 <? Z.land K 897 then 1 else 0).
    set (R12 := YK11.regupd R11 10%bv (w64 s12)).
    evD_fetch 0x950 (Op ALU_SLTU 10%bv 0%bv 10%bv).
    apply (evD_step W fxc R11 0x950 mem1 md3 md11 _ R12 0x954 Hsm11).
    { rewrite (step_sltu _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A11, getr_zero. unfold YK11.v_sltu, w64.
      rewrite YK00.c_ltu_lit by lia. rewrite evD_next. unfold R12, s12, w64.
      destruct (0 <? Z.land K 897); reflexivity. }
    clear Hf He Hd. intros md12 Hsm12.
    assert (A12 : getr R12 10%bv = w64 s12) by (unfold R12; apply getr_same; discriminate).
    assert (HF12 : evD_frame R12 regs) by (unfold R12; apply evD_frame_upd; [left; reflexivity | exact HF11]).
    clearbody R12.
    pose proof (evD_fclass bits) as HFC. fold K in HFC.
    (* +0x954 bnez a0 *)
    evD_fetch 0x954 (Branch BC_NE 10%bv 0%bv 160%bv).
    destruct (Z.eqb_spec (Z.land K 897) 0) as [EM | EM].
    - apply (evD_step W fxc R12 0x954 mem1 md3 md12 _ R12 0x958 Hsm12).
      { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite evD_next; reflexivity|].
        rewrite A12, getr_zero. unfold s12. rewrite EM. reflexivity. }
      intros md13 Hsm13.
      apply (KCa fxc W R12 mem1 md13 ly S Hp k i1 c j bits HPRE HFX).
      unfold ev_CC. cbv zeta.
      split; [exact (evD_mid_sbm _ _ _ _ _ _ _ _ _ _ _ _ MID1 Hsm13)|].
      split; [exact (evD_base_regs a W regs R12 mem1 i1 c HBASE1 HF12)|].
      split; [exact M112'|].
      split; [rewrite (HF12 21%bv) by discriminate; exact R21|].
      split; [exact M120'|]. split; [exact M96'|].
      split; [rewrite (HF12 22%bv) by discriminate; exact R22|].
      split; [lia|].
      split; [|split; [exact HSCR' | split; [exact MFR | exact FSH1]]].
      rewrite HN, <- HFC. cbn [andb]. reflexivity.
    - apply (evD_step W fxc R12 0x954 mem1 md3 md12 _ R12 0x9f4 Hsm12).
      { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite evD_btgt; reflexivity|].
        rewrite A12, getr_zero. unfold s12. replace (0 <? Z.land K 897) with true by (symmetry; apply Z.ltb_lt; lia).
        reflexivity. }
      intros md13 Hsm13.
      apply (KTa fxc W R12 mem1 md13 ly S Hp k i1 c HPRE HFX).
      unfold ev_CT. split; [exact (evD_base_regs a W regs R12 mem1 i1 c HBASE1 HF12)|].
      exists (-1), (Z.of_nat i1), (ea_dl a).
      split; [rewrite (HF12 21%bv) by discriminate; exact R21|].
      split; [exact (evD_mid_sbm _ _ _ _ _ _ _ _ _ _ _ _ MID1 Hsm13)|].
      split; [exact Hdl|].
      rewrite HN, <- HFC. cbn [andb]. auto. }
  (* +0x930 srli a1,a0,3 *)
  set (R4 := YK11.regupd R2 11%bv (w64 ((ea_scr a + cn) / 8))).
  evD_fetch 0x930 (ShiftImm ALU_SRL 11%bv 10%bv 3%bv).
  apply (evD_step W fxc R2 0x930 mem1 md3 md3 _ R4 0x934 (same_but_materialized_refl md3)).
  { rewrite (step_srli _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A2_10. unfold YK11.v_srli, w64.
    rewrite YK00.u64_lit by lia. rewrite Z.shiftr_div_pow2 by (vm_compute; discriminate).
    replace (2 ^ bv_unsigned 3%bv) with 8 by (vm_compute; reflexivity). rewrite evD_next. reflexivity. }
  clear Hf He Hd. intros md4 Hsm4.
  assert (A4_10 : getr R4 10%bv = w64 (ea_scr a + cn)) by (unfold R4; rewrite getr_other by discriminate; exact A2_10).
  assert (A4_11 : getr R4 11%bv = w64 ((ea_scr a + cn) / 8)) by (unfold R4; apply getr_same; discriminate).
  assert (HF4 : evD_frame R4 regs) by (unfold R4; apply evD_frame_upd; [right; left; reflexivity | exact HF2]).
  clearbody R4.
  (* +0x934 add a1,a1,s8 *)
  set (R5 := YK11.regupd R4 11%bv (w64 (shadow_addr (ea_scr a + cn)))).
  evD_fetch 0x934 (Op ALU_ADD 11%bv 11%bv 24%bv).
  apply (evD_step W fxc R4 0x934 mem1 md3 md4 _ R5 0x938 Hsm4).
  { rewrite (step_add _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A4_11, (HF4 24%bv) by discriminate. rewrite R24r.
    unfold YK11.v_add, w64. rewrite !YK00.u64_lit by (unfold SHADOW_OFF; lia). rewrite evD_next.
    unfold R5, w64, shadow_addr. rewrite (Z.add_comm ((ea_scr a + cn) / 8) SHADOW_OFF). reflexivity. }
  clear Hf He Hd. intros md5 Hsm5.
  assert (A5_10 : getr R5 10%bv = w64 (ea_scr a + cn)) by (unfold R5; rewrite getr_other by discriminate; exact A4_10).
  assert (A5_11 : getr R5 11%bv = w64 (shadow_addr (ea_scr a + cn))) by (unfold R5; apply getr_same; discriminate).
  assert (HF5 : evD_frame R5 regs) by (unfold R5; apply evD_frame_upd; [right; left; reflexivity | exact HF4]).
  clearbody R5.
  (* +0x938 lb a1,0(a1): the shadow byte of end (wdest_ok's range_addressable for the scratch, at mem1) *)
  pose proof MID1 as (_ & _ & _ & _ & _ & _ & _ & HWD1 & _).
  pose proof HWD1 as (_ & _ & _ & _ & HRA1 & _).
  destruct (HRA1 (ea_scr a + cn) ltac:(lia)) as (s & Hsv & Hsok).
  unfold aview in Hsv.
  destruct (mbyte SEGS (mrestrict (w_H W) mem1) (shadow_of_addr SHADOW_OFF (ea_scr a + cn))) as [sb|] eqn:Esb;
    [|discriminate Hsv].
  cbn [option_map] in Hsv. injection Hsv as Hsb.
  change (shadow_of_addr SHADOW_OFF (ea_scr a + cn)) with (shadow_addr (ea_scr a + cn)) in Esb.
  assert (Hs8 : 0 <= s < 8) by (unfold saddr_ok in Hsok; pose proof (Z.mod_pos_bound (ea_scr a + cn) 8); lia).
  assert (Hrd6 : rdn SEGS (mrestrict (w_H W) mem1) (Z_to_bv 64 (shadow_addr (ea_scr a + cn))) 1 = Some [sb]).
  { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
    cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Esb. }
  set (R6 := YK11.regupd R5 11%bv (w64 s)).
  evD_fetch 0x938 (Load SZ1 true 11%bv 11%bv 0%bv).
  apply (evD_step W fxc R5 0x938 mem1 md3 md5 _ R6 0x93c Hsm5).
  { rewrite (step_lb _ _ _ _ _ _ _ _ _ sb Hf He Hd).
    - replace (v_lb sb) with (Z_to_bv 64 s) by (symmetry; exact (YCbn.cellval_small true sb s Hsb ltac:(lia))).
      rewrite evD_next. reflexivity.
    - rewrite A5_11. unfold w64. rewrite YCbn.v_addi_lit. evD_bvs. rewrite Z.add_0_r. exact Hrd6. }
  clear Hf He Hd. intros md6 Hsm6.
  assert (A6_10 : getr R6 10%bv = w64 (ea_scr a + cn)) by (unfold R6; rewrite getr_other by discriminate; exact A5_10).
  assert (A6_11 : getr R6 11%bv = w64 s) by (unfold R6; apply getr_same; discriminate).
  assert (HF6 : evD_frame R6 regs) by (unfold R6; apply evD_frame_upd; [right; left; reflexivity | exact HF5]).
  clearbody R6.
  (* +0x93c bnez a1 *)
  evD_fetch 0x93c (Branch BC_NE 11%bv 0%bv 720%bv).
  destruct (Z.eqb_spec s 0) as [Es | Es].
  - apply (evD_step W fxc R6 0x93c mem1 md3 md6 _ R6 0x940 Hsm6).
    { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite evD_next; reflexivity|].
      rewrite A6_11, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_eq. exact Es. }
    intros md7 Hsm7. exact (TAIL R6 md7 Hsm7 HF6 A6_10).
  - apply (evD_step W fxc R6 0x93c mem1 md3 md6 _ R6 0xc0c Hsm6).
    { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite evD_btgt; reflexivity|].
      rewrite A6_11, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_neq. exact Es. }
    clear Hf He Hd. intros md7 Hsm7.
    (* +0xc0c andi a2,a0,7 *)
    set (R7 := YK11.regupd R6 12%bv (w64 ((ea_scr a + cn) mod 8))).
    evD_fetch 0xc0c (OpImm ALU_AND 12%bv 10%bv 7%bv).
    apply (evD_step W fxc R6 0xc0c mem1 md3 md7 _ R7 0xc10 Hsm7).
    { rewrite (step_andi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A6_10. evD_bvs. unfold YK11.v_andi, w64.
      rewrite YK00.u64_lit by lia. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia.
      rewrite evD_next. reflexivity. }
    clear Hf He Hd. intros md8 Hsm8.
    assert (A7_10 : getr R7 10%bv = w64 (ea_scr a + cn)) by (unfold R7; rewrite getr_other by discriminate; exact A6_10).
    assert (A7_11 : getr R7 11%bv = w64 s) by (unfold R7; rewrite getr_other by discriminate; exact A6_11).
    assert (A7_12 : getr R7 12%bv = w64 ((ea_scr a + cn) mod 8)) by (unfold R7; apply getr_same; discriminate).
    assert (HF7 : evD_frame R7 regs) by (unfold R7; apply evD_frame_upd; [right; right; reflexivity | exact HF6]).
    clearbody R7.
    (* +0xc10 blt a2,a1 -> +0x940 *)
    evD_fetch 0xc10 (Branch BC_LT 12%bv 11%bv 7472%bv).
    apply (evD_step W fxc R7 0xc10 mem1 md3 md8 _ R7 0x940 Hsm8).
    { rewrite (step_blt_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite evD_btgt; reflexivity|].
      rewrite A7_12, A7_11. unfold w64, YK11.c_lts.
      pose proof (Z.mod_pos_bound (ea_scr a + cn) 8).
      rewrite YCbn.bv_lts_small by lia. apply Z.ltb_lt.
      destruct Hsok as [Hs0|[Hs1 Hs2]]; [exfalso; exact (Es Hs0) | exact Hs1]. }
    intros md9 Hsm9. exact (TAIL R7 md9 Hsm9 HF7 A7_10).
Qed.
End d.
