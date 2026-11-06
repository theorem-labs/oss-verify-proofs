(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT (cut CN, B 0x837a4 = exv_pc 0x278): the PURE part - the grammar reading the arm computes
   and the three byte tests image B's code makes, each shown equal to PjGrammar's predicate by a 256-case
   vm_compute. No machine state, no listing, no allocator.
   The three tests, read off the neutral listing
   the internal file ex_value.fuzz_preset.asan-ubsan.s (a Theorem Labs lane's listing of the B' pin):
     B 0x837e0-0x837e8  `addi a3,a0,-58; li a4,-10; bltu a3,a4, reject`        -> digit
     B 0x83818-0x83820  `addi a0,a0,-58; li a3,-11; bltu a3,a0, reject`        -> digit (the byte after a lead '0')
     B 0x83864-0x8387c  `addi a7,a6,-58; bltu a3(-11),a7 -> take;
                         addi a6,a6,-43; bltu a4(58),a6 -> stop;
                         srl a6,a5,a6; andi a6,a6,1; beqz -> stop`              -> numch
   with a5 = ((2 ^ 32 + 1) * 2 ^ 26 + 13), the value B 0x83838-0x83848 builds
   (`li a0,1; slli a0,a0,0x20; addi a0,a0,1; slli a0,a0,0x1a; addi a5,a0,13`).
   Numerals: 58, 43, -10, -11, 48, 45 (WORD: the immediates of those instructions and the ASCII '0' / '-');
   288230376218820621 (WORD: the mask the five instructions above build); 2 ^ 64, 64, 256, 8, 1, 13, 26, 32
   (DERIVED / LENGTH: the word modulus, the shift width, the byte modulus, widths). No ADDRESS.
   The grammar side (PjGrammar.digit / numch / span / skip, ReaderRes.jr_strtod) is preset's released PLAIN model,
   taken as a definition only; no released lemma is cited and no lib/Prog or lib/U proof is Required. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition exn_M64 : Z := 2 ^ 64.
Definition exn_MASK : Z := (2 ^ 32 + 1) * 2 ^ 26 + 13.

(* the unsigned comparison `bltu` makes, on the 64-bit differences the code computes *)
Definition exn_ult (x y : Z) : bool := (x mod exn_M64) <? (y mod exn_M64).

(* B 0x83864-0x8387c *)
Definition exn_scan_ok (b : Z) : bool :=
  exn_ult (-11) (b - 58) || (negb (exn_ult 58 (b - 43)) && Z.testbit exn_MASK ((b - 43) mod exn_M64 mod 64)).
(* B 0x837e0-0x837e8 *)
Definition exn_first_digit (b : Z) : bool := negb (exn_ult (b - 58) (-10)).
(* B 0x83818-0x83820 *)
Definition exn_next_digit (n : Z) : bool := exn_ult (-11) (n - 58).

Lemma exn_MASK_value : exn_MASK = 288230376218820621.
Proof. reflexivity. Qed.

Definition exn_bytes256 : list Z := map Z.of_nat (seq 0 256).

Lemma exn_in_bytes256 : forall b, 0 <= b < 256 -> In b exn_bytes256.
Proof.
intros b Hb. unfold exn_bytes256. apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.

Lemma exn_forallb_bytes256 : forall (f : Z -> bool), forallb f exn_bytes256 = true -> forall b, 0 <= b < 256 -> f b = true.
Proof. intros f Hf b Hb. rewrite forallb_forall in Hf. exact (Hf b (exn_in_bytes256 b Hb)). Qed.

Lemma exn_scan_ok_all : forallb (fun b => Bool.eqb (exn_scan_ok b) (numch b)) exn_bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma exn_first_digit_all : forallb (fun b => Bool.eqb (exn_first_digit b) (digit b)) exn_bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma exn_next_digit_all : forallb (fun b => Bool.eqb (exn_next_digit b) (digit b)) exn_bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem exn_scan_ok_numch : forall b, 0 <= b < 256 -> exn_scan_ok b = numch b.
Proof.
intros b Hb. pose proof (exn_forallb_bytes256 _ exn_scan_ok_all b Hb) as H. cbv beta in H.
apply Bool.eqb_prop in H. exact H.
Qed.

Theorem exn_first_digit_digit : forall b, 0 <= b < 256 -> exn_first_digit b = digit b.
Proof.
intros b Hb. pose proof (exn_forallb_bytes256 _ exn_first_digit_all b Hb) as H. cbv beta in H.
apply Bool.eqb_prop in H. exact H.
Qed.

Theorem exn_next_digit_digit : forall n, 0 <= n < 256 -> exn_next_digit n = digit n.
Proof.
intros n Hn. pose proof (exn_forallb_bytes256 _ exn_next_digit_all n Hn) as H. cbv beta in H.
apply Bool.eqb_prop in H. exact H.
Qed.

(* ---- the scan's span ---- *)
Lemma exn_span_cons_true : forall b x, numch b = true ->
  span numch (b :: x) = (b :: fst (span numch x), snd (span numch x)).
Proof. intros b x Hb. cbn [span]. rewrite Hb. destruct (span numch x). reflexivity. Qed.

Lemma exn_span_cons_false : forall b x, numch b = false -> span numch (b :: x) = ([], b :: x).
Proof. intros b x Hb. cbn [span]. rewrite Hb. reflexivity. Qed.

Lemma exn_span_app : forall x, fst (span numch x) ++ snd (span numch x) = x.
Proof.
induction x as [|b x IH]; [reflexivity|]. cbn [span]. destruct (numch b) eqn:Eb.
- destruct (span numch x) as [a r] eqn:E. cbn [fst snd app] in IH |- *.
  f_equal. exact IH.
- cbn [fst snd app]. reflexivity.
Qed.

Lemma exn_span_all_numch : forall x, Forall (fun z => numch z = true) (fst (span numch x)).
Proof.
induction x as [|b x IH]; [constructor|]. cbn [span]. destruct (numch b) eqn:Eb.
- destruct (span numch x) as [a r] eqn:E. cbn [fst snd] in IH |- *.
  constructor; [exact Eb | exact IH].
- cbn [fst]. constructor.
Qed.

Lemma exn_span_stop : forall x, snd (span numch x) = [] \/
  exists b r, snd (span numch x) = b :: r /\ numch b = false.
Proof.
induction x as [|b x IH]; [left; reflexivity|]. cbn [span]. destruct (numch b) eqn:Eb.
- destruct (span numch x) as [a r] eqn:E. cbn [fst snd] in IH |- *. exact IH.
- right. exists b, x. split; [cbn [snd]; reflexivity | exact Eb].
Qed.

(* the span's length is the number of leading numch bytes: the scan's exit index *)
Lemma exn_span_firstn : forall x, fst (span numch x) = firstn (length (fst (span numch x))) x.
Proof.
induction x as [|b x IH]; [reflexivity|]. cbn [span]. destruct (numch b) eqn:Eb.
- destruct (span numch x) as [a r] eqn:E. cbn [fst snd length firstn] in IH |- *.
  f_equal. exact IH.
- cbn [fst snd length firstn]. reflexivity.
Qed.

Lemma exn_span_skipn : forall x, snd (span numch x) = skipn (length (fst (span numch x))) x.
Proof.
induction x as [|b x IH]; [reflexivity|]. cbn [span]. destruct (numch b) eqn:Eb.
- destruct (span numch x) as [a r] eqn:E. cbn [fst snd length skipn] in IH |- *. exact IH.
- cbn [fst snd length skipn]. reflexivity.
Qed.

Lemma exn_nth_skipn : forall (l : list Z) k b r, skipn k l = b :: r -> nth k l 0 = b.
Proof.
induction l as [|a l IH]; intros [|k] b r H; cbn [skipn] in H; try discriminate H.
- injection H as H1 H2. cbn [nth]. exact H1.
- cbn [nth]. exact (IH k b r H).
Qed.

(* the byte the dispatch reads is not whitespace: it is the head of a skip *)
Lemma exn_skip_head : forall l b y, skip l = b :: y -> ws b = false.
Proof.
induction l as [|a l IH]; intros b y H; cbn [skip] in H; [discriminate H|].
destruct (ws a) eqn:Ea; [exact (IH b y H)|].
injection H as H1 H2. rewrite <- H1. exact Ea.
Qed.

(* ---- skip ---- *)
Lemma exn_skip_suffix : forall l, exists m, (m <= length l)%nat /\ skip l = skipn m l.
Proof.
induction l as [|b l IH]; [exists 0%nat; split; [cbn; lia | reflexivity]|].
cbn [skip]. destruct (ws b).
- destruct IH as (m & Hm & Hs). exists (S m). split; [cbn [length]; lia | cbn [skipn]; exact Hs].
- exists 0%nat. split; [cbn [length]; lia | reflexivity].
Qed.

Lemma exn_skipn_length_eq : forall (l : list Z) m, (m <= length l)%nat ->
  skipn (length l - length (skipn m l))%nat l = skipn m l.
Proof.
intros l m Hm. rewrite length_skipn. replace (length l - (length l - m))%nat with m by lia. reflexivity.
Qed.

(* the position the dispatch reached: skipn i1 of the whole text, with i1 = len - |skip (skipn i0 x)| *)
Lemma exn_at_i1 : forall (x : list Z) (i0 : nat), (i0 <= length x)%nat ->
  skipn (length x - length (skip (skipn i0 x)))%nat x = skip (skipn i0 x).
Proof.
intros x i0 Hi0. destruct (exn_skip_suffix (skipn i0 x)) as (m & Hm & Hs).
rewrite length_skipn in Hm.
rewrite Hs, skipn_skipn, length_skipn.
replace (length x - (length x - (m + i0)))%nat with (m + i0)%nat by lia.
reflexivity.
Qed.

(* ---- the number arm's reading, at ReaderRes.jr_strtod ---- *)
Definition exn_N (xs : list Z) : option (PjTree.jv * list Z) :=
  fst (fst (PjGrammar.jr_number ReaderRes.jr_strtod xs [])).
Definition exn_sg (c : Z) : nat := if c =? 45 then 1%nat else 0%nat.
Definition exn_sub (x : list Z) (a z : nat) : list Z := firstn (z - a) (skipn a x).

(* the dispatch class of ex_value's switch (ExvB_Stmt.exv_disp's bytes) *)
Definition exn_other (c : Z) : Prop := c <> 34 /\ c <> 91 /\ c <> 123 /\ c <> 116 /\ c <> 102 /\ c <> 110.

(* jr_value at a point whose first byte is not whitespace and not a dispatch byte IS the number arm *)
Lemma exn_value_is_number : forall (d : nat) (xs : list Z) b y,
  skip xs = b :: y -> ws b = false -> exn_other b ->
  fst (fst (PjGrammar.jr_value ReaderRes.jr_strtod d xs [])) = exn_N (b :: y).
Proof.
intros d xs b y Hs Hw (H34 & H91 & H123 & H116 & H102 & H110).
unfold PjGrammar.jr_value. cbn [PjGrammar.jrv]. rewrite Hs.
repeat (match goal with |- context [Z.eqb b ?k] => destruct (Z.eqb_spec b k); [lia|] end).
reflexivity.
Qed.

(* the arm's reading, unfolded one step: the sign, the lead digit test, the span *)
Lemma exn_N_unfold : forall (xs : list Z),
  exn_N xs =
  (let j := match xs with b :: _ => if b =? 45 then 1%nat else 0%nat | [] => 0%nat end in
   match skipn j xs with
   | [] => None
   | c :: z =>
     if negb (digit c) then None
     else if (c =? 48) && match z with c1 :: _ => digit c1 | [] => false end then None
     else
       let txt := firstn j xs ++ c :: fst (span numch z) in
       if whole ReaderRes.jr_strtod txt
       then Some (PjTree.JNum txt (snd (ReaderRes.jr_strtod txt)), snd (span numch z))
       else None
   end).
Proof.
intros xs. unfold exn_N, PjGrammar.jr_number. cbv zeta.
destruct (skipn _ xs) as [|c z]; [reflexivity|].
destruct (negb (digit c)); [reflexivity|].
destruct ((c =? 48) && _); [reflexivity|].
destruct (span numch z) as [a r] eqn:Es. cbv beta iota zeta.
unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take. cbn [fst snd].
try match goal with |- context [whole ?m ?t] => destruct (whole m t) end; reflexivity.
Qed.
