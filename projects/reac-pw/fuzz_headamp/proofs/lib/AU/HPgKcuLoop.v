(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the engine run from a fresh entry state and
   its re-seat at a fixed pc) for the value dispatch and the Int arm of reac-pw/fuzz_role's image-A segment M02
   (0x82318 .. 0x823e0). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyI.v at 7e8cf15c304 (the run / branch
   / exit pattern of a value dispatch, the entry state re-seated once the value entry's address is formed) and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v at 7e8cf15c304 (m2k_ent_type_slice, m2k_ent_size_slice,
   m2k_ent_word_slice) for reac-pw/fuzz_headamp image A: the m2i_ / m2k_ prefixes are renamed hvd_, every address
   is headamp's own, role's two arms and its MAL exit are replaced by headamp's Bool and Int arms with their five
   exits, and the cuts are lib/A/HPgSegM.v's and lib/A/HPgM3dBase.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dDisp.v, with its module names and addresses changed; 1442 of its 1596 lines of code are new or changed and 516 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgM3dDispU.v, with its module paths and module names changed; 830 of its 923 lines of code are new or changed and 1503 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgKcLoop.v at bba3a77011a0; the same two
   loop turns for image B. Image B's code differs from image A's at every instruction of this range: B tests the
   cursor after each step against the one's complement of the string's start (four UBSan trap branches here), B
   reads the sign and the first digit inside its digits loop (A reads them in a block of its own before it), B
   keeps read_channel's bound in t4 from the key piece's head (A loads it from the real frame here), and B's
   digits loop checks its multiply with `mulh` against the arithmetic shift of the low word. So the three block
   lemmas below are B's own; what is ported is the shape (a read-only region of one byte, an alias fact, one
   shadow entry, srr_branch_tok on each test, a post that keeps the journal and the registers outside the block's
   clobber list) and the model lemmas of read_channel. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): parts 2 and 3 of the piece "the key and the channel" of the walk of
   LLVMFuzzerTestOneInput (lib/AU/HPgKcuCut.v hku_P2_stmt and hku_P3_stmt at rsegs): one turn of read_channel's
   blanks loop with the sign, and one turn of its digits loop. Proves no function (kind: segment lemma).

   THE CODE (fuzz_headamp.c:67-90, read_channel inlined; rest = a0, i = a1, the key in s7)
     BL 0x832e8 .. SG 0x83328  a3 := a0 + a1; the instrumented 1-byte check of rest + i (slow block 0x8331c);
                               lbu a3; (a3 - 9) <u a6 (= 5) or a3 = a7 (= 0x20): a1++, the cursor's trap test
                               `bgeu a2,a1` 0x8330c, back to BL; else to SG
     SG 0x83328 .. DG 0x83364  a3 = '+' or '-': a1++, a3 := (c != '-'); else a3 := 1; the cursor's trap test
                               0x8334c; a4 := 0, ra := 0, s5 := 0, a5 := s7 + a1, a6 := a5 + 13; to DG
     DG 0x83364 .. DG / DOT    t0 := a6 + a4; the instrumented 1-byte check of rest + d + j (slow block 0x833bc);
                               a7 := a5 + a4; lbu t0,13(a7); t1 := t0 - 48; (t2 = 9) <u t1: to DOT 0x833c8; else
                               the big rule against t4 (= 1000000), s5 := s5 * t3 + (t0 & 15) with the multiply's
                               trap test 0x833a0, a4++, the cursor's trap test 0x833b4, back to DG
   No store, no call: the turns write no byte and change no float register. Each branch to `unimp` (0x8330c's
   fall-through 0x83310, 0x8334c, 0x833a0, 0x833b4) is shown not taken from the cut's own bounds: the key lies
   below 2 ^ 47 and its cursor below 130, so the one's complement of the string's start is above every index the
   loop forms; the accumulator is at most 10000009, so its product with 10 has a zero high word and a zero sign
   word. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require KeyFacts.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgKcuCut HPgKcuLib HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the model ================================ *)
Lemma ku_prefix_len13 : length HA_PREFIX = 13%nat.
Proof. reflexivity. Qed.

Lemma ku_prefix_len : forall k, ha_prefix k = true -> (13 <= length k)%nat.
Proof.
intros k H. unfold ha_prefix in H. apply Cursor.bytes_eqb_eq in H.
assert (L : length (firstn (length HA_PREFIX) k) = length HA_PREFIX) by (rewrite H; reflexivity).
rewrite length_firstn, ku_prefix_len13 in L. lia.
Qed.

Lemma ku_nth_skipn : forall (l : list byte) m n, nth n (skipn m l) Cursor.NUL = nth (m + n) l Cursor.NUL.
Proof.
intros l m. revert l. induction m as [|m IH]; intros l n; [reflexivity|].
destruct l as [|b l]; [destruct n; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* the byte i of rest is the byte 13 + i of the key and its NUL *)
Lemma ku_nth_rest : forall (k : list byte) i, (13 <= length k)%nat -> (i <= length (hku_rest k))%nat ->
nth (13 + i) (k ++ [Cursor.NUL]) Cursor.NUL = nth i (hku_rest k) Cursor.NUL.
Proof.
intros k i Hk Hi. unfold hku_rest in *. rewrite ku_prefix_len13 in *. rewrite length_skipn in Hi.
rewrite ku_nth_skipn.
destruct (Nat.lt_ge_cases (13 + i) (length k)) as [Hl|Hl].
- apply app_nth1. exact Hl.
- rewrite app_nth2 by lia. replace (13 + i - length k)%nat with 0%nat by lia. cbn [nth].
  rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma ku_skipn_cons : forall (s : list byte) n, (n < length s)%nat ->
skipn n s = nth n s Cursor.NUL :: skipn (S n) s.
Proof.
induction s as [|b s IH]; intros n Hn; cbn [length] in Hn; [lia|].
destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma ku_digit_lt : forall (s : list byte) i, rc_digit (nth i s Cursor.NUL) = true -> (i < length s)%nat.
Proof.
intros s i H. destruct (Nat.lt_ge_cases i (length s)) as [L|L]; [exact L|].
rewrite nth_overflow in H by exact L. vm_compute in H. discriminate H.
Qed.

Lemma ku_digits_stop : forall s n acc big, rc_digit (nth n s Cursor.NUL) = false ->
rc_digits acc big (skipn n s) = (acc, big, 0%nat).
Proof.
intros s n acc big H. destruct (Nat.lt_ge_cases n (length s)) as [Hl|Hl].
- rewrite (ku_skipn_cons s n Hl). cbn [rc_digits]. rewrite H. reflexivity.
- rewrite skipn_all2 by lia. reflexivity.
Qed.

(* the digits loop's equation, one digit further *)
Definition ku_acc (acc c : Z) : Z := if 1000000 <? acc then acc else acc * 10 + (c - 48).
Definition ku_big (acc : Z) (big : bool) : bool := if 1000000 <? acc then true else big.

Lemma ku_dg_step : forall (s : list byte) d j acc big,
rc_digit (nth (d + j) s Cursor.NUL) = true ->
rc_digits 0 false (skipn d s) =
  (fst (fst (rc_digits acc big (skipn (d + j) s))), snd (fst (rc_digits acc big (skipn (d + j) s))),
   (j + snd (rc_digits acc big (skipn (d + j) s)))%nat) ->
rc_digits 0 false (skipn d s) =
  (fst (fst (rc_digits (ku_acc acc (bv_unsigned (nth (d + j) s Cursor.NUL))) (ku_big acc big) (skipn (d + S j) s))),
   snd (fst (rc_digits (ku_acc acc (bv_unsigned (nth (d + j) s Cursor.NUL))) (ku_big acc big) (skipn (d + S j) s))),
   (S j + snd (rc_digits (ku_acc acc (bv_unsigned (nth (d + j) s Cursor.NUL))) (ku_big acc big)
     (skipn (d + S j) s)))%nat).
Proof.
intros s d j acc big Hd Heq. rewrite Heq.
pose proof (ku_digit_lt s (d + j) Hd) as Hl.
rewrite (ku_skipn_cons s (d + j) Hl). cbn [rc_digits]. rewrite Hd.
replace (S (d + j)) with (d + S j)%nat by lia.
unfold ku_acc, ku_big. destruct (1000000 <? acc); cbn [fst snd]; f_equal; lia.
Qed.

(* the byte after the digits is not a digit: the whole answer of rc_digits from d *)
Lemma ku_dot : forall (s : list byte) d nd acc big,
rc_digit (nth (d + nd) s Cursor.NUL) = false ->
rc_digits 0 false (skipn d s) =
  (fst (fst (rc_digits acc big (skipn (d + nd) s))), snd (fst (rc_digits acc big (skipn (d + nd) s))),
   (nd + snd (rc_digits acc big (skipn (d + nd) s)))%nat) ->
rc_digits 0 false (skipn d s) = (acc, big, nd).
Proof.
intros s d nd acc big Hn Heq.
rewrite (ku_digits_stop s (d + nd) acc big Hn) in Heq. cbn [fst snd] in Heq.
rewrite Heq, Nat.add_0_r. reflexivity.
Qed.

(* the code's tests on a byte b (0 <= b < 256) *)
Definition ku_blank (b : Z) : bool := ((9 <=? b) && (b <=? 13)) || (b =? 32).

Lemma ku_blank_rc : forall x : byte, ku_blank (bv_unsigned x) = rc_blank x.
Proof.
intros x. unfold ku_blank, rc_blank. set (c := bv_unsigned x).
destruct (Z.eqb_spec c 32) as [E|E]; [rewrite orb_true_r; reflexivity|]. rewrite orb_false_r.
destruct (Z.leb_spec 9 c), (Z.leb_spec c 13); cbn [andb];
  repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end; cbn [orb]; try reflexivity; lia.
Qed.

Lemma ku_digit_rc : forall x : byte, ((bv_unsigned x - 48) mod 2 ^ 64 <? 10) = rc_digit x.
Proof.
intros x. unfold rc_digit. pose proof (Cursor.byte_range x) as Hx. set (c := bv_unsigned x) in *.
destruct (Z.leb_spec 48 c) as [H|H].
- rewrite Z.mod_small by lia. cbn [andb].
  destruct (Z.ltb_spec (c - 48) 10), (Z.leb_spec c 57); try reflexivity; lia.
- cbn [andb]. replace (c - 48) with ((c - 48 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma ku_blank_low : forall b, 0 <= b < 256 -> ((b - 9) mod 2 ^ 64 <? 5) = (9 <=? b) && (b <=? 13).
Proof.
intros b Hb. destruct (Z.leb_spec 9 b) as [H|H].
- rewrite Z.mod_small by lia. cbn [andb].
  destruct (Z.ltb_spec (b - 9) 5), (Z.leb_spec b 13); try reflexivity; lia.
- cbn [andb]. replace (b - 9) with ((b - 9 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.

(* the code's sign arithmetic (0x83328 .. 0x83360) on the byte c after the blanks *)
Definition ku_sgn (b : Z) : Z := if (b =? 43) || (b =? 45) then 1 else 0.
Definition ku_flag (b : Z) : Z := if b =? 45 then 0 else 1.
Lemma ku_d_sgn : forall s : list byte,
Z.of_nat (hku_d s) = Z.of_nat (rc_blanks s) + ku_sgn (bv_unsigned (nth (rc_blanks s) s Cursor.NUL)) /\
(if hku_neg s then 0 else 1) = ku_flag (bv_unsigned (nth (rc_blanks s) s Cursor.NUL)).
Proof.
intros s. unfold hku_d, hku_neg, ku_sgn, ku_flag. rewrite KeyFacts.rc_sign_at.
destruct ((bv_unsigned (nth (rc_blanks s) s Cursor.NUL) =? 43) ||
          (bv_unsigned (nth (rc_blanks s) s Cursor.NUL) =? 45)) eqn:Es; cbn [fst snd].
- split; [lia | reflexivity].
- split; [lia|].
  assert (E45 : (bv_unsigned (nth (rc_blanks s) s Cursor.NUL) =? 45) = false)
    by (apply orb_false_iff in Es as [_ E]; exact E).
  rewrite E45. reflexivity.
Qed.
Lemma ku_hk_d_le : forall s : list byte, (hku_d s <= length s)%nat.
Proof.
intros s. unfold hku_d. pose proof (KeyFacts.rc_blanks_le s) as Hb.
rewrite KeyFacts.rc_sign_at.
destruct ((bv_unsigned (nth (rc_blanks s) s Cursor.NUL) =? 43) ||
          (bv_unsigned (nth (rc_blanks s) s Cursor.NUL) =? 45)) eqn:Es; cbn [snd]; [|lia].
assert (Hnz : bv_unsigned (nth (rc_blanks s) s Cursor.NUL) <> 0).
{ apply orb_true_iff in Es as [E1|E1]; apply Z.eqb_eq in E1; lia. }
pose proof (KeyFacts.nth_nonnul_lt s (rc_blanks s) Hnz). lia.
Qed.

Lemma ku_land15 : forall c, 48 <= c <= 57 -> Z.land c 15 = c - 48.
Proof.
intros c Hc.
assert (H : c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/ c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
repeat (destruct H as [->|H]; [reflexivity|]). subst c. reflexivity.
Qed.

Lemma ku_bigz_b2z : forall acc big, (if 1000000 <? acc then 1 else Z.b2z big) = Z.b2z (ku_big acc big).
Proof. intros acc big. unfold ku_big. destruct (1000000 <? acc); reflexivity. Qed.
Lemma ku_acc_bound : forall acc c, 0 <= acc <= 10000009 -> 48 <= c <= 57 -> 0 <= ku_acc acc c <= 10000009.
Proof. intros acc c Ha Hc. unfold ku_acc. destruct (Z.ltb_spec 1000000 acc); lia. Qed.
Lemma ku_digit_range : forall x : byte, rc_digit x = true -> 48 <= bv_unsigned x <= 57.
Proof.
intros x H. unfold rc_digit in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ================================ the code table and the engine's set-up ================================ *)
Definition KU_SG : Z := 0x83328.   (* the sign test (fuzz_headamp.c:74) *)
(* the 56 words 0x832e8 .. 0x833c4 (the slow blocks 0x8331c and 0x833bc included); the end DOT 0x833c8 lies
   outside it *)
Definition ku_tbl : ctable := build_table rsegs HKU_BL 56 TEmpty.
Lemma ku_tbl_ok : table_ok rsegs ku_tbl.
Proof. apply build_table_ok0. unfold HKU_BL. lia. Qed.

(* the shadow base: register s11 (atom 27) holds SHADOW_OFF *)
Definition KUSB : Z := 0x7fff8000.
Definition KUBx : sv := SOff 27 0.
Definition KUBspan : Z * Z := (KUSB, KUSB + 2 ^ 44 - 1).
(* the bound of a byte address in the pp block (below the allocator's ceiling) *)
Definition KU_PHI : Z := 2 ^ 47 - 0x100.

(* a read-only region of one byte at atom 32, holding atom 33; its shadow entry [P, P + 8) *)
Definition ku_RB : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition ku_SH : list shent := [mkSHE 32 0 8].
Definition ku_ex (P b : Z) : list word := [w64 P; w64 b].

Lemma ku_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma ku_soff : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.
Lemma ku_U_soff : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof. intros E n v c H Hv. rewrite U_SOff, H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma ku_U_addlit : forall E x c, U E (SAlu ALU_ADD x (SLit c)) = (U E x + c) mod 2 ^ 64.
Proof.
intros E x c. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
(* the value of the one's complement the cursor tests compare against *)
Lemma ku_U_not : forall E (n : nat) v, ew E n = w64 (hqu_not v) -> 0 <= v < 2 ^ 64 ->
U E (SOff n 0) = 2 ^ 64 - 1 - v.
Proof.
intros E n v H Hv. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit, Z.add_0_r.
unfold zcanon, M64. rewrite Zmod_mod. apply hqu_not_mod. exact Hv.
Qed.
(* the byte a `lbu` of a one-byte chunk loads *)
Lemma ku_zext8 : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
sv_denot E (SExt false 8 (SOff n 0)) = w64 b.
Proof. intros E n b H Hb. rewrite denot_lit_U, (U_zext8 E n b H Hb). reflexivity. Qed.
(* `addi a3,a3,-45; snez a3,a3` on the sign byte b *)
Lemma ku_snez : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff n (-45))) = w64 (if b =? 45 then 0 else 1).
Proof.
intros E n b H Hb. rewrite denot_lit_U, U_SAlu, U_SLit, (ku_U_soff E n b (-45) H) by lia.
cbn [zalu_raw]. unfold w64. f_equal.
destruct (Z.eqb_spec b 45) as [->|Hn]; [reflexivity|].
assert (Hp : 0 < (b + -45) mod 2 ^ 64).
{ destruct (Z.leb_spec 45 b).
  - rewrite Z.mod_small by lia. lia.
  - replace (b + -45) with ((b + -45 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
change (zcanon 0) with 0. destruct (Z.ltb_spec 0 ((b + -45) mod 2 ^ 64)); [reflexivity | lia].
Qed.
(* `mulh a7,s5,t3` and `mul s5,s5,t3; srai t1,s5,0x3f` with 0 <= acc <= 10000009 and t3 = 10: both words are 0,
   so the overflow test `bne a7,t1` 0x833a0 is not taken *)
Lemma ku_mulh0 : forall E acc, ew E 21 = Z_to_bv 64 acc -> ew E 28 = Z_to_bv 64 10 -> 0 <= acc <= 10000009 ->
U E (SMd M_MULH (SOff 21 0) (SOff 28 0)) = 0.
Proof.
intros E acc E21 E28 Ha. rewrite U_SMd, (U_atom E 21 acc E21), (U_atom E 28 10 E28) by lia.
cbn [zmd_raw]. rewrite !swrap64_id by (unfold half64; lia).
change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
unfold zcanon, M64. apply Zmod_0_l.
Qed.
Lemma ku_sra0 : forall E acc, ew E 21 = Z_to_bv 64 acc -> ew E 28 = Z_to_bv 64 10 -> 0 <= acc <= 10000009 ->
U E (SAlu ALU_SRA (SMd M_MUL (SOff 21 0) (SOff 28 0)) (SLit 63)) = 0.
Proof.
intros E acc E21 E28 Ha.
assert (HM : U E (SMd M_MUL (SOff 21 0) (SOff 28 0)) = acc * 10).
{ rewrite U_SMd, (U_atom E 21 acc E21), (U_atom E 28 10 E28) by lia.
  cbn [zmd_raw]. unfold zcanon, M64. apply Z.mod_small. lia. }
assert (HS : forall s, 63 <= s -> Z.shiftr (acc * 10) s = 0).
{ intros s Hs. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|].
  apply (Z.lt_le_trans _ (2 ^ 63)); [lia | apply Z.pow_le_mono_r; lia]. }
rewrite U_SAlu, U_SLit, HM. cbn [zalu_raw].
rewrite swrap64_id by (unfold half64; lia).
replace (Z.land (zcanon 63) 63) with 63 by (vm_compute; reflexivity).
rewrite (HS 63 ltac:(lia)).
unfold zcanon, M64. apply Zmod_0_l.
Qed.
(* `mul s5,s5,t3; andi a7,t0,15; add s5,s5,a7` with acc <= 1000000 and the digit c: ku_acc acc c *)
Lemma ku_s5_val : forall E acc c, ew E 21 = Z_to_bv 64 acc -> ew E 28 = Z_to_bv 64 10 -> ew E 33 = Z_to_bv 64 c ->
(1000000 <? acc) = false -> 0 <= acc <= 10000009 -> 48 <= c <= 57 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SOff 28 0))
  (SAlu ALU_AND (SExt false 8 (SOff 33 0)) (SLit 15))) = w64 (ku_acc acc c).
Proof.
intros E acc c E21 E28 E33 Hn Hacc Hc. apply Z.ltb_ge in Hn.
rewrite denot_lit_U, U_SAlu, U_SMd, (U_and_lit E (SExt false 8 (SOff 33 0)) 15),
  (U_atom E 21 acc E21), (U_atom E 28 10 E28), (U_zext8 E 33 c E33) by lia.
cbn [zalu_raw zmd_raw]. rewrite ku_land15 by lia.
unfold ku_acc. replace (1000000 <? acc) with false by (symmetry; apply Z.ltb_ge; lia).
unfold zcanon, M64. rewrite (Z.mod_small (acc * 10)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac ku_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
Ltac ku_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
(* the memory after a run over read-only regions is the memory at the block's start *)
Ltac ku_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac ku_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok ku_tbl_ok HS HJ SHOK KUBspan; [awr_ok_tac | ] end.
Ltac ku_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok ku_tbl_ok HS HJ SHOK KUBspan pc; [awr_ok_tac | ] end.
Ltac ku_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok ku_tbl_ok HS SHOK KUBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* the state at a block's end pc: the world, the journal and the memory as at its start, the I/O state, every
   register outside clob, and what R says of the arm's registers *)
Definition ku_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (clob : list (bv 5))
(R : bvmap 5 word -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\ R regs2.

Lemma ku_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob
(R : bvmap 5 word -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc -> ms_mem ms = memc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md' k -> same_io mdc md' ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) -> R (ms_regs ms) ->
ku_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob R W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob R E' ss' ms md' HS Hrv Hpc Hm HJ Hio Hk HR.
split; [reflexivity|]. exists (ms_regs ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc, Hm; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk | exact HR].
Qed.

Ltac ku_post_intro :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HM : ms_mem ?ms = _,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  rewrite HM in HJ;
  eapply (ku_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' ss' ms _ HS eq_refl eq_refl HM HJ);
  [ ku_io
  | lazymatch goal with |- forall r : bv 5, _ -> ~ In r ?cl -> _ =>
      intros r Hr0 Hn; exact (regs_kept_of_st_ok rsegs E' ss' ms rg ex0 _ cl HS HAE ltac:(vm_compute; reflexivity) r Hr0 Hn) end
  | try rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) ] end.
Ltac ku_regs := lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.

(* ---------------- BL 0x832e8 .. SG 0x83328: the blank test ---------------- *)
Definition ku_facts1 : facts :=
  mkFacts [ (27%nat, mkAF KUSB KUSB 0); (32%nat, mkAF 0x4000 KU_PHI 0) ] []
          [ (SAlu ALU_ADD (SOff 10 0) (SOff 11 0), SOff 32 0) ].
Definition ku_ss1 : sstate := mkSS HKU_BL sr_atoms [ku_RB] None ku_facts1.

Lemma ku_A1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Q i b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 Q -> getr regs (Z_to_bv 5 11) = w64 i ->
getr regs (Z_to_bv 5 12) = w64 (hqu_not Q) ->
getr regs (Z_to_bv 5 16) = w64 5 -> getr regs (Z_to_bv 5 17) = w64 32 ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
0 <= i <= 64 -> 0x4000 <= Q -> Q + i <= KU_PHI -> 0 <= b < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (Q + i) 1 b ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (Q + i) 8 ->
(forall a, Q + i <= a < Q + i + 8 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs HKU_BL regs memc mdc)
(fun W2 c2 =>
 (ku_blank b = true /\ ku_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HKU_BL [11; 13; 14]%bv
    (fun regs2 => getr regs2 (Z_to_bv 5 11) = w64 (i + 1)) W2 c2) \/
 (ku_blank b = false /\ ku_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KU_SG [13; 14]%bv
    (fun regs2 => getr regs2 (Z_to_bv 5 13) = w64 b) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q i b HJ H10 H11 H12 H16 H17 H27
  Hi HQ0 HQ1 Hb Vb HRA Happ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (ku_ex (Q + i) b) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 Q) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 i) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew (Ereg regs ex) 12 = w64 (hqu_not Q)) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 5) by (rewrite (EA 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E17 : ew (Ereg regs ex) 17 = Z_to_bv 64 32) by (rewrite (EA 17%nat (Z_to_bv 5 17) eq_refl); exact H17).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (Q + i)) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 b) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) ku_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 HKU_BL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ku_ss1. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, ku_RB.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by (unfold KU_PHI in *; lia).
    split; [lia|]. split; [unfold KU_PHI in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ (Q + i) 0 1 (SOff 33 0) b);
      [rewrite ku_denot0; exact E33 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I|]].
    + cbn [ku_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E27, E32, !unsigned_lit_small by (unfold SHADOW_OFF, KU_PHI in *; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold KUSB, SHADOW_OFF, KU_PHI in *. repeat split; lia.
    + cbn [ku_facts1 f_alias alias_ok]. split; [|exact I]. apply U_inj.
      rewrite U_SAlu, (U_atom _ 10 Q E10), (U_atom _ 11 i E11), (U_atom _ 32 (Q + i) E32)
        by (unfold KU_PHI in *; lia).
      cbn [zalu_raw]. rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). reflexivity. }
assert (U27 : U (Ereg regs ex) KUBx = SHADOW_OFF) by (apply U_atom; [exact E27 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs KUBx ku_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, ku_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc _ KUBx 32 (Q + i) 8 (Q + i) 0 8 HRA U27); [| lia | lia |].
  - apply U_atom; [exact E32 | unfold KU_PHI in *; lia].
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HKU_BL) with (Z_to_bv 64 HKU_BL).
(* 0x832e8 .. 0x83300: the check and the byte; stop at 0x83304 bgeu a4,a6 *)
ku_run. ku_mem.
ku_branch Hc1; rewrite branch_geu_U, ku_U_addlit, (U_zext8 E 33 b E33 Hb), (U_atom E 16 5 E16) in Hc1 by lia;
  replace (b + -9) with (b - 9) in Hc1 by ring; rewrite (ku_blank_low b Hb) in Hc1.
- (* not 9 .. 13: 0x83314 beq a3,a7 *)
  apply negb_true_iff in Hc1.
  ku_run. ku_mem.
  ku_branch Hc2; rewrite branch_eq_U, (U_zext8 E 33 b E33 Hb), (U_atom E 17 32 E17) in Hc2 by lia.
  + (* the space: 0x83308 a1++, the cursor test, back to BL *)
    ku_run. ku_mem.
    ku_branch Hc3; rewrite branch_geu_U, (ku_U_not E 12 Q E12 ltac:(unfold KU_PHI in *; lia)),
      (ku_U_soff E 11 i 1 E11 ltac:(lia)) in Hc3.
    * ku_run_to HKU_BL. ku_mem. apply SRr_ret. left.
      split; [unfold ku_blank; rewrite Hc2, orb_true_r; reflexivity|].
      ku_post_intro. ku_sv. apply (ku_soff E 11 i 1 E11); lia.
    * exfalso. apply negb_false_iff, Z.ltb_lt in Hc3.
      rewrite Z.mod_small in Hc3 by lia. unfold KU_PHI in *. lia.
  + (* not a blank: to SG *)
    ku_run_to KU_SG. ku_mem. apply SRr_ret. right.
    split; [unfold ku_blank; rewrite Hc1, Hc2; reflexivity|].
    ku_post_intro. ku_sv. exact (ku_zext8 E 33 b E33 Hb).
- (* 9 .. 13: 0x83308 a1++, the cursor test, back to BL *)
  apply negb_false_iff in Hc1.
  ku_run. ku_mem.
  ku_branch Hc3; rewrite branch_geu_U, (ku_U_not E 12 Q E12 ltac:(unfold KU_PHI in *; lia)),
    (ku_U_soff E 11 i 1 E11 ltac:(lia)) in Hc3.
  + ku_run_to HKU_BL. ku_mem. apply SRr_ret. left.
    split; [unfold ku_blank; rewrite Hc1; reflexivity|].
    ku_post_intro. ku_sv. apply (ku_soff E 11 i 1 E11); lia.
  + exfalso. apply negb_false_iff, Z.ltb_lt in Hc3.
    rewrite Z.mod_small in Hc3 by lia. unfold KU_PHI in *. lia.
Qed.

(* ---------------- SG 0x83328 .. DG 0x83364: the sign and the digits loop's entry ---------------- *)
Definition ku_ss2 : sstate := mkSS KU_SG sr_atoms [] None (mkFacts [] [] []).
Definition ku_A2_R (K i b : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 11) = w64 (i + ku_sgn b) /\ getr regs2 (Z_to_bv 5 13) = w64 (ku_flag b) /\
getr regs2 (Z_to_bv 5 14) = w64 0 /\ getr regs2 (Z_to_bv 5 1) = w64 0 /\
getr regs2 (Z_to_bv 5 21) = w64 0 /\
getr regs2 (Z_to_bv 5 15) = w64 (K + (i + ku_sgn b)) /\
getr regs2 (Z_to_bv 5 16) = w64 (K + 13 + (i + ku_sgn b)).

Lemma ku_A2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (K i b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 11) = w64 i -> getr regs (Z_to_bv 5 13) = w64 b ->
getr regs (Z_to_bv 5 12) = w64 (hqu_not (K + 13)) -> getr regs (Z_to_bv 5 23) = w64 K ->
0 <= i <= 64 -> 0 <= K -> K + 160 <= KU_PHI -> 0 <= b < 256 ->
SRr rsegs W (cfg_at rsegs KU_SG regs memc mdc)
(ku_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HKU_DG
  [1; 11; 13; 14; 15; 16; 21]%bv (ku_A2_R K i b)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs K i b HJ H11 H13 H12 H23 Hi HK0 HK1 Hb.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember ([] : list word) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 i) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 b) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E12 : ew (Ereg regs ex) 12 = w64 (hqu_not (K + 13)))
  by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 K) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (HS : st_ok rsegs (Ereg regs ex) ku_ss2 (restrict (w_H W) (mkst regs (Z_to_bv 64 KU_SG) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ku_ss2. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint all_disjoint]. exact I.
  - split; [exact I|]. split; exact I. }
assert (SHOK : sh_ok rsegs KUBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 KU_SG) with (Z_to_bv 64 KU_SG).
(* 0x83328; stop at 0x8332c beq a3,a4 ('+') *)
ku_run. ku_mem.
ku_branch Hc1; rewrite branch_eq_U, (U_atom E 13 b E13), (U_lit E 43) in Hc1 by lia.
- (* '+': 0x83338 a1++, a3 := (c != '-'), then the cursor test *)
  ku_run. ku_mem.
  ku_branch Hc3; rewrite branch_ltu_U, (ku_U_not E 12 (K + 13) E12 ltac:(unfold KU_PHI in *; lia)),
    (ku_U_soff E 11 i 1 E11 ltac:(lia)) in Hc3.
  + exfalso. apply Z.ltb_lt in Hc3. rewrite Z.mod_small in Hc3 by lia. unfold KU_PHI in *. lia.
  + ku_run_to HKU_DG. ku_mem. apply SRr_ret.
    ku_post_intro. unfold ku_A2_R, ku_sgn, ku_flag. rewrite Hc1. cbn [orb]. ku_regs.
    split; [ku_sv; apply (ku_soff E 11 i 1 E11); lia|].
    split; [ku_sv; exact (ku_snez E 13 b E13 Hb)|].
    split; [ku_sv; reflexivity|]. split; [ku_sv; reflexivity|]. split; [ku_sv; reflexivity|].
    split.
    * ku_sv. rewrite denot_lit_U, U_SAlu, (ku_U_soff E 11 i 1 E11 ltac:(lia)), (U_atom E 23 K E23)
        by (unfold KU_PHI in *; lia).
      cbn [zalu_raw]. rewrite (Z.mod_small (i + 1)) by lia. unfold w64. f_equal.
      rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). lia.
    * ku_sv. rewrite denot_lit_U, U_SAlu, (ku_U_soff E 11 i 14 E11 ltac:(lia)), (U_atom E 23 K E23)
        by (unfold KU_PHI in *; lia).
      cbn [zalu_raw]. rewrite (Z.mod_small (i + 14)) by lia. unfold w64. f_equal.
      rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). lia.
- (* 0x83330 li a4,'-'; stop at 0x83334 bne a3,a4 *)
  ku_run. ku_mem.
  ku_branch Hc2; rewrite branch_ne_U, (U_atom E 13 b E13), (U_lit E 45) in Hc2 by lia.
  + (* no sign: 0x83348 a3 := 1, then the cursor test *)
    apply negb_true_iff in Hc2.
    ku_run. ku_mem.
    ku_branch Hc3; rewrite branch_ltu_U, (ku_U_not E 12 (K + 13) E12 ltac:(unfold KU_PHI in *; lia)),
      (ku_U_soff E 11 i 0 E11 ltac:(lia)) in Hc3.
    * exfalso. apply Z.ltb_lt in Hc3. rewrite Z.mod_small in Hc3 by lia. unfold KU_PHI in *. lia.
    * ku_run_to HKU_DG. ku_mem. apply SRr_ret.
      ku_post_intro. unfold ku_A2_R, ku_sgn, ku_flag. rewrite Hc1, Hc2. cbn [orb]. ku_regs.
      split; [ku_sv; rewrite ku_denot0, E11; rewrite Z.add_0_r; reflexivity|].
      split; [ku_sv; reflexivity|].
      split; [ku_sv; reflexivity|]. split; [ku_sv; reflexivity|]. split; [ku_sv; reflexivity|].
      split.
      -- ku_sv. rewrite denot_lit_U, U_SAlu, (U_atom E 11 i E11), (U_atom E 23 K E23)
           by (unfold KU_PHI in *; lia).
         cbn [zalu_raw]. unfold w64. f_equal. rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). lia.
      -- ku_sv. rewrite denot_lit_U, U_SAlu, (ku_U_soff E 11 i 13 E11 ltac:(lia)), (U_atom E 23 K E23)
           by (unfold KU_PHI in *; lia).
         cbn [zalu_raw]. rewrite (Z.mod_small (i + 13)) by lia. unfold w64. f_equal.
         rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). lia.
  + (* '-': 0x83338 *)
    apply negb_false_iff in Hc2.
    ku_run. ku_mem.
    ku_branch Hc3; rewrite branch_ltu_U, (ku_U_not E 12 (K + 13) E12 ltac:(unfold KU_PHI in *; lia)),
      (ku_U_soff E 11 i 1 E11 ltac:(lia)) in Hc3.
    * exfalso. apply Z.ltb_lt in Hc3. rewrite Z.mod_small in Hc3 by lia. unfold KU_PHI in *. lia.
    * ku_run_to HKU_DG. ku_mem. apply SRr_ret.
      ku_post_intro. unfold ku_A2_R, ku_sgn, ku_flag. rewrite Hc1, Hc2. cbn [orb]. ku_regs.
      split; [ku_sv; apply (ku_soff E 11 i 1 E11); lia|].
      split; [ku_sv; rewrite (ku_snez E 13 b E13 Hb), Hc2; reflexivity|].
      split; [ku_sv; reflexivity|]. split; [ku_sv; reflexivity|]. split; [ku_sv; reflexivity|].
      split.
      -- ku_sv. rewrite denot_lit_U, U_SAlu, (ku_U_soff E 11 i 1 E11 ltac:(lia)), (U_atom E 23 K E23)
           by (unfold KU_PHI in *; lia).
         cbn [zalu_raw]. rewrite (Z.mod_small (i + 1)) by lia. unfold w64. f_equal.
         rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). lia.
      -- ku_sv. rewrite denot_lit_U, U_SAlu, (ku_U_soff E 11 i 14 E11 ltac:(lia)), (U_atom E 23 K E23)
           by (unfold KU_PHI in *; lia).
         cbn [zalu_raw]. rewrite (Z.mod_small (i + 14)) by lia. unfold w64. f_equal.
         rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). lia.
Qed.

(* ---------------- DG 0x83364 .. DG / DOT 0x833c8: one digit ---------------- *)
Definition ku_facts3 : facts :=
  mkFacts [ (27%nat, mkAF KUSB KUSB 0); (32%nat, mkAF 0x4000 KU_PHI 0) ] []
          [ (SAlu ALU_ADD (SOff 16 0) (SOff 14 0), SOff 32 0);
            (SAlu ALU_ADD (SOff 15 0) (SOff 14 0), SOff 32 (-13)) ].
Definition ku_ss3 : sstate := mkSS HKU_DG sr_atoms [ku_RB] None ku_facts3.
Definition ku_dig (b : Z) : bool := (b - 48) mod 2 ^ 64 <? 10.
Definition ku_C_DOT (K d j b : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 5) = w64 b /\ getr regs2 (Z_to_bv 5 17) = w64 (K + d + j).
Definition ku_C_DG (j acc bz b : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 14) = w64 (j + 1) /\ getr regs2 (Z_to_bv 5 21) = w64 (ku_acc acc b) /\
getr regs2 (Z_to_bv 5 1) = w64 (if 1000000 <? acc then 1 else bz).

Lemma ku_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (K d j acc bz b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 7) = w64 9 -> getr regs (Z_to_bv 5 28) = w64 10 ->
getr regs (Z_to_bv 5 29) = w64 HQU_RC_BIG ->
getr regs (Z_to_bv 5 21) = w64 acc -> getr regs (Z_to_bv 5 1) = w64 bz ->
getr regs (Z_to_bv 5 11) = w64 d -> getr regs (Z_to_bv 5 12) = w64 (hqu_not (K + 13)) ->
getr regs (Z_to_bv 5 14) = w64 j ->
getr regs (Z_to_bv 5 15) = w64 (K + d) -> getr regs (Z_to_bv 5 16) = w64 (K + 13 + d) ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
0 <= d <= 64 -> 0 <= j <= 64 -> 0x4000 <= K -> K + 160 <= KU_PHI ->
0 <= acc <= 10000009 -> 0 <= bz <= 1 -> 0 <= b < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (K + 13 + d + j) 1 b ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (K + 13 + d + j) 8 ->
(forall a, K + 13 + d + j <= a < K + 13 + d + j + 8 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs HKU_DG regs memc mdc)
(fun W2 c2 =>
 (ku_dig b = false /\ ku_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HKU_DOT
    [5; 6; 17]%bv (ku_C_DOT K d j b) W2 c2) \/
 (ku_dig b = true /\ ku_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HKU_DG
    [1; 5; 6; 14; 17; 21]%bv (ku_C_DG j acc bz b) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs K d j acc bz b
  HJ H7 H28 H29 H21 H1 H11 H12 H14 H15 H16 H27 Hd Hj HK0 HK1 Hacc Hbz Hb Vb HRA Happ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (ku_ex (K + 13 + d + j) b) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E7 : ew (Ereg regs ex) 7 = Z_to_bv 64 9) by (rewrite (EA 7%nat (Z_to_bv 5 7) eq_refl); exact H7).
assert (E28 : ew (Ereg regs ex) 28 = Z_to_bv 64 10) by (rewrite (EA 28%nat (Z_to_bv 5 28) eq_refl); exact H28).
assert (E29 : ew (Ereg regs ex) 29 = Z_to_bv 64 HQU_RC_BIG)
  by (rewrite (EA 29%nat (Z_to_bv 5 29) eq_refl); exact H29).
assert (E21 : ew (Ereg regs ex) 21 = Z_to_bv 64 acc) by (rewrite (EA 21%nat (Z_to_bv 5 21) eq_refl); exact H21).
assert (E1 : ew (Ereg regs ex) 1 = Z_to_bv 64 bz) by (rewrite (EA 1%nat (Z_to_bv 5 1) eq_refl); exact H1).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 d) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew (Ereg regs ex) 12 = w64 (hqu_not (K + 13)))
  by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E14 : ew (Ereg regs ex) 14 = Z_to_bv 64 j) by (rewrite (EA 14%nat (Z_to_bv 5 14) eq_refl); exact H14).
assert (E15 : ew (Ereg regs ex) 15 = Z_to_bv 64 (K + d)) by (rewrite (EA 15%nat (Z_to_bv 5 15) eq_refl); exact H15).
assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 (K + 13 + d))
  by (rewrite (EA 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (K + 13 + d + j)) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 b) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) ku_ss3 (restrict (w_H W) (mkst regs (Z_to_bv 64 HKU_DG) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ku_ss3. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, ku_RB.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by (unfold KU_PHI in *; lia).
    split; [lia|]. split; [unfold KU_PHI in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ (K + 13 + d + j) 0 1 (SOff 33 0) b);
      [rewrite ku_denot0; exact E33 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I|]].
    + cbn [ku_facts3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E27, E32, !unsigned_lit_small by (unfold SHADOW_OFF, KU_PHI in *; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold KUSB, SHADOW_OFF, KU_PHI in *. repeat split; lia.
    + cbn [ku_facts3 f_alias alias_ok]. split; [|split; [|exact I]]; apply U_inj.
      * rewrite U_SAlu, (U_atom _ 16 (K + 13 + d) E16), (U_atom _ 14 j E14),
          (U_atom _ 32 (K + 13 + d + j) E32) by (unfold KU_PHI in *; lia).
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64, KU_PHI in *; lia). reflexivity.
      * rewrite U_SAlu, (U_atom _ 15 (K + d) E15), (U_atom _ 14 j E14),
          (ku_U_soff _ 32 (K + 13 + d + j) (-13) E32) by (unfold KU_PHI in *; lia).
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64, KU_PHI in *; lia).
        rewrite Z.mod_small by (unfold KU_PHI in *; lia). lia. }
assert (U27 : U (Ereg regs ex) KUBx = SHADOW_OFF) by (apply U_atom; [exact E27 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs KUBx ku_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, ku_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc _ KUBx 32 (K + 13 + d + j) 8 (K + 13 + d + j) 0 8 HRA U27);
    [| lia | lia |].
  - apply U_atom; [exact E32 | unfold KU_PHI in *; lia].
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HKU_DG) with (Z_to_bv 64 HKU_DG).
(* 0x83364 .. 0x83380: the check, a7, the byte, t1; stop at 0x83384 bltu t2,t1 *)
ku_run. ku_mem.
ku_branch Hc; rewrite branch_ltu_U, (U_atom E 7 9 E7), ku_U_addlit, (U_zext8 E 33 b E33 Hb) in Hc by lia.
- (* not a digit: to DOT *)
  ku_run_to HKU_DOT. ku_mem. apply SRr_ret. left.
  split; [unfold ku_dig; apply Z.ltb_ge; apply Z.ltb_lt in Hc;
    replace (b - 48) with (b + -48) by ring; lia|].
  ku_post_intro. unfold ku_C_DOT. ku_regs.
  split; [ku_sv; exact (ku_zext8 E 33 b E33 Hb)|].
  ku_sv. rewrite (ku_soff E 32 (K + 13 + d + j) (-13) E32 ltac:(unfold KU_PHI in *; lia)
    ltac:(unfold KU_PHI in *; lia)).
  unfold w64. f_equal. lia.
- (* a digit: the big rule, the multiply, a4++, the cursor test, back to DG *)
  assert (Hdg : ku_dig b = true).
  { unfold ku_dig. apply Z.ltb_lt. apply Z.ltb_ge in Hc.
    replace (b - 48) with (b + -48) by ring.
    pose proof (Z.mod_pos_bound (b + -48) (2 ^ 64) ltac:(lia)). lia. }
  assert (Hc48 : 48 <= b <= 57).
  { unfold ku_dig in Hdg. apply Z.ltb_lt in Hdg.
    destruct (Z.leb_spec 48 b) as [Hl|Hl]; [rewrite Z.mod_small in Hdg by lia; lia|].
    exfalso. replace (b - 48) with ((b - 48 + 2 ^ 64) + (-1) * 2 ^ 64) in Hdg by ring.
    rewrite Z.mod_add in Hdg by lia. rewrite Z.mod_small in Hdg by lia. lia. }
  ku_run. ku_mem.
  ku_branch Hc1; rewrite YO0c.branch_ge, !ku_denot0, E29, E21, !unsigned_lit_small,
    !YO0b.s64_small in Hc1 by (unfold HQU_RC_BIG; lia).
  + (* acc <= 1000000: the multiply and its trap test *)
    apply negb_true_iff in Hc1. unfold HQU_RC_BIG in Hc1. apply Z.ltb_ge in Hc1.
    ku_run. ku_mem.
    ku_branch Hc2; rewrite branch_ne_U, (ku_mulh0 E acc E21 E28 ltac:(lia)),
      (ku_sra0 E acc E21 E28 ltac:(lia)) in Hc2.
    * exfalso. cbn in Hc2. discriminate Hc2.
    * ku_run. ku_mem.
      ku_branch Hc3; rewrite branch_ltu_U, (ku_U_not E 12 (K + 13) E12 ltac:(unfold KU_PHI in *; lia)),
        U_SAlu, (ku_U_soff E 11 d 1 E11 ltac:(lia)), (U_atom E 14 j E14) in Hc3
        by (unfold KU_PHI in *; lia).
      -- exfalso. apply Z.ltb_lt in Hc3. cbn [zalu_raw] in Hc3.
         rewrite (Z.mod_small (d + 1)) in Hc3 by lia.
         rewrite zcanon_id in Hc3 by (unfold M64; lia). unfold KU_PHI in *. lia.
      -- ku_run_to HKU_DG. ku_mem. apply SRr_ret. right. split; [exact Hdg|].
         ku_post_intro. unfold ku_C_DG. ku_regs.
         split; [ku_sv; apply (ku_soff E 14 j 1 E14); lia|].
         split; [ku_sv; apply (ku_s5_val E acc b E21 E28 E33);
           [apply Z.ltb_ge; lia | lia | lia]|].
         ku_sv. rewrite ku_denot0, E1.
         replace (1000000 <? acc) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  + (* 1000000 < acc: ra := 1, the accumulator kept *)
    apply negb_false_iff in Hc1. unfold HQU_RC_BIG in Hc1. apply Z.ltb_lt in Hc1.
    ku_run. ku_mem.
    ku_branch Hc3; rewrite branch_ltu_U, (ku_U_not E 12 (K + 13) E12 ltac:(unfold KU_PHI in *; lia)),
      U_SAlu, (ku_U_soff E 11 d 1 E11 ltac:(lia)), (U_atom E 14 j E14) in Hc3
      by (unfold KU_PHI in *; lia).
    * exfalso. apply Z.ltb_lt in Hc3. cbn [zalu_raw] in Hc3.
      rewrite (Z.mod_small (d + 1)) in Hc3 by lia.
      rewrite zcanon_id in Hc3 by (unfold M64; lia). unfold KU_PHI in *. lia.
    * ku_run_to HKU_DG. ku_mem. apply SRr_ret. right. split; [exact Hdg|].
      ku_post_intro. unfold ku_C_DG. ku_regs.
      split; [ku_sv; apply (ku_soff E 14 j 1 E14); lia|].
      split; [ku_sv; rewrite ku_denot0, E21; unfold ku_acc;
        replace (1000000 <? acc) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
      ku_sv. replace (1000000 <? acc) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

End d.
End b.

(* ================================ the cut lists ================================ *)
Section lists. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma ku_at_reg : forall (cx : hsu_scx rsegs) W2 mem2 regs2 L r v, hsu_at_cx rsegs cx W2 mem2 regs2 L ->
In (LReg r, v) L -> getr regs2 (Z_to_bv 5 r) = w64 v.
Proof.
intros cx W2 mem2 regs2 L r v HL Hin. unfold hsu_at_cx, hsu_at in HL. rewrite Forall_forall in HL.
exact (HL _ Hin).
Qed.
Lemma ku_at_sub : forall (cx : hsu_scx rsegs) W2 mem2 regs2 L L', hsu_at_cx rsegs cx W2 mem2 regs2 L ->
(forall x, In x L' -> In x L) -> hsu_at_cx rsegs cx W2 mem2 regs2 L'.
Proof.
intros cx W2 mem2 regs2 L L' HL Hs. unfold hsu_at_cx, hsu_at in *. rewrite Forall_forall in *.
intros x Hx. exact (HL x (Hs x Hx)).
Qed.
End lists.
Ltac ku_in := cbn [In app]; repeat (first [left; reflexivity | right]).

(* a register outside a block's clobber list keeps its value *)
Lemma ku_keep : forall (regs2 regs3 : bvmap 5 word) (clob : list (bv 5)) (qs : list Z),
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs3 r = getr regs2 r) ->
forallb (fun q => negb (bv_unsigned (Z_to_bv 5 q) =? 0) && negb (existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob)) qs
  = true ->
forall q, In q qs -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q).
Proof.
intros regs2 regs3 clob qs Hk Hb q Hq.
pose proof (proj1 (forallb_forall _ _) Hb q Hq) as Hq'. apply andb_prop in Hq' as [H1 H2].
apply negb_true_iff in H1, H2. apply Hk.
- apply Z.eqb_neq. exact H1.
- intros Hin.
  assert (He : existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob = true)
    by (apply existsb_exists; exists (Z_to_bv 5 q); split; [exact Hin | apply bv_eqb_eq; reflexivity]).
  rewrite He in H2. discriminate H2.
Qed.
(* the registers hku_inv_regs asks to be kept *)
Definition ku_qs : list Z := 2 :: 3 :: 4 :: hku_keep.
Lemma ku_qs_in : forall q : Z, q = 2 \/ q = 3 \/ q = 4 \/ In q hku_keep -> In q ku_qs.
Proof. intros q [->|[->|[->|Hq]]]; unfold ku_qs; cbn [In]; tauto. Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.

(* the lemmas of HPgKcuLib, with or without the Section hypothesis errno_low *)
Ltac ku_lib L H := first [pose proof (L errno_low) as H | pose proof L as H].

(* a register kept by the block whose post gives Hk: its value from Rq *)
Ltac ku_kept Hk Rq :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?q) = _ =>
    rewrite (ku_keep _ _ _ [q] Hk ltac:(vm_compute; reflexivity) q (or_introl eq_refl)); exact Rq end.
(* hku_inv_regs's register premise across a chain of blocks *)
Ltac ku_keepq :=
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq; apply ku_qs_in in Hq;
  repeat match goal with Hk : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r _ -> getr ?ra r = getr ?rb r |- getr ?ra _ = _ =>
    rewrite (ku_keep _ _ _ ku_qs Hk ltac:(vm_compute; reflexivity) q Hq) end;
  reflexivity.

(* the key's address and the bounds every block asks of it *)
Lemma ku_kaddr_bounds : forall cx m, 4096 <= e_pp (x_e rsegs cx) ->
e_pp (x_e rsegs cx) + 19744 <= alloc_ceiling -> alloc_ceiling <= 140737479966720 -> (m <= 31)%nat ->
0x4000 <= hku_kaddr rsegs cx m /\ hku_kaddr rsegs cx m + 160 <= KU_PHI.
Proof.
intros cx m H1 H2 H3 Hm. unfold hku_kaddr, Layout.OFF_ENT, Layout.ENT_SIZE, KU_PHI.
assert (Z.of_nat m <= 31) by lia. split; lia.
Qed.

Theorem hku_P2 : hku_P2_stmt rsegs B MT.
Proof.
intros cx POST r ev at0 m i HS HBL1 HDG.
intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf HC.
pose proof HC as (HI & Hat & Hi).
pose proof HI as (Hb3 & HL & Hfs9 & Hfs18 & Hfs19 & Hlive & Hat0 & Hk & Hp & Hx & Hcs).
pose proof Hb3 as (Hcore & _). pose proof Hcore as (HJ & _).
pose proof Hp as (Hv & Hpre & Hm & Hfold).
pose proof (ku_prefix_len k Hpre) as Hk13.
pose proof (hku_start_wf rsegs B cx r ev HS) as Hw.
destruct (Model.ents_wf r Hw) as [Hn32 _].
ku_lib (@hku_keymem fx rc SK B MT) KM.
destruct (KM cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb3 ltac:(lia) Hk)
  as (Hk44 & Hnul & Vk & _ & _ & _ & Hpp4k & Hppc & _ & HRA & Happ). clear KM.
ku_lib (@hku_inv_regs fx rc SK B MT) KI.
pose proof (@alloc_ceiling_value rc) as [[_ Hceil] _].
set (K := hku_kaddr rsegs cx m) in *.
assert (HPPS : Layout.PP_SIZE = 19744) by reflexivity. rewrite HPPS in Hppc.
destruct (ku_kaddr_bounds cx m Hpp4k Hppc Hceil ltac:(lia)) as [HK0 HK1].
pose proof (hku_rest_len k) as Hrl. pose proof (KeyFacts.rc_blanks_le (hku_rest k)) as Hbl.
assert (Hrl' : length (hku_rest k) = (length k - 13)%nat)
  by (unfold hku_rest; rewrite ku_prefix_len13, length_skipn; reflexivity).
(* the registers at BL *)
pose proof (ku_at_reg _ _ _ _ _ 23 K Hat ltac:(ku_in)) as R23.
pose proof (ku_at_reg _ _ _ _ _ 10 (K + 13) Hat ltac:(ku_in)) as R10.
pose proof (ku_at_reg _ _ _ _ _ 11 (Z.of_nat i) Hat ltac:(ku_in)) as R11.
pose proof (ku_at_reg _ _ _ _ _ 12 (hqu_not (K + 13)) Hat ltac:(ku_in)) as R12.
pose proof (ku_at_reg _ _ _ _ _ 16 5 Hat ltac:(ku_in)) as R16.
pose proof (ku_at_reg _ _ _ _ _ 17 32 Hat ltac:(ku_in)) as R17.
pose proof (ku_at_reg _ _ _ _ _ 7 9 Hat ltac:(ku_in)) as R7.
pose proof (ku_at_reg _ _ _ _ _ 28 10 Hat ltac:(ku_in)) as R28.
pose proof (ku_at_reg _ _ _ _ _ 29 HQU_RC_BIG Hat ltac:(ku_in)) as R29.
pose proof (ku_at_reg _ _ _ _ _ 27 SHADOW_OFF HL ltac:(unfold hku_L, hqu_L_seg, hqu_L_frame; ku_in)) as R27.
(* the byte rest[i] *)
remember (bv_unsigned (nth i (hku_rest k) Cursor.NUL)) as b eqn:Eb.
assert (Hb : 0 <= b < 256) by (rewrite Eb; apply Cursor.byte_range).
assert (Vb : val_mem rsegs (mrestrict (w_H W2) mem2) (K + 13 + Z.of_nat i) 1 b).
{ pose proof (Vk (13 + i)%nat ltac:(lia)) as V. rewrite (ku_nth_rest k i Hk13 ltac:(lia)) in V.
  replace (K + 13 + Z.of_nat i) with (K + Z.of_nat (13 + i)) by lia. rewrite Eb. exact V. }
eapply SRr_bind.
{ apply (ku_A1 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (K + 13) (Z.of_nat i) b HJ).
  all: first [ exact Vb | exact R10 | exact R11 | exact R12 | exact R16 | exact R17 | exact R27
             | (apply (ra_sub _ _ _ _ _ _ HRA); lia) | (intros a Ha; apply Happ; lia)
             | (unfold KU_PHI in *; lia) | lia ]. }
intros W3 c3 _ [(Hbl1 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)
  | (Hbl1 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)].
- (* a blank: BL at i + 1 *)
  rewrite Eb, ku_blank_rc in Hbl1.
  pose proof (KeyFacts.rc_blanks_go (hku_rest k) i Hi Hbl1) as Hi1.
  apply (HBL1 fx2 ly2 S2 W2 regs3 mem2 md3 k cs keys rf).
  split; [|split; [|exact Hi1]].
  + exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3 ltac:(ku_keepq)).
  + unfold hsu_at_cx, hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    * ku_kept Hk3 R23.
    * ku_kept Hk3 R10.
    * rewrite HR3. unfold w64. f_equal. lia.
    * ku_kept Hk3 R12.
    * ku_kept Hk3 R16.
    * ku_kept Hk3 R17.
    * ku_kept Hk3 R7.
    * ku_kept Hk3 R28.
    * ku_kept Hk3 R29.
- (* not a blank: i is the blanks' end; the sign *)
  rewrite Eb, ku_blank_rc in Hbl1.
  pose proof (KeyFacts.rc_blanks_stop (hku_rest k) i Hi Hbl1) as Hie.
  destruct (ku_d_sgn (hku_rest k)) as [Hd Hflag]. rewrite <- Hie, <- Eb in Hd, Hflag.
  pose proof (ku_hk_d_le (hku_rest k)) as Hdl.
  assert (R23' : getr regs3 (Z_to_bv 5 23) = w64 K) by ku_kept Hk3 R23.
  assert (R11' : getr regs3 (Z_to_bv 5 11) = w64 (Z.of_nat i)) by ku_kept Hk3 R11.
  assert (R12' : getr regs3 (Z_to_bv 5 12) = w64 (hqu_not (K + 13))) by ku_kept Hk3 R12.
  eapply SRr_bind.
  { apply (ku_A2 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 K (Z.of_nat i) b HJ3);
      [exact R11' | exact HR3 | exact R12' | exact R23' | lia | lia | lia | lia]. }
  intros W4 c4 _ (-> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & HR4).
  destruct HR4 as (Q11 & Q13 & Q14 & Q1 & Q21 & Q15 & Q16).
  rewrite <- Hd in Q11, Q15, Q16. rewrite <- Hflag in Q13.
  apply (HDG fx2 ly2 S2 W2 regs4 mem2 md4 k cs keys rf 0 false).
  split; [exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs4 md4 HS HI HJ4
    (same_io_trans _ _ _ Hio3 Hio4) ltac:(ku_keepq))|].
  split.
  { unfold hsu_at_cx, hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - ku_kept Hk4 R23'. 
    - rewrite (ku_keep _ _ _ [10] Hk4 ltac:(vm_compute; reflexivity) 10 (or_introl eq_refl)).
      ku_kept Hk3 R10.
    - rewrite (ku_keep _ _ _ [12] Hk4 ltac:(vm_compute; reflexivity) 12 (or_introl eq_refl)). exact R12'.
    - exact Q11.
    - exact Q13.
    - rewrite Q14. reflexivity.
    - rewrite Q1. reflexivity.
    - rewrite Q21. reflexivity.
    - rewrite Q15. reflexivity.
    - rewrite Q16. unfold w64. f_equal. lia.
    - rewrite (ku_keep _ _ _ [7] Hk4 ltac:(vm_compute; reflexivity) 7 (or_introl eq_refl)). ku_kept Hk3 R7.
    - rewrite (ku_keep _ _ _ [28] Hk4 ltac:(vm_compute; reflexivity) 28 (or_introl eq_refl)). ku_kept Hk3 R28.
    - rewrite (ku_keep _ _ _ [29] Hk4 ltac:(vm_compute; reflexivity) 29 (or_introl eq_refl)). ku_kept Hk3 R29. }
  split; [rewrite Nat.add_0_r; lia|].
  split; [rewrite Nat.add_0_r;
    destruct (rc_digits 0 false (skipn (hku_d (hku_rest k)) (hku_rest k))) as [[a0 b0] n0]; reflexivity|].
  lia.
Qed.

Theorem hku_P3 : hku_P3_stmt rsegs B MT.
Proof.
intros cx POST r ev at0 m j HS HDG1 HDOT.
intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf acc big HC.
pose proof HC as (HI & Hat & Hj & Heq & Hacc).
pose proof HI as (Hb3 & HL & _ & _ & _ & _ & _ & Hk & Hp & _).
pose proof Hb3 as (Hcore & _). pose proof Hcore as (HJ & _).
pose proof Hp as (_ & Hpre & Hm & _).
pose proof (ku_prefix_len k Hpre) as Hk13.
pose proof (hku_start_wf rsegs B cx r ev HS) as Hw.
destruct (Model.ents_wf r Hw) as [Hn32 _].
ku_lib (@hku_keymem fx rc SK B MT) KM.
destruct (KM cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb3 ltac:(lia) Hk)
  as (Hk44 & Hnul & Vk & _ & _ & _ & Hpp4k & Hppc & _ & HRA & Happ). clear KM.
ku_lib (@hku_inv_regs fx rc SK B MT) KI.
pose proof (@alloc_ceiling_value rc) as [[_ Hceil] _].
set (K := hku_kaddr rsegs cx m) in *.
assert (HPPS : Layout.PP_SIZE = 19744) by reflexivity. rewrite HPPS in Hppc.
destruct (ku_kaddr_bounds cx m Hpp4k Hppc Hceil ltac:(lia)) as [HK0 HK1].
pose proof (hku_rest_len k) as Hrl.
assert (Hrl' : length (hku_rest k) = (length k - 13)%nat)
  by (unfold hku_rest; rewrite ku_prefix_len13, length_skipn; reflexivity).
pose proof (ku_hk_d_le (hku_rest k)) as Hdl.
set (d := hku_d (hku_rest k)) in *.
(* the registers at DG *)
pose proof (ku_at_reg _ _ _ _ _ 23 K Hat ltac:(ku_in)) as R23.
pose proof (ku_at_reg _ _ _ _ _ 10 (K + 13) Hat ltac:(ku_in)) as R10.
pose proof (ku_at_reg _ _ _ _ _ 12 (hqu_not (K + 13)) Hat ltac:(ku_in)) as R12.
pose proof (ku_at_reg _ _ _ _ _ 11 (Z.of_nat d) Hat ltac:(ku_in)) as R11.
pose proof (ku_at_reg _ _ _ _ _ 13 _ Hat ltac:(ku_in)) as R13.
pose proof (ku_at_reg _ _ _ _ _ 14 (Z.of_nat j) Hat ltac:(ku_in)) as R14.
pose proof (ku_at_reg _ _ _ _ _ 1 (Z.b2z big) Hat ltac:(ku_in)) as R1.
pose proof (ku_at_reg _ _ _ _ _ 21 acc Hat ltac:(ku_in)) as R21.
pose proof (ku_at_reg _ _ _ _ _ 15 (K + Z.of_nat d) Hat ltac:(ku_in)) as R15.
pose proof (ku_at_reg _ _ _ _ _ 16 (K + Z.of_nat d + 13) Hat ltac:(ku_in)) as R16.
pose proof (ku_at_reg _ _ _ _ _ 7 9 Hat ltac:(ku_in)) as R7.
pose proof (ku_at_reg _ _ _ _ _ 28 10 Hat ltac:(ku_in)) as R28.
pose proof (ku_at_reg _ _ _ _ _ 29 HQU_RC_BIG Hat ltac:(ku_in)) as R29.
pose proof (ku_at_reg _ _ _ _ _ 27 SHADOW_OFF HL ltac:(unfold hku_L, hqu_L_seg, hqu_L_frame; ku_in)) as R27.
(* the byte rest[d + j] *)
remember (bv_unsigned (nth (d + j) (hku_rest k) Cursor.NUL)) as b eqn:Eb.
assert (Hb : 0 <= b < 256) by (rewrite Eb; apply Cursor.byte_range).
assert (Vb : val_mem rsegs (mrestrict (w_H W2) mem2) (K + 13 + Z.of_nat d + Z.of_nat j) 1 b).
{ pose proof (Vk (13 + (d + j))%nat ltac:(lia)) as V.
  rewrite (ku_nth_rest k (d + j) Hk13 ltac:(lia)) in V.
  replace (K + 13 + Z.of_nat d + Z.of_nat j) with (K + Z.of_nat (13 + (d + j))) by lia.
  rewrite Eb. exact V. }
eapply SRr_bind.
{ apply (ku_C (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 K (Z.of_nat d) (Z.of_nat j) acc
    (Z.b2z big) b HJ).
  all: first [ exact Vb | exact R7 | exact R28 | exact R29 | exact R21 | exact R1 | exact R11 | exact R12
             | exact R14 | exact R27
             | (rewrite R15; reflexivity) | (rewrite R16; unfold w64; f_equal; lia)
             | (apply (ra_sub _ _ _ _ _ _ HRA); lia) | (intros a Ha; apply Happ; lia)
             | (destruct big; cbn; lia) | (unfold KU_PHI in *; lia) | lia ]. }
intros W3 c3 _ [(Hd3 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)
  | (Hd3 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)];
  unfold ku_dig in Hd3; rewrite Eb, ku_digit_rc in Hd3.
- (* not a digit: DOT with nd = j *)
  destruct HR3 as (Q5 & Q17).
  apply (HDOT fx2 ly2 S2 W2 regs3 mem2 md3 k cs keys rf j acc big).
  split; [exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3
    ltac:(ku_keepq))|].
  split.
  { unfold hsu_at_cx, hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - ku_kept Hk3 R23.
    - ku_kept Hk3 R10.
    - ku_kept Hk3 R12.
    - ku_kept Hk3 R11.
    - ku_kept Hk3 R13.
    - ku_kept Hk3 R14.
    - ku_kept Hk3 R1.
    - ku_kept Hk3 R21.
    - rewrite Q17. reflexivity.
    - rewrite Q5, Eb. reflexivity. }
  split; [exact Hj|]. split; [exact Hd3|].
  split; [exact (ku_dot (hku_rest k) d j acc big Hd3 Heq) | lia].
- (* a digit: DG at j + 1 *)
  destruct HR3 as (Q14 & Q21 & Q1).
  pose proof (ku_digit_lt (hku_rest k) (d + j) Hd3) as Hdj.
  assert (Hc48 : 48 <= b <= 57) by (rewrite Eb; apply ku_digit_range; exact Hd3).
  rewrite ku_bigz_b2z in Q1.
  apply (HDG1 fx2 ly2 S2 W2 regs3 mem2 md3 k cs keys rf (ku_acc acc b) (ku_big acc big)).
  split; [exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3
    ltac:(ku_keepq))|].
  split.
  { unfold hsu_at_cx, hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - ku_kept Hk3 R23.
    - ku_kept Hk3 R10.
    - ku_kept Hk3 R12.
    - ku_kept Hk3 R11.
    - ku_kept Hk3 R13.
    - rewrite Q14. unfold w64. f_equal. lia.
    - exact Q1.
    - exact Q21.
    - ku_kept Hk3 R15.
    - ku_kept Hk3 R16.
    - ku_kept Hk3 R7.
    - ku_kept Hk3 R28.
    - ku_kept Hk3 R29. }
  split; [lia|].
  split; [rewrite Eb; exact (ku_dg_step (hku_rest k) d j acc big Hd3 Heq)|].
  apply ku_acc_bound; lia.
Qed.

End e.

Print Assumptions hku_P2.
Print Assumptions hku_P3.
