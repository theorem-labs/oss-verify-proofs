(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v; 402 of its 445 lines of code are new or changed and 971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanInner.v, with its module paths and module names changed; 851 of its 923 lines of code are new or changed and 373 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): parts 2 and 3 of the piece "the key and the channel" of the walk of
   LLVMFuzzerTestOneInput (lib/A/HPgKcCut.v hk_P2_stmt and hk_P3_stmt at rsegs): one turn of read_channel's
   blanks loop with the sign and the first digit, and one turn of its digits loop. Proves no function (kind:
   segment lemma).

   THE CODE (fuzz_headamp.c:67-90, read_channel inlined; rest = a0, i = a1, the key in s2)
     BL 0x831c0 .. 0x831f8  a2 := a0 + a1; the instrumented 1-byte check of rest + i (slow block 0x831f0); lbu a2;
                            (a2 - 9) <u 5 (a5 = 5) or a2 = 0x20 (a6): a1++ and back to BL; else to SG
     SG 0x831fc .. 0x83224  a3 := '+'; a7 := 10; t0 := ld R+0xc0 (1000000); '+' or '-': a1++, a2 := (c != '-');
                            else a2 := 1; all to SN
     SN 0x83228 .. 0x83260  a0 := a0 + a1 (rest + d); the instrumented check (slow block 0x835e8); lbu a3;
                            a0 := a3 - 48; t3 := 4; a4 := 9; bltu 9, a0: no digit, to RF 0x83460; else a0 := 0,
                            t4 := 0, t1 := 0, s2 := s2 + a1, a4 := s2 + 14, to DG
     DG 0x83264 .. 0x832ac  bge t0,t1 (else t4 := 1); blt t0,t1 (else t1 := t1 * a7 + (a3 & 15)); a3 := a4 + a0;
                            the instrumented check (slow block 0x832a4); lbu a3; a5 := a3 - 48; a0++;
                            bltu a5,a7: a digit, back to DG; else to DOT 0x832b0
   No store, no call: the turns write no byte and change no float register.

   HOW. Four block lemmas over the token engine (lib/Reusable YCbn.v / YCbq.v), one per block above, each from a
   state whose registers are atoms, with a read-only region over the byte it reads (the key's byte, as role's
   RPgScanInner.v reads the pp block's bytes) or over the cell R+0xc0, an alias fact that makes the address the
   code computes an atom, and one shadow entry [P, P + 8) over the byte's address (paid from hk_keymem's
   addressable span of the entry). The post kl_post keeps the world, the memory, the journal and every register
   outside the block's clobber list, and gives the registers the arm computes. hk_P2 runs BL, SG and SN in turn
   and rebuilds BL at i + 1, RF (BAD_KEY) or DG at j = 0; hk_P3 runs DG and rebuilds DG at j + 1 or DOT. The cut
   hk_inv is carried by hk_inv_regs (lib/A/HPgKcLib.v). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgKcCut HPgKcLib HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the model ================================ *)
Lemma kl_prefix_len13 : length HA_PREFIX = 13%nat.
Proof. reflexivity. Qed.

Lemma kl_prefix_len : forall k, ha_prefix k = true -> (13 <= length k)%nat.
Proof.
intros k H. unfold ha_prefix in H. apply Cursor.bytes_eqb_eq in H.
assert (L : length (firstn (length HA_PREFIX) k) = length HA_PREFIX) by (rewrite H; reflexivity).
rewrite length_firstn, kl_prefix_len13 in L. lia.
Qed.

Lemma kl_nth_skipn : forall (l : list byte) m n, nth n (skipn m l) Cursor.NUL = nth (m + n) l Cursor.NUL.
Proof.
intros l m. revert l. induction m as [|m IH]; intros l n; [reflexivity|].
destruct l as [|b l]; [destruct n; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* the byte i of rest is the byte 13 + i of the key and its NUL *)
Lemma kl_nth_rest : forall (k : list byte) i, (13 <= length k)%nat -> (i <= length (hk_rest k))%nat ->
nth (13 + i) (k ++ [Cursor.NUL]) Cursor.NUL = nth i (hk_rest k) Cursor.NUL.
Proof.
intros k i Hk Hi. unfold hk_rest in *. rewrite kl_prefix_len13 in *. rewrite length_skipn in Hi.
rewrite kl_nth_skipn.
destruct (Nat.lt_ge_cases (13 + i) (length k)) as [Hl|Hl].
- apply app_nth1. exact Hl.
- rewrite app_nth2 by lia. replace (13 + i - length k)%nat with 0%nat by lia. cbn [nth].
  rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma kl_blank_nul : rc_blank Cursor.NUL = false.
Proof. reflexivity. Qed.
Lemma kl_digit_nul : rc_digit Cursor.NUL = false.
Proof. reflexivity. Qed.

Lemma kl_blanks_true : forall s i, (i < rc_blanks s)%nat -> rc_blank (nth i s Cursor.NUL) = true.
Proof.
induction s as [|b s IH]; intros i Hi; cbn [rc_blanks] in Hi; [lia|].
destruct (rc_blank b) eqn:Eb; [|lia].
destruct i as [|i]; [exact Eb|]. cbn [nth]. apply IH. lia.
Qed.

Lemma kl_blanks_stop : forall s, rc_blank (nth (rc_blanks s) s Cursor.NUL) = false.
Proof.
induction s as [|b s IH]; cbn [rc_blanks]; [reflexivity|].
destruct (rc_blank b) eqn:Eb; [exact IH | exact Eb].
Qed.

Lemma kl_blank_lt : forall s i, (i <= rc_blanks s)%nat -> rc_blank (nth i s Cursor.NUL) = true ->
(S i <= rc_blanks s)%nat.
Proof.
intros s i Hi Hb. destruct (Nat.eq_dec i (rc_blanks s)) as [->|Hn]; [|lia].
rewrite kl_blanks_stop in Hb. discriminate Hb.
Qed.

Lemma kl_blank_eq : forall s i, (i <= rc_blanks s)%nat -> rc_blank (nth i s Cursor.NUL) = false ->
i = rc_blanks s.
Proof.
intros s i Hi Hb. destruct (Nat.eq_dec i (rc_blanks s)) as [->|Hn]; [reflexivity|].
rewrite (kl_blanks_true s i ltac:(lia)) in Hb. discriminate Hb.
Qed.

Lemma kl_sign : forall (s : list byte) i, rc_sign (skipn i s) =
(if (bv_unsigned (nth i s Cursor.NUL) =? 43) || (bv_unsigned (nth i s Cursor.NUL) =? 45)
 then (bv_unsigned (nth i s Cursor.NUL) =? 45, 1%nat) else (false, 0%nat)).
Proof.
induction s as [|b s IH]; intros i.
- rewrite skipn_nil. destruct i; reflexivity.
- destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH.
Qed.

Lemma kl_skipn_cons : forall (s : list byte) n, (n < length s)%nat ->
skipn n s = nth n s Cursor.NUL :: skipn (S n) s.
Proof.
induction s as [|b s IH]; intros n Hn; cbn [length] in Hn; [lia|].
destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma kl_digits_stop : forall s n acc big, rc_digit (nth n s Cursor.NUL) = false ->
rc_digits acc big (skipn n s) = (acc, big, 0%nat).
Proof.
intros s n acc big H. destruct (Nat.lt_ge_cases n (length s)) as [Hl|Hl].
- rewrite (kl_skipn_cons s n Hl). cbn [rc_digits]. rewrite H. reflexivity.
- rewrite skipn_all2 by lia. reflexivity.
Qed.

(* no digit after the blanks and the sign: read_channel reads nothing and the key is a bad key *)
Lemma kl_bad_key : forall k v, rc_digit (nth (hk_d (hk_rest k)) (hk_rest k) Cursor.NUL) = false ->
expect_cell k v = inl REFUSE_BAD_KEY.
Proof.
intros k v H.
assert (Hrc : read_channel (hk_rest k) = (0%nat, 0, false)).
{ unfold read_channel. cbv zeta. unfold hk_d in H.
  rewrite (kl_digits_stop _ _ 0 false H). reflexivity. }
unfold expect_cell. change (skipn (length HA_PREFIX) k) with (hk_rest k).
unfold expect_key. rewrite Hrc. reflexivity.
Qed.

(* the digits loop's equation, one digit further *)
Definition kl_acc (acc c : Z) : Z := if 1000000 <? acc then acc else acc * 10 + (c - 48).
Definition kl_big (acc : Z) (big : bool) : bool := if 1000000 <? acc then true else big.

Lemma kl_dg_step : forall (s : list byte) d j acc big,
rc_digit (nth (d + j) s Cursor.NUL) = true ->
rc_digits 0 false (skipn d s) =
  (fst (fst (rc_digits acc big (skipn (d + j) s))), snd (fst (rc_digits acc big (skipn (d + j) s))),
   (j + snd (rc_digits acc big (skipn (d + j) s)))%nat) ->
rc_digits 0 false (skipn d s) =
  (fst (fst (rc_digits (kl_acc acc (bv_unsigned (nth (d + j) s Cursor.NUL))) (kl_big acc big) (skipn (d + S j) s))),
   snd (fst (rc_digits (kl_acc acc (bv_unsigned (nth (d + j) s Cursor.NUL))) (kl_big acc big) (skipn (d + S j) s))),
   (S j + snd (rc_digits (kl_acc acc (bv_unsigned (nth (d + j) s Cursor.NUL))) (kl_big acc big)
     (skipn (d + S j) s)))%nat).
Proof.
intros s d j acc big Hd Heq. rewrite Heq.
pose proof (hk_digit_lt s (d + j) Hd) as Hl.
rewrite (kl_skipn_cons s (d + j) Hl). cbn [rc_digits]. rewrite Hd.
replace (S (d + j)) with (d + S j)%nat by lia.
unfold kl_acc, kl_big. destruct (1000000 <? acc); cbn [fst snd]; f_equal; lia.
Qed.

(* the byte after the digits is not a digit: read_channel's answer *)
Lemma kl_dot : forall (s : list byte) nd acc big, (1 <= nd)%nat ->
rc_digit (nth (hk_d s + nd) s Cursor.NUL) = false ->
rc_digits 0 false (skipn (hk_d s) s) =
  (fst (fst (rc_digits acc big (skipn (hk_d s + nd) s))), snd (fst (rc_digits acc big (skipn (hk_d s + nd) s))),
   (nd + snd (rc_digits acc big (skipn (hk_d s + nd) s)))%nat) ->
read_channel s = ((hk_d s + nd)%nat, (if hk_neg s then - acc else acc), big).
Proof.
intros s nd acc big Hnd Hn Heq.
rewrite (kl_digits_stop s (hk_d s + nd) acc big Hn) in Heq. cbn [fst snd] in Heq.
unfold read_channel. cbv zeta. unfold hk_d, hk_neg in *. rewrite Heq. cbn [fst snd].
destruct nd as [|nd]; [lia|]. rewrite Nat.add_0_r. reflexivity.
Qed.

(* the code's tests on a byte b (0 <= b < 256) *)
Definition kl_blank (b : Z) : bool := ((9 <=? b) && (b <=? 13)) || (b =? 32).

Lemma kl_blank_rc : forall x : byte, kl_blank (bv_unsigned x) = rc_blank x.
Proof.
intros x. unfold kl_blank, rc_blank. set (c := bv_unsigned x).
destruct (Z.eqb_spec c 32) as [E|E]; [rewrite orb_true_r; reflexivity|]. rewrite orb_false_r.
destruct (Z.leb_spec 9 c), (Z.leb_spec c 13); cbn [andb];
  repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end; cbn [orb]; try reflexivity; lia.
Qed.

Lemma kl_digit_rc : forall x : byte, ((bv_unsigned x - 48) mod 2 ^ 64 <? 10) = rc_digit x.
Proof.
intros x. unfold rc_digit. pose proof (Cursor.byte_range x) as Hx. set (c := bv_unsigned x) in *.
destruct (Z.leb_spec 48 c) as [H|H].
- rewrite Z.mod_small by lia. cbn [andb].
  destruct (Z.ltb_spec (c - 48) 10), (Z.leb_spec c 57); try reflexivity; lia.
- cbn [andb]. replace (c - 48) with ((c - 48 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma kl_blank_low : forall b, 0 <= b < 256 -> ((b - 9) mod 2 ^ 64 <? 5) = (9 <=? b) && (b <=? 13).
Proof.
intros b Hb. destruct (Z.leb_spec 9 b) as [H|H].
- rewrite Z.mod_small by lia. cbn [andb].
  destruct (Z.ltb_spec (b - 9) 5), (Z.leb_spec b 13); try reflexivity; lia.
- cbn [andb]. replace (b - 9) with ((b - 9 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.

(* the code's sign arithmetic (0x831fc .. 0x83224) on the byte c after the blanks *)
Definition kl_sgn (b : Z) : Z := if (b =? 43) || (b =? 45) then 1 else 0.
Definition kl_flag (b : Z) : Z := if b =? 45 then 0 else 1.
Lemma kl_d_sgn : forall s : list byte,
Z.of_nat (hk_d s) = Z.of_nat (rc_blanks s) + kl_sgn (bv_unsigned (nth (rc_blanks s) s Cursor.NUL)) /\
(if hk_neg s then 0 else 1) = kl_flag (bv_unsigned (nth (rc_blanks s) s Cursor.NUL)).
Proof.
intros s. unfold hk_d, hk_neg, kl_sgn, kl_flag. rewrite kl_sign.
set (c := bv_unsigned (nth (rc_blanks s) s Cursor.NUL)).
destruct (Z.eqb_spec c 43) as [H43|H43]; destruct (Z.eqb_spec c 45) as [H45|H45]; cbn [orb fst snd];
  try lia; split; try reflexivity; lia.
Qed.
Lemma kl_hk_d_le : forall s : list byte, (hk_d s <= length s)%nat.
Proof.
intros s. unfold hk_d. destruct (rc_sign_split (skipn (rc_blanks s) s)) as [_ L].
rewrite length_skipn in L. pose proof (hk_rc_blanks_le s). lia.
Qed.

Lemma kl_land15 : forall c, 48 <= c <= 57 -> Z.land c 15 = c - 48.
Proof.
intros c Hc.
assert (H : c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/ c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
repeat (destruct H as [->|H]; [reflexivity|]). subst c. reflexivity.
Qed.

(* ================================ the code table and the engine's set-up ================================ *)
Definition KL_SG : Z := 0x831fc.   (* the sign test (fuzz_headamp.c:74) *)
Definition KL_SN : Z := 0x83228.   (* the first digit's read (fuzz_headamp.c:79) *)
(* the 60 words 0x831c0 .. 0x832ac (the slow blocks 0x831f0 and 0x832a4 included); the ends RF 0x83460 and
   DOT 0x832b0 lie outside it *)
Definition kl_tbl : ctable := build_table rsegs HK_BL 60 TEmpty.
Lemma kl_tbl_ok : table_ok rsegs kl_tbl.
Proof. apply build_table_ok0. unfold HK_BL. lia. Qed.

(* the shadow base: register s7 (atom 23) holds SHADOW_OFF *)
Definition KLSB : Z := 0x7fff8000.
Definition KLBx : sv := SOff 23 0.
Definition KLBspan : Z * Z := (KLSB, KLSB + 2 ^ 44 - 1).
(* the bound of a byte address in the pp block (below the allocator's ceiling) *)
Definition KL_PHI : Z := 2 ^ 47 - 0x100.

(* a read-only region of one byte at atom 32, holding atom 33; its shadow entry [P, P + 8) *)
Definition kl_RB : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition kl_SH : list shent := [mkSHE 32 0 8].
Definition kl_ex (P b : Z) : list word := [w64 P; w64 b].

Lemma kl_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma kl_soff : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.
Lemma kl_U_soff : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof. intros E n v c H Hv. rewrite U_SOff, H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma kl_U_addlit : forall E x c, U E (SAlu ALU_ADD x (SLit c)) = (U E x + c) mod 2 ^ 64.
Proof.
intros E x c. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
(* the byte a `lbu` of a one-byte chunk loads *)
Lemma kl_zext8 : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
sv_denot E (SExt false 8 (SOff n 0)) = w64 b.
Proof. intros E n b H Hb. rewrite denot_lit_U, (U_zext8 E n b H Hb). reflexivity. Qed.
(* `addi a2,a2,-45; snez a2,a2` on the sign byte b: the flag of fuzz_headamp.c:75 *)
Lemma kl_snez : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff n (-45))) = w64 (if b =? 45 then 0 else 1).
Proof.
intros E n b H Hb. rewrite denot_lit_U, U_SAlu, U_SLit, (kl_U_soff E n b (-45) H) by lia.
cbn [zalu_raw]. unfold w64. f_equal.
destruct (Z.eqb_spec b 45) as [->|Hn]; [reflexivity|].
assert (Hp : 0 < (b + -45) mod 2 ^ 64).
{ destruct (Z.leb_spec 45 b).
  - rewrite Z.mod_small by lia. lia.
  - replace (b + -45) with ((b + -45 + 2 ^ 64) + (-1) * 2 ^ 64) by ring.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
change (zcanon 0) with 0. destruct (Z.ltb_spec 0 ((b + -45) mod 2 ^ 64)); [reflexivity | lia].
Qed.
(* `mul a5,t1,a7; andi a3,a3,15; add t1,a5,a3` with acc <= 1000000 and the digit c: kl_acc acc c *)
Lemma kl_t1_val : forall E acc c, ew E 6 = Z_to_bv 64 acc -> ew E 17 = Z_to_bv 64 10 -> ew E 13 = Z_to_bv 64 c ->
(1000000 <? acc) = false -> 0 <= acc <= 10000009 -> 48 <= c <= 57 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 6 0) (SOff 17 0)) (SAlu ALU_AND (SOff 13 0) (SLit 15))) = w64 (kl_acc acc c).
Proof.
intros E acc c E6 E17 E13 Hn Hacc Hc. apply Z.ltb_ge in Hn.
rewrite denot_lit_U, U_SAlu, U_SMd, (U_and_lit E (SOff 13 0) 15), (U_atom E 6 acc E6), (U_atom E 17 10 E17),
  (U_atom E 13 c E13) by lia.
cbn [zalu_raw zmd_raw]. rewrite kl_land15 by lia.
unfold kl_acc. replace (1000000 <? acc) with false by (symmetry; apply Z.ltb_ge; lia).
unfold zcanon, M64. rewrite (Z.mod_small (acc * 10)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac kl_t1 E E6 E17 E13 Hc1 Hacc Hc := exact (kl_t1_val E _ _ E6 E17 E13 Hc1 Hacc Hc).

Ltac kl_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.
Ltac kl_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
(* the memory after a run over read-only regions is the memory at the block's start *)
Ltac kl_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac kl_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok kl_tbl_ok HS HJ SHOK KLBspan; [awr_ok_tac | ] end.
Ltac kl_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok kl_tbl_ok HS HJ SHOK KLBspan pc; [awr_ok_tac | ] end.
Ltac kl_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok kl_tbl_ok HS SHOK KLBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* the state at a block's end pc: the world, the journal and the memory as at its start, the I/O state, every
   register outside clob, and what R says of the arm's registers *)
Definition kl_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (clob : list (bv 5))
(R : bvmap 5 word -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) memc (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md2 k /\ same_io mdc md2 /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\ R regs2.

Lemma kl_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob
(R : bvmap 5 word -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc -> ms_mem ms = memc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc md' k -> same_io mdc md' ->
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs r) -> R (ms_regs ms) ->
kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob R W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob R E' ss' ms md' HS Hrv Hpc Hm HJ Hio Hk HR.
split; [reflexivity|]. exists (ms_regs ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc, Hm; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk | exact HR].
Qed.

Ltac kl_post_intro :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HM : ms_mem ?ms = _,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  rewrite HM in HJ;
  eapply (kl_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' ss' ms _ HS eq_refl eq_refl HM HJ);
  [ kl_io
  | lazymatch goal with |- forall r : bv 5, _ -> ~ In r ?cl -> _ =>
      intros r Hr0 Hn; exact (regs_kept_of_st_ok rsegs E' ss' ms rg ex0 _ cl HS HAE ltac:(vm_compute; reflexivity) r Hr0 Hn) end
  | try rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) ] end.
Ltac kl_regs := lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.

(* ---------------- BL 0x831c0 .. SG 0x831fc: the blank test ---------------- *)
Definition kl_facts1 : facts :=
  mkFacts [ (23%nat, mkAF KLSB KLSB 0); (32%nat, mkAF 0x4000 KL_PHI 0) ] []
          [ (SAlu ALU_ADD (SOff 10 0) (SOff 11 0), SOff 32 0) ].
Definition kl_ss1 : sstate := mkSS HK_BL sr_atoms [kl_RB] None kl_facts1.

Lemma kl_A1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (P i b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 (P - i) -> getr regs (Z_to_bv 5 11) = w64 i ->
getr regs (Z_to_bv 5 15) = w64 5 -> getr regs (Z_to_bv 5 16) = w64 32 ->
getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
0 <= i <= 64 -> 0x4000 <= P - i -> P <= KL_PHI -> 0 <= b < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) P 1 b ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF P 8 ->
(forall a, P <= a < P + 8 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs HK_BL regs memc mdc)
(fun W2 c2 =>
 (kl_blank b = true /\ kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HK_BL [11; 12; 13]%bv
    (fun regs2 => getr regs2 (Z_to_bv 5 11) = w64 (i + 1)) W2 c2) \/
 (kl_blank b = false /\ kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KL_SG [12; 13]%bv
    (fun regs2 => getr regs2 (Z_to_bv 5 12) = w64 b) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P i b HJ H10 H11 H15 H16 H23
  Hi HP0 HP1 Hb Vb HRA Happ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (kl_ex P b) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 (P - i)) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 i) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E15 : ew (Ereg regs ex) 15 = Z_to_bv 64 5) by (rewrite (EA 15%nat (Z_to_bv 5 15) eq_refl); exact H15).
assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 32) by (rewrite (EA 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 P) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 b) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) kl_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 HK_BL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold kl_ss1. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, kl_RB.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by (unfold KL_PHI in *; lia).
    split; [lia|]. split; [unfold KL_PHI in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ P 0 1 (SOff 33 0) b); [rewrite kl_denot0; exact E33 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I|]].
    + cbn [kl_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E23, E32, !unsigned_lit_small by (unfold SHADOW_OFF, KL_PHI in *; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold KLSB, SHADOW_OFF, KL_PHI in *. repeat split; lia.
    + cbn [kl_facts1 f_alias alias_ok]. split; [|exact I]. apply U_inj.
      rewrite U_SAlu, (U_atom _ 10 (P - i) E10), (U_atom _ 11 i E11), (U_atom _ 32 P E32) by (unfold KL_PHI in *; lia).
      cbn [zalu_raw]. rewrite zcanon_id by (unfold M64, KL_PHI in *; lia). f_equal. lia. }
assert (U23 : U (Ereg regs ex) KLBx = SHADOW_OFF) by (apply U_atom; [exact E23 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs KLBx kl_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, kl_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc _ KLBx 32 P 8 P 0 8 HRA U23); [| lia | lia |].
  - apply U_atom; [exact E32 | unfold KL_PHI in *; lia].
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HK_BL) with (Z_to_bv 64 HK_BL).
(* 0x831c0 .. 0x831d8: the check and the byte; stop at 0x831dc bgeu a3,a5 *)
kl_run. kl_mem.
kl_branch Hc1; rewrite branch_geu_U, kl_U_addlit, (U_zext8 E 33 b E33 Hb), (U_atom E 15 5 E15) in Hc1 by lia;
  replace (b + -9) with (b - 9) in Hc1 by ring; rewrite (kl_blank_low b Hb) in Hc1.
- (* not 9 .. 13: 0x831e8 beq a2,a6 *)
  apply negb_true_iff in Hc1.
  kl_run. kl_mem.
  kl_branch Hc2; rewrite branch_eq_U, (U_zext8 E 33 b E33 Hb), (U_atom E 16 32 E16) in Hc2 by lia.
  + (* the space: a1++ and back to BL *)
    kl_run_to HK_BL. kl_mem. apply SRr_ret. left.
    split; [unfold kl_blank; rewrite Hc2, orb_true_r; reflexivity|].
    kl_post_intro. kl_sv. apply (kl_soff E 11 i 1 E11); lia.
  + (* not a blank: to SG *)
    kl_run_to KL_SG. kl_mem. apply SRr_ret. right.
    split; [unfold kl_blank; rewrite Hc1, Hc2; reflexivity|].
    kl_post_intro. kl_sv. exact (kl_zext8 E 33 b E33 Hb).
- (* 9 .. 13: a1++ and back to BL *)
  apply negb_false_iff in Hc1.
  kl_run_to HK_BL. kl_mem. apply SRr_ret. left.
  split; [unfold kl_blank; rewrite Hc1; reflexivity|].
  kl_post_intro. kl_sv. apply (kl_soff E 11 i 1 E11); lia.
Qed.

(* ---------------- SG 0x831fc .. SN 0x83228: the sign ---------------- *)
(* the cell R+0xc0 (atom 9 = s1 = R), holding read_channel's bound *)
Definition kl_RC : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0 0 [YP09.mkChunk 0xc0 (CVal 8 (SLit HQ_RC_BIG))].
Definition kl_ss2 : sstate := mkSS KL_SG sr_atoms [kl_RC] None (mkFacts [] [] []).
Definition kl_A2_R (i b : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 11) = w64 (i + kl_sgn b) /\ getr regs2 (Z_to_bv 5 12) = w64 (kl_flag b) /\
getr regs2 (Z_to_bv 5 5) = w64 HQ_RC_BIG /\ getr regs2 (Z_to_bv 5 17) = w64 10.

Lemma kl_A2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R i b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 11) = w64 i -> getr regs (Z_to_bv 5 12) = w64 b ->
0 <= R -> R + 0xc8 <= 2 ^ 64 -> 0 <= i <= 64 -> 0 <= b < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 HQ_RC_BIG ->
SRr rsegs W (cfg_at rsegs KL_SG regs memc mdc)
(kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KL_SN [5; 11; 12; 13; 17]%bv (kl_A2_R i b)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i b HJ H9 H11 H12 HR0 HR1 Hi Hb VC.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember ([] : list word) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 i) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew (Ereg regs ex) 12 = Z_to_bv 64 b) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (HS : st_ok rsegs (Ereg regs ex) kl_ss2 (restrict (w_H W) (mkst regs (Z_to_bv 64 KL_SG) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold kl_ss2. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, kl_RC.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0xc0 8 (SLit HQ_RC_BIG) HQ_RC_BIG);
      [reflexivity | unfold HQ_RC_BIG; cbn; lia | cbn; lia | exact VC].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [exact I|]. split; exact I. }
assert (SHOK : sh_ok rsegs KLBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 KL_SG) with (Z_to_bv 64 KL_SG).
(* 0x831fc .. 0x83204; stop at 0x83208 beq a2,a3 ('+') *)
kl_run. kl_mem.
kl_branch Hc1; rewrite branch_eq_U, (U_atom E 12 b E12), (U_lit E 43) in Hc1 by lia.
- (* '+': 0x83214 a1++, a2 := (c != '-') *)
  kl_run_to KL_SN. kl_mem. apply SRr_ret.
  kl_post_intro. unfold kl_A2_R. kl_regs.
  split; [kl_sv; unfold kl_sgn; rewrite Hc1; cbn [orb]; apply (kl_soff E 11 i 1 E11); lia|].
  split; [kl_sv; exact (kl_snez E 12 b E12 Hb)|].
  split; kl_sv; reflexivity.
- (* 0x8320c li a3,'-'; stop at 0x83210 bne a2,a3 *)
  kl_run. kl_mem.
  kl_branch Hc2; rewrite branch_ne_U, (U_atom E 12 b E12), (U_lit E 45) in Hc2 by lia.
  + (* no sign: 0x83224 a2 := 1 *)
    apply negb_true_iff in Hc2.
    kl_run_to KL_SN. kl_mem. apply SRr_ret.
    kl_post_intro. unfold kl_A2_R. kl_regs.
    split; [kl_sv; rewrite kl_denot0, E11; unfold kl_sgn; rewrite Hc1, Hc2; cbn [orb]; rewrite Z.add_0_r; reflexivity|].
    split; [kl_sv; unfold kl_flag; rewrite Hc2; reflexivity|].
    split; kl_sv; reflexivity.
  + (* '-': 0x83214 *)
    apply negb_false_iff in Hc2.
    kl_run_to KL_SN. kl_mem. apply SRr_ret.
    kl_post_intro. unfold kl_A2_R. kl_regs.
    split; [kl_sv; unfold kl_sgn; rewrite Hc1, Hc2; cbn [orb]; apply (kl_soff E 11 i 1 E11); lia|].
    split; [kl_sv; exact (kl_snez E 12 b E12 Hb)|].
    split; kl_sv; reflexivity.
Qed.

(* ---------------- SN 0x83228 .. RF 0x83460 / DG 0x83264: the first digit ---------------- *)
Definition kl_dig (b : Z) : bool := (b - 48) mod 2 ^ 64 <? 10.
Definition kl_B_RF (regs2 : bvmap 5 word) : Prop := getr regs2 (Z_to_bv 5 28) = w64 REFUSE_BAD_KEY.
Definition kl_B_DG (K d b : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 10) = w64 0 /\ getr regs2 (Z_to_bv 5 29) = w64 0 /\ getr regs2 (Z_to_bv 5 6) = w64 0 /\
getr regs2 (Z_to_bv 5 18) = w64 (K + d) /\ getr regs2 (Z_to_bv 5 14) = w64 (K + d + 14) /\
getr regs2 (Z_to_bv 5 13) = w64 b /\ getr regs2 (Z_to_bv 5 28) = w64 REFUSE_BAD_KEY.

Lemma kl_B : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (P d K b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 (P - d) -> getr regs (Z_to_bv 5 11) = w64 d -> getr regs (Z_to_bv 5 18) = w64 K ->
getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
0 <= d <= 64 -> 0x4000 <= P - d -> P <= KL_PHI -> 0 <= K -> K + d + 14 < 2 ^ 64 -> 0 <= b < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) P 1 b ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF P 8 ->
(forall a, P <= a < P + 8 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs KL_SN regs memc mdc)
(fun W2 c2 =>
 (kl_dig b = false /\ kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_RF [10; 13; 14; 28]%bv
    kl_B_RF W2 c2) \/
 (kl_dig b = true /\ kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HK_DG
    [6; 10; 13; 14; 18; 28; 29]%bv (kl_B_DG K d b) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P d K b HJ H10 H11 H18 H23
  Hd HP0 HP1 HK0 HK1 Hb Vb HRA Happ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (kl_ex P b) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 (P - d)) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 d) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 K) by (rewrite (EA 18%nat (Z_to_bv 5 18) eq_refl); exact H18).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 P) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 b) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) (mkSS KL_SN sr_atoms [kl_RB] None kl_facts1)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 KL_SN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, kl_RB.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by (unfold KL_PHI in *; lia).
    split; [lia|]. split; [unfold KL_PHI in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ P 0 1 (SOff 33 0) b); [rewrite kl_denot0; exact E33 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I|]].
    + cbn [kl_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E23, E32, !unsigned_lit_small by (unfold SHADOW_OFF, KL_PHI in *; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold KLSB, SHADOW_OFF, KL_PHI in *. repeat split; lia.
    + cbn [kl_facts1 f_alias alias_ok]. split; [|exact I]. apply U_inj.
      rewrite U_SAlu, (U_atom _ 10 (P - d) E10), (U_atom _ 11 d E11), (U_atom _ 32 P E32) by (unfold KL_PHI in *; lia).
      cbn [zalu_raw]. rewrite zcanon_id by (unfold M64, KL_PHI in *; lia). f_equal. lia. }
assert (U23 : U (Ereg regs ex) KLBx = SHADOW_OFF) by (apply U_atom; [exact E23 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs KLBx kl_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, kl_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc _ KLBx 32 P 8 P 0 8 HRA U23); [| lia | lia |].
  - apply U_atom; [exact E32 | unfold KL_PHI in *; lia].
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 KL_SN) with (Z_to_bv 64 KL_SN).
(* 0x83228 .. 0x83248: the check, the byte, a0 := c - 48; stop at 0x8324c bltu a4,a0 *)
kl_run. kl_mem.
kl_branch Hc; rewrite branch_ltu_U, (U_lit E 9), kl_U_addlit, (U_zext8 E 33 b E33 Hb) in Hc by lia.
- (* no digit: to RF *)
  kl_run_to HQ_RF. kl_mem. apply SRr_ret. left.
  split; [unfold kl_dig; apply Z.ltb_ge; apply Z.ltb_lt in Hc; replace (b - 48) with (b + -48) by ring; lia|].
  kl_post_intro. unfold kl_B_RF. kl_regs. kl_sv. reflexivity.
- (* a digit: 0x83250 .. 0x83260, to DG *)
  kl_run_to HK_DG. kl_mem. apply SRr_ret. right.
  split; [unfold kl_dig; apply Z.ltb_lt; apply Z.ltb_ge in Hc; replace (b - 48) with (b + -48) by ring;
    pose proof (Z.mod_pos_bound (b + -48) (2 ^ 64)); lia|].
  kl_post_intro. unfold kl_B_DG. kl_regs.
  split; [kl_sv; reflexivity|]. split; [kl_sv; reflexivity|]. split; [kl_sv; reflexivity|].
  split; [kl_sv; rewrite denot_lit_U, U_SAlu, (U_atom E 11 d E11), (U_atom E 18 K E18) by lia;
    cbn [zalu_raw]; unfold w64; f_equal; rewrite zcanon_id by (unfold M64; lia); lia|].
  split; [kl_sv; rewrite denot_lit_U, U_SAlu, (U_atom_off E 11 d 14 E11), (U_atom E 18 K E18) by lia;
    cbn [zalu_raw]; unfold w64; f_equal; rewrite zcanon_id by (unfold M64; lia); lia|].
  split; [kl_sv; exact (kl_zext8 E 33 b E33 Hb)|]. kl_sv; reflexivity.
Qed.

(* ---------------- DG 0x83264 .. DG / DOT 0x832b0: one digit ---------------- *)
Definition kl_facts3 : facts :=
  mkFacts [ (23%nat, mkAF KLSB KLSB 0); (32%nat, mkAF 0x4000 KL_PHI 0) ] []
          [ (SAlu ALU_ADD (SOff 14 0) (SOff 10 0), SOff 32 0) ].
Definition kl_bigz (acc bz : Z) : Z := if 1000000 <? acc then 1 else bz.
Definition kl_C_R (j acc c bz b : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 10) = w64 (j + 1) /\ getr regs2 (Z_to_bv 5 6) = w64 (kl_acc acc c) /\
getr regs2 (Z_to_bv 5 29) = w64 (kl_bigz acc bz) /\ getr regs2 (Z_to_bv 5 13) = w64 b.

Lemma kl_C : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (P j acc c bz b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 5) = w64 HQ_RC_BIG -> getr regs (Z_to_bv 5 6) = w64 acc ->
getr regs (Z_to_bv 5 29) = w64 bz -> getr regs (Z_to_bv 5 13) = w64 c ->
getr regs (Z_to_bv 5 14) = w64 (P - j) -> getr regs (Z_to_bv 5 10) = w64 j ->
getr regs (Z_to_bv 5 17) = w64 10 -> getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
0 <= j <= 64 -> 0x4000 <= P - j -> P <= KL_PHI -> 0 <= acc <= 10000009 -> 0 <= bz <= 1 -> 48 <= c <= 57 ->
0 <= b < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) P 1 b ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF P 8 ->
(forall a, P <= a < P + 8 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs HK_DG regs memc mdc)
(fun W2 c2 =>
 (kl_dig b = true /\ kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HK_DG [6; 10; 13; 15; 29]%bv
    (kl_C_R j acc c bz b) W2 c2) \/
 (kl_dig b = false /\ kl_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HK_DOT [6; 10; 13; 15; 29]%bv
    (kl_C_R j acc c bz b) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P j acc c bz b HJ H5 H6 H29 H13 H14 H10 H17 H23
  Hj HP0 HP1 Hacc Hbz Hc Hb Vb HRA Happ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (kl_ex P b) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E5 : ew (Ereg regs ex) 5 = Z_to_bv 64 HQ_RC_BIG) by (rewrite (EA 5%nat (Z_to_bv 5 5) eq_refl); exact H5).
assert (E6 : ew (Ereg regs ex) 6 = Z_to_bv 64 acc) by (rewrite (EA 6%nat (Z_to_bv 5 6) eq_refl); exact H6).
assert (E29 : ew (Ereg regs ex) 29 = Z_to_bv 64 bz) by (rewrite (EA 29%nat (Z_to_bv 5 29) eq_refl); exact H29).
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 c) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E14 : ew (Ereg regs ex) 14 = Z_to_bv 64 (P - j)) by (rewrite (EA 14%nat (Z_to_bv 5 14) eq_refl); exact H14).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 j) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E17 : ew (Ereg regs ex) 17 = Z_to_bv 64 10) by (rewrite (EA 17%nat (Z_to_bv 5 17) eq_refl); exact H17).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 P) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 b) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) (mkSS HK_DG sr_atoms [kl_RB] None kl_facts3)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HK_DG) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, kl_RB.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by (unfold KL_PHI in *; lia).
    split; [lia|]. split; [unfold KL_PHI in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ P 0 1 (SOff 33 0) b); [rewrite kl_denot0; exact E33 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I|]].
    + cbn [kl_facts3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E23, E32, !unsigned_lit_small by (unfold SHADOW_OFF, KL_PHI in *; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold KLSB, SHADOW_OFF, KL_PHI in *. repeat split; lia.
    + cbn [kl_facts3 f_alias alias_ok]. split; [|exact I]. apply U_inj.
      rewrite U_SAlu, (U_atom _ 14 (P - j) E14), (U_atom _ 10 j E10), (U_atom _ 32 P E32) by (unfold KL_PHI in *; lia).
      cbn [zalu_raw]. rewrite zcanon_id by (unfold M64, KL_PHI in *; lia). f_equal. lia. }
assert (U23 : U (Ereg regs ex) KLBx = SHADOW_OFF) by (apply U_atom; [exact E23 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs KLBx kl_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, kl_SH. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc _ KLBx 32 P 8 P 0 8 HRA U23); [| lia | lia |].
  - apply U_atom; [exact E32 | unfold KL_PHI in *; lia].
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HK_DG) with (Z_to_bv 64 HK_DG).
(* stop at once at 0x83264 bge t0,t1 *)
kl_branch Hc1; rewrite !kl_denot0, E5, E6, YO0c.branch_ge, !unsigned_lit_small, !YO0b.s64_small in Hc1
  by (unfold HQ_RC_BIG; lia).
- (* acc <= 1000000: 0x8326c .. 0x83298, t1 := acc * 10 + digit; stop at 0x8329c bltu a5,a7 *)
  apply negb_true_iff in Hc1. unfold HQ_RC_BIG in Hc1.
  kl_run. kl_mem.
  kl_branch Hc2; rewrite branch_ltu_U, kl_U_addlit, (U_zext8 E 33 b E33 Hb), (U_atom E 17 10 E17) in Hc2 by lia;
    replace (b + -48) with (b - 48) in Hc2 by ring.
  + kl_run_to HK_DG. kl_mem. apply SRr_ret. left. split; [exact Hc2|].
    kl_post_intro. unfold kl_C_R. kl_regs.
    split; [kl_sv; apply (kl_soff E 10 j 1 E10); lia|].
    split; [kl_sv; kl_t1 E E6 E17 E13 Hc1 Hacc Hc|].
    split; [kl_sv; rewrite kl_denot0, E29; unfold kl_bigz; rewrite Hc1; reflexivity|].
    kl_sv; exact (kl_zext8 E 33 b E33 Hb).
  + kl_run_to HK_DOT. kl_mem. apply SRr_ret. right. split; [exact Hc2|].
    kl_post_intro. unfold kl_C_R. kl_regs.
    split; [kl_sv; apply (kl_soff E 10 j 1 E10); lia|].
    split; [kl_sv; kl_t1 E E6 E17 E13 Hc1 Hacc Hc|].
    split; [kl_sv; rewrite kl_denot0, E29; unfold kl_bigz; rewrite Hc1; reflexivity|].
    kl_sv; exact (kl_zext8 E 33 b E33 Hb).
- (* 1000000 < acc: t4 := 1, acc kept *)
  apply negb_false_iff in Hc1. unfold HQ_RC_BIG in Hc1.
  kl_run. kl_mem.
  kl_branch Hc2; rewrite branch_ltu_U, kl_U_addlit, (U_zext8 E 33 b E33 Hb), (U_atom E 17 10 E17) in Hc2 by lia;
    replace (b + -48) with (b - 48) in Hc2 by ring.
  + kl_run_to HK_DG. kl_mem. apply SRr_ret. left. split; [exact Hc2|].
    kl_post_intro. unfold kl_C_R. kl_regs.
    split; [kl_sv; apply (kl_soff E 10 j 1 E10); lia|].
    split; [kl_sv; rewrite kl_denot0, E6; unfold kl_acc; rewrite Hc1; reflexivity|].
    split; [kl_sv; unfold kl_bigz; rewrite Hc1; reflexivity|].
    kl_sv; exact (kl_zext8 E 33 b E33 Hb).
  + kl_run_to HK_DOT. kl_mem. apply SRr_ret. right. split; [exact Hc2|].
    kl_post_intro. unfold kl_C_R. kl_regs.
    split; [kl_sv; apply (kl_soff E 10 j 1 E10); lia|].
    split; [kl_sv; rewrite kl_denot0, E6; unfold kl_acc; rewrite Hc1; reflexivity|].
    split; [kl_sv; unfold kl_bigz; rewrite Hc1; reflexivity|].
    kl_sv; exact (kl_zext8 E 33 b E33 Hb).
Qed.

End d.
End b.

(* ================================ the cut lists ================================ *)
Section lists. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma kl_at_reg : forall (cx : hs_scx rsegs) W2 mem2 regs2 L r v, hs_at_cx rsegs cx W2 mem2 regs2 L ->
In (LReg r, v) L -> getr regs2 (Z_to_bv 5 r) = w64 v.
Proof. intros cx W2 mem2 regs2 L r v HL Hin. unfold hs_at_cx, hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
Lemma kl_at_cell : forall (cx : hs_scx rsegs) W2 mem2 regs2 L b o v, hs_at_cx rsegs cx W2 mem2 regs2 L ->
In (LCell b o, v) L -> val_mem rsegs (mrestrict (w_H W2) mem2) (hd_xv (x_e rsegs cx) b + o) 8 (v mod 2 ^ 64).
Proof. intros cx W2 mem2 regs2 L b o v HL Hin. unfold hs_at_cx, hs_at in HL. rewrite Forall_forall in HL. exact (HL _ Hin). Qed.
Lemma kl_at_sub : forall (cx : hs_scx rsegs) W2 mem2 regs2 L L', hs_at_cx rsegs cx W2 mem2 regs2 L ->
(forall x, In x L' -> In x L) -> hs_at_cx rsegs cx W2 mem2 regs2 L'.
Proof.
intros cx W2 mem2 regs2 L L' HL Hs. unfold hs_at_cx, hs_at in *. rewrite Forall_forall in *.
intros x Hx. exact (HL x (Hs x Hx)).
Qed.
End lists.
Ltac kl_in := cbn [In app]; repeat (first [left; reflexivity | right]).

(* a register outside a block's clobber list keeps its value *)
Lemma kl_keep : forall (regs2 regs3 : bvmap 5 word) (clob : list (bv 5)) (qs : list Z),
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
(* the registers hk_inv_regs asks to be kept *)
Definition kl_qs : list Z := 2 :: 3 :: 4 :: hk_keep.
Lemma kl_qs_in : forall q : Z, q = 2 \/ q = 3 \/ q = 4 \/ In q hk_keep -> In q kl_qs.
Proof. intros q [->|[->|[->|Hq]]]; unfold kl_qs; cbn [In]; tauto. Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.

(* the only look into hq_start_M03: its first conjunct (the segment's start), for R's place *)
Lemma kl_start_R : forall cx r ev, hq_start_M03 rsegs B cx r ev ->
0 <= e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) + 0xc8 <= 2 ^ 64.
Proof.
intros cx r ev HS. destruct HS as (HP & _). unfold hs_pre in HP.
destruct HP as (HJ & _ & _ & _ & _ & HeS & _ & Hrsz & Hwin & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (_ & HSTK & Hceil & Hslo & Hshi & H47 & _).
cbn [hi_rsz headamp_himg_A] in Hrsz.
assert (Has : T_SEG_STK = 16384) by reflexivity.
pose proof (@alloc_ceiling_value rc) as [[Hc1 _] _].
split; lia.
Qed.

(* the lemmas of HPgKcLib, with or without the Section hypothesis errno_low *)
Ltac kl_lib L H := first [pose proof (L errno_low) as H | pose proof L as H].

(* a register kept by the block whose post gives Hk: its value from Rq *)
Ltac kl_kept Hk Rq :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?q) = _ =>
    rewrite (kl_keep _ _ _ [q] Hk ltac:(vm_compute; reflexivity) q (or_introl eq_refl)); exact Rq end.
(* hk_inv_regs's register premise across a chain of blocks *)
Ltac kl_keepq :=
  let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq; apply kl_qs_in in Hq;
  repeat match goal with Hk : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r _ -> getr ?ra r = getr ?rb r |- getr ?ra _ = _ =>
    rewrite (kl_keep _ _ _ kl_qs Hk ltac:(vm_compute; reflexivity) q Hq) end;
  reflexivity.

Theorem hk_P2 : hk_P2_stmt rsegs B MT.
Proof.
intros cx POST r ev at0 m i HS HBL1 HRF HDG.
intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf HC.
pose proof HC as (HI & Hat & Hi).
pose proof HI as (Hb3 & HL & Hfs9 & Hfs18 & Hlive & Hat0 & Hk & Hp & Hx & Hcs).
pose proof Hb3 as (Hcore & _). pose proof Hcore as (HJ & _).
pose proof Hp as (Hv & Hpre & Hm & Hfold).
pose proof (kl_prefix_len k Hpre) as Hk13.
pose proof (hk_start_wf rsegs B cx r ev HS) as Hw.
destruct (Model.ents_wf r Hw) as [Hn32 _].
kl_lib (@hk_keymem fx rc SK B MT) KM.
destruct (KM cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb3 ltac:(lia) Hk)
  as (Hk44 & Hnul & Vk & _ & _ & _ & Hpp4k & Hppc & _ & HRA & Happ). clear KM.
kl_lib (@hk_inv_regs fx rc SK B MT) KI.
pose proof (@alloc_ceiling_value rc) as [[_ Hceil] _].
pose proof (kl_start_R cx r ev HS) as [HR0 HR1].
set (K := hk_kaddr rsegs cx m) in *.
assert (HK : K = e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) by reflexivity.
assert (HPPS : Layout.PP_SIZE = 19744) by reflexivity. rewrite HPPS in Hppc.
pose proof (hk_rest_len k) as Hrl. pose proof (hk_rc_blanks_le (hk_rest k)) as Hbl.
assert (Hrl' : length (hk_rest k) = (length k - 13)%nat)
  by (unfold hk_rest; rewrite kl_prefix_len13, length_skipn; reflexivity).
(* the registers at BL *)
pose proof (kl_at_reg _ _ _ _ _ 18 K Hat ltac:(kl_in)) as R18.
pose proof (kl_at_reg _ _ _ _ _ 10 (K + 13) Hat ltac:(kl_in)) as R10.
pose proof (kl_at_reg _ _ _ _ _ 11 (Z.of_nat i) Hat ltac:(kl_in)) as R11.
pose proof (kl_at_reg _ _ _ _ _ 15 5 Hat ltac:(kl_in)) as R15.
pose proof (kl_at_reg _ _ _ _ _ 16 32 Hat ltac:(kl_in)) as R16.
pose proof (kl_at_reg _ _ _ _ _ 9 (e_R (x_e rsegs cx)) HL ltac:(unfold hk_L, hq_L_seg, hq_L_frame; kl_in)) as R9.
pose proof (kl_at_reg _ _ _ _ _ 23 SHADOW_OFF HL ltac:(unfold hk_L, hq_L_seg, hq_L_frame; kl_in)) as R23.
pose proof (kl_at_cell _ _ _ _ _ XR 0xc0 HQ_RC_BIG HL ltac:(unfold hk_L, hq_L_seg, hq_L_frame, hq_L_loopc; kl_in))
  as VC.
cbn [hd_xv] in VC. rewrite (Z.mod_small HQ_RC_BIG) in VC by (unfold HQ_RC_BIG; lia).
(* the byte rest[i] *)
remember (bv_unsigned (nth i (hk_rest k) Cursor.NUL)) as b eqn:Eb.
assert (Hb : 0 <= b < 256) by (rewrite Eb; apply Cursor.byte_range).
assert (Vb : val_mem rsegs (mrestrict (w_H W2) mem2) (K + 13 + Z.of_nat i) 1 b).
{ pose proof (Vk (13 + i)%nat ltac:(lia)) as V. rewrite (kl_nth_rest k i Hk13 ltac:(lia)) in V.
  replace (K + 13 + Z.of_nat i) with (K + Z.of_nat (13 + i)) by lia. rewrite Eb. exact V. }
eapply SRr_bind.
{ apply (kl_A1 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (K + 13 + Z.of_nat i) (Z.of_nat i) b HJ).
  all: first [ exact Vb | (apply (ra_sub _ _ _ _ _ _ HRA); lia) | (intros a Ha; apply Happ; lia)
             | (rewrite ?R10, ?R11, ?R15, ?R16, ?R23; unfold w64; f_equal; lia) | (unfold KL_PHI; lia) | lia ]. }
intros W3 c3 _ [(Hbl1 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)
  | (Hbl1 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)].
- (* a blank: BL at i + 1 *)
  rewrite Eb, kl_blank_rc in Hbl1.
  pose proof (kl_blank_lt (hk_rest k) i Hi Hbl1) as Hi1.
  apply (HBL1 fx2 ly2 S2 W2 regs3 mem2 md3 k cs keys rf).
  split; [|split; [|exact Hi1]].
  + exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3 ltac:(kl_keepq)).
  + unfold hs_at_cx, hs_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    * kl_kept Hk3 R18.
    * kl_kept Hk3 R10.
    * rewrite HR3. unfold w64. f_equal. lia.
    * kl_kept Hk3 R15.
    * kl_kept Hk3 R16.
- (* not a blank: i is the blanks' end; the sign *)
  rewrite Eb, kl_blank_rc in Hbl1.
  pose proof (kl_blank_eq (hk_rest k) i Hi Hbl1) as Hie.
  destruct (kl_d_sgn (hk_rest k)) as [Hd Hflag]. rewrite <- Hie, <- Eb in Hd, Hflag.
  pose proof (kl_hk_d_le (hk_rest k)) as Hdl.
  eapply SRr_bind.
  { apply (kl_A2 (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e rsegs cx)) (Z.of_nat i) b HJ3);
      [kl_kept Hk3 R9 | kl_kept Hk3 R11 | exact HR3 | lia | lia | lia | lia | exact VC]. }
  intros W4 c4 _ (-> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & HR4).
  destruct HR4 as (Q11 & Q12 & Q5 & Q17). rewrite <- Hd in Q11. rewrite <- Hflag in Q12.
  set (d := hk_d (hk_rest k)) in *.
  assert (R10' : getr regs3 (Z_to_bv 5 10) = w64 (K + 13)) by kl_kept Hk3 R10.
  assert (R18' : getr regs3 (Z_to_bv 5 18) = w64 K) by kl_kept Hk3 R18.
  assert (R23' : getr regs3 (Z_to_bv 5 23) = w64 SHADOW_OFF) by kl_kept Hk3 R23.
  remember (bv_unsigned (nth d (hk_rest k) Cursor.NUL)) as bd eqn:Ebd.
  assert (Hbd : 0 <= bd < 256) by (rewrite Ebd; apply Cursor.byte_range).
  assert (Vbd : val_mem rsegs (mrestrict (w_H W2) mem2) (K + 13 + Z.of_nat d) 1 bd).
  { pose proof (Vk (13 + d)%nat ltac:(lia)) as V. rewrite (kl_nth_rest k d Hk13 ltac:(lia)) in V.
    replace (K + 13 + Z.of_nat d) with (K + Z.of_nat (13 + d)) by lia. rewrite Ebd. exact V. }
  eapply SRr_bind.
  { apply (kl_B (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs4 (K + 13 + Z.of_nat d) (Z.of_nat d) K bd HJ4).
    all: first [ exact Vbd | (apply (ra_sub _ _ _ _ _ _ HRA); lia) | (intros a Ha; apply Happ; lia)
               | (kl_kept Hk4 R10'; fail) | (rewrite Q11; reflexivity)
               | (rewrite (kl_keep _ _ _ [10] Hk4 ltac:(vm_compute; reflexivity) 10 (or_introl eq_refl)), R10';
                  unfold w64; f_equal; lia)
               | kl_kept Hk4 R18' | kl_kept Hk4 R23' | (unfold KL_PHI; lia) | lia ]. }
  intros W5 c5 _ [(Hnd & -> & regs5 & md5 & -> & HJ5 & Hio5 & Hk5 & HR5)
    | (Hdg & -> & regs5 & md5 & -> & HJ5 & Hio5 & Hk5 & HR5)].
  + (* no digit: RF with BAD_KEY *)
    unfold kl_dig in Hnd. rewrite Ebd, kl_digit_rc in Hnd.
    pose proof (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs5 md5 HS HI HJ5
      (same_io_trans _ _ _ (same_io_trans _ _ _ Hio3 Hio4) Hio5) ltac:(kl_keepq)) as HI5.
    pose proof HI5 as (Hb35 & HL5 & _ & _ & _ & _ & _ & _ & Hx5 & _).
    apply (HRF fx2 ly2 S2 W2 regs5 mem2 md5 k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) REFUSE_BAD_KEY cs keys rf).
    split; [exact Hb35|].
    split.
    { apply (kl_at_sub _ _ _ _ (hk_L rsegs cx r m ++ [(LReg 28, REFUSE_BAD_KEY)])).
      - unfold hs_at_cx, hs_at in *. apply Forall_app. split; [exact HL5|].
        repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd]. exact HR5.
      - intros y Hy. unfold hk_L in *. repeat rewrite in_app_iff in Hy. repeat rewrite in_app_iff.
        cbn [In] in Hy |- *. tauto. }
    split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hlive|]. split; [exact Hat0|].
    split; [exact (kl_bad_key k _ Hnd)|]. split; [left; reflexivity|].
    split; [exact Hp | exact Hx5].
  + (* a digit: DG at j = 0 *)
    unfold kl_dig in Hdg. rewrite Ebd, kl_digit_rc in Hdg.
    destruct HR5 as (P10 & P29 & P6 & P18 & P14 & P13 & P28).
    apply (HDG fx2 ly2 S2 W2 regs5 mem2 md5 k cs keys rf 0 false).
    split; [exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs5 md5 HS HI HJ5
      (same_io_trans _ _ _ (same_io_trans _ _ _ Hio3 Hio4) Hio5) ltac:(kl_keepq))|].
    split.
    { unfold hs_at_cx, hs_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
      - rewrite P18. reflexivity.
      - rewrite P14. reflexivity.
      - rewrite P10. reflexivity.
      - kl_kept Hk5 Q11.
      - kl_kept Hk5 Q12.
      - rewrite P13, Ebd, Nat.add_0_r. reflexivity.
      - kl_kept Hk5 Q17.
      - kl_kept Hk5 Q5.
      - rewrite P6. reflexivity.
      - rewrite P29. reflexivity.
      - rewrite P28. reflexivity. }
    split; [rewrite Nat.add_0_r; exact Hdg|].
    split; [rewrite Nat.add_0_r; destruct (rc_digits 0 false (skipn (hk_d (hk_rest k)) (hk_rest k))) as [[a0 b0] n0];
      reflexivity|].
    lia.
Qed.

Lemma kl_bigz_b2z : forall acc big, kl_bigz acc (Z.b2z big) = Z.b2z (kl_big acc big).
Proof. intros acc big. unfold kl_bigz, kl_big. destruct (1000000 <? acc); reflexivity. Qed.
Lemma kl_acc_bound : forall acc c, 0 <= acc <= 10000009 -> 48 <= c <= 57 -> 0 <= kl_acc acc c <= 10000009.
Proof. intros acc c Ha Hc. unfold kl_acc. destruct (Z.ltb_spec 1000000 acc); lia. Qed.
Lemma kl_digit_range : forall x : byte, rc_digit x = true -> 48 <= bv_unsigned x <= 57.
Proof.
intros x H. unfold rc_digit in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Theorem hk_P3 : hk_P3_stmt rsegs B MT.
Proof.
intros cx POST r ev at0 m j HS HDG1 HDOT.
intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf acc big HC.
pose proof HC as (HI & Hat & Hdig & Heq & Hacc).
pose proof HI as (Hb3 & HL & _ & _ & _ & _ & Hk & Hp & _).
pose proof Hb3 as (Hcore & _). pose proof Hcore as (HJ & _).
pose proof Hp as (_ & Hpre & Hm & _).
pose proof (kl_prefix_len k Hpre) as Hk13.
pose proof (hk_start_wf rsegs B cx r ev HS) as Hw.
destruct (Model.ents_wf r Hw) as [Hn32 _].
kl_lib (@hk_keymem fx rc SK B MT) KM.
destruct (KM cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb3 ltac:(lia) Hk)
  as (Hk44 & Hnul & Vk & _ & _ & _ & Hpp4k & Hppc & _ & HRA & Happ). clear KM.
kl_lib (@hk_inv_regs fx rc SK B MT) KI.
pose proof (@alloc_ceiling_value rc) as [[_ Hceil] _].
set (K := hk_kaddr rsegs cx m) in *.
assert (HK : K = e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) by reflexivity.
assert (HPPS : Layout.PP_SIZE = 19744) by reflexivity. rewrite HPPS in Hppc.
pose proof (hk_rest_len k) as Hrl.
assert (Hrl' : length (hk_rest k) = (length k - 13)%nat)
  by (unfold hk_rest; rewrite kl_prefix_len13, length_skipn; reflexivity).
pose proof (hk_digit_lt _ _ Hdig) as Hdj.
pose proof (kl_digit_range _ Hdig) as Hc.
(* the registers at DG *)
pose proof (kl_at_reg _ _ _ _ _ 18 _ Hat ltac:(kl_in)) as R18.
pose proof (kl_at_reg _ _ _ _ _ 14 _ Hat ltac:(kl_in)) as R14.
pose proof (kl_at_reg _ _ _ _ _ 10 _ Hat ltac:(kl_in)) as R10.
pose proof (kl_at_reg _ _ _ _ _ 11 _ Hat ltac:(kl_in)) as R11.
pose proof (kl_at_reg _ _ _ _ _ 12 _ Hat ltac:(kl_in)) as R12.
pose proof (kl_at_reg _ _ _ _ _ 13 _ Hat ltac:(kl_in)) as R13.
pose proof (kl_at_reg _ _ _ _ _ 17 _ Hat ltac:(kl_in)) as R17.
pose proof (kl_at_reg _ _ _ _ _ 5 _ Hat ltac:(kl_in)) as R5.
pose proof (kl_at_reg _ _ _ _ _ 6 _ Hat ltac:(kl_in)) as R6.
pose proof (kl_at_reg _ _ _ _ _ 29 _ Hat ltac:(kl_in)) as R29.
pose proof (kl_at_reg _ _ _ _ _ 28 _ Hat ltac:(kl_in)) as R28.
pose proof (kl_at_reg _ _ _ _ _ 23 SHADOW_OFF HL ltac:(unfold hk_L, hq_L_seg, hq_L_frame; kl_in)) as R23.
(* the next byte, rest[d + j + 1] *)
pose proof (Cursor.byte_range (nth (hk_d (hk_rest k) + S j) (hk_rest k) Cursor.NUL)) as Hbn.
assert (Vbn : val_mem rsegs (mrestrict (w_H W2) mem2) (K + Z.of_nat (hk_d (hk_rest k)) + 14 + Z.of_nat j) 1
  (bv_unsigned (nth (hk_d (hk_rest k) + S j) (hk_rest k) Cursor.NUL))).
{ pose proof (Vk (13 + (hk_d (hk_rest k) + S j))%nat ltac:(lia)) as V.
  rewrite (kl_nth_rest k (hk_d (hk_rest k) + S j) Hk13 ltac:(lia)) in V.
  replace (K + Z.of_nat (hk_d (hk_rest k)) + 14 + Z.of_nat j)
    with (K + Z.of_nat (13 + (hk_d (hk_rest k) + S j))) by lia. exact V. }
eapply SRr_bind.
{ apply (kl_C (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (K + Z.of_nat (hk_d (hk_rest k)) + 14 + Z.of_nat j)
    (Z.of_nat j) acc (bv_unsigned (nth (hk_d (hk_rest k) + j) (hk_rest k) Cursor.NUL)) (Z.b2z big)
    (bv_unsigned (nth (hk_d (hk_rest k) + S j) (hk_rest k) Cursor.NUL)) HJ).
  all: first [ exact Vbn | (apply (ra_sub _ _ _ _ _ _ HRA); lia) | (intros a Ha; apply Happ; lia)
             | exact R5 | exact R6 | exact R29 | exact R13 | exact R10 | exact R17 | exact R23
             | (rewrite R14; unfold w64; f_equal; lia) | (destruct big; cbn; lia) | (unfold KL_PHI; lia) | lia ]. }
intros W3 c3 _ [(Hd3 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)
  | (Hd3 & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR3)];
  destruct HR3 as (Q10 & Q6 & Q29 & Q13); unfold kl_dig in Hd3; rewrite kl_digit_rc in Hd3;
  rewrite kl_bigz_b2z in Q29.
- (* a digit: DG at j + 1 *)
  apply (HDG1 fx2 ly2 S2 W2 regs3 mem2 md3 k cs keys rf
    (kl_acc acc (bv_unsigned (nth (hk_d (hk_rest k) + j) (hk_rest k) Cursor.NUL))) (kl_big acc big)).
  split; [exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3 ltac:(kl_keepq))|].
  split.
  { unfold hs_at_cx, hs_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - kl_kept Hk3 R18.
    - kl_kept Hk3 R14.
    - rewrite Q10. unfold w64. f_equal. lia.
    - kl_kept Hk3 R11.
    - kl_kept Hk3 R12.
    - exact Q13.
    - kl_kept Hk3 R17.
    - kl_kept Hk3 R5.
    - exact Q6.
    - exact Q29.
    - kl_kept Hk3 R28. }
  split; [exact Hd3|].
  split; [exact (kl_dg_step (hk_rest k) (hk_d (hk_rest k)) j acc big Hdig Heq)|].
  apply kl_acc_bound; lia.
- (* not a digit: DOT with nd = j + 1 *)
  apply (HDOT fx2 ly2 S2 W2 regs3 mem2 md3 k cs keys rf (S j)
    (kl_acc acc (bv_unsigned (nth (hk_d (hk_rest k) + j) (hk_rest k) Cursor.NUL))) (kl_big acc big)).
  split; [exact (KI cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3 ltac:(kl_keepq))|].
  split.
  { unfold hs_at_cx, hs_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - kl_kept Hk3 R18.
    - rewrite Q10. unfold w64. f_equal. lia.
    - kl_kept Hk3 R11.
    - kl_kept Hk3 R12.
    - exact Q13.
    - exact Q6.
    - exact Q29.
    - kl_kept Hk3 R28. }
  split; [lia|].
  split; [apply kl_dot; [lia | exact Hd3 | exact (kl_dg_step (hk_rest k) (hk_d (hk_rest k)) j acc big Hdig Heq)]|].
  apply kl_acc_bound; lia.
Qed.

End e.

Print Assumptions hk_P2.
Print Assumptions hk_P3.
