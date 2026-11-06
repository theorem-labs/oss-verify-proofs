(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module paths and module names changed; 500 of its 611 lines of code are new or changed and 1549 lines of the source are left out. *)
(* check_words' ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan), segment I2: item a of call c, from the point
   IK (0x87db8, listing 0x1888), where the template cursor s7 is past the spaces and the item's kind byte is next, to
   ICMP (0x87ee4, listing 0x19b4). The B twin of lib/A/Prog/check_words_sI2a.v (an earlier version).
     0x87db8 .. 0x87dfc  s4 := the kind byte, s3 := ~s7; '#' (35) -> a0 := 1; '*' (42) -> s5 := 0, ICMP; else
                         s5 := line; 'L' (76) -> ICMP; else a0 := (s4 = '?'); then the trap site 0x87df4 (s7 + a0
                         wraps) and atoi(s7 + a0) through the atoi wrapper (0x45230, at 0x87dfc).
     0x87e00 .. 0x87ee0  after atoi (k = the word number): k >= read -> s5 := (s4 = '?') ? 0 : "" (0x212c0), ICMP;
                         k < read -> the instrumented check of w at Wd + 16, w->w, the trap sites of &w->w[k] and the
                         instrumented check of &w->w[k]; '#' -> atoi(w->w[k]) (0x87e9c), snprintf(number, 16, "%d",
                         that) (0x87eb8), s5 := number, ICMP; a word or '?' -> s5 := w->w[k], ICMP.
   Every arm meets at ICMP (B has one strcspn call, at 0x87ef0, in segment I3).
   The walk seats a fresh symbolic state after every call (points 0x87e00 and 0x87ea0), each with only the regions its
   stretch reads. This file holds what the stretches share (the state i2_st, the list, arithmetic and item facts, the
   two atoi steps) and the statements of the two stretches after a call, frozen here so that each is proved in its
   own file: i2_A_spec (0x87e00, check_words_sI2x.v: i2_at_A : i2_H_spec B MT -> i2_A_spec B MT) and i2_H_spec
   (0x87ea0, check_words_sI2h.v: i2_at_H : i2_H_spec B MT). check_words_sI2.v proves the stretch from IK to the first
   atoi and assembles seg_I2. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0t YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d check_words_ki.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* list and arithmetic facts *)
Lemma i2_skipn_nth : forall {A} (l : list A) n x r, skipn n l = x :: r -> nth_error l n = Some x.
Proof.
intros A l. induction l as [|y l IH]; intros [|n] x r H; cbn [skipn] in H; try discriminate H.
- injection H as -> _. reflexivity.
- cbn [nth_error]. exact (IH n x r H).
Qed.
Lemma i2_skipn_S : forall {A} (l : list A) n x r, skipn n l = x :: r -> skipn (S n) l = r.
Proof.
intros A l. induction l as [|y l IH]; intros [|n] x r H; cbn [skipn] in H; try discriminate H.
- injection H as _ ->. reflexivity.
- cbn [skipn]. exact (IH n x r H).
Qed.
Lemma i2_tl_skipn : forall {A} (l : list A) n, tl (skipn n l) = skipn (S n) l.
Proof. intros A l. induction l as [|y l IH]; intros [|n]; cbn [skipn tl]; [reflexivity | reflexivity | reflexivity | apply IH]. Qed.
Lemma i2_nth_hd : forall (l : list byte) j, (j <= length l)%nat ->
  nth j (l ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = hd (Z_to_bv 8 0) (skipn j l).
Proof.
induction l as [|y l IH]; intros [|j] Hj; cbn [length] in Hj; cbn [app nth skipn hd]; try reflexivity; [lia|].
apply IH. lia.
Qed.
Lemma i2_den_off : forall E n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn. cbn [sv_denot]. rewrite Hn. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma i2_reg_off : forall E (regs' : bvmap 5 word) n (r : bv 5) v off,
  ew E n = Z_to_bv 64 v -> getr regs' r = sv_denot E (SOff n off) -> getr regs' r = Z_to_bv 64 (v + off).
Proof. intros E regs' n r v off Hn H. rewrite H. apply i2_den_off. exact Hn. Qed.
Lemma i2_U_add : forall E x y vx vy, U E x = vx -> U E y = vy -> 0 <= vx + vy < 2 ^ 64 ->
  U E (SAlu ALU_ADD x y) = vx + vy.
Proof. intros E x y vx vy Hx Hy R. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.
Lemma i2_den_U : forall E x v, U E x = v -> sv_denot E x = Z_to_bv 64 v.
Proof. intros E x v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma i2_o16 : forall s1 s0, s1 mod 32 = 0 -> s0 mod 16 = 0 -> (s1 - s0) mod 16 = 0.
Proof.
intros s1 s0 H1 H0. pose proof (Z.div_mod s1 32 ltac:(lia)) as D1. pose proof (Z.div_mod s0 16 ltac:(lia)) as D0.
rewrite H1 in D1. rewrite H0 in D0. replace (s1 - s0) with ((2 * (s1 / 32) - s0 / 16) * 16) by lia.
apply Z_mod_mult.
Qed.
Lemma i2_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : x / 8 <= x' / 8) by (apply Z.div_le_mono; lia).
assert (A2 : (x' + n' - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) ltac:(lia)).
pose proof (R8 (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) ltac:(lia)). lia.
Qed.
(* the signed compares of two small non-negative atoms, and of an atom with a literal *)
Lemma i2_lt : forall E n m x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = (x <? y).
Proof.
intros E n m x y Hn Hm Hx Hy. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)).
change (bv_signed (sv_denot E (SOff m 0))) with (Sg E (SOff m 0)).
rewrite !S_SOff, Hn, Hm, !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma i2_eq_lit : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v =? z).
Proof. intros E n v z Hn Hv Hz. rewrite branch_eq_U, (U_atom E n v Hn Hv), U_SLit. rewrite zcanon_id by (unfold M64; lia). reflexivity. Qed.
Lemma i2_ne_lit : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = negb (v =? z).
Proof. intros E n v z Hn Hv Hz. rewrite branch_ne_U, (U_atom E n v Hn Hv), U_SLit. rewrite zcanon_id by (unfold M64; lia). reflexivity. Qed.
(* (b = '?') of `addi a0,s4,-63; seqz a0,a0` (0x87ddc .. 0x87de0), and s7 + it (0x87df8) *)
Lemma i2_U_seq63 : forall E nb b, ew E nb = Z_to_bv 64 b -> 0 <= b <= 255 ->
  U E (SAlu ALU_SLTU (SOff nb (-63)) (SLit 1)) = if b =? 63 then 1 else 0.
Proof.
intros E nb b Hb R0. rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hb, U_SLit, unsigned_lit_small by lia.
change (zcanon 1) with 1.
destruct (Z.eqb_spec b 63) as [->|Hne]; [reflexivity|].
destruct (Z_lt_le_dec b 63) as [Hl|Hl].
- assert (Hin : zcanon (b + -63) = b + -63 + 2 ^ 64).
  { unfold zcanon, M64. rewrite <- (Z.mod_add (b + -63) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
  rewrite Hin. replace (b + -63 + 2 ^ 64 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- rewrite (zcanon_id (b + -63)) by (unfold M64; lia).
  replace (b + -63 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma i2_U_seqz : forall E nc nb p b, U E (SOff nc 0) = p -> ew E nb = Z_to_bv 64 b -> 0 <= b <= 255 -> 0 <= p ->
  p + 1 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff nc 0) (SAlu ALU_SLTU (SOff nb (-63)) (SLit 1))) = p + (if b =? 63 then 1 else 0).
Proof.
intros E nc nb p b Hp Hb R0 R1 R2. apply i2_U_add; [exact Hp | exact (i2_U_seq63 E nb b Hb R0) |].
destruct (b =? 63); lia.
Qed.
(* a UBSan wrap check `bltu ~p, v` (p + v past 2^64 - 1, the trap sites 0x87df4) is not taken when p + v < 2^64 *)
Lemma i2_nowrap : forall E n p a v, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> U E a = v -> p + v < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1)))) (sv_denot E a) = false.
Proof.
intros E n p a v Hn Hp Ha Hv. rewrite branch_ltu_U, (YI08.U_not E n p Hn Hp), Ha. apply Z.ltb_ge. lia.
Qed.
(* s3 = ~s7 (0x87dbc) *)
Lemma i2_den_not : forall E n p, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = w64 (cw_not p).
Proof. intros E n p Hn Hp. unfold w64, cw_not. apply i2_den_U. exact (YI08.U_not E n p Hn Hp). Qed.

(* the items of call_items: the word numbers are 0 .. 3 (one closed check over the 26 functions' items) *)
Definition i2_kok (i : PCW.witem) : bool :=
  match i with PCW.IWord k | PCW.INum k | PCW.IOpt k => (0 <=? k) && (k <=? 3) | _ => true end.
Lemma i2_items_ok : forall fn, forallb i2_kok (PCW.call_items fn) = true.
Proof.
intros fn. destruct (cw_fn26 fn) as (f & Hf & _ & _ & E). rewrite E.
assert (Hc : forallb (fun f => forallb i2_kok (PCW.call_items f)) (map Z.of_nat (seq 0 26)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hc. apply Hc. apply in_map_iff. exists (Z.to_nat f). split; [lia | apply in_seq; lia].
Qed.
Lemma i2_item_k : forall fn a it, nth_error (PCW.call_items fn) a = Some it -> i2_kok it = true.
Proof. intros fn a it H. pose proof (i2_items_ok fn) as Hf. rewrite forallb_forall in Hf. apply Hf. exact (nth_error_In _ _ H). Qed.
(* the item of a kind byte other than '*' and 'L' *)
Definition i2_kitem (b k : Z) : PCW.witem := if b =? 35 then PCW.INum k else if b =? 63 then PCW.IOpt k else PCW.IWord k.
Lemma i2_item_A : forall s, bv_unsigned (hd (Z_to_bv 8 0) s) <> 42 -> bv_unsigned (hd (Z_to_bv 8 0) s) <> 76 ->
  item_of_a s = i2_kitem (bv_unsigned (hd (Z_to_bv 8 0) s))
    (atoi_a (if (bv_unsigned (hd (Z_to_bv 8 0) s) =? 35) || (bv_unsigned (hd (Z_to_bv 8 0) s) =? 63) then tl s else s)).
Proof.
intros s H42 H76. unfold item_of_a, i2_kitem. cbv zeta.
destruct (Z.eqb_spec (bv_unsigned (hd (Z_to_bv 8 0) s)) 35) as [E|E]; [reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) H42), (proj2 (Z.eqb_neq _ _) H76).
destruct (Z.eqb_spec (bv_unsigned (hd (Z_to_bv 8 0) s)) 63); reflexivity.
Qed.
Lemma i2_kitem_k : forall b k, i2_kok (i2_kitem b k) = true -> 0 <= k <= 3.
Proof.
intros b k H. unfold i2_kitem in H. destruct (b =? 35); [|destruct (b =? 63)]; cbn [i2_kok] in H;
  apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia.
Qed.

(* the "%d" text of a 32-bit int: at most 11 bytes, none of them 0 *)
Lemma i2_digits_len : forall f x acc j, 0 <= x < 10 ^ Z.of_nat j -> (1 <= j)%nat ->
  (length (pf_digits f x acc) <= j + length acc)%nat.
Proof.
induction f as [|f IH]; intros x acc j Hx Hj; cbn [pf_digits]; [lia|].
destruct (Z.ltb_spec x 10) as [Hl|Hl]; [cbn [length]; lia|].
destruct j as [|j]; [lia|]. destruct j as [|j].
- exfalso. cbn in Hx. lia.
- pose proof (IH (x / 10) ((48 + x mod 10) :: acc) (S j)) as H.
  assert (Hd : 0 <= x / 10 < 10 ^ Z.of_nat (S j)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    replace (10 * 10 ^ Z.of_nat (S j)) with (10 ^ Z.of_nat (S (S j))) by (rewrite !Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
    lia. }
  specialize (H Hd ltac:(lia)). cbn [length] in H. lia.
Qed.
Lemma i2_pf_dec_len : forall v, -2^31 <= v < 2^31 -> (length (pf_dec v) <= 11)%nat.
Proof.
intros v Hv. unfold pf_dec. assert (E : 10 ^ Z.of_nat 10 = 10000000000) by reflexivity.
destruct (Z.ltb_spec v 0) as [Hn|Hn].
- cbn [length]. pose proof (i2_digits_len 11 (- v) [] 10 ltac:(rewrite E; lia) ltac:(lia)) as HL. cbn [length] in HL. lia.
- pose proof (i2_digits_len 11 v [] 10 ltac:(rewrite E; lia) ltac:(lia)) as HL. cbn [length] in HL. lia.
Qed.
Lemma i2_digits_nz : forall f x acc, 0 <= x -> Forall (fun c => 0 < c < 256) acc ->
  Forall (fun c => 0 < c < 256) (pf_digits f x acc).
Proof.
induction f as [|f IH]; intros x acc Hx Ha; cbn [pf_digits]; [exact Ha|].
destruct (Z.ltb_spec x 10).
- constructor; [lia | exact Ha].
- apply IH; [apply Z.div_pos; lia|]. constructor; [pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia | exact Ha].
Qed.
Lemma i2_pf_dec_nz : forall v, Forall (fun c => 0 < c < 256) (pf_dec v).
Proof.
intros v. unfold pf_dec. destruct (Z.ltb_spec v 0).
- constructor; [lia|]. apply i2_digits_nz; [lia | constructor].
- apply i2_digits_nz; [lia | constructor].
Qed.
Lemma i2_pf_bytes_nonul : forall l, Forall (fun c => 0 < c < 256) l -> ~ In (Z_to_bv 8 0) (pf_bytes l).
Proof.
intros l H Hin. unfold pf_bytes in Hin. apply in_map_iff in Hin as (c & Hc & Hin).
rewrite Forall_forall in H. specialize (H c Hin). apply (f_equal bv_unsigned) in Hc.
rewrite !Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc. change (bv_modulus 8) with 256 in Hc.
rewrite Z.mod_small in Hc by lia. change (0 mod 256) with 0 in Hc. lia.
Qed.
(* the value of the ASan atoi wrapper is an int *)
Lemma i2_atoi_range : forall s, -2^31 <= atoi_a s < 2^31.
Proof.
intros s. unfold atoi_a, bv_swrap, bv_wrap.
assert (Hm : bv_modulus 32 = 2 ^ 32) by reflexivity. assert (Hh : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
rewrite Hm, Hh.
match goal with |- context [(?z + 2 ^ 31) mod 2 ^ 32] => pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)) end.
lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the walk's shadow base: s6 (x22) holds CW_SB from 0x87b44 on, so the inline checks' Bx is that register's atom *)
Definition IBx : sv := SOff 22 0.
Definition IBspan : Z * Z := (CW_SB, CW_SB + 2 ^ 44 - 1).
(* the allocation ceiling of the pointer atoms (heap blocks and the side-stack frame lie below it) *)
Definition PCEIL : Z := 140737479966720.

(* the registers a stretch keeps: sp, gp, tp, s0, s1 = sp1, s2 = a, s3 = ~s7, s6 = the shadow base, s7 = the cursor,
   s8 .. s11 (the item registers of cw_iregs); I2_RL0 without s3, which the run from IK sets at 0x87dbc *)
Definition I2_RL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition I2_RL0 : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition i2_rk0 (regs regs' : bvmap 5 word) : Prop :=
  getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
  getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
  getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Definition i2_rk (regs regs' : bvmap 5 word) : Prop := i2_rk0 regs regs' /\ getr regs' 19 = getr regs 19.
Lemma i2_rk_of_pres : forall regs regs', aregs_preserved regs regs' -> i2_rk regs regs'.
Proof.
intros regs regs' HP. unfold aregs_preserved, acallee_saved in HP.
split; [|exact (HP 19 ltac:(lia))].
split; [exact (HP 2 ltac:(lia))|]. split; [exact (HP 3 ltac:(lia))|]. split; [exact (HP 4 ltac:(lia))|].
split; [exact (HP 8 ltac:(lia))|]. split; [exact (HP 9 ltac:(lia))|]. split; [exact (HP 18 ltac:(lia))|].
split; [exact (HP 22 ltac:(lia))|]. split; [exact (HP 23 ltac:(lia))|]. split; [exact (HP 24 ltac:(lia))|].
split; [exact (HP 25 ltac:(lia))|]. split; [exact (HP 26 ltac:(lia)) | exact (HP 27 ltac:(lia))].
Qed.
Lemma i2_rk_trans : forall r1 r2 r3, i2_rk r1 r2 -> i2_rk r2 r3 -> i2_rk r1 r3.
Proof.
intros r1 r2 r3 ((A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) & A13)
  ((B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12) & B13).
split; [repeat split; congruence | congruence].
Qed.
Lemma i2_rk0_in : forall (P : bv 5 -> Prop), (forall r, In r I2_RL0 -> P r) ->
  P 2%bv /\ P 3%bv /\ P 4%bv /\ P 8%bv /\ P 9%bv /\ P 18%bv /\ P 22%bv /\ P 23%bv /\ P 24%bv /\
  P 25%bv /\ P 26%bv /\ P 27%bv.
Proof. intros P H. unfold I2_RL0 in H. repeat split; apply H; repeat (first [left; reflexivity | right]). Qed.
Lemma i2_rk_in : forall (P : bv 5 -> Prop), (forall r, In r I2_RL -> P r) ->
  (P 2%bv /\ P 3%bv /\ P 4%bv /\ P 8%bv /\ P 9%bv /\ P 18%bv /\ P 22%bv /\ P 23%bv /\ P 24%bv /\
   P 25%bv /\ P 26%bv /\ P 27%bv) /\ P 19%bv.
Proof. intros P H. unfold I2_RL in H. repeat split; apply H; repeat (first [left; reflexivity | right]). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:124-141) this file uses, word for word *)
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis RRO : RRO_P.
(* the record facts of check_words_d.v (check_words_rf.v proves them from lib/B/Prog/CmdRecFacts.v) *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Let errno_low := pal_env B TL.

#[local] Notation CWJ e pos lyc Sc Wc memc mdc :=
  (ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
     lyc Sc Wc memc mdc EV_JOINED).

(* the state at every point of the segment after 0x87dbc: INV_IK's parts and s3 = ~s7 *)
Definition i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args (j1 : nat) : Prop :=
  cw_icommon B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args /\
  (j1 <= length (cw_tpl fn))%nat /\ getr regs 23 = w64 (cw_tptr fn + Z.of_nat j1) /\
  getr regs 19 = w64 (cw_not (cw_tptr fn + Z.of_nat j1)) /\
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn).

(* cw_icommon at a later state of the same call: the registers cw_core and cw_iregs name kept, the memory changed only
   where a runtime entry called at sp1 writes (ki's cw_mem_kept) *)
Lemma i2_icommon_kept : forall e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args,
  cw_ent B MT e -> cw_icommon B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args -> CWJ e pos lyc Sc Wc mem' md' ->
  i2_rk0 regs regs' -> cw_mem_kept B (rdW Wc mem) (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) ->
  cw_icommon B MT e lyc Sc Wc regs' mem' md' pos sp1 line c a fn args.
Proof.
intros e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args HE HI HJ' HR HM.
destruct HI as (HC & HL & HLS & HCS & H168 & HIR & Hc & Hnth & Ha).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & _ & R24 & R25 & R26 & R27).
assert (HCR : cw_cregs_kept regs regs') by (repeat split; assumption).
destruct (cw_base_kept B MT LAWS TL e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c HE HC HL HLS HCS HJ' HCR HM)
  as (HC' & HL' & HLS' & HCS').
pose proof HC as (_ & _ & _ & Hrng & _).
destruct HIR as (I26 & I18 & I25 & I24 & I27).
split; [exact HC'|]. split; [exact HL'|]. split; [exact HLS'|]. split; [exact HCS'|].
split.
{ apply (cw_aval_kept (rdW Wc mem)); [|exact H168].
  intros k Hk. apply (cw_above_kept B LAWS TL e lyc Sc Wc regs mem md mem' pos sp1 EV_JOINED HC HM). lia. }
split; [|split; [exact Hc | split; [exact Hnth | exact Ha]]].
split; [rewrite R26; exact I26|]. split; [rewrite R18; exact I18|]. split; [rewrite R25; exact I25|].
split; [rewrite R24; exact I24 | rewrite R27; exact I27].
Qed.
(* i2_st from INV_IK's parts at the state after the first run, s3 set *)
Lemma i2_st_of_ik : forall e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args j1,
  cw_ent B MT e -> cw_icommon B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args ->
  (j1 <= length (cw_tpl fn))%nat -> getr regs 23 = w64 (cw_tptr fn + Z.of_nat j1) ->
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn) ->
  CWJ e pos lyc Sc Wc mem' md' -> i2_rk0 regs regs' ->
  getr regs' 19 = w64 (cw_not (cw_tptr fn + Z.of_nat j1)) ->
  cw_mem_kept B (rdW Wc mem) (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) ->
  i2_st e lyc Sc Wc regs' mem' md' pos sp1 line c a fn args j1.
Proof.
intros e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args j1 HE HC Hj H23 Heq HJ HR H19 HM.
split; [exact (i2_icommon_kept e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args HE HC HJ HR HM)|].
split; [exact Hj|]. split; [|split; [exact H19 | exact Heq]].
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & R23 & _). rewrite R23. exact H23.
Qed.
Lemma i2_st_kept : forall e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args j1,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 -> CWJ e pos lyc Sc Wc mem' md' ->
  i2_rk regs regs' -> cw_mem_kept B (rdW Wc mem) (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) ->
  i2_st e lyc Sc Wc regs' mem' md' pos sp1 line c a fn args j1.
Proof.
intros e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args j1 HE (HC & Hj & H23 & H19 & Heq) HJ [HR R19] HM.
apply (i2_st_of_ik e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args j1 HE HC Hj H23 Heq HJ HR); [|exact HM].
rewrite R19. exact H19.
Qed.
(* INV_ICMP from the state and s5 *)
Lemma i2_icmp : forall e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 q wq,
  i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  getr regs 21 = w64 q -> cw_wq B e lyc Sc (rdW Wc mem) pos line q wq ->
  want_at atoi_a (cw_read e) (e_ws e) (item_of_a (skipn j1 (cw_tpl fn))) = wq ->
  INV_ICMP B MT e lyc Sc Wc regs mem md pos sp1 line c a j1 q wq.
Proof.
intros e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 q wq (HC & Hj & H23 & H19 & Heq) H21 Hwq Hw.
exists fn, args. exact (conj HC (conj Hj (conj H23 (conj H19 (conj Heq (conj H21 (conj Hwq Hw))))))).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the two stretches after a call (frozen statements) *)
(* 0x87e00 (listing 0x18d0), after the first atoi (of the template from s7 + (b = '#' or '?')), with b the kind byte
   in s4 and k the word number in a0. The '#' arm goes on through i2_H_spec, so ST_ICMP at every FP state *)
Definition i2_A_spec : Prop := forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) ->
  forall e lyc Sc Wc regs mem md pos sp1 line fn args j1 b k,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  b = bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn))) -> b <> 42 -> b <> 76 ->
  item_of_a (skipn j1 (cw_tpl fn)) = i2_kitem b k ->
  getr regs 20 = w64 b -> getr regs 10 = w64 k ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x18d0)) mem (seg_rom SEGS)) md) (cw_post B MT e).
(* 0x87ea0 (listing 0x1970), after atoi(w->w[k]) of a '#' item: snprintf(number, 16, "%d", a0), s5 := number, on to
   ICMP. snprintf returns at some FP state fx1 (pass 4), so the stretch takes ST_ICMP at every FP state *)
Definition i2_H_spec : Prop := forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) ->
  forall e lyc Sc Wc regs mem md pos sp1 line fn args j1 k,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  item_of_a (skipn j1 (cw_tpl fn)) = PCW.INum k -> 0 <= k < cw_read e ->
  getr regs 10 = w64 (atoi_a (nth (Z.to_nat k) (e_ws e) [])) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x1970)) mem (seg_rom SEGS)) md) (cw_post B MT e).

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seeds' tools *)
Lemma i2_val_of_aval : forall H (m : word -> option byte) a n v,
  aval_mem (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate Hv].
cbn in Hv. injection Hv as Hv. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. do 2 f_equal. exact Hv.
Qed.
Lemma i2_kept_ro : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' Hf Hw a Ha. apply (kept_of_frame (segs:=SEGS) E rs H m m' (fun _ => False) Hf); [|exact Ha|tauto].
intros b wlo whi a' Hin Hr. unfold windows in Hin. apply in_map_iff in Hin as (r & Hr' & Hin').
rewrite forallb_forall in Hw. specialize (Hw r Hin'). apply Z.leb_le in Hw. injection Hr' as <- <- <-. lia.
Qed.
Lemma i2_arodata_now : forall e pos lyc Sc Wc memc mdc k, cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros e pos lyc Sc Wc memc mdc k Hent HJ a Hro Ho He.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hg)]).
rewrite (cw_img_kept B e lyc Sc Wc memc mdc pos k a HJ Himg Ho He).
pose proof Hent as (_ & _ & HROD & _). exact (HROD a Hro Ho He).
Qed.
Lemma i2_EE : forall (regsc : bvmap 5 word) extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regsc extra)) n = getr regsc r.
Proof.
intros regsc extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma i2_EX : forall (regsc : bvmap 5 word) extra j, (32 + j < A_TEXT)%nat ->
  ew (Eimg (Ereg regsc extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regsc extra j Hj. rewrite Eimg_low by lia. apply ew_Ereg_extra. Qed.
Lemma i2_HAE : forall (regsc : bvmap 5 word) extra, env_agree 32 (Ereg regsc extra) (Eimg (Ereg regsc extra)).
Proof. intros regsc extra. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* a range of the caller's stack is addressable at every AR state (AR's zero shadow over the stack) *)
Lemma i2_stk_addressable : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> a + n + 8 <= ly_stk_hi ly -> 0 <= n ->
  range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi Hn.
pose proof (am_zshadow _ _ _ _ (proj1 HAR)) as Z. unfold zshadow_ok, zero_shadow_ranges in Z.
pose proof (Forall_inv Z) as Z0. cbn [fst snd] in Z0.
destruct (YG0t.zshadow_range_facts B ly S _ _ (proj1 HAR) (or_introl eq_refl)) as (Hal & _). cbn [fst] in Hal.
intros x Hx. exists 0. split; [|left; reflexivity].
replace x with (ly_stk_lo ly + (x - ly_stk_lo ly)) by lia. rewrite shadow_of_addr_aligned_off by exact Hal.
apply Z0. split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|].
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
pose proof (Z.mul_div_le (x - ly_stk_lo ly) 8 ltac:(lia)). lia.
Qed.
(* "%d" at 0x218e0 at the current state *)
Lemma i2_fmt_at : forall e lyc Sc Wc memc mdc pos k, cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  astr_atR (rdW Wc memc) 0x218e0 (pf_bytes [37; 100]) /\ range_addressable (rdW Wc memc) SHADOW_OFF 0x218e0 3 /\
  shadow_hull_vis (rdW Wc memc) 0x218e0 3 /\ atail_vis SEGS Wc memc 0x218e2.
Proof.
intros e lyc Sc Wc memc mdc pos k HE HJ.
assert (Hzsh : In (0x218e0, 3) CW_ZSH) by (apply cw_in_pair_of_existsb; vm_compute; reflexivity).
pose proof HE as (_ & _ & _ & _ & HRO & _). destruct HRO as [HROB _].
assert (Hb0 : abytes_atR (rdW (e_W e) (e_mem e)) 0x218e0 RO_lit_218e0).
{ clear - HROB. unfold cmd_ro_bytes in HROB.
  repeat lazymatch type of HROB with
  | abytes_atR _ 0x218e0 _ /\ _ => exact (proj1 HROB)
  | _ /\ _ => apply proj2 in HROB
  end. }
destruct (ZSH_cw lyc Sc Wc memc mdc _ _ (proj1 HJ) Hzsh) as [Hra Hhv].
split; [split|].
{ replace (pf_bytes [37; 100] ++ [Z_to_bv 8 0]) with RO_lit_218e0 by (vm_compute; reflexivity).
  apply (cw_abytes_kept (rdW (e_W e) (e_mem e))); [|exact Hb0].
  intros i Hi. change (length RO_lit_218e0) with 3%nat in Hi.
  destruct (cw_ro_unowned 0x218e0 3 (Z.of_nat i) Hzsh ltac:(unfold A_G_REC; lia) ltac:(lia)) as (H1 & H2 & H3).
  exact (cw_img_kept B e lyc Sc Wc memc mdc pos k _ HJ H1 H2 H3). }
{ apply cw_notin0. vm_compute. reflexivity. }
split; [exact Hra|]. split; [exact Hhv|].
apply (cmd_tail_vis lyc Sc Wc memc mdc _ (proj1 HJ)). apply cw_in_of_existsb. vm_compute. reflexivity.
Qed.

Ltac i2_preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.
(* the registers a stretch does not change, from its final symbolic state (a closed register list) *)
Lemma i2_rk_pi : forall E ss ms regsc extra, st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsc extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) I2_RL = true ->
  i2_rk regsc (ms_regs ms).
Proof.
intros E ss ms regsc extra HS HA Hl.
destruct (i2_rk_in _ (regs_kept_of_st_ok_pi E ss ms regsc extra I2_RL HS HA Hl))
  as ((R2 & R3 & R4 & R8 & R9 & R18 & R22 & R23 & R24 & R25 & R26 & R27) & R19).
split; [repeat split; assumption | exact R19].
Qed.
Lemma i2_rk_st : forall E ss ms regsc extra, st_ok SEGS E ss ms -> env_agree 32 (Ereg regsc extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) I2_RL = true ->
  i2_rk regsc (ms_regs ms).
Proof.
intros E ss ms regsc extra HS HA Hl.
destruct (i2_rk_in _ (regs_kept_of_st_ok SEGS E ss ms regsc extra I2_RL HS HA Hl))
  as ((R2 & R3 & R4 & R8 & R9 & R18 & R22 & R23 & R24 & R25 & R26 & R27) & R19).
split; [repeat split; assumption | exact R19].
Qed.
Lemma i2_rk0_pi : forall E ss ms regsc extra, st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsc extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) I2_RL0 = true ->
  i2_rk0 regsc (ms_regs ms).
Proof.
intros E ss ms regsc extra HS HA Hl.
destruct (i2_rk0_in _ (regs_kept_of_st_ok_pi E ss ms regsc extra I2_RL0 HS HA Hl))
  as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R23 & R24 & R25 & R26 & R27).
repeat split; assumption.
Qed.
Lemma i2_rk0_st : forall E ss ms regsc extra, st_ok SEGS E ss ms -> env_agree 32 (Ereg regsc extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) I2_RL0 = true ->
  i2_rk0 regsc (ms_regs ms).
Proof.
intros E ss ms regsc extra HS HA Hl.
destruct (i2_rk0_in _ (regs_kept_of_st_ok SEGS E ss ms regsc extra I2_RL0 HS HA Hl))
  as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R23 & R24 & R25 & R26 & R27).
repeat split; assumption.
Qed.

(* the string s5 names, at a state whose memory is the same *)
Lemma i2_wsrc_eq : forall e lyc Sc (rd rd' : reader) pos line q y,
  (forall x, 0 <= x < 2 ^ 64 -> rd' x = rd x) -> 0 <= q -> q + Z.of_nat (length y) + 1 <= 2 ^ 64 ->
  cw_wsrc B e lyc Sc rd pos line q y -> cw_wsrc B e lyc Sc rd' pos line q y.
Proof.
intros e lyc Sc rd rd' pos line q y K Hq Hy ([Hb Hnz] & Hpos & Hor).
split; [|split; [exact Hpos | exact Hor]]. split; [|exact Hnz].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite K by lia.
apply Hb. rewrite length_app. cbn [length]. lia.
Qed.
(* item a of the template's parse *)
Lemma i2_parse_nth : forall fn a j1 cs,
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn cs (skipn j1 (cw_tpl fn))) = skipn (Z.to_nat a) (PCW.call_items fn) ->
  nth_error (PCW.call_items fn) (Z.to_nat a) = Some (item_of_a (skipn j1 (cw_tpl fn))).
Proof. intros fn a j1 cs Heq. exact (i2_skipn_nth _ _ _ _ (eq_sym Heq)). Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the two atoi steps: atoi(s7 + d) on the template from its byte j (0x87dfc), atoi(w->w[k]) on word k (0x87e9c) *)
Lemma i2_call_atoi : forall e lyc Sc Wc regsT memT mdT pos sp1 fn j retk Q,
  cw_ent B MT e -> CWJ e pos lyc Sc Wc memT mdT ->
  spZ regsT = sp1 -> cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 -> sp1 mod 32 = 0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + retk) ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 10 = w64 (cw_tptr fn + Z.of_nat j) -> (j <= length (cw_tpl fn))%nat ->
  (forall regs2 mem2 md2, CWJ e pos lyc Sc Wc mem2 md2 ->
    aregs_preserved regsT regs2 -> getr regs2 10 = w64 (atoi_a (skipn j (cw_tpl fn))) ->
    cw_mem_kept B (rdW Wc memT) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
    SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_atoi)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e lyc Sc Wc regsT memT mdT pos sp1 fn j retk Q HE HJ Hsp Hrng Hsp32 Hgp Htp Hra Hrk Hrk2 Ha0 Hj HK.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc memT mdT pos EV_JOINED fn HE HJ)
  as ([TB TN] & TRA & THV & TTL & Tlo & Thi & T8).
pose proof (i2_arodata_now e pos lyc Sc Wc memT mdT EV_JOINED HE HJ) as HROD.
destruct (cmd_rec_cells lyc Sc Wc memT mdT (proj1 HJ)) as (Hflag & Hguard & ev & Herr).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (3 * ESTACK) (aerrno_cell B)
    (SIG CS___interceptor_trampoline_atoi) Wc regsT memT CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e)
    (e_mem e) (e_md e) [(0, pos)] lyc Sc mdT EV_JOINED (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + retk)) _ HJ
    ltac:(rewrite Hsp; lia) ltac:(apply i2_o16; [exact Hsp32 | exact Hal16]) ltac:(lia) ltac:(lia)
    ltac:(rewrite Hes, WS; lia) Hra (fun a H => H)).
  apply (AATOI fx lyc Sc Wc regsT memT mdT (cw_tptr fn + Z.of_nat j) (skipn j (cw_tpl fn)) ev).
  - exact Hflag.
  - exact Hguard.
  - apply (ecall_pre_stk_at SEGS B (3 * ESTACK) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
      (e_md e) [(0, pos)] lyc Sc Wc memT mdT EV_JOINED regsT (sp1 - cw_sp0 e) HJ);
      [rewrite Hsp; lia | apply i2_o16; [exact Hsp32 | exact Hal16] | lia | rewrite Hes; lia | rewrite Hes, WS; lia
      | rewrite Hra; apply ret_ok_codeptr_v; [lia | exact Hrk2] | exact Hgp | exact Htp].
  - exact Ha0.
  - lia.
  - apply (astr_atR_view SEGS). exact (astr_atR_skipn _ _ _ j (conj TB TN) Hj).
  - unfold aread_ok, astr_len. rewrite length_skipn.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros x Hx. split.
      - replace x with (cw_tptr fn + Z.of_nat (Z.to_nat (x - cw_tptr fn))) by lia.
        rewrite (TB (Z.to_nat (x - cw_tptr fn))) by (rewrite length_app; cbn [length]; lia). discriminate.
      - unfold ascratch_stk. rewrite Hsp. lia. }
    split; [unfold amem_range; left; rewrite C5; lia|].
    split; [apply (range_addressable_sub _ _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact TRA | lia | lia]|].
    intros _. apply (i2_hull_sub _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact THV | lia | lia | lia].
  - (* the `+ 8` band premise: the template is a .rodata literal, far below the low band's end *)
    unfold astr_len. rewrite length_skipn. unfold amem_range; left; rewrite C5; lia.
  - unfold astr_len. rewrite length_skipn.
    replace (cw_tptr fn + Z.of_nat j + Z.of_nat (length (cw_tpl fn) - j))
      with (cw_tptr fn + Z.of_nat (length (cw_tpl fn))) by lia.
    exact TTL.
  - exact Herr.
  - (* contract 2: the string does not hold the errno cell: no byte of an item string is the errno cell
       (cw_ro_unowned_P at the template's CW_ZSH range) *)
    pose proof (cw_tpl_facts fn) as (_ & Tin & _ & _ & _ & _ & Tne & _).
    unfold astr_len. rewrite length_skipn.
    destruct (Z_le_gt_dec (cw_tptr fn + Z.of_nat j + Z.of_nat (length (cw_tpl fn) - j) + 1) (as_errno B)) as [Hl|Hl];
      [left; exact Hl|]. right.
    destruct (Z_le_gt_dec (as_errno B + 4) (cw_tptr fn + Z.of_nat j)) as [Hr|Hr]; [exact Hr|]. exfalso.
    destruct (cw_ro_unowned _ _ (Z.max (cw_tptr fn + Z.of_nat j) (as_errno B) - cw_tptr fn) Tin Tne ltac:(lia))
      as (_ & _ & Hne).
    apply Hne. lia.
  - apply cmd_rom_view_on. exact HROD. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQa & _) & Hfr2).
apply (HK regs2 mem2 md2 HJ2 HP2).
- rewrite HQa. reflexivity.
- intros x Hx Hw He _. apply (Hfr2 x Hx); [lia | exact He].
Qed.

(* atoi(w->w[n]) on word n of the message, a string inside a heap block live since the entry *)
Lemma i2_call_atoi_w : forall e lyc Sc Wc regsT memT mdT pos sp1 n retk Q,
  cw_ent B MT e -> CWJ e pos lyc Sc Wc memT mdT ->
  (forall bk, In bk (ablocks B (e_ly e) (e_S e)) -> In bk (ablocks B lyc Sc)) -> (n < length (e_ws e))%nat ->
  spZ regsT = sp1 -> cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 -> sp1 mod 32 = 0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + retk) ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 10 = w64 (nth n (e_wp e) 0) ->
  (forall regs2 mem2 md2, CWJ e pos lyc Sc Wc mem2 md2 ->
    aregs_preserved regsT regs2 -> getr regs2 10 = w64 (atoi_a (nth n (e_ws e) [])) ->
    cw_mem_kept B (rdW Wc memT) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
    SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_atoi)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e lyc Sc Wc regsT memT mdT pos sp1 n retk Q HE HJ Hsub Hn Hsp Hrng Hsp32 Hgp Htp Hra Hrk Hrk2 Ha0 HK.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cw_word_at B MT LAWS e lyc Sc Wc memT mdT pos EV_JOINED n HE HJ Hsub Hn)
  as (_ & _ & _ & _ & Hwp64 & (p & q & Hin & Hp & Hpq) & Hws).
destruct (al_blocks _ _ LAWS lyc Sc Wc memT mdT p q (proj1 HJ) Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hq).
pose proof (req_size_pos q ltac:(lia)) as [_ Hrq].
set (x := nth n (e_wp e) 0) in *. set (s := nth n (e_ws e) []) in *.
pose proof (Zle_0_nat (length s)) as Hs0.
pose proof (i2_arodata_now e pos lyc Sc Wc memT mdT EV_JOINED HE HJ) as HROD.
destruct (cmd_rec_cells lyc Sc Wc memT mdT (proj1 HJ)) as (Hflag & Hguard & ev & Herr).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (3 * ESTACK) (aerrno_cell B)
    (SIG CS___interceptor_trampoline_atoi) Wc regsT memT CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e)
    (e_mem e) (e_md e) [(0, pos)] lyc Sc mdT EV_JOINED (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + retk)) _ HJ
    ltac:(rewrite Hsp; lia) ltac:(apply i2_o16; [exact Hsp32 | exact Hal16]) ltac:(lia) ltac:(lia)
    ltac:(rewrite Hes, WS; lia) Hra (fun a H => H)).
  apply (AATOI fx lyc Sc Wc regsT memT mdT x s ev).
  - exact Hflag.
  - exact Hguard.
  - apply (ecall_pre_stk_at SEGS B (3 * ESTACK) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
      (e_md e) [(0, pos)] lyc Sc Wc memT mdT EV_JOINED regsT (sp1 - cw_sp0 e) HJ);
      [rewrite Hsp; lia | apply i2_o16; [exact Hsp32 | exact Hal16] | lia | rewrite Hes; lia | rewrite Hes, WS; lia
      | rewrite Hra; apply ret_ok_codeptr_v; [lia | exact Hrk2] | exact Hgp | exact Htp].
  - exact Ha0.
  - lia.
  - apply (astr_atR_view SEGS). exact Hws.
  - unfold astr_len. apply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) lyc Sc Wc regsT memT mdT p q x _ (proj1 HJ) Hin);
      [lia | lia | lia | rewrite Hsp, Hes; lia].
  - (* the `+ 8` band premise: the word lies in a live heap block *)
    unfold astr_len. apply (amem8_of_block SEGS B LAWS lyc Sc Wc memT mdT p q x _ (proj1 HJ) Hin); lia.
  - unfold astr_len. apply (cmd_heap_tail_vis lyc Sc Wc memT mdT p q _ (proj1 HJ) Hin). lia.
  - exact Herr.
  - (* contract 2: the word does not hold the errno cell: the errno cell's bytes are image bytes (api_env, from
       PALib), the bytes of a live block are not (RecBLemmas.recb_heap_noimg_m) *)
    pose proof errno_low as (_ & Herrimg & _).
    unfold astr_len in *.
    destruct (Z_le_gt_dec (x + Z.of_nat (length s) + 1) (as_errno B)) as [Hl|Hl]; [left; exact Hl|]. right.
    destruct (Z_le_gt_dec (as_errno B + 4) x) as [Hr|Hr]; [exact Hr|]. exfalso.
    apply (RecBLemmas.recb_heap_noimg_m (PI := PI) B lyc Sc Wc memT mdT p q (Z.max x (as_errno B)) (proj1 HJ) Hin).
    + lia.
    + apply Herrimg. lia.
  - apply cmd_rom_view_on. exact HROD. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQa & _) & Hfr2).
apply (HK regs2 mem2 md2 HJ2 HP2).
- rewrite HQa. reflexivity.
- intros x' Hx Hw He _. apply (Hfr2 x' Hx); [lia | exact He].
Qed.

End e.
End f.
End d.
