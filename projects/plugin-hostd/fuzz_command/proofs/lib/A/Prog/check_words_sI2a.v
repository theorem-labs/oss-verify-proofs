(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module paths and module names changed; 756 of its 895 lines of code are new or changed and 1521 lines of the source are left out. *)
(* check_words' ASan walk (plugin-hostd/fuzz_command), segment I2: item a of call c, from the point IK (0x87b38,
   listing 0x1654), where the template cursor s2 is past the spaces and the item's kind byte is next.
     0x87b38 .. 0x87b60  s6 := the kind byte; '#' (35) -> atoi(s2 + 1); '*' (42) -> strcspn(s2, " ") and the latch IL;
                         'L' (76) -> s5 := line, on to ICMP (0x87bfc); any other byte -> atoi(s2 + (s6 = '?')).
     0x87b70 .. 0x87bcc  after atoi (n = the word number): '?' with n >= read -> strcspn(s2, " ") and IL; otherwise
                         s5 := "" and, when n < read, s5 := w->w[n] through two inline checks (W + 16, &w->w[n]);
                         n >= read -> ICMP with "".
     0x87bd4 .. 0x87bf8  '#': atoi(w->w[n]), snprintf(number, 16, "%d", that), s5 := number, on to ICMP.
     0x87c50 .. 0x87c64  a word item: strcspn(s2, " "), s2 += it, `bnez s5` -> ICMP2 (0x87c0c).
   The walk seats a fresh symbolic state after every call (points 0x168c, 0x1700, 0x16ac, 0x1778), each with only the
   regions its stretch reads. This file holds what the stretches share (the state i2_st, the seeds, the list and
   arithmetic facts) and the statements of the four stretches after a call, frozen here so that each is proved in its
   own file: i2_H_spec (0x1700, check_words_sI2h.v: i2_at_H : i2_H_spec B MT), i2_A_spec (0x168c, check_words_sI2x.v:
   i2_at_A : i2_H_spec B MT -> i2_S_spec B MT -> i2_C_spec B MT -> i2_A_spec B MT), i2_S_spec (0x16ac) and i2_C_spec
   (0x1778) (check_words_sI2.v, with seg_I2). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_art check_words_ki.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require RecBLemmas.
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
Lemma i2_cspn_le : forall set s, (PCspn.cspn_len set s <= length s)%nat.
Proof.
intros set s. induction s as [|x s IH]; cbn [PCspn.cspn_len length]; [lia|].
destruct (existsb _ set); lia.
Qed.
Lemma i2_den_off : forall E n v off, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n off) = Z_to_bv 64 (v + off).
Proof.
intros E n v off Hn. cbn [sv_denot]. rewrite Hn. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma i2_reg_off : forall E (regs' : bvmap 5 word) n (r : bv 5) v off,
  ew E n = Z_to_bv 64 v -> getr regs' r = sv_denot E (SOff n off) -> getr regs' r = Z_to_bv 64 (v + off).
Proof. intros E regs' n r v off Hn H. rewrite H. apply i2_den_off. exact Hn. Qed.
Lemma i2_reg_same : forall E (regsc regs' : bvmap 5 word) n (r : bv 5),
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r) -> Z.of_nat n = bv_unsigned r ->
  getr regs' r = sv_denot E (SOff n 0) -> getr regs' r = getr regsc r.
Proof. intros E regsc regs' n r EV Hn H. rewrite H. cbn [sv_denot]. rewrite (EV n r Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
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
Lemma i2_ge : forall E n m x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = negb (x <? y).
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
(* s2 + (s6 = '?') of 0x87b58 .. 0x87b68 *)
Lemma i2_U_seqz : forall E p b, U E (SOff 18 0) = p -> ew E 32 = Z_to_bv 64 b -> 0 <= b <= 255 -> 0 <= p -> p + 1 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff 18 0) (SAlu ALU_SLTU (SOff 32 (-63)) (SLit 1))) = p + (if b =? 63 then 1 else 0).
Proof.
intros E p b Hp Hb R0 R1 R2. rewrite !U_SAlu. cbn [zalu_raw]. rewrite Hp, U_SOff, Hb, U_SLit, unsigned_lit_small by lia.
change (zcanon 1) with 1.
assert (Hs : zcanon (if zcanon (b + -63) <? 1 then 1 else 0) = if b =? 63 then 1 else 0).
{ destruct (Z.eqb_spec b 63) as [->|Hne]; [reflexivity|].
  destruct (Z_lt_le_dec b 63) as [Hl|Hl].
  - assert (Hin : zcanon (b + -63) = b + -63 + 2 ^ 64).
    { unfold zcanon, M64. rewrite <- (Z.mod_add (b + -63) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Hin. replace (b + -63 + 2 ^ 64 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - rewrite (zcanon_id (b + -63)) by (unfold M64; lia).
    replace (b + -63 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite Hs. apply zcanon_id. unfold M64. destruct (b =? 63); lia.
Qed.

(* the items of call_items: the word numbers are 0 .. 3 *)
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
Definition i2_aj (b : Z) (j : nat) : nat := if (b =? 35) || (b =? 63) then S j else j.
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

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seeds *)
Definition IBx : sv := SOff 23 0.
Definition IBspan : Z * Z := (CW_SB, CW_SB + 2 ^ 44 - 1).
Definition i2_shx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 23 0).
Definition PCEIL : Z := 140737479966720.
(* IK: atom 32 is the kind byte at s2, atom 33 the line pointer at s1 + 144 *)
Definition k_regions : smem :=
[ YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 33 0))] ].
Definition k_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (18%nat, mkAF 0x21120 0x21ab0 0); (23%nat, mkAF CW_SB CW_SB 0);
          (32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 (2^47) 0) ] [] [].
Definition ssK : sstate := mkSS CW_PC_IK sr_atoms k_regions None k_facts.
(* after atoi (0x168c): atoms 9 sp1, 10 n, 18 s2, 22 the kind byte, 23 SB; extra 32 = W + 16, 33 = read, 34 = w->w,
   35 = &w->w[n], 36 = w->w[n]; the alias resolves the engine's form of &w->w[n] *)
Definition a_scr : YP09.region :=
YP09.mkRegion (Some 9%nat) 88 160 0 0
[YP09.mkChunk 88 (CVal 8 (i2_shx 32)); YP09.mkChunk 96 (CVal 8 (SOff 32 0));
 YP09.mkChunk 104 (CVal 8 (SLit 0x21280)); YP09.mkChunk 152 (CVal 8 (SOff 33 0))].
Definition a_ww : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition a_ws : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].
Definition a_regions (hi : bool) : smem := if hi then [a_scr; a_ww; a_ws] else [a_scr].
Definition a_atoms : list (nat * afact) :=
[ (9%nat, mkAF (2^46) (2^47) 5); (10%nat, mkAF 0 3 0); (18%nat, mkAF 0x21120 0x21ab0 0); (22%nat, mkAF 0 255 0);
  (23%nat, mkAF CW_SB CW_SB 0); (32%nat, mkAF (2^46) (2^47 - 16) 0); (33%nat, mkAF 0 64 0);
  (34%nat, mkAF 0 (2^64 - 1) 0); (35%nat, mkAF 4096 PCEIL 0); (36%nat, mkAF 4096 PCEIL 0) ].
Definition a_ali : sv := SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 10 0) (SLit 3)).
Definition a_facts (hi : bool) : facts := mkFacts a_atoms [] (if hi then [(a_ali, SOff 35 0)] else []).
Definition ssA (hi : bool) : sstate := mkSS 0x168c sr_atoms (a_regions hi) None (a_facts hi).
Definition a_SH (hi : bool) : list shent := if hi then [mkSHE 32 0 8; mkSHE 35 0 8] else [].
(* after the second atoi (0x1700): extra atom 32 = number = F + 32 *)
Definition h_regions : smem :=
[ YP09.mkRegion (Some 9%nat) 40 56 0 0 [YP09.mkChunk 40 (CVal 8 (SLit 0x218a0)); YP09.mkChunk 48 (CVal 8 (SOff 32 0))] ].
Definition h_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (23%nat, mkAF CW_SB CW_SB 0); (32%nat, mkAF 4096 PCEIL 0) ] [] [].
Definition ssH : sstate := mkSS 0x1700 sr_atoms h_regions None h_facts.
(* after strcspn at 0x16a8 (0x16ac) and at 0x1774 (0x1778): no region; at 0x1778 s5 (atom 21) is a word pointer *)
Definition ssS : sstate := mkSS 0x16ac sr_atoms [] None (mkFacts [ (23%nat, mkAF CW_SB CW_SB 0) ] [] []).
Definition ssC : sstate := mkSS 0x1778 sr_atoms [] None
  (mkFacts [ (21%nat, mkAF 4096 PCEIL 0); (23%nat, mkAF CW_SB CW_SB 0) ] [] []).

(* the registers kept by a stretch that moves s2 *)
Definition I2_RL0 : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma i2_rk0_in : forall (P : bv 5 -> Prop), (forall r, In r I2_RL0 -> P r) ->
  P 2%bv /\ P 3%bv /\ P 4%bv /\ P 8%bv /\ P 9%bv /\ P 19%bv /\ P 20%bv /\ P 21%bv /\ P 23%bv /\ P 24%bv /\
  P 25%bv /\ P 26%bv /\ P 27%bv.
Proof.
intros P H. unfold I2_RL0 in H.
repeat split; apply H; repeat (first [left; reflexivity | right]).
Qed.

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
(* the statement's hypotheses (check_words_c.v:88-104), word for word *)
Hypothesis HJOINED : tjoined_spec B MT.
Hypothesis HADD : tcheck_words_add_spec B MT.
Hypothesis HCHAIN : tcheck_words_chain_spec B MT.
Hypothesis HPIN : tcwps_spec B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASMALLOC0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : aatoi_realizes SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
(* the record facts of lib/A/Prog/CmdRecFacts.v, carried until that file lands *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Hypothesis cmd_got_rec : cmd_got_rec_P B.
(* the allocator record: its errno address, for the separation premise of atoi on an item *)
Hypothesis HB : AF0m.CmdBSyms B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

#[local] Notation CWJ e pos lyc Sc Wc memc mdc :=
  (ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
     lyc Sc Wc memc mdc EV_JOINED).

(* the state at every point of the segment: INV_IK's parts *)
Definition i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args (j1 : nat) : Prop :=
  cw_icommon B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args /\
  (j1 <= length (cw_tpl fn))%nat /\ getr regs 18 = w64 (cw_tptr fn + Z.of_nat j1) /\
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn))) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn).

Lemma i2_st_kept : forall e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args j1,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 -> CWJ e pos lyc Sc Wc mem' md' ->
  cw_regs_kept regs regs' -> getr regs' 18 = getr regs 18 ->
  cw_mem_kept B (rdW Wc mem) (rdW Wc mem') sp1 (frame_addr (e_ly e) 0 pos) ->
  i2_st e lyc Sc Wc regs' mem' md' pos sp1 line c a fn args j1.
Proof.
intros e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args j1 HE (HC & Hj & H18 & Heq) HJ HR R18 HM.
split; [exact (cw_icommon_kept B MT LAWS TL e lyc Sc Wc regs mem md regs' mem' md' pos sp1 line c a fn args HE HC HJ HR HM)|].
split; [exact Hj|]. split; [rewrite R18; exact H18 | exact Heq].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the four stretches after a call (frozen statements) *)
(* 0x16ac, after strcspn(s2, " ") of '*' and of an absent '?': s2 += the span, on to the latch IL *)
Definition i2_S_spec : Prop := forall c a, ST_IL B MT c a ->
  forall e lyc Sc Wc regs mem md pos sp1 line fn args j1,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  getr regs 10 = w64 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x16ac)) mem (seg_rom SEGS)) md) (cw_post B MT e).
(* 0x1778, after strcspn(s2, " ") of a word item: s2 += the span, `bnez s5` on to ICMP2 with s5 = q *)
Definition i2_C_spec : Prop := forall c a, ST_ICMP2 B MT c a ->
  forall e lyc Sc Wc regs mem md pos sp1 line fn args j1 q y,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  getr regs 10 = w64 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))) ->
  getr regs 21 = w64 q -> 4096 <= q -> q + Z.of_nat (length y) + 1 <= PCEIL ->
  cw_wsrc B e lyc Sc (rdW Wc mem) pos line q y ->
  want_at atoi_a (cw_read e) (e_ws e) (item_of_a (skipn j1 (cw_tpl fn))) = Some y ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x1778)) mem (seg_rom SEGS)) md) (cw_post B MT e).
(* 0x1700, after atoi(w->w[k]) of a '#' item: snprintf(number, 16, "%d", a0), on to ICMP with s5 = number. snprintf
   returns at some FP state fx1 (pass 4), so the stretch takes ST_ICMP at every FP state *)
Definition i2_H_spec : Prop := forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) ->
  forall e lyc Sc Wc regs mem md pos sp1 line fn args j1 k,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  item_of_a (skipn j1 (cw_tpl fn)) = PCW.INum k -> 0 <= k < cw_read e ->
  getr regs 10 = w64 (atoi_a (nth (Z.to_nat k) (e_ws e) [])) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x1700)) mem (seg_rom SEGS)) md) (cw_post B MT e).
(* 0x168c, after atoi of the item ('#', '?' or a word), with b the kind byte in s6 and k the word number in a0; the
   '#' arm goes on through i2_H_spec, so ST_ICMP at every FP state *)
Definition i2_A_spec : Prop := forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) ->
  ST_ICMP2 B MT c a -> ST_IL B MT c a ->
  forall e lyc Sc Wc regs mem md pos sp1 line fn args j1 b k,
  cw_ent B MT e -> i2_st e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  b = bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn))) -> b <> 42 -> b <> 76 ->
  item_of_a (skipn j1 (cw_tpl fn)) = i2_kitem b k ->
  getr regs 22 = w64 b -> getr regs 10 = w64 k ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x168c)) mem (seg_rom SEGS)) md) (cw_post B MT e).

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
(* "%d" at 0x218a0 at the current state *)
Lemma i2_fmt_at : forall e lyc Sc Wc memc mdc pos k, cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  astr_atR (rdW Wc memc) 0x218a0 (pf_bytes [37; 100]) /\ range_addressable (rdW Wc memc) SHADOW_OFF 0x218a0 3 /\
  shadow_hull_vis (rdW Wc memc) 0x218a0 3 /\ atail_vis SEGS Wc memc 0x218a2.
Proof.
intros e lyc Sc Wc memc mdc pos k HE HJ.
assert (Hzsh : In (0x218a0, 3) CW_ZSH) by (apply cw_in_pair_of_existsb; vm_compute; reflexivity).
pose proof HE as (_ & _ & _ & _ & HRO & _). destruct HRO as [HROB _].
assert (Hb0 : abytes_atR (rdW (e_W e) (e_mem e)) 0x218a0 RO_lit_218a0).
{ clear - HROB. unfold cmd_ro_bytes in HROB.
  repeat lazymatch type of HROB with
  | abytes_atR _ 0x218a0 _ /\ _ => exact (proj1 HROB)
  | _ /\ _ => apply proj2 in HROB
  end. }
destruct (ZSH_cw lyc Sc Wc memc mdc _ _ (proj1 HJ) Hzsh) as [Hra Hhv].
split; [split|].
{ replace (pf_bytes [37; 100] ++ [Z_to_bv 8 0]) with RO_lit_218a0 by (vm_compute; reflexivity).
  apply (cw_abytes_kept (rdW (e_W e) (e_mem e))); [|exact Hb0].
  intros i Hi. change (length RO_lit_218a0) with 3%nat in Hi.
  destruct (cw_ro_unowned 0x218a0 3 (Z.of_nat i) Hzsh ltac:(unfold A_G_REC; lia) ltac:(lia)) as (H1 & H2 & H3).
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
Ltac i2_env HS := lazymatch type of HS with
  | st_ok_pi _ _ ?E _ _ => E
  | st_ok _ ?E _ _ => E
  end.
(* the registers a stretch does not change, from its final symbolic state (a closed register list) *)
Definition I2_RL : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma i2_rk_in : forall (P : bv 5 -> Prop), (forall r, In r I2_RL -> P r) ->
  P 2%bv /\ P 3%bv /\ P 4%bv /\ P 8%bv /\ P 9%bv /\ P 18%bv /\ P 19%bv /\ P 20%bv /\ P 23%bv /\ P 24%bv /\
  P 25%bv /\ P 26%bv /\ P 27%bv.
Proof.
intros P H. unfold I2_RL in H.
repeat split; apply H; repeat (first [left; reflexivity | right]).
Qed.
Lemma i2_rk_pi : forall E ss ms regsc extra, st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsc extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) I2_RL = true ->
  cw_regs_kept regsc (ms_regs ms) /\ getr (ms_regs ms) 18 = getr regsc 18.
Proof.
intros E ss ms regsc extra HS HA Hl.
destruct (i2_rk_in _ (regs_kept_of_st_ok_pi E ss ms regsc extra I2_RL HS HA Hl))
  as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
split; [repeat split; assumption | exact R18].
Qed.
Lemma i2_rk_st : forall E ss ms regsc extra, st_ok SEGS E ss ms -> env_agree 32 (Ereg regsc extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) I2_RL = true ->
  cw_regs_kept regsc (ms_regs ms) /\ getr (ms_regs ms) 18 = getr regsc 18.
Proof.
intros E ss ms regsc extra HS HA Hl.
destruct (i2_rk_in _ (regs_kept_of_st_ok SEGS E ss ms regsc extra I2_RL HS HA Hl))
  as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
split; [repeat split; assumption | exact R18].
Qed.
Ltac i2_kept HFr K := lazymatch type of HFr with frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) =>
  pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seeds' validity *)
Lemma i2_seedK : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 p b line,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 23 = w64 CW_SB ->
  getr regsc 18 = w64 p -> 0x21120 <= p <= 0x21ab0 -> 0 <= b <= 255 -> 4096 <= line <= 2 ^ 47 ->
  aval_mem (rdW W memc) p 1 b -> aval_mem (rdW W memc) (sp1 + 144) 8 line ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 b; Z_to_bv 64 line])) ssK
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_IK)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc sp1 p b line H9 Hsp Hsp32 H23 H18 Hp Hb Hl Vb Vl.
set (E := Eimg (Ereg regsc [Z_to_bv 64 b; Z_to_bv 64 line])).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (subst E; rewrite (i2_EE regsc _ 9%nat 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 p) by (subst E; rewrite (i2_EE regsc _ 18%nat 18%bv eq_refl); exact H18).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 line) by (subst E; exact (i2_EX regsc _ 1 ltac:(unfold A_TEXT; lia))).
unfold ssK. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold k_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E18, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (i2_val_of_aval _ _ _ _ _ Vb).
  + rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ sp1 144 8 (SOff 33 0) line);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ Vl).
- apply pairwise_disjoint_of_extents. unfold k_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E18, E9, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok k_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E18, E23, E32, E33, !unsigned_lit_small by (unfold CW_SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  change (2 ^ 5) with 32. unfold CW_SB. repeat split; lia.
Qed.

Lemma i2_seedA : forall (hi : bool) (W : world SEGS) (regsc : bvmap 5 word) memc sp1 p b k W16 rdv arr q wq,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 23 = w64 CW_SB ->
  getr regsc 10 = w64 k -> 0 <= k <= 3 -> getr regsc 18 = w64 p -> 0x21120 <= p <= 0x21ab0 ->
  getr regsc 22 = w64 b -> 0 <= b <= 255 ->
  2 ^ 46 <= W16 <= 2 ^ 47 - 16 -> sp1 + 160 <= W16 -> 0 <= rdv <= 64 -> 0 <= arr < 2 ^ 64 ->
  4096 <= q <= PCEIL -> q + 8 <= sp1 -> 4096 <= wq <= PCEIL ->
  aval_mem (rdW W memc) (sp1 + 88) 8 (CW_SB + W16 / 8) -> aval_mem (rdW W memc) (sp1 + 96) 8 W16 ->
  aval_mem (rdW W memc) (sp1 + 104) 8 0x21280 -> aval_mem (rdW W memc) (sp1 + 152) 8 rdv ->
  (hi = true -> q = arr + 8 * k /\ aval_mem (rdW W memc) W16 8 arr /\ aval_mem (rdW W memc) q 8 wq) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))) (ssA hi)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x168c)) memc (seg_rom SEGS))).
Proof.
intros hi W regsc memc sp1 p b k W16 rdv arr q wq H9 Hsp Hsp32 H23 H10 Hk H18 Hp H22 Hb HW HWs Hrd Harr Hq Hqs Hwq
  V88 V96 V104 V152 Vhi.
set (E := Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (subst E; rewrite (i2_EE regsc _ 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 k) by (subst E; rewrite (i2_EE regsc _ 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 p) by (subst E; rewrite (i2_EE regsc _ 18%nat 18%bv eq_refl); exact H18).
assert (E22 : ew E 22 = Z_to_bv 64 b) by (subst E; rewrite (i2_EE regsc _ 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 W16) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 rdv) by (subst E; exact (i2_EX regsc _ 1 ltac:(unfold A_TEXT; lia))).
assert (E34 : ew E 34 = Z_to_bv 64 arr) by (subst E; exact (i2_EX regsc _ 2 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 q) by (subst E; exact (i2_EX regsc _ 3 ltac:(unfold A_TEXT; lia))).
assert (E36 : ew E 36 = Z_to_bv 64 wq) by (subst E; exact (i2_EX regsc _ 4 ltac:(unfold A_TEXT; lia))).
unfold CW_SB in *.
assert (RSCR : region_ok SEGS E (mrestrict (w_H W) memc) a_scr).
{ unfold region_ok, a_scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ sp1 88 8 _ (2147450880 + W16 / 8));
      [unfold i2_shx; rewrite (denot_shx E 32 23 0 W16 2147450880 E32 E23) by lia; rewrite Z.add_0_r; reflexivity
      | split; [pose proof (Z.div_pos W16 8 ltac:(lia) ltac:(lia)); lia | pose proof (Z.div_le_upper_bound W16 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]
      | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V88).
  - apply (chunk_ok_val SEGS E _ sp1 96 8 (SOff 32 0) W16);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V96).
  - apply (chunk_ok_val SEGS E _ sp1 104 8 (SLit 0x21280) 0x21280); [cbn [sv_denot]; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V104).
  - apply (chunk_ok_val SEGS E _ sp1 152 8 (SOff 33 0) rdv);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V152). }
assert (FACTS : atoms_ok E a_atoms).
{ unfold a_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E10, E18, E22, E23, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold PCEIL in *; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold CW_SB. repeat split; lia. }
unfold ssA. rewrite restrict_mkst_fx. destruct hi.
- destruct (Vhi eq_refl) as (Hqd & Vww & Vws). apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold a_regions. apply Forall_cons; [exact RSCR|]. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [a_ww a_ws YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ W16 0 8 (SOff 34 0) arr);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact (i2_val_of_aval _ _ _ _ _ Vww).
    * rewrite E35, unsigned_lit_small by (unfold PCEIL in *; lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 36 0) wq);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold PCEIL in *; lia | lia |].
      rewrite Z.add_0_r. exact (i2_val_of_aval _ _ _ _ _ Vws).
  + apply pairwise_disjoint_of_extents. unfold a_regions, a_scr, a_ww, a_ws, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E32, E35, !unsigned_lit_small by (unfold PCEIL in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [exact FACTS|]. split; [exact I|]. cbn [f_alias a_facts alias_ok]. split; [|exact I].
    apply U_inj. rewrite (U_atom E 35 q E35) by (unfold PCEIL in *; lia). unfold a_ali.
    rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 34 arr E34) by lia. rewrite (U_atom E 10 k E10) by lia.
    rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (zcanon_small (k * 8)) by lia. rewrite zcanon_small by (unfold PCEIL in *; lia). lia.
- apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold a_regions. apply Forall_cons; [exact RSCR | apply Forall_nil].
  + apply pairwise_disjoint_of_extents. cbn [a_regions map zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [exact FACTS|]. split; exact I.
Qed.

Lemma i2_shokA : forall (hi : bool) (W : world SEGS) (regsc : bvmap 5 word) memc W16 rdv arr q wq,
  getr regsc 23 = w64 CW_SB -> 2 ^ 46 <= W16 <= 2 ^ 47 - 16 -> 4096 <= q <= PCEIL ->
  (hi = true -> range_addressable (rdW W memc) SHADOW_OFF W16 8 /\ range_addressable (rdW W memc) SHADOW_OFF q 8 /\
     in_app q 8) ->
  sh_ok SEGS IBx (a_SH hi) (Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))) (mrestrict (w_H W) memc).
Proof.
intros hi W regsc memc W16 rdv arr q wq H23 HW Hq HRA.
set (E := Eimg (Ereg regsc (map (Z_to_bv 64) [W16; rdv; arr; q; wq]))).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 W16) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 q) by (subst E; exact (i2_EX regsc _ 3 ltac:(unfold A_TEXT; lia))).
destruct hi; [|unfold sh_ok, a_SH; apply Forall_nil].
destruct (HRA eq_refl) as (RA1 & RA2 & Happ). unfold sh_ok, a_SH. repeat apply Forall_cons; try apply Forall_nil.
- apply (shent_ok_of_range SEGS (w_H W) memc E IBx 32 W16 8 W16 0 8 RA1).
  + unfold IBx. rewrite (U_atom E 23 _ E23) by (unfold CW_SB; lia). reflexivity.
  + apply (U_atom E 32 _ E32). lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range SEGS (w_H W) memc E IBx 35 q 8 q 0 8 RA2).
  + unfold IBx. rewrite (U_atom E 23 _ E23) by (unfold CW_SB; lia). reflexivity.
  + apply (U_atom E 35 _ E35). unfold PCEIL in *; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, PCEIL in *. lia.
Qed.

Lemma i2_seedH : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 d,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 23 = w64 CW_SB ->
  4096 <= d <= PCEIL ->
  aval_mem (rdW W memc) (sp1 + 40) 8 0x218a0 -> aval_mem (rdW W memc) (sp1 + 48) 8 d ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 d])) ssH
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x1700)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc sp1 d H9 Hsp Hsp32 H23 Hd V40 V48.
set (E := Eimg (Ereg regsc [Z_to_bv 64 d])).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (subst E; rewrite (i2_EE regsc _ 9%nat 9%bv eq_refl); exact H9).
assert (E23 : ew E 23 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 d) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
unfold ssH. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold h_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ sp1 40 8 (SLit 0x218a0) 0x218a0); [cbn [sv_denot]; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V40).
  + apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 32 0) d);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold PCEIL in *; lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ V48).
- apply pairwise_disjoint_of_extents. cbn [h_regions map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok h_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E23, E32, !unsigned_lit_small by (unfold CW_SB, PCEIL in *; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  change (2 ^ 5) with 32. unfold CW_SB. repeat split; lia.
Qed.

Lemma i2_seedS : forall (W : world SEGS) (regsc : bvmap 5 word) memc,
  getr regsc 23 = w64 CW_SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) ssS
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x16ac)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc H23.
assert (E23 : ew (Eimg (Ereg regsc [])) 23 = Z_to_bv 64 CW_SB) by (rewrite (i2_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
unfold ssS. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E23, unsigned_lit_small by (unfold CW_SB; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold CW_SB. repeat split; lia.
Qed.

Lemma i2_seedC : forall (W : world SEGS) (regsc : bvmap 5 word) memc q,
  getr regsc 23 = w64 CW_SB -> getr regsc 21 = w64 q -> 4096 <= q <= PCEIL ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) ssC
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x1778)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc q H23 H21 Hq.
assert (E23 : ew (Eimg (Ereg regsc [])) 23 = Z_to_bv 64 CW_SB) by (rewrite (i2_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E21 : ew (Eimg (Ereg regsc [])) 21 = Z_to_bv 64 q) by (rewrite (i2_EE regsc _ 21%nat 21%bv eq_refl); exact H21).
unfold ssC. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E21, E23, !unsigned_lit_small by (unfold CW_SB, PCEIL in *; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold CW_SB. repeat split; lia.
Qed.

Lemma i2_rk0_pi : forall E ss ms regsc extra, st_ok_pi SEGS VAL E ss ms -> env_agree 32 (Ereg regsc extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) I2_RL0 = true ->
  cw_regs_kept regsc (ms_regs ms) /\ getr (ms_regs ms) 21 = getr regsc 21.
Proof.
intros E ss ms regsc extra HS HA Hl.
destruct (i2_rk0_in _ (regs_kept_of_st_ok_pi E ss ms regsc extra I2_RL0 HS HA Hl))
  as (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R21 & R23 & R24 & R25 & R26 & R27).
split; [repeat split; assumption | exact R21].
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

(* the item a of the template's parse, and the rest *)
Lemma i2_parse_next : forall fn a j1 cs,
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn cs (skipn j1 (cw_tpl fn))) = skipn (Z.to_nat a) (PCW.call_items fn) ->
  cw_parse (skipn (j1 + cs) (cw_tpl fn)) = skipn (S (Z.to_nat a)) (PCW.call_items fn) /\
  nth_error (PCW.call_items fn) (Z.to_nat a) = Some (item_of_a (skipn j1 (cw_tpl fn))).
Proof.
intros fn a j1 cs Heq. split.
- rewrite (i2_skipn_S _ _ _ _ (eq_sym Heq)). rewrite skipn_skipn. f_equal. f_equal. lia.
- exact (i2_skipn_nth _ _ _ _ (eq_sym Heq)).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the two runtime calls on the template (s2 = the template from its byte j): strcspn(s2, " ") and atoi(s2) *)
Lemma i2_call_cspn : forall e lyc Sc Wc regsT memT mdT pos sp1 fn j retk Q,
  cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memT mdT EV_JOINED ->
  spZ regsT = sp1 -> cw_sp0 e - 304 <= sp1 <= cw_sp0 e - 288 -> sp1 mod 32 = 0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + retk) ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 10 = w64 (cw_tptr fn + Z.of_nat j) -> getr regsT 11 = w64 0x21120 -> (j <= length (cw_tpl fn))%nat ->
  (forall regs2 mem2 md2,
    ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
      lyc Sc Wc mem2 md2 EV_JOINED ->
    aregs_preserved regsT regs2 -> getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j (cw_tpl fn)))) ->
    cw_mem_kept B (rdW Wc memT) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
    SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_strcspn)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e lyc Sc Wc regsT memT mdT pos sp1 fn j retk Q HE HJ Hsp Hrng Hsp32 Hgp Htp Hra Hrk Hrk2 Ha0 Ha1 Hj HK.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc memT mdT pos EV_JOINED fn HE HJ)
  as ([TB TN] & TRA & THV & TTL & Tlo & Thi & T8).
destruct (cw_sp1_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc memT mdT pos EV_JOINED HE HJ)
  as (SP & SRA & SHV & STL).
pose proof (i2_arodata_now e pos lyc Sc Wc memT mdT EV_JOINED HE HJ) as HROD.
eapply SRr_bind.
{ apply (aj_strcspn_at B LAWS TL cmd_rec_cells _ ASTRCSPN Wc _ _ CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e)
    (e_W e) (e_mem e) (e_md e) [(0, pos)] lyc Sc mdT EV_JOINED (cw_tptr fn + Z.of_nat j) 0x21120
    (skipn j (cw_tpl fn)) CW_SP1 (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + retk)) HJ Ha0 Ha1).
  - lia.
  - lia.
  - rewrite Hsp. lia.
  - apply i2_o16; [exact Hsp32 | exact Hal16].
  - lia.
  - rewrite Hes, WS. lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - apply ret_ok_codeptr_v; [lia | exact Hrk2].
  - apply (astr_atR_view SEGS). exact (astr_atR_skipn _ _ _ j (conj TB TN) Hj).
  - apply (astr_atR_view SEGS). exact SP.
  - unfold aread_ok, astr_len. rewrite length_skipn.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros x Hx. split.
      - replace x with (cw_tptr fn + Z.of_nat (Z.to_nat (x - cw_tptr fn))) by lia.
        rewrite (TB (Z.to_nat (x - cw_tptr fn))) by (rewrite length_app; cbn [length]; lia). discriminate.
      - unfold ascratch_stk. rewrite Hsp. lia. }
    split; [unfold amem_range; left; rewrite C5; lia|].
    split; [apply (range_addressable_sub _ _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact TRA | lia | lia]|].
    intros _. apply (i2_hull_sub _ (cw_tptr fn) (Z.of_nat (length (cw_tpl fn)) + 1)); [exact THV | lia | lia | lia].
  - (* the item's band (+ 8): a g_call_words literal in .rodata, low band (band-premise survey, call sites 7, 10) *)
    unfold amem_range, astr_len. rewrite length_skipn. left. rewrite C5. lia.
  - change (astr_len CW_SP1 + 1) with 2. destruct SP as [SB2 _]. unfold aread_ok.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros x Hx. split.
      - replace x with (0x21120 + Z.of_nat (Z.to_nat (x - 0x21120))) by lia.
        rewrite (SB2 (Z.to_nat (x - 0x21120))) by (cbn [length app CW_SP1]; lia). discriminate.
      - unfold ascratch_stk. rewrite Hsp. lia. }
    split; [unfold amem_range; left; rewrite C5; lia|]. split; [exact SRA|]. intros _. exact SHV.
  - (* the set " " at 0x21120, .rodata, low band *)
    change (astr_len CW_SP1 + 8) with 9. unfold amem_range. left. rewrite C5. lia.
  - unfold astr_len. rewrite length_skipn.
    replace (cw_tptr fn + Z.of_nat j + Z.of_nat (length (cw_tpl fn) - j))
      with (cw_tptr fn + Z.of_nat (length (cw_tpl fn))) by lia.
    exact TTL.
  - change (0x21120 + astr_len CW_SP1) with 0x21121. exact STL.
  - apply cmd_rom_view_on. exact HROD. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcs & Hfr2).
apply (HK regs2 mem2 md2 HJ2 HP2 Hcs).
intros x Hx Hw _ _. apply (Hfr2 x Hx); [lia | exact (fun f : False => f)].
Qed.

Lemma i2_call_atoi : forall e lyc Sc Wc regsT memT mdT pos sp1 fn j retk Q,
  cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memT mdT EV_JOINED ->
  spZ regsT = sp1 -> cw_sp0 e - 304 <= sp1 <= cw_sp0 e - 288 -> sp1 mod 32 = 0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + retk) ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 10 = w64 (cw_tptr fn + Z.of_nat j) -> (j <= length (cw_tpl fn))%nat ->
  (forall regs2 mem2 md2,
    ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
      lyc Sc Wc mem2 md2 EV_JOINED ->
    aregs_preserved regsT regs2 -> getr regs2 10 = w64 (atoi_a (skipn j (cw_tpl fn))) ->
    cw_mem_kept B (rdW Wc memT) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
    SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_atoi)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e lyc Sc Wc regsT memT mdT pos sp1 fn j retk Q HE HJ Hsp Hrng Hsp32 Hgp Htp Hra Hrk Hrk2 Ha0 Hj HK.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
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
  apply (AATOI lyc Sc Wc regsT memT mdT (cw_tptr fn + Z.of_nat j) (skipn j (cw_tpl fn)) ev).
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
  - (* the item's band (+ 8): a g_call_words literal in .rodata, low band (band-premise survey, call site 6) *)
    unfold amem_range, astr_len. rewrite length_skipn. left. rewrite C5. lia.
  - unfold astr_len. rewrite length_skipn.
    replace (cw_tptr fn + Z.of_nat j + Z.of_nat (length (cw_tpl fn) - j))
      with (cw_tptr fn + Z.of_nat (length (cw_tpl fn))) by lia.
    exact TTL.
  - exact Herr.
  - (* the item apart from the errno cell (RtNumber.v:73): the literal ends below 0x21ab0, errno is 0x5e44f4 (.bss) *)
    left. rewrite (AF0m.ts_errno B HB). unfold AF0m.TFIB_ERRNO, astr_len. rewrite length_skipn. lia.
  - apply cmd_rom_view_on. exact HROD. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQa & _) & Hfr2).
apply (HK regs2 mem2 md2 HJ2 HP2).
- rewrite HQa. reflexivity.
- intros x Hx Hw He _. apply (Hfr2 x Hx); [lia | exact He].
Qed.

(* atoi(w->w[n]) on word n of the message, a string inside a heap block live since the entry *)
Lemma i2_call_atoi_w : forall e lyc Sc Wc regsT memT mdT pos sp1 n retk Q,
  cw_ent B MT e ->
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memT mdT EV_JOINED ->
  (forall bk, In bk (ablocks B (e_ly e) (e_S e)) -> In bk (ablocks B lyc Sc)) -> (n < length (e_ws e))%nat ->
  spZ regsT = sp1 -> cw_sp0 e - 304 <= sp1 <= cw_sp0 e - 288 -> sp1 mod 32 = 0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + retk) ->
  0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 10 = w64 (nth n (e_wp e) 0) ->
  (forall regs2 mem2 md2,
    ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
      lyc Sc Wc mem2 md2 EV_JOINED ->
    aregs_preserved regsT regs2 -> getr regs2 10 = w64 (atoi_a (nth n (e_ws e) [])) ->
    cw_mem_kept B (rdW Wc memT) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
    SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_atoi)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros e lyc Sc Wc regsT memT mdT pos sp1 n retk Q HE HJ Hsub Hn Hsp Hrng Hsp32 Hgp Htp Hra Hrk Hrk2 Ha0 HK.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
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
  apply (AATOI lyc Sc Wc regsT memT mdT x s ev).
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
  - (* the word's band (+ 8): w->w[n] in a live heap block (band-premise survey, call site 8) *)
    unfold astr_len. apply (amem8_of_block SEGS B LAWS lyc Sc Wc memT mdT p q x _ (proj1 HJ) Hin); lia.
  - unfold astr_len. apply (cmd_heap_tail_vis lyc Sc Wc memT mdT p q _ (proj1 HJ) Hin). lia.
  - exact Herr.
  - (* the word apart from the errno cell (RtNumber.v:73): a byte in both would be a heap byte, not an image byte
       (RecBLemmas.recb_heap_noimg_m), and an errno byte, an image byte (api_env) *)
    pose proof errno_low as (_ & Herrimg & _). unfold astr_len.
    destruct (Z_le_gt_dec (x + Z.of_nat (length s) + 1) (as_errno B)) as [He1|He1]; [left; exact He1|].
    destruct (Z_le_gt_dec (as_errno B + 4) x) as [He2|He2]; [right; exact He2|].
    exfalso. apply (RecBLemmas.recb_heap_noimg_m B lyc Sc Wc memT mdT p q (Z.max x (as_errno B)) (proj1 HJ) Hin);
      [lia | apply Herrimg; lia].
  - apply cmd_rom_view_on. exact HROD. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQa & _) & Hfr2).
apply (HK regs2 mem2 md2 HJ2 HP2).
- rewrite HQa. reflexivity.
- intros x' Hx Hw He _. apply (Hfr2 x' Hx); [lia | exact He].
Qed.

End e.
End f.
End d.
