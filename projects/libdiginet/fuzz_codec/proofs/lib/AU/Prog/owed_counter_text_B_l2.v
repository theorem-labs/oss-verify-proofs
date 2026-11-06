(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACfg.v, with its module paths and module names changed; 398 of its 428 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_counter_text_A_x.v, with its module paths and module names changed; 1044 of its 1092 lines of code are new or changed and 380 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/diginet_counter_text_B_l2.v, with its module names and numbers changed; 754 of its 888 lines of code are new or changed and 958 lines of the source are left out. *)
(* Segment L2 of owed_counter_text's walk in image B (owed_counter_text_B_inv.v): one digit of the second loop, from
   the loop head 0x84764 (digit i, from = i - (8 - n)):
     0x84764-0x8476c  subw / sub of a3 - t0 and bne -> trap: the engine decides it (the two agree);
     0x84770          bltz t2: the walk splits on the sign of from;
     from >= 0: 0x84774 bltu a7,t2 -> trap and 0x8477c bltu ~(F + 32),t2 -> trap, both refuted (from <= 7); a0 := atom
       36 = F + 32 + from, lbu t3 = s[from]; 0x84788 bltu a6,a4 -> trap refuted (~sg >= i);
     from < 0: t3 := 0; 0x84794 bltu a6,a4 -> trap refuted;
     0x84798-0x847b0  a0 := atom 35 = sg + i, the check of seg[i] (shadow entry mkSHE 35 0 1), seg[i] := t3;
     0x847b4          bltz t2 (decided); from >= 0: 0x847bc bltu s11,4 from -> trap refuted; a0 := atom 37 =
       F + 64 + 4 from, the check of dot[from] (mkSHE 37 0 4), lw dot[from]; beqz: a clear dot goes on at 0x847fc;
       a set dot on digit 7 is E_RANGE (0x8483c, to 0x84840); on digit i < 7: dt's shadow byte (region at atom 41,
       its slow path 0x84828 shown not to reach the error path), dt |= 1 << i;
     0x847fc-0x84804  a4 += 1, a3 += 1; bne a4,8: back to 0x84764, else 0x84834 a0 := 0, to 0x84840.
   The digit writes seg[i] and dt only. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_inv owed_counter_text_B_s0_a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_s0 owed_counter_text_B_l1_base.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_l1_e owed_counter_text_B_l1_a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_l1_b.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* t2 = a3 - t0 = from, as the engine writes it *)
Lemma l2_Uj : forall E n i, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit (-1))) (SOff 13 0)) = (n - 8 + i) mod 2 ^ 64.
Proof.
intros E n i H13 H5 Hn Hi. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 13 i H13) by lia. rewrite (U_atom E 5 (8 - n) H5) by lia. rewrite U_SLit.
unfold zcanon, M64.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace ((8 - n) * (2 ^ 64 - 1)) with ((n - 8) + (8 - n) * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite Z.add_mod_idemp_l by lia. try (f_equal; lia).
Qed.
Lemma l2_Dj : forall E n i, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit (-1))) (SOff 13 0)) = Z_to_bv 64 (n - 8 + i).
Proof.
intros E n i H13 H5 Hn Hi. rewrite denot_lit_U, (l2_Uj E n i H13 H5 Hn Hi).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
(* bltz t2 *)
Lemma l2_bltzj : forall E n i, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  branch_taken BC_LT (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit (-1))) (SOff 13 0))) (sv_denot E (SLit 0)) =
  (n - 8 + i <? 0).
Proof.
intros E n i H13 H5 Hn Hi. rewrite (l2_Dj E n i H13 H5 Hn Hi). cbn [sv_denot branch_taken]. unfold bv_lts.
rewrite !signed_lit. unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63).
change (bv_modulus 64) with (2 ^ 64).
replace (((n - 8 + i) mod 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63) with (n - 8 + i) by (Z.div_mod_to_equations; lia).
replace ((0 mod 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63) with 0 by reflexivity. reflexivity.
Qed.
(* bltu x, t2 -> the trap: x >= from *)
Lemma l2_bltu_j : forall E k x n i, ew E k = Z_to_bv 64 x -> ew E 13 = w64 i -> ew E 5 = w64 (8 - n) ->
  0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i -> n - 8 + i <= x < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff k 0)) (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit (-1))) (SOff 13 0))) = false.
Proof.
intros E k x n i Hk H13 H5 Hn Hi Hf Hx. rewrite branch_ltu_U, (U_atom E k x Hk) by lia.
rewrite (l2_Uj E n i H13 H5 Hn Hi), Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma l2_Uj2 : forall E n i, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit 18446744073709551615)) (SOff 13 0)) = (n - 8 + i) mod 2 ^ 64.
Proof.
intros E n i H13 H5 Hn Hi. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 13 i H13) by lia. rewrite (U_atom E 5 (8 - n) H5) by lia. rewrite U_SLit.
unfold zcanon, M64.
replace (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace ((8 - n) * (2 ^ 64 - 1)) with ((n - 8) + (8 - n) * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite Z.add_mod_idemp_l by lia. try (f_equal; lia).
Qed.
(* a0 = s2 + t2 = F + 32 + from *)
Lemma l2_Ds : forall E n i x, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> ew E 18 = w64 x ->
  0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i -> 0 <= x -> x + 8 <= 2 ^ 63 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit 18446744073709551615)) (SOff 13 0)) (SOff 18 0)) =
  Z_to_bv 64 (x + (n - 8 + i)).
Proof.
intros E n i x H13 H5 H18 Hn Hi Hf Hx Hx2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 18 x H18) by lia.
rewrite (l2_Uj2 E n i H13 H5 Hn Hi), (Z.mod_small (n - 8 + i)) by lia.
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.
Lemma l2_Dadd : forall E k m x y, ew E k = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff k 0) (SOff m 0)) = Z_to_bv 64 (x + y).
Proof.
intros E k m x y Hk Hm Hx Hy Hxy. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E k x Hk), (U_atom E m y Hm) by lia.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* a0 = t2 << 2 = 4 from, as the engine writes it *)
Lemma l2_U4j : forall E n i, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit 73786976294838206460)) (SAlu ALU_SLL (SOff 13 0) (SLit 2))) = 4 * (n - 8 + i).
Proof.
intros E n i H13 H5 Hn Hi Hf. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 13 i H13) by lia. rewrite (U_atom E 5 (8 - n) H5) by lia. rewrite !U_SLit.
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
unfold zcanon, M64.
replace (73786976294838206460 mod 2 ^ 64) with (2 ^ 64 - 4) by reflexivity.
replace ((8 - n) * (2 ^ 64 - 4)) with ((-4) * (8 - n) + (8 - n) * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (i * 4)) by lia. rewrite Z.add_mod_idemp_l by lia.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma l2_U4j2 : forall E n i, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> 0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit 18446744073709551612)) (SAlu ALU_SLL (SOff 13 0) (SLit 2))) = 4 * (n - 8 + i).
Proof.
intros E n i H13 H5 Hn Hi Hf. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 13 i H13) by lia. rewrite (U_atom E 5 (8 - n) H5) by lia. rewrite !U_SLit.
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
unfold zcanon, M64.
replace (18446744073709551612 mod 2 ^ 64) with (2 ^ 64 - 4) by reflexivity.
replace ((8 - n) * (2 ^ 64 - 4)) with ((-4) * (8 - n) + (8 - n) * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (i * 4)) by lia. rewrite Z.add_mod_idemp_l by lia.
rewrite Z.mod_small by lia. lia.
Qed.
(* a0 = s5 + 4 from = F + 64 + 4 from *)
Lemma l2_Dd : forall E n i x, ew E 13 = w64 i -> ew E 5 = w64 (8 - n) -> ew E 21 = w64 x ->
  0 <= n <= 8 -> 0 <= i < 8 -> 0 <= n - 8 + i -> 0 <= x -> x + 32 <= 2 ^ 63 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 5 0) (SLit 18446744073709551612))
    (SAlu ALU_SLL (SOff 13 0) (SLit 2))) (SOff 21 0)) = Z_to_bv 64 (x + 4 * (n - 8 + i)).
Proof.
intros E n i x H13 H5 H21 Hn Hi Hf Hx Hx2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 21 x H21) by lia. rewrite (l2_U4j2 E n i H13 H5 Hn Hi Hf).
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.
Lemma l2_mod64_32 : forall z, z mod 2 ^ 64 mod 2 ^ 32 = z mod 2 ^ 32.
Proof. intros z. Z.div_mod_to_equations. lia. Qed.
(* sllw t2,t1,a3 = 1 << i, i <= 6 *)
Lemma l2_U_sllw : forall E i, ew E 6 = w64 1 -> ew E 13 = w64 i -> 0 <= i <= 6 ->
  U E (SAluw ALU_SLL (SOff 6 0) (SOff 13 0)) = 2 ^ i.
Proof.
intros E i H6 H13 Hi. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite !U_SOff, H6, H13, !Z.add_0_r.
unfold w64. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !(Z.mod_small 1 (2 ^ 64)) by lia. rewrite !(Z.mod_small i (2 ^ 64)) by lia.
rewrite !(Z.mod_small 1 (2 ^ 32)) by lia. rewrite !(Z.mod_small i (2 ^ 32)) by lia.
assert (Hl : Z.land i 31 = i)
  by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; change (2 ^ 5) with 32; lia).
rewrite Hl, Z.shiftl_1_l.
assert (Hp : 0 < 2 ^ i <= 64) by (split; [apply Z.pow_pos_nonneg; lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
generalize dependent (2 ^ i). intros p Hp.
change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648 in *.
Z.div_mod_to_equations. lia.
Qed.
Lemma l2_lor_small : forall d i, 0 <= d < 128 -> 0 <= i <= 6 -> 0 <= Z.lor d (2 ^ i) < 128.
Proof.
intros d i Hd Hi.
assert (Hp : 0 < 2 ^ i <= 64) by (split; [apply Z.pow_pos_nonneg; lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor d (2 ^ i)) 0) as [E|E]; [rewrite E; lia|].
assert (Hpos : 0 < Z.lor d (2 ^ i)) by (pose proof (Z.lor_nonneg d (2 ^ i)); lia).
change 128 with (2 ^ 7). apply (Z.log2_lt_pow2 _ _ Hpos). rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia.
apply Z.max_lub_lt; [|lia].
destruct (Z.eq_dec d 0) as [->|Hd0]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 7) with 128. lia.
Qed.
(* or a0,a0,t2 *)
Lemma l2_D_or : forall E d i, ew E 40 = Z_to_bv 64 d -> ew E 6 = w64 1 -> ew E 13 = w64 i -> 0 <= d < 128 -> 0 <= i <= 6 ->
  sv_denot E (SAlu ALU_OR (SOff 40 0) (SAluw ALU_SLL (SOff 6 0) (SOff 13 0))) = Z_to_bv 64 (Z.lor d (2 ^ i)).
Proof.
intros E d i H40 H6 H13 Hd Hi. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (l2_U_sllw E i H6 H13 Hi), U_SOff, H40, Z.add_0_r.
rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
pose proof (l2_lor_small d i Hd Hi) as Hl.
rewrite !(Z.mod_small d (2 ^ 64)) by lia.
apply Z.mod_small. lia.
Qed.
(* the regions of the start state: the spills 40 .. 64 of s1, seg[i] (atom 35), dt (atom 39), dt's shadow byte
   (atom 41); with from >= 0 also s[from] (atom 36) and dot[from] (atom 37) *)
Definition l2_mem (b : bool) : smem :=
  [YP09.mkRegion (Some 9%nat) 40 64 40 40
     [YP09.mkChunk 40 (CVal 8 (SOff 39 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 43 0))];
   YP09.mkRegion (Some 35%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 39%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 40 0))];
   YP09.mkRegion (Some 41%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 42 0))]] ++
  (if b then [YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))];
              YP09.mkRegion (Some 37%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 38 0))]] else []).
Definition l2_af : list (nat * afact) :=
  [(32%nat, mkAF SB SB 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF 0 8 0); (13%nat, mkAF 0 7 0);
   (14%nat, mkAF 0 7 0); (5%nat, mkAF 0 8 0); (33%nat, mkAF 1 (2 ^ 47 - 9) 0); (34%nat, mkAF 0 127 0);
   (35%nat, mkAF 1 (2 ^ 47 - 2) 0); (36%nat, mkAF 0 (2 ^ 47 - 2) 0); (37%nat, mkAF 0 (2 ^ 47 - 8) 0);
   (38%nat, mkAF 0 1 0); (39%nat, mkAF 1 (2 ^ 47 - 2) 0); (40%nat, mkAF 0 127 0); (41%nat, mkAF SB (SB + 2 ^ 44 - 1) 0);
   (42%nat, mkAF 0 7 0); (43%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0)].

Ltac hX n := lazymatch goal with H : ew _ n = Z_to_bv 64 _ |- _ => rewrite H end.
Ltac hX_in n Hb := lazymatch goal with H : ew _ n = Z_to_bv 64 _ |- _ => rewrite H in Hb end.
(* the write windows of a digit: seg[i] (atom 35) and dt (atom 39), bytes of the write set *)
Ltac awr_l2 :=
  cbn [ss_mem];
  lazymatch goal with |- awr_ok ?Ev ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen;
    [ reflexivity | ewpeel; first [hX 35%nat | hX 39%nat]; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      lazymatch goal with Hp : oc_pre _ ?g, HJx : ajournal _ _ _ _ _ _ _ _ _ _ ((1, ?ps) :: _) ?l2 ?s2 ?w2 ?m2 ?d2 _,
        HPx : Permutation (ablocks _ ?l2 ?s2) _, Lx : AR_laws _ ?Bv |- _ =>
        apply (ocl_awr_wr Bv Lx g ps l2 s2 w2 m2 d2 a Hp HJx HPx); unfold oc_wr; lia end
    | ] ].
Ltac kwr_l2 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
          [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
            first [ exfalso; lia
                  | hX_in 35%nat Hb; rewrite unsigned_lit_small in Hb by lia; lia
                  | hX_in 39%nat Hb; rewrite unsigned_lit_small in Hb by lia; lia ] | ]);
  destruct Hr.


(* ---- list helpers ---- *)
Lemma l2_nth_set_ne : forall (sacc sj : list Z) (i j : nat) (v : Z), length sacc = i -> (length sj = 8)%nat ->
  (i < 8)%nat -> j <> i -> nth j (sacc ++ v :: skipn (S i) sj) 0 = nth j (sacc ++ skipn i sj) 0.
Proof.
intros sacc sj i j v Hl Hsj Hi Hj.
destruct (Nat.lt_ge_cases j i) as [Hlt | Hge].
- rewrite !app_nth1 by lia. reflexivity.
- rewrite !app_nth2 by lia. rewrite Hl.
  replace (j - i)%nat with (S (j - S i)) by lia. cbn [nth]. rewrite !nth_skipn.
  f_equal. lia.
Qed.
Lemma l2_nth_set_eq : forall (sacc sj : list Z) (i : nat) (v : Z), length sacc = i ->
  nth i (sacc ++ v :: skipn (S i) sj) 0 = v.
Proof. intros sacc sj i v Hl. rewrite app_nth2 by lia. rewrite Hl, Nat.sub_diag. reflexivity. Qed.
Lemma l2_len_set : forall (sacc sj : list Z) (i : nat) (v : Z), length sacc = i -> (length sj = 8)%nat -> (i < 8)%nat ->
  length (sacc ++ v :: skipn (S i) sj) = 8%nat.
Proof. intros sacc sj i v Hl Hsj Hi. rewrite length_app. cbn [length]. rewrite length_skipn. lia. Qed.
Lemma l2_len_base : forall (sacc sj : list Z) (i : nat), length sacc = i -> (length sj = 8)%nat -> (i < 8)%nat ->
  length (sacc ++ skipn i sj) = 8%nat.
Proof. intros sacc sj i Hl Hsj Hi. rewrite length_app, length_skipn. lia. Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the seg array after the store of v to seg[i] *)
Lemma l2_seg_after : forall g (W2 : world tfibsegs) mem2 mem3 i sacc v, oc_pre B g -> 0 <= i < 8 ->
  length sacc = Z.to_nat i ->
  garr8 tfibsegs (rd W2 mem2) (og_sg g) (sacc ++ skipn (Z.to_nat i) (og_sj g)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (a = og_sg g + i \/ a = og_dt g) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  val_mem tfibsegs (rd W2 mem3) (og_sg g + i) 1 v -> 0 <= v < 256 ->
  garr8 tfibsegs (rd W2 mem3) (og_sg g) ((sacc ++ [v]) ++ skipn (Z.to_nat (i + 1)) (og_sj g)).
Proof.
intros g W2 mem2 mem3 i sacc v Hpre Hi Hl Hseg KE Hv Hv8.
pose proof Hpre as (_ & _ & _ & _ & (Hsg0 & Hsg63 & _) & _ & Lsj & _ & _ & _ & Hd1 & _).
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite <- app_assoc. cbn [app].
intros k Hk. rewrite (l2_len_set sacc (og_sj g) (Z.to_nat i) v Hl Lsj ltac:(lia)) in Hk.
destruct (Nat.eq_dec k (Z.to_nat i)) as [-> | Hne].
- rewrite (l2_nth_set_eq sacc (og_sj g) (Z.to_nat i) v Hl). rewrite Z2Nat.id by lia. split; [exact Hv | lia].
- rewrite (l2_nth_set_ne sacc (og_sj g) (Z.to_nat i) k v Hl Lsj ltac:(lia) Hne).
  destruct (Hseg k ltac:(rewrite l2_len_base; [lia | exact Hl | exact Lsj | lia])) as (Vk & Rk). split; [|exact Rk].
  apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Vk].
  intros x Hx. cbn in Hx. apply KE; [lia|]. intros [Hx' | Hx']; [|lia].
  apply Hne. lia.
Qed.

(* the boundary at the end of a digit: the loop head 0x84764 (digit i + 1) or the exit 0x84840 *)
Lemma l2_close : forall g pos pc (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model ->
    world tfibsegs -> Prop) ly2 S2 regs2 mem2 md2 W2 ms md3 i,
  oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) -> ~ In (1, pos) (frames (og_Sc g)) ->
  same_io (og_mdc g) md2 -> mo_le MT (og_Sc g) S2 0 -> oc_common g pos regs2 mem2 W2 ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 (ms_mem ms) md3 (og_k g) ->
  same_io md2 md3 ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs) ->
  oc_kregs (ms_regs ms) regs2 -> 0 <= i < 8 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (a = og_sg g + i \/ a = og_dt g) ->
     aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a) ->
  P ly2 S2 (ms_regs ms) (ms_mem ms) md3 W2 ->
  oc_cut B MT g pos pc P W2 (mkCfg ms md3).
Proof.
intros g pos pc P ly2 S2 regs2 mem2 md2 W2 ms md3 i Hpre HJ HK HP Hni Hio Hmo HC HJ3 Hio3 Hms HR Hi KE KP HPk.
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (oc_zv g pos a \/ oc_wr g a) ->
  aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha Hz. apply KE; [exact Ha|]. intros [Ha' | Ha']; apply Hz; right; unfold oc_wr; lia. }
destruct (ocl_keep_w B LAWS g pos ly2 S2 regs2 mem2 md2 W2 (ms_mem ms) Hpre HJ HP HK HC KE2 KP) as (HK3 & HC3).
exists ly2, S2, (ms_regs ms), (ms_mem ms), md3.
split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|].
split; [exact HJ3|]. split; [exact HK3|]. split; [exact HP|]. split; [exact Hni|].
split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|].
split; [exact (oc_common_regs g pos regs2 (ms_regs ms) (ms_mem ms) W2 HR HC3)|].
exact HPk.
Qed.

(* the frame's arrays through a digit (it writes seg[i] and dt only) *)
Lemma l2_arrays : forall g pos ly2 S2 W2 mem2 md2 mem3 i n s dot, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) -> 0 <= i < 8 -> n <= 8 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (a = og_sg g + i \/ a = og_dt g) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  oc_arrays g pos W2 mem2 n s dot -> oc_arrays g pos W2 mem3 n s dot.
Proof.
intros g pos ly2 S2 W2 mem2 md2 mem3 i n s dot Hpre HJ HP Hi Hn KE Harr.
apply (ocl_arrays_kept g pos W2 W2 mem2 mem3 n s dot); [|exact Hn | exact Harr].
intros a Ha. destruct (ocl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & _ & HF0 & HFc & _).
pose proof alloc_ceiling_val as Hac.
apply KE; [lia|]. intros [Ha' | Ha'].
- assert (Hw : oc_wr g a) by (unfold oc_wr; left; lia).
  exact (proj1 (ocl_wr_off B LAWS g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Hw) Ha).
- assert (Hw : oc_wr g a) by (unfold oc_wr; right; lia).
  exact (proj1 (ocl_wr_off B LAWS g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Hw) Ha).
Qed.
End e.

(* ---- the second loop's step (ct2_go of lib/Spec/DgnLib.v) ---- *)
Lemma l2_ct2_neg : forall n s dot i k sg d, n - 8 + i < 0 ->
  ct2_go n s dot i (S k) sg d = ct2_go n s dot (i + 1) k (sg ++ [0]) d.
Proof.
intros n s dot i k sg d H. cbn [ct2_go]. replace (i - (8 - n)) with (n - 8 + i) by lia.
rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.leb_gt 0 _) H). reflexivity.
Qed.
Lemma l2_ct2_nodot : forall n s dot i k sg d, 0 <= n - 8 + i -> nth (Z.to_nat (n - 8 + i)) dot 0 = 0 ->
  ct2_go n s dot i (S k) sg d = ct2_go n s dot (i + 1) k (sg ++ [nth (Z.to_nat (n - 8 + i)) s 0]) d.
Proof.
intros n s dot i k sg d H H0. cbn [ct2_go]. replace (i - (8 - n)) with (n - 8 + i) by lia.
rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H), H0. reflexivity.
Qed.
Lemma l2_ct2_dot : forall n s dot i k sg d, 0 <= n - 8 + i -> nth (Z.to_nat (n - 8 + i)) dot 0 <> 0 ->
  ct2_go n s dot i (S k) sg d =
  if i =? 7 then (E_RANGE, sg ++ [nth (Z.to_nat (n - 8 + i)) s 0], d)
  else ct2_go n s dot (i + 1) k (sg ++ [nth (Z.to_nat (n - 8 + i)) s 0]) (Z.lor d (2 ^ i)).
Proof.
intros n s dot i k sg d H H0. cbn [ct2_go]. replace (i - (8 - n)) with (n - 8 + i) by lia.
rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H), (proj2 (Z.eqb_neq _ _) H0). reflexivity.
Qed.
(* a 1-byte chunk of the state's region based at atom nb, offset 0 *)
Ltac l2_chunk1 nb base e v Hn :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
    let ix := oc_ridx HS nb in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) ix _ HS eq_refl) as HR;
    cbn [ms_mem restrict] in HR;
    lazymatch type of HR with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR end;
    pose proof (field_of_region _ _ nb base _ _ _ _ _ 0 1%N e v HR
      ltac:(ewpeel; lazymatch goal with H : ew _ nb = Z_to_bv 64 base |- _ => rewrite H end; apply unsigned_lit_small; lia)
      ltac:(oc_in) ltac:(first [rewrite sv_denot_SOff0; ewpeel; assumption | reflexivity | assumption])
      ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(cbn; lia)) as Hn;
    rewrite Z.add_0_r in Hn; change (N.to_nat 1) with 1%nat in Hn; clear HR end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem oc_l2_holds : oc_seg_L2 B MT RLO RHI GLYPHA ROSTRS.
Proof.
unfold oc_seg_L2. intros g pos kk W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (i & n & d & s & dot & sacc & R13 & R14 & R15 & R16 & R17 & R5 & R6 & R11 & R12 & R19 & Hkk & Hi & Hspec &
  Hl1 & Hsacl & Hsacc & Hd128 & Harr & Hseg & Hdv).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ocl_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ocl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & V40 & V48 & V56 & _ & _ & Hsh).
pose proof Hpre as (_ & _ & _ & _ & Hsg & _ & Lsj & _ & Hdt & _).
pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & Hsgra & Hdtra & _).
pose proof Hl1 as ((Hn0 & Hdl & Hdz) & Hd01 & Hsl & Hs128).
pose proof alloc_ceiling_val as Hac.
set (F := og_F g pos) in *.
assert (HFa : frame_addr (og_lyc g) 1 pos = F) by reflexivity.
assert (HF8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8. lia. }
assert (Hdtb : 0 < og_dt g /\ og_dt g + 1 <= 2 ^ 63 /\ amem_range (og_dt g) 1)
  by (destruct Hdt as [((Hx0 & Hx1 & _ & _ & _ & _ & Ham & _) & _) | (Hx0 & Hx1 & _ & _ & _ & _ & _ & Ham & _)];
      (split; [|split]; assumption)).
destruct Hdtb as (Hdt0 & Hdt63 & Hdtam).
assert (Hdt47 : og_dt g + 2 <= 2 ^ 47) by (pose proof Hdtam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
pose proof Hsg as (Hsg0 & Hsg63 & _ & _ & _ & _ & Hsgam & _).
assert (Hsg47 : og_sg g + 9 <= 2 ^ 47) by (pose proof Hsgam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
  unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
unfold TB_owed_counter_text, ESTACK in *.
destruct (Hdtra (og_dt g) ltac:(lia)) as (kd & Hkd & Hkok). unfold shadow_of_addr in Hkd. rewrite <- SB_SHADOW_OFF in Hkd.
assert (Hkd7 : 0 <= kd < 8) by (destruct Hkok as [-> | (? & ?)]; [lia | pose proof (Z.mod_pos_bound (og_dt g) 8 ltac:(lia)); lia]).
assert (Hkok2 : kd <> 0 -> og_dt g mod 8 < kd) by (intros Hk0; destruct Hkok as [Hk1 | (Hk1 & _)]; [lia | exact Hk1]).
clear Hkok.
assert (Hdt8 : 0 <= og_dt g / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
set (j := n - 8 + i).
assert (Hj : -8 <= j < n) by (unfold j; lia).
destruct (Z.leb_spec 0 j) as [Hj0 | Hj0].
- (* from >= 0 *)
  set (sv := nth (Z.to_nat j) s 0). set (dvj := nth (Z.to_nat j) dot 0).
  assert (Hsv : 0 <= sv <= 127).
  { assert (Hin : In sv s) by (apply nth_In; lia). rewrite Forall_forall in Hs128. pose proof (Hs128 _ Hin). lia. }
  assert (Hdvj : 0 <= dvj <= 1).
  { assert (Hin : In dvj dot) by (apply nth_In; lia). rewrite Forall_forall in Hd01. exact (Hd01 _ Hin). }
  assert (Vs : val_mem tfibsegs (mrestrict (w_H W2) mem2) (F + 32 + j) 1 sv) by exact (proj2 Harr j ltac:(lia)).
  assert (Vd : val_mem tfibsegs (mrestrict (w_H W2) mem2) (F + 64 + 4 * j) 4 dvj) by exact (proj1 Harr j ltac:(lia)).
  set (xs := [og_sg g; sv; og_sg g + i; F + 32 + j; F + 64 + 4 * j; dvj; og_dt g; d; SB + og_dt g / 8; kd;
              onot (F + 32)]).
  remember (Ereg regs2 (cw_extra xs)) as E eqn:HEE.
  assert (EW : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
    by (intros k r Hk; subst E; exact (ew_Ereg_nat regs2 _ k r Hk)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (X33 : ew E 33 = Z_to_bv 64 (og_sg g)) by (subst E; exact (cw_ew_x regs2 xs 0)).
  assert (X34 : ew E 34 = Z_to_bv 64 sv) by (subst E; exact (cw_ew_x regs2 xs 1)).
  assert (X35 : ew E 35 = Z_to_bv 64 (og_sg g + i)) by (subst E; exact (cw_ew_x regs2 xs 2)).
  assert (X36 : ew E 36 = Z_to_bv 64 (F + 32 + j)) by (subst E; exact (cw_ew_x regs2 xs 3)).
  assert (X37 : ew E 37 = Z_to_bv 64 (F + 64 + 4 * j)) by (subst E; exact (cw_ew_x regs2 xs 4)).
  assert (X38 : ew E 38 = Z_to_bv 64 dvj) by (subst E; exact (cw_ew_x regs2 xs 5)).
  assert (X39 : ew E 39 = Z_to_bv 64 (og_dt g)) by (subst E; exact (cw_ew_x regs2 xs 6)).
  assert (X40 : ew E 40 = Z_to_bv 64 d) by (subst E; exact (cw_ew_x regs2 xs 7)).
  assert (X41 : ew E 41 = Z_to_bv 64 (SB + og_dt g / 8)) by (subst E; exact (cw_ew_x regs2 xs 8)).
  assert (X42 : ew E 42 = Z_to_bv 64 kd) by (subst E; exact (cw_ew_x regs2 xs 9)).
  assert (X43 : ew E 43 = Z_to_bv 64 (onot (F + 32))) by (subst E; exact (cw_ew_x regs2 xs 10)).
  assert (E9 : ew E 9 = w64 (og_sp1 g)) by (rewrite (EW 9%nat 9%bv eq_refl); exact R9).
  assert (E13 : ew E 13 = w64 i) by (rewrite (EW 13%nat 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 i) by (rewrite (EW 14%nat 14%bv eq_refl); exact R14).
  assert (E5 : ew E 5 = w64 (8 - n)) by (rewrite (EW 5%nat 5%bv eq_refl); exact R5).
  assert (E19 : ew E 19 = w64 n) by (rewrite (EW 19%nat 19%bv eq_refl); exact R19).
  assert (E6 : ew E 6 = w64 1) by (rewrite (EW 6%nat 6%bv eq_refl); exact R6).
  assert (E12 : ew E 12 = w64 (og_dt g mod 8)) by (rewrite (EW 12%nat 12%bv eq_refl); exact R12).
  assert (E15 : ew E 15 = w64 8) by (rewrite (EW 15%nat 15%bv eq_refl); exact R15).
  assert (E16 : ew E 16 = w64 (onot (og_sg g))) by (rewrite (EW 16%nat 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 7) by (rewrite (EW 17%nat 17%bv eq_refl); exact R17).
  assert (E18 : ew E 18 = w64 (F + 32)) by (rewrite (EW 18%nat 18%bv eq_refl); exact R18).
  assert (E21 : ew E 21 = w64 (F + 64)) by (rewrite (EW 21%nat 21%bv eq_refl); exact R21).
  assert (E27 : ew E 27 = w64 (onot (F + 64))) by (rewrite (EW 27%nat 27%bv eq_refl); exact R27).
  assert (U9 : bv_unsigned (ew E 9) = og_sp1 g) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = og_sg g + i) by (rewrite X35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = F + 32 + j) by (rewrite X36; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = F + 64 + 4 * j) by (rewrite X37; apply unsigned_lit_small; lia).
  assert (U39 : bv_unsigned (ew E 39) = og_dt g) by (rewrite X39; apply unsigned_lit_small; lia).
  assert (U41 : bv_unsigned (ew E 41) = SB + og_dt g / 8) by (rewrite X41; apply unsigned_lit_small; unfold SB; lia).
  assert (Wsg : oc_wr g (og_sg g + i)) by (unfold oc_wr; left; lia).
  assert (Wdt : oc_wr g (og_dt g)) by (unfold oc_wr; right; lia).
  assert (YS : st_ok tfibsegs E (mkSS PC_L2 sr_atoms (l2_mem true) None (mkFacts l2_af [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_L2) mem2 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
    - apply regs_ok_Ereg.
    - reflexivity.
    - unfold l2_mem. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil;
      unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9, ?U35, ?U36, ?U37, ?U39, ?U41.
      + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 40 8 (SOff 39 0) (og_dt g));
          [rewrite sv_denot_SOff0; exact X39 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V40].
        * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 48 8 (SOff 33 0) (og_sg g));
          [rewrite sv_denot_SOff0; exact X33 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V48].
        * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 56 8 (SOff 43 0) (onot (F + 32)));
          [rewrite sv_denot_SOff0; exact X43 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold onot; lia | cbn; lia | exact V56].
      + split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. replace (og_sg g + i + o) with (og_sg g + i) by lia. apply (YCbq.apresent_writable tfibsegs).
        exact (ocl_present B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP HK Wsg).
      + split; [lia|]. split; [lia|]. split.
        * intros o Ho. replace (og_dt g + o) with (og_dt g) by lia. apply (YCbq.apresent_writable tfibsegs).
          exact (ocl_present B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP HK Wdt).
        * apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val tfibsegs _ _ (og_dt g) 0 1 (SOff 40 0) d);
          [rewrite sv_denot_SOff0; exact X40 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | rewrite Z.add_0_r; exact Hdv].
      + unfold SB in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs _ _ (SB + og_dt g / 8) 0 1 (SOff 42 0) kd);
        [rewrite sv_denot_SOff0; exact X42 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (oc_vm1_of_aview _ _ _ _ Hkd).
      + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs _ _ (F + 32 + j) 0 1 (SOff 34 0) sv);
        [rewrite sv_denot_SOff0; exact X34 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | rewrite Z.add_0_r; exact Vs].
      + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs _ _ (F + 64 + 4 * j) 0 4 (SOff 38 0) dvj);
        [rewrite sv_denot_SOff0; exact X38 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vd].
    - pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd1 & _).
    destruct (ocl_wr_off B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP Wsg) as (Osg1 & Osg2 & Osg3).
    destruct (ocl_wr_off B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP Wdt) as (Odt1 & Odt2 & Odt3).
    unfold TB_owed_counter_text, ESTACK in Osg3, Odt3.
    assert (Hsgapp : og_sg g + 8 <= SB - 1 \/ SB + 2 ^ 44 <= og_sg g)
      by (pose proof Hsgam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
          unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; unfold SB; lia).
    assert (Hdtapp : og_dt g + 1 <= SB - 1 \/ SB + 2 ^ 44 <= og_dt g)
      by (pose proof Hdtam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
          unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; unfold SB; lia).
    assert (HFapp' : F + 128 <= SB - 4096 \/ SB + 2 ^ 44 <= F)
      by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; unfold SB; lia).
      apply pairwise_disjoint_of_extents. unfold l2_mem, extent_of_region. cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U9, U35, ?U36, ?U37, U39, U41. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold SB in *. repeat split;
      first [ exact I
            | solve [clear - Hsp1 Osg3; lia] | solve [clear - Hsp1 Odt3; lia] | solve [clear - Hsp1 H46 Hdt8; lia]
            | solve [clear - Hsp1 Hceil HFc Hj Hj0 Hn0; lia] | solve [clear - Hd1 Hi; lia] | solve [clear - Hsgapp Hi Hdt8; lia]
            | solve [clear - Osg1 Hj Hj0 Hn0; lia] | solve [clear - Hdtapp Hdt8; lia] | solve [clear - Odt1 Hj Hj0 Hn0; lia]
            | solve [clear - HFapp' Hdt8 Hj Hj0 Hn0; lia] | solve [clear - Hj Hj0 Hn0; lia] ].
    - split; [|split; exact I]. cbn [f_atoms atoms_ok l2_af]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, U9, E19, E13, E14, E5, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43. unfold w64.
      clear - Hsg0 Hsg47 Hsv Hdvj Hdt0 Hdt47 Hd128 Hkd7 Hdt8 Hi Hn0 Hj0 Hj HF0 HFc Hac Hsp1 Hsp1a H46 H47.
      rewrite !unsigned_lit_small by (unfold SB, onot; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, onot. repeat split; first [exact I | exact Hsp1a | lia]. }
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (23%bv : bv 5) (SOff 32 0) YS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, R23; reflexivity)) as HS.
  clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (11%bv : bv 5) (SOff 41 0) HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, X41, R11; reflexivity)) as YS.
  clear HS. rename YS into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 35 0 1; mkSHE 39 0 1; mkSHE 37 0 4] E (mrestrict (w_H W2) mem2)).
  { repeat apply Forall_cons; try apply Forall_nil.
    - apply (cw_shent_ra W2 mem2 E 35 (og_sg g + i) 1); [| | lia | lia | lia | exact X35 | exact E32].
      + eapply range_addressable_sub; [exact Hsgra | lia | lia].
      + pose proof Hsgam as Ham. unfold amem_range in Ham |- *. rewrite ?C3, ?C4, ?C5 in Ham |- *.
        unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham |- *. lia.
    - apply (cw_shent_ra W2 mem2 E 39 (og_dt g) 1); [exact Hdtra | exact Hdtam | lia | lia | lia | exact X39 | exact E32].
    - apply (cw_shent_ra W2 mem2 E 37 (F + 64 + 4 * j) 4);
      [ replace (F + 64 + 4 * j) with (F + (64 + 4 * j)) by lia;
        apply ocl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | right; lia | exact Hsh]
      | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite ?C3, ?C4, ?C5 in *;
        unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
      | lia | lia | lia | exact X37 | exact E32 ]. }
  cw_keep_j0 HJ HJ0.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = og_sg g + i \/ a = og_dt g) ->
    aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
  assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
  unfold cfg_at. change (w64 PC_L2) with (Z_to_bv 64 PC_L2).
  cw_run awr_l2. ctk_keep kwr_l2.
  cw_branch Hc1.
  { exfalso. lazymatch type of Hc1 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite (l2_bltzj Ec n i ltac:(ewpeel; exact E13) ltac:(ewpeel; exact E5) ltac:(lia) ltac:(lia)) in Hc1 end.
    apply Z.ltb_lt in Hc1. lia. }
  (* bltu a7,t2 (0x84774) -> the trap *)
  cw_run awr_l2. ctk_keep kwr_l2.
  cw_branch Hc2.
  { exfalso. lazymatch type of Hc2 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite (l2_bltu_j Ec 17 7 n i ltac:(ewpeel; exact E17) ltac:(ewpeel; exact E13) ltac:(ewpeel; exact E5)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hc2 end. discriminate Hc2. }
  (* bltu a0,t2 (0x8477c), a0 = ~(F + 32) -> the trap *)
  cw_run awr_l2. ctk_keep kwr_l2.
  cw_branch Hc3.
  { exfalso. lazymatch type of Hc3 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite (l2_bltu_j Ec 43 (onot (F + 32)) n i ltac:(ewpeel; exact X43) ltac:(ewpeel; exact E13) ltac:(ewpeel; exact E5)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold onot; lia)) in Hc3 end. discriminate Hc3. }
  cw_run_to awr_l2 0x84784. ctk_keep kwr_l2.
  (* a0 = F + 32 + from: atom 36 *)
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
    pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 36 0) HS eq_refl
      ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite X36; symmetry;
            replace (F + 32 + j) with (F + 32 + (n - 8 + i)) by (unfold j; lia);
            apply (l2_Ds Ev n i (F + 32)); [ewpeel; exact E13 | ewpeel; exact E5 | ewpeel; exact E18 | lia | lia | lia | lia | lia]))
      as YS end.
  clear HS. rename YS into HS. norm_ss HS.
  cw_run awr_l2. ctk_keep kwr_l2.
  (* bltu a6,a4 (0x84788): ~sg against i -> the trap *)
  cw_branch Hc4.
  { exfalso. lazymatch type of Hc4 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite branch_ltu_U, (U_atom Ec 16 (onot (og_sg g))), (U_atom Ec 14 i) in Hc4
        by (first [ewpeel; first [exact E16 | exact E14] | unfold onot; lia | lia]) end.
    apply Z.ltb_lt in Hc4. unfold onot in Hc4. lia. }
  cw_run_to awr_l2 0x847a0. ctk_keep kwr_l2.
  (* a0 = sg + i: atom 35 *)
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
    pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 35 0) HS eq_refl
      ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite X35; symmetry;
            rewrite Z.add_comm; apply (l2_Dadd Ev 14 33 i (og_sg g)); [ewpeel; exact E14 | ewpeel; exact X33 | lia | lia | lia]))
      as YS end.
  clear HS. rename YS into HS. norm_ss HS.
  cw_run awr_l2. ctk_keep kwr_l2.
  (* bltu s11,a0 (0x847bc): ~(F + 64) against 4 from -> the trap *)
  cw_branch Hc5.
  { exfalso. lazymatch type of Hc5 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite branch_ltu_U, (U_atom Ec 27 (onot (F + 64))), (l2_U4j Ec n i) in Hc5
        by (first [ewpeel; first [exact E27 | exact E13 | exact E5] | unfold onot; lia | lia]) end.
    apply Z.ltb_lt in Hc5. unfold onot in Hc5. lia. }
  cw_run_to awr_l2 0x847c4. ctk_keep kwr_l2.
  (* a0 = F + 64 + 4 from: atom 37 *)
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
    pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 37 0) HS eq_refl
      ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite X37; symmetry;
            replace (F + 64 + 4 * j) with (F + 64 + 4 * (n - 8 + i)) by (unfold j; lia);
            apply (l2_Dd Ev n i (F + 64)); [ewpeel; exact E13 | ewpeel; exact E5 | ewpeel; exact E21 | lia | lia | lia | lia | lia]))
      as YS end.
  clear HS. rename YS into HS. norm_ss HS.
  cw_run awr_l2. ctk_keep kwr_l2.
  (* beqz a0 (0x847d8): dot[from] *)
  cw_branch Hc6.
  all: rewrite branch_eq_U, (U_atom _ 38 dvj) in Hc6 by (first [ewpeel; exact X38 | lia]); rewrite U_lit in Hc6 by lia.
  + (* clear: the next digit *)
    apply Z.eqb_eq in Hc6.
    cw_run awr_l2. ctk_keep kwr_l2.
    cw_branch Hc7.
    all: rewrite branch_ne_U, (U_atom_off _ 14 i 1), (U_atom _ 15 8) in Hc7 by (first [ewpeel; first [exact E14 | exact E15] | lia]).
    * (* i + 1 <> 8: back to the head *)
      apply negb_true_iff, Z.eqb_neq in Hc7.
      destruct kk as [|kk]; [exfalso; lia|].
      cw_run_to awr_l2 PC_L2. ctk_keep kwr_l2.
      l2_chunk1 35%nat (og_sg g + i) (SOff 34 0) sv Vseg.
      l2_chunk1 39%nat (og_dt g) (SOff 40 0) d Vdt.
      apply SRr_ret. cbv beta. left.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (l2_close B MT LAWS g pos PC_L2 (P_L2 g pos (S kk)) ly2 S2 regs2 mem2 md2 W2 msv _ i Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac | lia | exact KE | exact KP | ] end.
      exists (i + 1), n, d, s, dot, (sacc ++ [sv]).
      split; [reg_off E13 i 1|]. split; [reg_off E14 i 1|]. split; [reg_atom E15|]. split; [reg_atom E16|].
      split; [reg_atom E17|]. split; [reg_atom E5|]. split; [reg_atom E6|]. split; [reg_atom X41|]. split; [reg_atom E12|].
      split; [reg_atom E19|]. split; [lia|]. split; [lia|].
      split; [rewrite Hspec, (l2_ct2_nodot n s dot i (S kk) sacc d) by (fold j; first [lia | exact Hc6]); reflexivity|].
      split; [exact Hl1|]. split; [rewrite length_app, Hsacl; cbn [length]; lia|].
      split; [apply Forall_app; split; [exact Hsacc | constructor; [lia | constructor]]|]. split; [lia|].
      split; [eapply (l2_arrays B LAWS g pos ly2 S2 W2 mem2 md2 _ i n s dot Hpre HJ0 HP ltac:(lia) ltac:(lia) KE Harr)|].
      split; [exact (l2_seg_after B g W2 mem2 _ i sacc sv Hpre ltac:(lia) Hsacl Hseg KE Vseg ltac:(lia))|].
      exact Vdt.
    * (* i = 7: the end, a0 = 0 *)
      apply negb_false_iff, Z.eqb_eq in Hc7. assert (Hi7 : i = 7) by lia. subst i.
      assert (Hk0 : kk = 0%nat) by lia. subst kk.
      cw_run_to awr_l2 PC_X. ctk_keep kwr_l2.
      l2_chunk1 35%nat (og_sg g + 7) (SOff 34 0) sv Vseg.
      l2_chunk1 39%nat (og_dt g) (SOff 40 0) d Vdt.
      apply SRr_ret. cbv beta. right.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (l2_close B MT LAWS g pos PC_X (P_X g) ly2 S2 regs2 mem2 md2 W2 msv _ 7 Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac | lia | exact KE | exact KP | ] end.
      assert (Hres : owed_counter_text_spec (og_tb g) = (0, sacc ++ [sv], d))
        by (rewrite Hspec, (l2_ct2_nodot n s dot 7 0 sacc d) by (fold j; first [lia | exact Hc6]); reflexivity).
      unfold P_X, oc_res. rewrite Hres.
      split; [rv0; reflexivity|].
      split; [intros _; split; [|exact Vdt]|intros Hr; exfalso; exact (Hr eq_refl)].
      pose proof (l2_seg_after B g W2 mem2 _ 7 sacc sv Hpre ltac:(lia) Hsacl Hseg KE Vseg ltac:(lia)) as G.
      rewrite skipn_all2 in G by (rewrite Lsj; lia). rewrite app_nil_r in G. exact G.
  + (* set *)
    apply Z.eqb_neq in Hc6.
    cw_run awr_l2. ctk_keep kwr_l2.
    (* beq a4,a7 (0x847dc): digit 7 *)
    cw_branch Hc7.
    all: rewrite branch_eq_U, (U_atom _ 14 i), (U_atom _ 17 7) in Hc7 by (first [ewpeel; first [exact E14 | exact E17] | lia]).
    * (* digit 7 with a dot: E_RANGE *)
      apply Z.eqb_eq in Hc7. subst i.
      cw_run_to awr_l2 PC_X. ctk_keep kwr_l2.
      l2_chunk1 35%nat (og_sg g + 7) (SOff 34 0) sv Vseg.
      l2_chunk1 39%nat (og_dt g) (SOff 40 0) d Vdt.
      apply SRr_ret. cbv beta. right.
      lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (l2_close B MT LAWS g pos PC_X (P_X g) ly2 S2 regs2 mem2 md2 W2 msv _ 7 Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac | lia | exact KE | exact KP | ] end.
      assert (Hres : owed_counter_text_spec (og_tb g) = (E_RANGE, sacc ++ [sv], d))
        by (rewrite Hspec, (l2_ct2_dot n s dot 7 kk sacc d) by (fold j; first [lia | exact Hc6]); reflexivity).
      unfold P_X, oc_res. rewrite Hres.
      split; [rv0; unfold E_RANGE, w64; cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
      split; [intros Hr; exfalso; unfold E_RANGE in Hr; lia|].
      intros _. exists (sacc ++ [sv]), d.
      pose proof (l2_seg_after B g W2 mem2 _ 7 sacc sv Hpre ltac:(lia) Hsacl Hseg KE Vseg ltac:(lia)) as G.
      rewrite skipn_all2 in G by (rewrite Lsj; lia). rewrite app_nil_r in G.
      split; [exact G|]. split; [rewrite length_app, Hsacl; reflexivity | exact Vdt].
    * (* digit i < 7 with a dot: bit i of dt *)
      apply Z.eqb_neq in Hc7.
      cw_run awr_l2. ctk_keep kwr_l2.
      (* bnez a0 (0x847e4): dt's shadow byte *)
      cw_branch Hc8.
      all: rewrite branch_ne_U, (U_atom _ 42 kd), U_lit in Hc8 by (first [ewpeel; exact X42 | lia]).
      -- (* not 0: blt a2,a0 (0x84828) *)
         apply negb_true_iff, Z.eqb_neq in Hc8.
         cw_run awr_l2. ctk_keep kwr_l2.
         cw_branch Hc9.
         all: lazymatch type of Hc9 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
           rewrite (oc_blt_small Ec _ _ (og_dt g mod 8) kd) in Hc9;
           [ | apply (U_atom Ec 12 (og_dt g mod 8)); [ewpeel; exact E12 | pose proof (Z.mod_pos_bound (og_dt g) 8 ltac:(lia)); lia]
             | apply (U_atom Ec 42 kd); [ewpeel; exact X42 | lia]
             | pose proof (Z.mod_pos_bound (og_dt g) 8 ltac:(lia)); lia | lia ] end.
         ++ cw_run awr_l2. ctk_keep kwr_l2.
   (* bne a4,a5 (0x84804) after dt |= 1 << i: back to the head *)
            cw_branch Hc10.
            all: rewrite branch_ne_U, (U_atom_off _ 14 i 1), (U_atom _ 15 8) in Hc10 by (first [ewpeel; first [exact E14 | exact E15] | lia]).
            2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hc10. lia. }
            destruct kk as [|kk]; [exfalso; lia|].
            cw_run_to awr_l2 PC_L2. ctk_keep kwr_l2.
            l2_chunk1 35%nat (og_sg g + i) (SOff 34 0) sv Vseg.
            assert (Hdo : 0 <= Z.lor d (2 ^ i) < 128) by (apply l2_lor_small; lia).
            lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
              let ix := oc_ridx HS 39%nat in
              let HR := fresh "HR" in
              pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) ix _ HS eq_refl) as HR;
              cbn [ms_mem restrict] in HR;
              lazymatch type of HR with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR end;
              pose proof (field_of_region _ _ 39 (og_dt g) _ _ _ _ _ 0 1%N _ (Z.lor d (2 ^ i)) HR
                ltac:(ewpeel; rewrite X39; apply unsigned_lit_small; lia) ltac:(oc_in)
                ltac:(apply (l2_D_or Ev d i); [ewpeel; exact X40 | ewpeel; exact E6 | ewpeel; exact E13 | lia | lia])
                ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(cbn; lia)) as Vdt;
              rewrite Z.add_0_r in Vdt; change (N.to_nat 1) with 1%nat in Vdt; clear HR end.
            apply SRr_ret. cbv beta. left.
            lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
              apply (l2_close B MT LAWS g pos PC_L2 (P_L2 g pos (S kk)) ly2 S2 regs2 mem2 md2 W2 msv _ i Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
              [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac | lia | exact KE | exact KP | ] end.
            exists (i + 1), n, (Z.lor d (2 ^ i)), s, dot, (sacc ++ [sv]).
            split; [reg_off E13 i 1|]. split; [reg_off E14 i 1|]. split; [reg_atom E15|]. split; [reg_atom E16|].
            split; [reg_atom E17|]. split; [reg_atom E5|]. split; [reg_atom E6|]. split; [reg_atom X41|]. split; [reg_atom E12|].
            split; [reg_atom E19|]. split; [lia|]. split; [lia|].
            split; [rewrite Hspec, (l2_ct2_dot n s dot i (S kk) sacc d) by (fold j; first [lia | exact Hc6]);
                    rewrite (proj2 (Z.eqb_neq i 7) Hc7); reflexivity|].
            split; [exact Hl1|]. split; [rewrite length_app, Hsacl; cbn [length]; lia|].
            split; [apply Forall_app; split; [exact Hsacc | constructor; [lia | constructor]]|]. split; [lia|].
            split; [eapply (l2_arrays B LAWS g pos ly2 S2 W2 mem2 md2 _ i n s dot Hpre HJ0 HP ltac:(lia) ltac:(lia) KE Harr)|].
            split; [exact (l2_seg_after B g W2 mem2 _ i sacc sv Hpre ltac:(lia) Hsacl Hseg KE Vseg ltac:(lia))|].
            exact Vdt.
         ++ exfalso. apply Z.ltb_ge in Hc9. pose proof (Hkok2 Hc8). lia.
      -- apply negb_false_iff, Z.eqb_eq in Hc8.
         cw_run awr_l2. ctk_keep kwr_l2.
         (* bne a4,a5 (0x84804) after dt |= 1 << i: back to the head *)
         cw_branch Hc10.
         all: rewrite branch_ne_U, (U_atom_off _ 14 i 1), (U_atom _ 15 8) in Hc10 by (first [ewpeel; first [exact E14 | exact E15] | lia]).
         2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hc10. lia. }
         destruct kk as [|kk]; [exfalso; lia|].
         cw_run_to awr_l2 PC_L2. ctk_keep kwr_l2.
         l2_chunk1 35%nat (og_sg g + i) (SOff 34 0) sv Vseg.
         assert (Hdo : 0 <= Z.lor d (2 ^ i) < 128) by (apply l2_lor_small; lia).
         lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
           let ix := oc_ridx HS 39%nat in
           let HR := fresh "HR" in
           pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) ix _ HS eq_refl) as HR;
           cbn [ms_mem restrict] in HR;
           lazymatch type of HR with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in HR end;
           pose proof (field_of_region _ _ 39 (og_dt g) _ _ _ _ _ 0 1%N _ (Z.lor d (2 ^ i)) HR
             ltac:(ewpeel; rewrite X39; apply unsigned_lit_small; lia) ltac:(oc_in)
             ltac:(apply (l2_D_or Ev d i); [ewpeel; exact X40 | ewpeel; exact E6 | ewpeel; exact E13 | lia | lia])
             ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(cbn; lia)) as Vdt;
           rewrite Z.add_0_r in Vdt; change (N.to_nat 1) with 1%nat in Vdt; clear HR end.
         apply SRr_ret. cbv beta. left.
         lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
           apply (l2_close B MT LAWS g pos PC_L2 (P_L2 g pos (S kk)) ly2 S2 regs2 mem2 md2 W2 msv _ i Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
           [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac | lia | exact KE | exact KP | ] end.
         exists (i + 1), n, (Z.lor d (2 ^ i)), s, dot, (sacc ++ [sv]).
         split; [reg_off E13 i 1|]. split; [reg_off E14 i 1|]. split; [reg_atom E15|]. split; [reg_atom E16|].
         split; [reg_atom E17|]. split; [reg_atom E5|]. split; [reg_atom E6|]. split; [reg_atom X41|]. split; [reg_atom E12|].
         split; [reg_atom E19|]. split; [lia|]. split; [lia|].
         split; [rewrite Hspec, (l2_ct2_dot n s dot i (S kk) sacc d) by (fold j; first [lia | exact Hc6]);
                 rewrite (proj2 (Z.eqb_neq i 7) Hc7); reflexivity|].
         split; [exact Hl1|]. split; [rewrite length_app, Hsacl; cbn [length]; lia|].
         split; [apply Forall_app; split; [exact Hsacc | constructor; [lia | constructor]]|]. split; [lia|].
         split; [eapply (l2_arrays B LAWS g pos ly2 S2 W2 mem2 md2 _ i n s dot Hpre HJ0 HP ltac:(lia) ltac:(lia) KE Harr)|].
         split; [exact (l2_seg_after B g W2 mem2 _ i sacc sv Hpre ltac:(lia) Hsacl Hseg KE Vseg ltac:(lia))|].
         exact Vdt.
- (* from < 0: digit i takes 0 *)
  set (xs := [og_sg g; 0; og_sg g + i; F + 32 + 0; F + 64 + 4 * 0; 0; og_dt g; d; SB + og_dt g / 8; kd;
              onot (F + 32)]).
  remember (Ereg regs2 (cw_extra xs)) as E eqn:HEE.
  assert (EW : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs2 r)
    by (intros k r Hk; subst E; exact (ew_Ereg_nat regs2 _ k r Hk)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (X33 : ew E 33 = Z_to_bv 64 (og_sg g)) by (subst E; exact (cw_ew_x regs2 xs 0)).
  assert (X34 : ew E 34 = Z_to_bv 64 0) by (subst E; exact (cw_ew_x regs2 xs 1)).
  assert (X35 : ew E 35 = Z_to_bv 64 (og_sg g + i)) by (subst E; exact (cw_ew_x regs2 xs 2)).
  assert (X36 : ew E 36 = Z_to_bv 64 (F + 32 + 0)) by (subst E; exact (cw_ew_x regs2 xs 3)).
  assert (X37 : ew E 37 = Z_to_bv 64 (F + 64 + 4 * 0)) by (subst E; exact (cw_ew_x regs2 xs 4)).
  assert (X38 : ew E 38 = Z_to_bv 64 0) by (subst E; exact (cw_ew_x regs2 xs 5)).
  assert (X39 : ew E 39 = Z_to_bv 64 (og_dt g)) by (subst E; exact (cw_ew_x regs2 xs 6)).
  assert (X40 : ew E 40 = Z_to_bv 64 d) by (subst E; exact (cw_ew_x regs2 xs 7)).
  assert (X41 : ew E 41 = Z_to_bv 64 (SB + og_dt g / 8)) by (subst E; exact (cw_ew_x regs2 xs 8)).
  assert (X42 : ew E 42 = Z_to_bv 64 kd) by (subst E; exact (cw_ew_x regs2 xs 9)).
  assert (X43 : ew E 43 = Z_to_bv 64 (onot (F + 32))) by (subst E; exact (cw_ew_x regs2 xs 10)).
  assert (E9 : ew E 9 = w64 (og_sp1 g)) by (rewrite (EW 9%nat 9%bv eq_refl); exact R9).
  assert (E13 : ew E 13 = w64 i) by (rewrite (EW 13%nat 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = w64 i) by (rewrite (EW 14%nat 14%bv eq_refl); exact R14).
  assert (E5 : ew E 5 = w64 (8 - n)) by (rewrite (EW 5%nat 5%bv eq_refl); exact R5).
  assert (E19 : ew E 19 = w64 n) by (rewrite (EW 19%nat 19%bv eq_refl); exact R19).
  assert (E6 : ew E 6 = w64 1) by (rewrite (EW 6%nat 6%bv eq_refl); exact R6).
  assert (E12 : ew E 12 = w64 (og_dt g mod 8)) by (rewrite (EW 12%nat 12%bv eq_refl); exact R12).
  assert (E15 : ew E 15 = w64 8) by (rewrite (EW 15%nat 15%bv eq_refl); exact R15).
  assert (E16 : ew E 16 = w64 (onot (og_sg g))) by (rewrite (EW 16%nat 16%bv eq_refl); exact R16).
  assert (E17 : ew E 17 = w64 7) by (rewrite (EW 17%nat 17%bv eq_refl); exact R17).
  assert (E18 : ew E 18 = w64 (F + 32)) by (rewrite (EW 18%nat 18%bv eq_refl); exact R18).
  assert (E21 : ew E 21 = w64 (F + 64)) by (rewrite (EW 21%nat 21%bv eq_refl); exact R21).
  assert (E27 : ew E 27 = w64 (onot (F + 64))) by (rewrite (EW 27%nat 27%bv eq_refl); exact R27).
  assert (U9 : bv_unsigned (ew E 9) = og_sp1 g) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = og_sg g + i) by (rewrite X35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = F + 32 + 0) by (rewrite X36; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = F + 64 + 4 * 0) by (rewrite X37; apply unsigned_lit_small; lia).
  assert (U39 : bv_unsigned (ew E 39) = og_dt g) by (rewrite X39; apply unsigned_lit_small; lia).
  assert (U41 : bv_unsigned (ew E 41) = SB + og_dt g / 8) by (rewrite X41; apply unsigned_lit_small; unfold SB; lia).
  assert (Wsg : oc_wr g (og_sg g + i)) by (unfold oc_wr; left; lia).
  assert (Wdt : oc_wr g (og_dt g)) by (unfold oc_wr; right; lia).
  assert (YS : st_ok tfibsegs E (mkSS PC_L2 sr_atoms (l2_mem false) None (mkFacts l2_af [] []))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_L2) mem2 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
    - apply regs_ok_Ereg.
    - reflexivity.
    - unfold l2_mem. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil;
      unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9, ?U35, ?U36, ?U37, ?U39, ?U41.
      + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 40 8 (SOff 39 0) (og_dt g));
          [rewrite sv_denot_SOff0; exact X39 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V40].
        * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 48 8 (SOff 33 0) (og_sg g));
          [rewrite sv_denot_SOff0; exact X33 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V48].
        * apply (chunk_ok_val tfibsegs _ _ (og_sp1 g) 56 8 (SOff 43 0) (onot (F + 32)));
          [rewrite sv_denot_SOff0; exact X43 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold onot; lia | cbn; lia | exact V56].
      + split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. replace (og_sg g + i + o) with (og_sg g + i) by lia. apply (YCbq.apresent_writable tfibsegs).
        exact (ocl_present B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP HK Wsg).
      + split; [lia|]. split; [lia|]. split.
        * intros o Ho. replace (og_dt g + o) with (og_dt g) by lia. apply (YCbq.apresent_writable tfibsegs).
          exact (ocl_present B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP HK Wdt).
        * apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val tfibsegs _ _ (og_dt g) 0 1 (SOff 40 0) d);
          [rewrite sv_denot_SOff0; exact X40 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | rewrite Z.add_0_r; exact Hdv].
      + unfold SB in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs _ _ (SB + og_dt g / 8) 0 1 (SOff 42 0) kd);
        [rewrite sv_denot_SOff0; exact X42 | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (oc_vm1_of_aview _ _ _ _ Hkd).
    - pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd1 & _).
    destruct (ocl_wr_off B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP Wsg) as (Osg1 & Osg2 & Osg3).
    destruct (ocl_wr_off B LAWS g pos ly2 S2 W2 mem2 md2 _ Hpre HJ HP Wdt) as (Odt1 & Odt2 & Odt3).
    unfold TB_owed_counter_text, ESTACK in Osg3, Odt3.
    assert (Hsgapp : og_sg g + 8 <= SB - 1 \/ SB + 2 ^ 44 <= og_sg g)
      by (pose proof Hsgam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
          unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; unfold SB; lia).
    assert (Hdtapp : og_dt g + 1 <= SB - 1 \/ SB + 2 ^ 44 <= og_dt g)
      by (pose proof Hdtam as Ham; unfold amem_range in Ham; rewrite ?C3, ?C4, ?C5 in Ham;
          unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; unfold SB; lia).
    assert (HFapp' : F + 128 <= SB - 4096 \/ SB + 2 ^ 44 <= F)
      by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; unfold SB; lia).
      apply pairwise_disjoint_of_extents. unfold l2_mem, extent_of_region. cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U9, U35, ?U36, ?U37, U39, U41. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold SB in *. repeat split;
      first [ exact I
            | solve [clear - Hsp1 Osg3; lia] | solve [clear - Hsp1 Odt3; lia] | solve [clear - Hsp1 H46 Hdt8; lia]
            | solve [clear - Hsp1 Hceil HFc Hj Hj0 Hn0; lia] | solve [clear - Hd1 Hi; lia] | solve [clear - Hsgapp Hi Hdt8; lia]
            | solve [clear - Osg1 Hj Hj0 Hn0; lia] | solve [clear - Hdtapp Hdt8; lia] | solve [clear - Odt1 Hj Hj0 Hn0; lia]
            | solve [clear - HFapp' Hdt8 Hj Hj0 Hn0; lia] | solve [clear - Hj Hj0 Hn0; lia] ].
    - split; [|split; exact I]. cbn [f_atoms atoms_ok l2_af]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, U9, E19, E13, E14, E5, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43. unfold w64.
      clear - Hsg0 Hsg47 Hdt0 Hdt47 Hd128 Hkd7 Hdt8 Hi Hn0 Hj0 Hj HF0 HFc Hac Hsp1 Hsp1a H46 H47.
      rewrite !unsigned_lit_small by (unfold SB, onot; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SB, onot. repeat split; first [exact I | exact Hsp1a | lia]. }
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (23%bv : bv 5) (SOff 32 0) YS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, R23; reflexivity)) as HS.
  clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (11%bv : bv 5) (SOff 41 0) HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, X41, R11; reflexivity)) as YS.
  clear HS. rename YS into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 35 0 1; mkSHE 39 0 1] E (mrestrict (w_H W2) mem2)).
  { repeat apply Forall_cons; try apply Forall_nil.
    - apply (cw_shent_ra W2 mem2 E 35 (og_sg g + i) 1); [| | lia | lia | lia | exact X35 | exact E32].
      + eapply range_addressable_sub; [exact Hsgra | lia | lia].
      + pose proof Hsgam as Ham. unfold amem_range in Ham |- *. rewrite ?C3, ?C4, ?C5 in Ham |- *.
        unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham |- *. lia.
    - apply (cw_shent_ra W2 mem2 E 39 (og_dt g) 1); [exact Hdtra | exact Hdtam | lia | lia | lia | exact X39 | exact E32].
   }
  cw_keep_j0 HJ HJ0.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = og_sg g + i \/ a = og_dt g) ->
    aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
  assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
  unfold cfg_at. change (w64 PC_L2) with (Z_to_bv 64 PC_L2).
  cw_run awr_l2. ctk_keep kwr_l2.
  cw_branch Hc1.
  2: { exfalso. lazymatch type of Hc1 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
         rewrite (l2_bltzj Ec n i ltac:(ewpeel; exact E13) ltac:(ewpeel; exact E5) ltac:(lia) ltac:(lia)) in Hc1 end.
       apply Z.ltb_ge in Hc1. lia. }
  cw_run awr_l2. ctk_keep kwr_l2.
  (* bltu a6,a4 (0x84794): ~sg against i -> the trap *)
  cw_branch Hc4.
  { exfalso. lazymatch type of Hc4 with branch_taken _ (sv_denot ?Ec _) _ = _ =>
      rewrite branch_ltu_U, (U_atom Ec 16 (onot (og_sg g))), (U_atom Ec 14 i) in Hc4
        by (first [ewpeel; first [exact E16 | exact E14] | unfold onot; lia | lia]) end.
    apply Z.ltb_lt in Hc4. unfold onot in Hc4. lia. }
  cw_run_to awr_l2 0x847a0. ctk_keep kwr_l2.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
    pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 35 0) HS eq_refl
      ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite X35; symmetry;
            rewrite Z.add_comm; apply (l2_Dadd Ev 14 33 i (og_sg g)); [ewpeel; exact E14 | ewpeel; exact X33 | lia | lia | lia]))
      as YS end.
  clear HS. rename YS into HS. norm_ss HS.
  cw_run awr_l2. ctk_keep kwr_l2.
  cw_branch Hc7.
  all: rewrite branch_ne_U, (U_atom_off _ 14 i 1), (U_atom _ 15 8) in Hc7 by (first [ewpeel; first [exact E14 | exact E15] | lia]).
  * (* i + 1 <> 8: back to the head *)
    apply negb_true_iff, Z.eqb_neq in Hc7.
    destruct kk as [|kk]; [exfalso; lia|].
    cw_run_to awr_l2 PC_L2. ctk_keep kwr_l2.
    l2_chunk1 35%nat (og_sg g + i) (SLit 0) 0 Vseg.
    l2_chunk1 39%nat (og_dt g) (SOff 40 0) d Vdt.
    apply SRr_ret. cbv beta. left.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (l2_close B MT LAWS g pos PC_L2 (P_L2 g pos (S kk)) ly2 S2 regs2 mem2 md2 W2 msv _ i Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac | lia | exact KE | exact KP | ] end.
    exists (i + 1), n, d, s, dot, (sacc ++ [0]).
    split; [reg_off E13 i 1|]. split; [reg_off E14 i 1|]. split; [reg_atom E15|]. split; [reg_atom E16|].
    split; [reg_atom E17|]. split; [reg_atom E5|]. split; [reg_atom E6|]. split; [reg_atom X41|]. split; [reg_atom E12|].
    split; [reg_atom E19|]. split; [lia|]. split; [lia|].
    split; [rewrite Hspec, (l2_ct2_neg n s dot i (S kk) sacc d) by (fold j; lia); reflexivity|].
    split; [exact Hl1|]. split; [rewrite length_app, Hsacl; cbn [length]; lia|].
    split; [apply Forall_app; split; [exact Hsacc | constructor; [lia | constructor]]|]. split; [lia|].
    split; [eapply (l2_arrays B LAWS g pos ly2 S2 W2 mem2 md2 _ i n s dot Hpre HJ0 HP ltac:(lia) ltac:(lia) KE Harr)|].
    split; [exact (l2_seg_after B g W2 mem2 _ i sacc 0 Hpre ltac:(lia) Hsacl Hseg KE Vseg ltac:(lia))|].
    exact Vdt.
  * (* i = 7: the end, a0 = 0 *)
    apply negb_false_iff, Z.eqb_eq in Hc7. assert (Hi7 : i = 7) by lia. subst i.
    assert (Hk0 : kk = 0%nat) by lia. subst kk.
    cw_run_to awr_l2 PC_X. ctk_keep kwr_l2.
    l2_chunk1 35%nat (og_sg g + 7) (SLit 0) 0 Vseg.
    l2_chunk1 39%nat (og_dt g) (SOff 40 0) d Vdt.
    apply SRr_ret. cbv beta. right.
    lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (l2_close B MT LAWS g pos PC_X (P_X g) ly2 S2 regs2 mem2 md2 W2 msv _ 7 Hpre HJ0 HK HP Hni Hio Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) | oc_kregs_tac | lia | exact KE | exact KP | ] end.
    assert (Hres : owed_counter_text_spec (og_tb g) = (0, sacc ++ [0], d))
      by (rewrite Hspec, (l2_ct2_neg n s dot 7 0 sacc d) by (fold j; lia); reflexivity).
    unfold P_X, oc_res. rewrite Hres.
    split; [rv0; reflexivity|].
    split; [intros _; split; [|exact Vdt]|intros Hr; exfalso; exact (Hr eq_refl)].
    pose proof (l2_seg_after B g W2 mem2 _ 7 sacc 0 Hpre ltac:(lia) Hsacl Hseg KE Vseg ltac:(lia)) as G.
    rewrite skipn_all2 in G by (rewrite Lsj; lia). rewrite app_nil_r in G. exact G.

Qed.
End d.
