(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset image B (asan-ubsan, record image f8f98a95bc524311faf7a8b817fa91103ed12ec8f5802da61a604ab84b493485;
   neutral listing of the record image's objdump 21ef4d1ecc75490a4dfee955bcb4448e830cdcae765881e1692b9a06e6d176f8,
   the internal file ex_utf8.fuzz_preset.asan-ubsan.s): ex_utf8 (fuzz_preset.c :130-156; entry B_prog_sigma AS_ex_utf8, 148
   instructions) against ExsB_Callee.v's achain-free run form texutf8_runB, proved AS STATED: ex_utf8_run_B.
   THE WALK. One engine run per (code-point arm, output zone) from the entry to the `ret`: the entry facts on cp (atom 11,
   [0, 127] / [128, 2047] / [2048, 65535] / [65536, 2 ^ 21 - 1]; the third arm also carries the condition
   (cp >>w 16) = 0, exu_c3) decide the three arm branches inside the run; the entry facts on o (atom 10, inside one of the
   four zones below, so 4096 <= o and o + n <= 2 ^ 47) decide every UBSan branch inside the run; every instrumented
   check of an output byte is a shadow token whose obligation is the premise range_addressable o n (exu_ob).
   WHY FOUR ZONES and no shadow entry (SH = []): the premise lets an output byte be ANY awr_byte, also a shadow byte of
   one of the caller's own fake frames (in_frames' second arm). A shadow entry needs its range apart from the shadow
   band (YCbn.v app_apart), so it cannot cover such an o. The obligation form needs only that the run's write windows
   miss the shadow span the tokens read (YCbn.v cells_safe_b); that holds once o is placed in one zone (exu_wr_byte):
   Z1 = [4096, kLowShadowBeg) and Z2 = [kHighMemBeg, 2 ^ 47) (application memory: stack, blocks, frames), Z3 / Z4 = the
   shadow of the low / high application range (own fake frames), each with the span exu_Bspan of its own shadow cells.
   n <= 4 keeps the n output bytes in one zone (the zones are more than 4 apart).
   REPORT SITES (exstr rows of the internal file preset-report-sites-asan-ubsan.tsv and the internal file SITES-B.tsv, B pcs):
     0x84d1c unimp (UBSan), entry edges beqz o 0x84b70 / 0x84b98 / 0x84bf0 / 0x84c6c, beq o,-1 0x84bbc / 0x84c14 /
       0x84c90, bltu -3,o 0x84c40 / 0x84cbc, bltu -4,o 0x84ce8: FORM A (entry edge not taken), decided inside the
       run of each exu_i_* lemma by the atom-10 fact (10, mkAF zlo (zhi - n) 0) of ss_exu, established by exu_entry from
       4096 <= o, o + n <= 2 ^ 47.
     0x84d28 / 0x84d34 / 0x84d4c / 0x84d58 (__asan_report_store1, byte o + 0 of arms 1 / 2 / 3 / 4), 0x84d40 / 0x84d68 /
       0x84d78 (byte o + 1 of arms 2 / 3 / 4), 0x84d84 / 0x84d94 (byte o + 2 of arms 3 / 4), 0x84da0 (byte o + 3 of arm 4):
       FORM A and FORM B (the token's two outcomes: shadow 0 -> the bnez entry edge is not taken; partial granule ->
       the slow block's blt is taken since (x & 7) < k), both from the token obligation `range_addressable (rd_of m)
       SHADOW_OFF (o + i) 1` (saddr_ok's two disjuncts) that the run of exu_i_<arm>_<zone> leaves and exu_ob
       discharges from the premise range_addressable o n.
   REUSED (rule 24; proof-index v5 16:10Z / lemma index 16:30Z: ex_utf8 has no released proof; a census-1 cold/*
   sweep found the earlier B walk origin/cold/h-hpreset-7-walk-S8b dafa4151f913 lib/B/Prog/ExUtf8B.v + lib/A/Prog/ExUtf8W.v,
   which proves ex_utf8 under afn_pre_x with o inside a live block and an older engine (AR_laws_x without HL): its
   image-free helpers are PORTED below (exu_arm1..4, exu_low_byte_mod .. exu_garr8_cons, exu_srlw16_U, exu_c3, the entry
   state's shape, exu_entry's region proofs), its block-only premise and shadow-entry form are not usable here).
   Runner paj_run_x_inv / paj_ret_at / pa_entry_st_ok_full (YC1fP / YC1fPx), awr_byte_cases_x / blk_img_x / frm_img_x /
   ajournal_x_materialize (YCbqG), the memnorm carrier of ExsB_Lib.v es_plaw (YSRrMemnorm).
   Numerals: 16 (LENGTH: the frame), 1 .. 4 (LENGTH: the UTF-8 byte counts), 127 / 2047 / 65535 / 2 ^ 21 (WORD: the arm
   bounds of the code), 512, 8 (DERIVED: shadow granule arithmetic), 665680 / 702200 (DERIVED: VAL (A_OBJ 0) / (A_OBJ 12)
   by vm_compute), 2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 64 (LENGTH: address-space widths). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExsB_Callee.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
(* the PLAIN build's sink head must never fill SK here (YC1fP.v:23-33): every SK below is passed explicitly *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the model's four arms (ExUtf8W.v u8_arm1..4, dafa4151f913) ---- *)
Lemma exu_arm1 : forall cp, 0 <= cp < 128 -> PjGrammar.utf8 cp = [cp].
Proof. intros cp H. unfold PjGrammar.utf8. rewrite (proj2 (Z.ltb_lt _ _) (proj2 H)). reflexivity. Qed.
Lemma exu_arm2 : forall cp, 128 <= cp < 2048 -> PjGrammar.utf8 cp = [192 + cp / 64; 128 + cp mod 64].
Proof.
intros cp H. unfold PjGrammar.utf8.
rewrite (proj2 (Z.ltb_ge cp 128) ltac:(lia)), (proj2 (Z.ltb_lt cp 2048) ltac:(lia)). reflexivity.
Qed.
Lemma exu_arm3 : forall cp, 2048 <= cp < 65536 ->
  PjGrammar.utf8 cp = [224 + cp / 4096; 128 + (cp / 64) mod 64; 128 + cp mod 64].
Proof.
intros cp H. unfold PjGrammar.utf8.
rewrite (proj2 (Z.ltb_ge cp 128) ltac:(lia)), (proj2 (Z.ltb_ge cp 2048) ltac:(lia)), (proj2 (Z.ltb_lt cp 65536) ltac:(lia)).
reflexivity.
Qed.
Lemma exu_arm4 : forall cp, 65536 <= cp ->
  PjGrammar.utf8 cp = [240 + cp / 262144; 128 + (cp / 4096) mod 64; 128 + (cp / 64) mod 64; 128 + cp mod 64].
Proof.
intros cp H. unfold PjGrammar.utf8.
rewrite (proj2 (Z.ltb_ge cp 128) ltac:(lia)), (proj2 (Z.ltb_ge cp 2048) ltac:(lia)), (proj2 (Z.ltb_ge cp 65536) ltac:(lia)).
reflexivity.
Qed.

(* ---- the symbolic entry state: atoms 2 sp, 10 o, 11 cp, 32 the shadow base; the n bytes at o writable; o in the zone
   [zlo, zhi); no shadow entry, the span of the tokens' cells is the zone's shadow ---- *)
Definition EXU_K : Z := B_prog_sigma AS_ex_utf8 - B_prog_base.
Definition EXU_Bx : sv := SOff 32 0.
Definition exu_Bspan (zlo zhi : Z) : Z * Z := (SHADOW_OFF + zlo / 8, SHADOW_OFF + (zhi - 1) / 8).
Definition exu_regions (n : Z) : smem :=
  [stack_region 16; got_regionP; bcell_regionP 32; YP09.mkRegion (Some 10%nat) 0 n 0 n []].
Definition ss_exu (n lo hi zlo zhi : Z) (cs : list acond) : sstate :=
  mkSS EXU_K sr_atoms (exu_regions n) None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF zlo (zhi - n) 0); (11%nat, mkAF lo hi 0);
              (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] cs []).
(* the four zones of an output byte (exu_wr_byte) *)
Definition EXU_Z1 : Z * Z := (4096, kLowShadowBeg).
Definition EXU_Z2 : Z * Z := (kHighMemBeg, 2 ^ 47).
Definition EXU_Z3 : Z * Z := (SHADOW_OFF + 512, SHADOW_OFF + kLowShadowBeg / 8).
Definition EXU_Z4 : Z * Z := (SHADOW_OFF + kHighMemBeg / 8, SHADOW_OFF + 0x7fffff800000 / 8).
Definition exu_zin (z : Z * Z) (x : Z) : Prop := fst z <= x < snd z.
Definition EXU_CS3 : list acond := [mkAC BC_EQ (SAluw ALU_SRL (SOff 11 0) (SLit 16)) (SLit 0)].
Ltac exu_lia :=
  unfold EXU_Z1, EXU_Z2, EXU_Z3, EXU_Z4, exu_zin, EXU_STK in *; cbn [fst snd] in *;
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.

(* ---- image-free helpers, ported from ExUtf8W.v (dafa4151f913; there from h-verbs-1's put_utf8_xw.v cfcf4ad0554) ---- *)
Lemma exu_low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma exu_val_of_chunk : forall {fx : YK11.FPState} segs E mem base off (n : N) (e : sv),
  YP09.chunk_ok segs E mem base (YP09.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
  val_mem segs mem (base + off) (N.to_nat n) (U E e mod 2 ^ (8 * Z.of_N n)).
Proof.
intros fx segs E mem base off n e H Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal. unfold U.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
set (u := bv_unsigned (sv_denot E e)) in *.
assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N n) < 2 ^ (8 * Z.of_nat (N.to_nat n))).
{ rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply exu_low_byte_mod; [lia | exact Hk].
Qed.
Lemma exu_field_of_region : forall {fx : YK11.FPState} {segs : list Segment} E m n b cs lo hi wlo whi od (w : N) e,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem segs m (b + od) (N.to_nat w) (U E e mod 2 ^ (8 * Z.of_N w)).
Proof.
intros fx segs E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (exu_val_of_chunk segs E m b od w e Hck Hw).
Qed.
Lemma exu_region_nth : forall {fx : YK11.FPState} segs E ss ms i r,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros fx segs E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma exu_low_canon : forall x, zcanon x mod 256 = x mod 256.
Proof.
intros x. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (x - 18446744073709551616 * (x / 18446744073709551616)) with (x + (- (72057594037927936 * (x / 18446744073709551616))) * 256) by lia.
apply Z.mod_add. lia.
Qed.
Lemma exu_lor_low : forall x k, 0 <= k <= 8 -> 0 <= x < 2 ^ k -> Z.lor x (2 ^ 64 - 2 ^ k) mod 256 = x + (256 - 2 ^ k).
Proof.
intros x k Hk Hx.
assert (H2k : 1 <= 2 ^ k <= 256) by (split; [apply (Z.pow_le_mono_r 2 0 k); lia | apply (Z.pow_le_mono_r 2 k 8); lia]).
assert (Hand : Z.land x (2 ^ 64 - 2 ^ k) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec i k) as [Hl|Hge].
  - replace (2 ^ 64 - 2 ^ k) with ((2 ^ (64 - k) - 1) * 2 ^ k) by (rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia; f_equal; f_equal; lia).
    rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - destruct (Z.eq_dec x 0) as [->|Hnz]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 x i); [reflexivity | lia |].
    apply (Z.lt_le_trans _ k); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite <- Z.lxor_lor by exact Hand. rewrite <- Z.add_nocarry_lxor by exact Hand.
replace (x + (2 ^ 64 - 2 ^ k)) with (x + (256 - 2 ^ k) + 72057594037927935 * 256) by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma exu_sll_srl : forall cp s, 0 <= cp -> 0 <= s <= 58 ->
  Z.shiftr (Z.shiftl cp s mod 2 ^ 64) 58 = (cp / 2 ^ (58 - s)) mod 64.
Proof.
intros cp s Hcp Hs. rewrite <- Z.shiftr_div_pow2 by lia. change 64 with (2 ^ 6) at 2.
apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
destruct (Z_lt_le_dec i 6) as [Hl|Hge].
- rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftl_spec by lia.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
- rewrite Z.mod_pow2_bits_high by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma exu_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma exu_land63 : forall s, 0 <= s < 64 -> Z.land s 63 = s.
Proof. intros s Hs. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia. Qed.
(* the three byte shapes the engine leaves in the stored chunks *)
Lemma exu_bA : forall E cp s c k r, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 -> 0 <= s < 64 -> 0 <= k <= 8 ->
  c = 2 ^ k -> cp / 2 ^ s < 2 ^ k -> r = cp / 2 ^ s + (256 - c) ->
  U E (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit s)) (SLit (- c))) mod 256 = r.
Proof.
intros E cp s c k r H11 Hcp Hs Hk Hc Hlt Hr.
rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 11 cp H11) by lia. cbn [zalu_raw].
rewrite exu_low_canon. rewrite (exu_zc s) by lia. rewrite exu_land63 by lia. rewrite Z.shiftr_div_pow2 by lia.
assert (Hq : 0 <= cp / 2 ^ s) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
assert (H2k : 1 <= 2 ^ k <= 256) by (split; [apply (Z.pow_le_mono_r 2 0 k); lia | apply (Z.pow_le_mono_r 2 k 8); lia]).
rewrite (exu_zc (cp / 2 ^ s)) by lia.
replace (zcanon (- c)) with (2 ^ 64 - 2 ^ k)
  by (unfold zcanon, M64; subst c; rewrite <- (Z.mod_add (- 2 ^ k) 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia).
rewrite exu_lor_low by lia. lia.
Qed.
Lemma exu_bB : forall E cp r, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 -> r = 128 + cp mod 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = r.
Proof.
intros E cp r H11 Hcp Hr.
rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 11 cp H11) by lia. cbn [zalu_raw].
rewrite exu_low_canon. rewrite (exu_zc 63) by lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
pose proof (Z.mod_pos_bound cp 64 ltac:(lia)) as Hm.
rewrite (exu_zc (cp mod 64)) by lia. change (zcanon (-128)) with 18446744073709551488.
replace (cp mod 64 + 18446744073709551488) with (cp mod 64 + 128 + 72057594037927935 * 256) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma exu_bC : forall E cp sh r, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 -> 0 <= sh <= 58 ->
  r = 128 + (cp / 2 ^ (58 - sh)) mod 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit sh)) (SLit 58)) (SLit (-128))) mod 256 = r.
Proof.
intros E cp sh r H11 Hcp Hsh Hr.
rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 11 cp H11) by lia. cbn [zalu_raw].
rewrite exu_low_canon. rewrite (exu_zc sh) by lia. rewrite (exu_zc 58) by lia. rewrite !exu_land63 by lia.
change (zcanon (Z.shiftl cp sh)) with (Z.shiftl cp sh mod 2 ^ 64).
rewrite exu_sll_srl by lia.
pose proof (Z.mod_pos_bound (cp / 2 ^ (58 - sh)) 64 ltac:(lia)) as Hm.
rewrite (exu_zc ((cp / 2 ^ (58 - sh)) mod 64)) by lia. change (zcanon (-128)) with 18446744073709551488.
replace ((cp / 2 ^ (58 - sh)) mod 64 + 18446744073709551488) with ((cp / 2 ^ (58 - sh)) mod 64 + 128 + 72057594037927935 * 256) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma exu_garr8_cons : forall segs (m : word -> option byte) p v L,
  val_mem segs m p 1 v -> 0 <= v < 256 -> garr8 segs m (p + 1) L -> garr8 segs m p (v :: L).
Proof.
intros segs m p v L Hv Hr HG j Hj. destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact Hv | exact Hr].
- cbn [nth]. cbn in Hj. destruct (HG j ltac:(lia)) as [Hv' Hr']. split; [|exact Hr'].
  replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. exact Hv'.
Qed.
(* the 32-bit shift of the third arm's test (ExUtf8W.v u8_srlw16_U, restated over YP0e's S_SAluw) *)
Lemma exu_srlw16_U : forall E cp, ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 21 ->
  U E (SAluw ALU_SRL (SOff 11 0) (SLit 16)) = cp / 65536.
Proof.
intros E cp H11 Hcp. rewrite U_of_S, S_SAluw, (U_atom E 11 cp H11) by lia. rewrite U_SLit. cbn [zalu_raw].
rewrite (Z.mod_small cp (2 ^ 32)) by lia. change (Z.land (zcanon 16 mod 2 ^ 32) 31) with 16.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
assert (Hq : 0 <= cp / 65536 < 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (bv_modulus 64) with 18446744073709551616.
rewrite (Z.mod_small (cp / 65536 + 2147483648) 4294967296) by lia.
rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the bytes the run leaves in the output region, per arm ---- *)
Section b. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Lemma exu_garr1 : forall E m o cp cs lo hi wlo whi,
  region_ok segs E m (YP09.mkRegion (Some 10%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 10) = o -> ew E 11 = Z_to_bv 64 cp -> 0 <= cp < 128 ->
  In (YP09.mkChunk 0 (CVal 1 (SOff 11 0))) cs ->
  garr8 segs m o (PjGrammar.utf8 cp).
Proof.
intros E m o cp cs lo hi wlo whi HR Ho H11 Hcp I0.
rewrite exu_arm1 by lia.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 0 1%N _ HR Ho I0 ltac:(cbn; lia)) as V0.
change (N.to_nat 1) with 1%nat in V0. change (2 ^ (8 * Z.of_N 1)) with 256 in V0.
rewrite (U_atom E 11 cp H11) in V0 by lia. rewrite Z.mod_small in V0 by lia. rewrite Z.add_0_r in V0.
apply exu_garr8_cons; [exact V0 | lia | apply garr8_nil].
Qed.
Lemma exu_garr2 : forall E m o cp cs lo hi wlo whi,
  region_ok segs E m (YP09.mkRegion (Some 10%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 10) = o -> ew E 11 = Z_to_bv 64 cp -> 128 <= cp < 2048 ->
  In (YP09.mkChunk 0 (CVal 1 (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 6)) (SLit (-64))))) cs ->
  In (YP09.mkChunk 1 (CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))))) cs ->
  garr8 segs m o (PjGrammar.utf8 cp).
Proof.
intros E m o cp cs lo hi wlo whi HR Ho H11 Hcp I0 I1.
rewrite exu_arm2 by lia.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 0 1%N _ HR Ho I0 ltac:(cbn; lia)) as V0.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 1 1%N _ HR Ho I1 ltac:(cbn; lia)) as V1.
change (N.to_nat 1) with 1%nat in V0, V1. change (2 ^ (8 * Z.of_N 1)) with 256 in V0, V1.
assert (B0 : U E (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 6)) (SLit (-64))) mod 256 = 192 + cp / 64).
{ apply (exu_bA E cp 6 64 6); [exact H11 | lia | lia | lia | reflexivity | | ]; change (2 ^ 6) with 64;
    [apply Z.div_lt_upper_bound; lia | lia]. }
assert (B1 : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = 128 + cp mod 64)
  by (apply (exu_bB E cp); [exact H11 | lia | reflexivity]).
rewrite B0 in V0. rewrite B1 in V1. rewrite Z.add_0_r in V0.
assert (Hq : 2 <= cp / 64 < 32) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
pose proof (Z.mod_pos_bound cp 64 ltac:(lia)).
apply exu_garr8_cons; [exact V0 | lia |].
apply exu_garr8_cons; [exact V1 | lia | apply garr8_nil].
Qed.
Lemma exu_garr3 : forall E m o cp cs lo hi wlo whi,
  region_ok segs E m (YP09.mkRegion (Some 10%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 10) = o -> ew E 11 = Z_to_bv 64 cp -> 2048 <= cp < 65536 ->
  In (YP09.mkChunk 0 (CVal 1 (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 12)) (SLit (-32))))) cs ->
  In (YP09.mkChunk 1 (CVal 1 (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))))) cs ->
  In (YP09.mkChunk 2 (CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))))) cs ->
  garr8 segs m o (PjGrammar.utf8 cp).
Proof.
intros E m o cp cs lo hi wlo whi HR Ho H11 Hcp I0 I1 I2.
rewrite exu_arm3 by lia.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 0 1%N _ HR Ho I0 ltac:(cbn; lia)) as V0.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 1 1%N _ HR Ho I1 ltac:(cbn; lia)) as V1.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 2 1%N _ HR Ho I2 ltac:(cbn; lia)) as V2.
change (N.to_nat 1) with 1%nat in V0, V1, V2. change (2 ^ (8 * Z.of_N 1)) with 256 in V0, V1, V2.
assert (B0 : U E (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 12)) (SLit (-32))) mod 256 = 224 + cp / 4096).
{ apply (exu_bA E cp 12 32 5); [exact H11 | lia | lia | lia | reflexivity | | ]; change (2 ^ 12) with 4096;
    change (2 ^ 5) with 32; [apply Z.div_lt_upper_bound; lia | lia]. }
assert (B1 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))) mod 256
  = 128 + (cp / 64) mod 64)
  by (apply (exu_bC E cp 52); [exact H11 | lia | lia | reflexivity]).
assert (B2 : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = 128 + cp mod 64)
  by (apply (exu_bB E cp); [exact H11 | lia | reflexivity]).
rewrite B0 in V0. rewrite B1 in V1. rewrite B2 in V2. rewrite Z.add_0_r in V0.
assert (Hq : 0 <= cp / 4096 < 16) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
pose proof (Z.mod_pos_bound cp 64 ltac:(lia)). pose proof (Z.mod_pos_bound (cp / 64) 64 ltac:(lia)).
apply exu_garr8_cons; [exact V0 | lia |].
apply exu_garr8_cons; [exact V1 | lia |].
replace (o + 1 + 1) with (o + 2) by lia.
apply exu_garr8_cons; [exact V2 | lia | apply garr8_nil].
Qed.
Lemma exu_garr4 : forall E m o cp cs lo hi wlo whi,
  region_ok segs E m (YP09.mkRegion (Some 10%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 10) = o -> ew E 11 = Z_to_bv 64 cp -> 65536 <= cp < 2 ^ 21 ->
  In (YP09.mkChunk 0 (CVal 1 (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 18)) (SLit (-16))))) cs ->
  In (YP09.mkChunk 1 (CVal 1 (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 46)) (SLit 58)) (SLit (-128))))) cs ->
  In (YP09.mkChunk 2 (CVal 1 (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))))) cs ->
  In (YP09.mkChunk 3 (CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))))) cs ->
  garr8 segs m o (PjGrammar.utf8 cp).
Proof.
intros E m o cp cs lo hi wlo whi HR Ho H11 Hcp I0 I1 I2 I3.
rewrite exu_arm4 by lia.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 0 1%N _ HR Ho I0 ltac:(cbn; lia)) as V0.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 1 1%N _ HR Ho I1 ltac:(cbn; lia)) as V1.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 2 1%N _ HR Ho I2 ltac:(cbn; lia)) as V2.
pose proof (exu_field_of_region E m 10%nat o cs lo hi wlo whi 3 1%N _ HR Ho I3 ltac:(cbn; lia)) as V3.
change (N.to_nat 1) with 1%nat in V0, V1, V2, V3. change (2 ^ (8 * Z.of_N 1)) with 256 in V0, V1, V2, V3.
assert (B0 : U E (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 18)) (SLit (-16))) mod 256 = 240 + cp / 262144).
{ apply (exu_bA E cp 18 16 4); [exact H11 | lia | lia | lia | reflexivity | | ]; change (2 ^ 18) with 262144;
    change (2 ^ 4) with 16; [apply Z.div_lt_upper_bound; lia | lia]. }
assert (B1 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 46)) (SLit 58)) (SLit (-128))) mod 256
  = 128 + (cp / 4096) mod 64)
  by (apply (exu_bC E cp 46); [exact H11 | lia | lia | reflexivity]).
assert (B2 : U E (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))) mod 256
  = 128 + (cp / 64) mod 64)
  by (apply (exu_bC E cp 52); [exact H11 | lia | lia | reflexivity]).
assert (B3 : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = 128 + cp mod 64)
  by (apply (exu_bB E cp); [exact H11 | lia | reflexivity]).
rewrite B0 in V0. rewrite B1 in V1. rewrite B2 in V2. rewrite B3 in V3. rewrite Z.add_0_r in V0.
assert (Hq : 0 <= cp / 262144 < 8) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
pose proof (Z.mod_pos_bound cp 64 ltac:(lia)). pose proof (Z.mod_pos_bound (cp / 64) 64 ltac:(lia)).
pose proof (Z.mod_pos_bound (cp / 4096) 64 ltac:(lia)).
apply exu_garr8_cons; [exact V0 | lia |].
apply exu_garr8_cons; [exact V1 | lia |].
replace (o + 1 + 1) with (o + 2) by lia.
apply exu_garr8_cons; [exact V2 | lia |].
replace (o + 2 + 1) with (o + 3) by lia.
apply exu_garr8_cons; [exact V3 | lia | apply garr8_nil].
Qed.
End b.

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
Definition EXU_E (regs : bvmap 5 word) : env :=
  Eimg (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
(* the memory-invariant carrier of the run (ExsB_Lib.v es_P / es_plaw) *)
Definition exu_P (memc : word -> option byte) : (word -> option byte) -> Prop :=
  fun m => YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs m.
Lemma exu_plaw : forall memc, srr_inv_laws rsegs (exu_P memc).
Proof. intros memc. exact (YSRrMemnorm.srr_inv_laws_imp rsegs _ memc (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)). Qed.

Lemma exu_pc_eq : B_prog_sigma AS_ex_utf8 = BASE + EXU_K.
Proof. vm_compute. reflexivity. Qed.
Lemma exu_obj_val : VAL (A_OBJ 0) = 665680 /\ VAL (A_OBJ 12) = 702200.
Proof. split; vm_compute; reflexivity. Qed.
Lemma exu_E_low : forall regs i, (i < A_TEXT)%nat -> ew (EXU_E regs) i = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) i.
Proof. intros regs i Hi. unfold EXU_E. apply Eimg_low. exact Hi. Qed.
Lemma exu_E_reg : forall regs (i : nat) (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  ew (EXU_E regs) i = getr regs r.
Proof. intros regs i r Hi Hr. rewrite exu_E_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ i r Hr). Qed.
Lemma exu_E32 : forall regs, ew (EXU_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. rewrite exu_E_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma exu_Usp : forall regs, bv_unsigned (ew (EXU_E regs) 2) = spZ regs.
Proof. intros regs. rewrite (exu_E_reg regs 2 2%bv) by (first [reflexivity | lia]). reflexivity. Qed.
Lemma exu_E10 : forall regs o, getr regs 10 = w64 o -> ew (EXU_E regs) 10 = Z_to_bv 64 o.
Proof. intros regs o H. rewrite (exu_E_reg regs 10 10%bv) by (first [reflexivity | lia]). exact H. Qed.
Lemma exu_E11 : forall regs cp, getr regs 11 = w64 cp -> ew (EXU_E regs) 11 = Z_to_bv 64 cp.
Proof. intros regs cp H. rewrite (exu_E_reg regs 11 11%bv) by (first [reflexivity | lia]). exact H. Qed.
Lemma exu_Uo : forall regs o, getr regs 10 = w64 o -> 0 <= o < 2 ^ 64 -> bv_unsigned (ew (EXU_E regs) 10) = o.
Proof. intros regs o H Ho. rewrite (exu_E10 regs o H). apply unsigned_lit_small. exact Ho. Qed.
Lemma exu_c3 : forall regs cp, getr regs 11 = w64 cp -> 2048 <= cp <= 65535 -> conds_ok (EXU_E regs) EXU_CS3.
Proof.
intros regs cp H11 Hcp. split; [|exact I].
change (branch_taken BC_EQ (sv_denot (EXU_E regs) (SAluw ALU_SRL (SOff 11 0) (SLit 16))) (sv_denot (EXU_E regs) (SLit 0)) = true).
rewrite branch_eq_U, (exu_srlw16_U _ cp (exu_E11 regs cp H11)) by lia.
change (U (EXU_E regs) (SLit 0)) with (zcanon 0).
rewrite (Z.div_small cp 65536) by lia. reflexivity.
Qed.

(* the shadow-base GOT word and the shadow cell are image bytes (find_segment over the record image's segments) *)
Lemma exu_obj_img : forall a, (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) \/ (VAL (A_OBJ 12) <= a < VAL (A_OBJ 12) + 8) ->
  in_img rsegs a.
Proof.
intros a Ha. destruct exu_obj_val as [E0 E12]. rewrite E0, E12 in Ha. destruct Ha as [Ha | Ha].
- assert (Hs : match find_segment rsegs 665680 8 with Some _ => true | None => false end = true) by (vm_compute; reflexivity).
  destruct (find_segment rsegs 665680 8) as [sg|] eqn:F; [|discriminate Hs].
  destruct (find_segment_hit _ _ _ _ F) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
- assert (Hs : match find_segment rsegs 702200 8 with Some _ => true | None => false end = true) by (vm_compute; reflexivity).
  destruct (find_segment rsegs 702200 8) as [sg|] eqn:F; [|discriminate Hs].
  destruct (find_segment_hit _ _ _ _ F) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

(* a run's frame keeps the reader's view off its write windows (CheckBoundedAllocB.v cba_aview_frame) *)
Lemma exu_aview_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' a Hf Ha Hn. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* the token obligation of an output byte: its shadow cell, from the premise range_addressable o n *)
Lemma exu_ob : forall (W : world SEGS) (m : word -> option byte) regs o nn i,
  getr regs 10 = w64 o -> 0 <= o -> o + nn < 2 ^ 64 -> 0 <= i -> i < nn ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF o nn ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) m)) (U (EXU_E regs) EXU_Bx) (U (EXU_E regs) (SOff 10 i)) 1.
Proof.
intros W m regs o nn i H10 Ho Hon Hi Hin HRA. unfold EXU_Bx.
rewrite (U_atom (EXU_E regs) 32 SHADOW_OFF (exu_E32 regs)) by (unfold SHADOW_OFF; lia).
rewrite (U_atom_off (EXU_E regs) 10 o i (exu_E10 regs o H10)) by lia.
intros x Hx. exact (HRA x ltac:(lia)).
Qed.

(* the entry state (ExUtf8W.v u8_entry's region proofs; the premises are the run form's, o in a zone) *)
Lemma exu_entry : forall (W : world SEGS) regs memc o cp nn lo hi zlo zhi cs,
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> lo <= cp <= hi -> 0 <= lo -> hi < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs - 16 -> spZ regs <= 2 ^ 47 ->
  (forall x, spZ regs - 16 <= x < spZ regs -> apresent (w_H W) memc x) ->
  0 <= zlo -> zlo <= o -> o + nn <= zhi -> zhi <= 2 ^ 47 -> 0 < nn ->
  (forall x, o <= x < o + nn -> apresent (w_H W) memc x) ->
  (spZ regs <= o \/ o + nn <= spZ regs - 16) ->
  (o + nn <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= o) ->
  (o + nn <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= o) ->
  rdword (aview SEGS (w_H W) memc) (VAL (A_OBJ 0)) = Some (VAL (A_OBJ 12)) ->
  rdword (aview SEGS (w_H W) memc) (VAL (A_OBJ 12)) = Some SHADOW_OFF ->
  conds_ok (EXU_E regs) cs -> regions_wf (exu_regions nn) = true ->
  st_ok_pi SEGS VAL (EXU_E regs) (ss_exu nn lo hi zlo zhi cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + EXU_K)) memc (seg_rom SEGS))).
Proof.
intros W regs memc o cp nn lo hi zlo zhi cs H10 H11 Hcp Hlo Hhi Hal Hsp1 Hsp2 Hfrm Hzl Hz1 Hz2 Hzh Hn Hout Hdj Hg Hc
  Kgot Kcell Hcs Hwf.
destruct exu_obj_val as [Eo0v Eo12v].
set (E := EXU_E regs) in *.
assert (E10 : ew E 10 = Z_to_bv 64 o) by exact (exu_E10 regs o H10).
assert (E11 : ew E 11 = Z_to_bv 64 cp) by exact (exu_E11 regs cp H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (exu_E32 regs).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EXU_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EXU_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by exact (exu_Usp regs).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn' Hv. cbn [base_val]. rewrite Hn'. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold ss_exu. apply pa_entry_st_ok_full.
- subst E. unfold EXU_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- unfold exu_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hfrm. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + rewrite (VB 10%nat o E10) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hout. lia.
- apply pairwise_disjoint_of_extents. unfold exu_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 10%nat o E10) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia.
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia.
  cbn [base_val]. rewrite Usp, Eo0v, Eo12v. rewrite Eo0v in Hg. rewrite Eo12v in Hc.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact Hcs | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E10, E11, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold spZ in *.
  repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

Section w.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
(* the engine laws of the allocator relation, and the image's GOT word / shadow cell binding (YC1fP.v PALibCore, which
   PALib gives by palib_core; lib/B/PALibB.v exvi_eh_palib proves PALib at image B's instance) *)
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis PALC : PALibCore (L := B_prog_listing) (PI := PI_prog_B) B.

(* an output byte is in one of the four zones and off the GOT word and the shadow cell *)
Lemma exu_wr_byte : forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k x,
  ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x ->
  (exu_zin EXU_Z1 x \/ exu_zin EXU_Z2 x \/ exu_zin EXU_Z3 x \/ exu_zin EXU_Z4 x) /\
  ~ (VAL (A_OBJ 0) <= x < VAL (A_OBJ 0) + 8) /\ ~ (VAL (A_OBJ 12) <= x < VAL (A_OBJ 12) + 8).
Proof.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k x HJ Hw.
pose proof HJ as (HARc & _ & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (_ & _ & Hc0 & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (exu_obj_img x) as HI. destruct exu_obj_val as [Eo0v Eo12v].
destruct (awr_byte_cases_x (SK := SK) rsegs B PST ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ Hw)
  as (_ & [(Hc & Hs) | [(Happ & b & m & Hin & Hr & _) | (cid & pos & Hown & [(Happ & Hr) | (Hsh & Hr)])]]).
- (* the caller's stack window: above the allocation ceiling *)
  rewrite Eo0v, Eo12v. split; [right; left; exu_lia | split; lia].
- (* a live block: application memory, no image byte *)
  pose proof (blk_img_x rsegs B ARx LAWS lyc Sc Hpc W memc mdc b m x HARc Hin Hr) as Hni.
  split; [|split; intros Hg; apply Hni, HI; [left | right]; exact Hg].
  destruct Happ as (Ha1 & [Ha2 | (Ha2 & Ha3)]); unfold ASAN_CEIL in *; [left | right; left]; exu_lia.
- (* an own frame's byte: application memory, no image byte *)
  assert (Hinf : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  pose proof (frm_img_x rsegs B ARx LAWS lyc Sc Hpc W memc mdc cid pos x HARc Hinf Hr) as Hni.
  split; [|split; intros Hg; apply Hni, HI; [left | right]; exact Hg].
  destruct Happ as (Ha1 & [Ha2 | (Ha2 & Ha3)]); unfold ASAN_CEIL in *; [left | right; left]; exu_lia.
- (* a shadow byte of an own frame: the shadow of the low or the high application range *)
  assert (Hinf : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
  destruct (alx_frames _ _ _ LAWS lyc Sc Hpc W memc mdc cid pos HARc Hinf) as (_ & Hfa & _).
  unfold in_zr in Hr. cbn [fst snd] in Hr. unfold shadow_addr in Hr.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  rewrite Eo0v, Eo12v. split; [|unfold kLowMemEnd in Hsh; split; lia].
  destruct Hfa as (Hf1 & [Hf2 | (Hf2 & Hf3)]); unfold ASAN_CEIL in *; [right; right; left | right; right; right]; exu_lia.
Qed.

(* the return: the post from the run's last state *)
Lemma exu_finish : forall (W : world SEGS) E' ssf ms md STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc memc k
    (regs : bvmap 5 word) o cp nn,
  st_ok_pi SEGS VAL E' ssf (restrict (w_H W) ms) ->
  (forall i, (i < 512)%nat -> ew E' i = ew (EXU_E regs) i) -> ed E' = ed (EXU_E regs) ->
  ss_resv ssf = None ->
  plookup (@pl_tpi _ PL_prog_B) (ss_pc ssf) = Some (PW RET_WORD_r) ->
  sr_get (ss_regs ssf) 1%bv = SOff 1 0 ->
  sr_get (ss_regs ssf) 10%bv = SLit nn ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssf) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  Z.of_nat (length (PjGrammar.utf8 cp)) = nn ->
  YK0s.ret_ok (getr regs 1) ->
  ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W (ms_mem ms) md k ->
  exu_P memc (ms_mem ms) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - EXU_STK <= x < spZ regs) -> ~ (o <= x < o + nn) ->
     aview rsegs (w_H W) (ms_mem ms) x = aview rsegs (w_H W) memc x) ->
  garr8 rsegs (mrestrict (w_H W) (ms_mem ms)) o (PjGrammar.utf8 cp) ->
  SRr rsegs W (mkCfg ms md) (texutf8_postB SK B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs o cp).
Proof.
intros W E' ssf ms md STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc memc k regs o cp nn
  HS EA ED Hrv Hpl R1s R10s Hcs Hlen Hra HJ HPM KEEP GA.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E').
{ split; [intros i Hi; rewrite EA by lia; apply exu_E_low; unfold A_TEXT; lia | rewrite ED; reflexivity]. }
assert (G1 : getr (ms_regs ms) 1%bv = getr regs 1%bv).
{ rewrite (st_ok_pi_restrict_reg _ _ _ _ 1%bv HS), R1s.
  rewrite denot_lit_U, U_SOff, Z.add_0_r, EA by lia.
  pose proof (bv_unsigned_in_range 64 (ew (EXU_E regs) 1)) as Hr1. change (bv_modulus 64) with (2 ^ 64) in Hr1.
  rewrite (exu_zc _ Hr1), Z_to_bv_bv_unsigned. apply (exu_E_reg regs 1 1%bv); first [reflexivity | lia]. }
pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as G10. rewrite R10s in G10.
apply (paj_ret_at (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B) W E' ssf ms md _ HS Hrv Hpl).
intros mat'. unfold texutf8_postB. split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat' md).
split; [rewrite G1, Hra; reflexivity|].
split; [eapply (ajournal_x_materialize (SK := SK));
  solve [exact HJ | exact LAWS | exact (@pa_segs_low _ B_prog_listing PI_prog_B)]|].
split; [eapply (aregs_preserved_of_st_ok SEGS (w_H W) E' _ ms regs [Z_to_bv 64 SHADOW_OFF] HS HAE); exact Hcs|].
split; [exact HPM|].
split; [rewrite Hlen; exact KEEP|].
split; [rewrite Hlen; exact G10|].
exact GA.
Qed.

(* ---- one arm in one zone: the run from the entry to the return ---- *)
Definition EXU_INST (nn lo hi zlo zhi : Z) : Prop :=
  forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (o cp : Z),
  ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> lo <= cp <= hi ->
  spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs - 16 -> spZ regs <= 2 ^ 47 ->
  sp0 - STK <= spZ regs - EXU_STK -> spZ regs <= sp0 ->
  (forall x, spZ regs - EXU_STK <= x < spZ regs -> apresent (w_H W) memc x) ->
  zlo <= o -> o + nn <= zhi ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o nn ->
  (forall x, o <= x < o + nn ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
  (spZ regs <= o \/ o + nn <= spZ regs - EXU_STK) ->
  (o + nn <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= o) ->
  (o + nn <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= o) ->
  rdword (aview SEGS (w_H W) memc) (VAL (A_OBJ 0)) = Some (VAL (A_OBJ 12)) ->
  rdword (aview SEGS (w_H W) memc) (VAL (A_OBJ 12)) = Some SHADOW_OFF ->
  SRr rsegs W (cfg_at rsegs (B_prog_sigma AS_ex_utf8) regs memc mdc)
    (texutf8_postB SK B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs o cp).

(* the window of a run's region list (the entry's exu_regions): the frame, the output, nothing else *)
Ltac exu_inwr Hr Ha regs o H10 :=
  cbn [ss_mem ss_exu exu_regions In] in Hr;
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
  cbn [stack_region got_regionP bcell_regionP YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?exu_Usp in Ha; rewrite ?(exu_Uo regs o H10) in Ha by exu_lia.
(* the output bytes the run left, per arm (exu_garr1..4) *)
Ltac exu_garr nn HR3 Ex regs o cp H10 H11 :=
  lazymatch eval vm_compute in (nn =? 1, nn =? 2, nn =? 3) with
  | (true, _, _) => eapply (exu_garr1 SEGS Ex _ o cp _ _ _ _ _ HR3)
  | (_, true, _) => eapply (exu_garr2 SEGS Ex _ o cp _ _ _ _ _ HR3)
  | (_, _, true) => eapply (exu_garr3 SEGS Ex _ o cp _ _ _ _ _ HR3)
  | _ => eapply (exu_garr4 SEGS Ex _ o cp _ _ _ _ _ HR3)
  end;
  first [ lazymatch goal with |- bv_unsigned _ = _ => idtac end;
          rewrite ?ew_ewset_other by lia; exact (exu_Uo regs o H10 ltac:(exu_lia))
        | lazymatch goal with |- ew _ _ = _ => idtac end;
          rewrite ?ew_ewset_other by lia; exact (exu_E11 regs cp H11)
        | lazymatch goal with |- In _ _ => idtac end; cbn [In]; repeat (first [left; reflexivity | right])
        | lia ].
(* one arm nn (cp in [lo, hi]) in one zone [zlo, zhi): entry state, ONE run to the `ret`, the return *)
Ltac exu_core nn lo hi zlo zhi :=
  unfold EXU_INST; intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs o cp
    HJ Hra H10 H11 Hcp Hal Hsp1 Hsp2 Hs1 Hs2 Hfrm Hz1 Hz2 HRA Hwr Hdj Hg Hc Kgot Kcell;
  unfold EXU_STK in Hs1, Hfrm, Hdj;
  let cs := lazymatch eval vm_compute in (nn =? 3) with true => constr:(EXU_CS3) | false => constr:(@nil acond) end in
  assert (Hcs : conds_ok (EXU_E regs) cs) by (first [exact I | exact (exu_c3 regs cp H11 ltac:(lia))]);
  pose proof (exu_entry W regs memc o cp nn lo hi zlo zhi cs H10 H11 Hcp ltac:(lia) ltac:(lia)
    Hal Hsp1 Hsp2 Hfrm ltac:(exu_lia) Hz1 Hz2 ltac:(exu_lia) ltac:(lia)
    (fun x Hx => proj2 (Hwr x Hx)) Hdj Hg Hc Kgot Kcell Hcs ltac:(vm_compute; reflexivity)) as HS;
  assert (HEI : img_env VAL A_LIM (EXU_E regs)) by (unfold EXU_E; apply Eimg_env);
  assert (SHOK : sh_ok SEGS EXU_Bx [] (EXU_E regs) (mrestrict (w_H W) memc)) by apply Forall_nil;
  assert (HPM : exu_P memc memc) by (intros Hm; exact Hm);
  pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B PST ARx LAWS _ (exu_plaw memc));
  unfold cfg_at, w64; rewrite exu_pc_eq;
  paj_run_tok_x_inv RUN HS HJ SHOK HPM (exu_Bspan zlo zhi);
  first
  [ (* a token obligation: the output byte o + i's shadow cell *)
    lazymatch goal with |- range_addressable _ _ (U _ (SOff 10 ?i)) _ =>
      apply (exu_ob W memc regs o nn i H10); [exu_lia | exu_lia | lia | lia | exact HRA] end
  | (* the write premise: the frame (the caller's window) and the output (awr_byte by the premise) *)
    lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ =>
      let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
      intros a (r & Hr & Ha); exu_inwr Hr Ha regs o H10;
      [ unfold awr_byte; left; lia | lia | lia | exact (proj1 (Hwr a ltac:(lia))) ] end
  | (* the return *)
    lazymatch goal with
    | HS0 : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx), HFr0 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- SRr _ _ _ _ =>
      let HR3 := fresh "HR3" in
      pose proof (exu_region_nth _ _ _ _ 3 _ HS0 eq_refl) as HR3; cbn [ms_mem restrict] in HR3;
      apply (exu_finish W Ex ssx msx _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc memc k regs o cp nn HS0);
      [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; rewrite ?ew_ewset_other by lia; reflexivity
      | reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | first [rewrite exu_arm1 by lia | rewrite exu_arm2 by lia | rewrite exu_arm3 by lia | rewrite exu_arm4 by lia];
        reflexivity
      | exact Hra
      | exact HJ
      | exact HPM
      | let x := fresh "x" in let Hx := fresh "Hx" in let Hn1 := fresh "Hn1" in let Hn2 := fresh "Hn2" in
        let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
        intros x Hx Hn1 Hn2; apply (exu_aview_frame _ _ _ _ _ x HFr0 Hx);
        intros (r & Hr & Ha); exu_inwr Hr Ha regs o H10; exu_lia
      | exu_garr nn HR3 Ex regs o cp H10 H11 ]
    end ].

Lemma exu_i_1_1 : EXU_INST 1 0 127 (fst EXU_Z1) (snd EXU_Z1). Proof. exu_core 1 0 127 (fst EXU_Z1) (snd EXU_Z1). Qed.
Lemma exu_i_1_2 : EXU_INST 1 0 127 (fst EXU_Z2) (snd EXU_Z2). Proof. exu_core 1 0 127 (fst EXU_Z2) (snd EXU_Z2). Qed.
Lemma exu_i_1_3 : EXU_INST 1 0 127 (fst EXU_Z3) (snd EXU_Z3). Proof. exu_core 1 0 127 (fst EXU_Z3) (snd EXU_Z3). Qed.
Lemma exu_i_1_4 : EXU_INST 1 0 127 (fst EXU_Z4) (snd EXU_Z4). Proof. exu_core 1 0 127 (fst EXU_Z4) (snd EXU_Z4). Qed.
Lemma exu_i_2_1 : EXU_INST 2 128 2047 (fst EXU_Z1) (snd EXU_Z1). Proof. exu_core 2 128 2047 (fst EXU_Z1) (snd EXU_Z1). Qed.
Lemma exu_i_2_2 : EXU_INST 2 128 2047 (fst EXU_Z2) (snd EXU_Z2). Proof. exu_core 2 128 2047 (fst EXU_Z2) (snd EXU_Z2). Qed.
Lemma exu_i_2_3 : EXU_INST 2 128 2047 (fst EXU_Z3) (snd EXU_Z3). Proof. exu_core 2 128 2047 (fst EXU_Z3) (snd EXU_Z3). Qed.
Lemma exu_i_2_4 : EXU_INST 2 128 2047 (fst EXU_Z4) (snd EXU_Z4). Proof. exu_core 2 128 2047 (fst EXU_Z4) (snd EXU_Z4). Qed.
Lemma exu_i_3_1 : EXU_INST 3 2048 65535 (fst EXU_Z1) (snd EXU_Z1). Proof. exu_core 3 2048 65535 (fst EXU_Z1) (snd EXU_Z1). Qed.
Lemma exu_i_3_2 : EXU_INST 3 2048 65535 (fst EXU_Z2) (snd EXU_Z2). Proof. exu_core 3 2048 65535 (fst EXU_Z2) (snd EXU_Z2). Qed.
Lemma exu_i_3_3 : EXU_INST 3 2048 65535 (fst EXU_Z3) (snd EXU_Z3). Proof. exu_core 3 2048 65535 (fst EXU_Z3) (snd EXU_Z3). Qed.
Lemma exu_i_3_4 : EXU_INST 3 2048 65535 (fst EXU_Z4) (snd EXU_Z4). Proof. exu_core 3 2048 65535 (fst EXU_Z4) (snd EXU_Z4). Qed.
Lemma exu_i_4_1 : EXU_INST 4 65536 (2 ^ 21 - 1) (fst EXU_Z1) (snd EXU_Z1).
Proof. exu_core 4 65536 (2 ^ 21 - 1) (fst EXU_Z1) (snd EXU_Z1). Qed.
Lemma exu_i_4_2 : EXU_INST 4 65536 (2 ^ 21 - 1) (fst EXU_Z2) (snd EXU_Z2).
Proof. exu_core 4 65536 (2 ^ 21 - 1) (fst EXU_Z2) (snd EXU_Z2). Qed.
Lemma exu_i_4_3 : EXU_INST 4 65536 (2 ^ 21 - 1) (fst EXU_Z3) (snd EXU_Z3).
Proof. exu_core 4 65536 (2 ^ 21 - 1) (fst EXU_Z3) (snd EXU_Z3). Qed.
Lemma exu_i_4_4 : EXU_INST 4 65536 (2 ^ 21 - 1) (fst EXU_Z4) (snd EXU_Z4).
Proof. exu_core 4 65536 (2 ^ 21 - 1) (fst EXU_Z4) (snd EXU_Z4). Qed.

(* ---- the run form texutf8_runB (ExsB_Callee.v), as stated ---- *)
Theorem ex_utf8_run_B : texutf8_runB SK B PST ARx (B_prog_sigma AS_ex_utf8).
Proof.
unfold texutf8_runB. intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs o cp. cbv zeta.
intros HJ Hra _ H10 H11 Hcp Hal Hs1 Hs2 Hfrm Ho Ho47 HRA Hwr Hdj.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (_ & _ & Hc0 & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Hsp1 : 2 ^ 46 <= spZ regs - 16) by (unfold EXU_STK in Hs1; lia).
assert (Hsp2 : spZ regs <= 2 ^ 47) by lia.
(* the shadow base through the GOT: the allocator's const law at the current state, at image B's atoms (PALibCore) *)
destruct (alx_const _ _ _ LAWS lyc Sc Hpc W memc mdc HARc) as (Kcell & _ & Kgot & _).
rewrite (palc_got_shadow _ PALC), (palc_cell _ PALC) in Kgot. rewrite (palc_cell _ PALC) in Kcell.
remember (Z.of_nat (length (PjGrammar.utf8 cp))) as n eqn:Hndef.
assert (Hn : 1 <= n <= 4).
{ rewrite Hndef. destruct (Z_lt_le_dec cp 128);
    [rewrite exu_arm1 by lia | destruct (Z_lt_le_dec cp 2048);
      [rewrite exu_arm2 by lia | destruct (Z_lt_le_dec cp 65536); [rewrite exu_arm3 by lia | rewrite exu_arm4 by lia]]];
    cbn; lia. }
(* every output byte: in a zone, off the GOT word and the shadow cell *)
assert (WB : forall x, o <= x < o + n ->
  (exu_zin EXU_Z1 x \/ exu_zin EXU_Z2 x \/ exu_zin EXU_Z3 x \/ exu_zin EXU_Z4 x) /\
  ~ (VAL (A_OBJ 0) <= x < VAL (A_OBJ 0) + 8) /\ ~ (VAL (A_OBJ 12) <= x < VAL (A_OBJ 12) + 8))
  by (intros x Hx; exact (exu_wr_byte STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k x HJ (proj1 (Hwr x Hx)))).
assert (Hg : o + n <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= o).
{ destruct (Z_le_gt_dec (o + n) (VAL (A_OBJ 0))) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_le_gt_dec (VAL (A_OBJ 0) + 8) o) as [Hr|Hr]; [right; exact Hr|].
  exfalso. destruct (WB (Z.max o (VAL (A_OBJ 0))) ltac:(lia)) as (_ & Hn0 & _). apply Hn0. lia. }
assert (Hc : o + n <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= o).
{ destruct (Z_le_gt_dec (o + n) (VAL (A_OBJ 12))) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_le_gt_dec (VAL (A_OBJ 12) + 8) o) as [Hr|Hr]; [right; exact Hr|].
  exfalso. destruct (WB (Z.max o (VAL (A_OBJ 12))) ltac:(lia)) as (_ & _ & Hn0). apply Hn0. lia. }
(* the first and the last output byte lie in one zone, so all n <= 4 bytes do (the zones are more than 4 apart) *)
assert (Hzone : (fst EXU_Z1 <= o /\ o + n <= snd EXU_Z1) \/ (fst EXU_Z2 <= o /\ o + n <= snd EXU_Z2) \/
                (fst EXU_Z3 <= o /\ o + n <= snd EXU_Z3) \/ (fst EXU_Z4 <= o /\ o + n <= snd EXU_Z4)).
{ destruct (WB o ltac:(lia)) as (Zo & _). destruct (WB (o + n - 1) ltac:(lia)) as (Ze & _).
  clear - Zo Ze Hn. exu_lia. }
assert (G : forall nn lo hi zlo zhi, EXU_INST nn lo hi zlo zhi -> n = nn -> lo <= cp <= hi -> zlo <= o -> o + n <= zhi ->
  SRr rsegs W (cfg_at rsegs (B_prog_sigma AS_ex_utf8) regs memc mdc)
    (texutf8_postB SK B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs o cp)).
{ intros nn lo hi zlo zhi HI Hnn Hcp' Hz1 Hz2. subst nn.
  exact (HI STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs o cp HJ Hra H10 H11 Hcp' Hal Hsp1 Hsp2
    Hs1 Hs2 Hfrm Hz1 Hz2 HRA Hwr Hdj Hg Hc Kgot Kcell). }
destruct (Z_lt_le_dec cp 128) as [A1|A1]; [|destruct (Z_lt_le_dec cp 2048) as [A2|A2];
  [|destruct (Z_lt_le_dec cp 65536) as [A3|A3]]].
- assert (En : n = 1) by (rewrite Hndef, exu_arm1 by lia; reflexivity).
  destruct Hzone as [[Z1 Z2]|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]].
  + exact (G 1 0 127 _ _ exu_i_1_1 En ltac:(lia) Z1 Z2).
  + exact (G 1 0 127 _ _ exu_i_1_2 En ltac:(lia) Z1 Z2).
  + exact (G 1 0 127 _ _ exu_i_1_3 En ltac:(lia) Z1 Z2).
  + exact (G 1 0 127 _ _ exu_i_1_4 En ltac:(lia) Z1 Z2).
- assert (En : n = 2) by (rewrite Hndef, exu_arm2 by lia; reflexivity).
  destruct Hzone as [[Z1 Z2]|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]].
  + exact (G 2 128 2047 _ _ exu_i_2_1 En ltac:(lia) Z1 Z2).
  + exact (G 2 128 2047 _ _ exu_i_2_2 En ltac:(lia) Z1 Z2).
  + exact (G 2 128 2047 _ _ exu_i_2_3 En ltac:(lia) Z1 Z2).
  + exact (G 2 128 2047 _ _ exu_i_2_4 En ltac:(lia) Z1 Z2).
- assert (En : n = 3) by (rewrite Hndef, exu_arm3 by lia; reflexivity).
  destruct Hzone as [[Z1 Z2]|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]].
  + exact (G 3 2048 65535 _ _ exu_i_3_1 En ltac:(lia) Z1 Z2).
  + exact (G 3 2048 65535 _ _ exu_i_3_2 En ltac:(lia) Z1 Z2).
  + exact (G 3 2048 65535 _ _ exu_i_3_3 En ltac:(lia) Z1 Z2).
  + exact (G 3 2048 65535 _ _ exu_i_3_4 En ltac:(lia) Z1 Z2).
- assert (En : n = 4) by (rewrite Hndef, exu_arm4 by lia; reflexivity).
  destruct Hzone as [[Z1 Z2]|[[Z1 Z2]|[[Z1 Z2]|[Z1 Z2]]]].
  + exact (G 4 65536 (2 ^ 21 - 1) _ _ exu_i_4_1 En ltac:(lia) Z1 Z2).
  + exact (G 4 65536 (2 ^ 21 - 1) _ _ exu_i_4_2 En ltac:(lia) Z1 Z2).
  + exact (G 4 65536 (2 ^ 21 - 1) _ _ exu_i_4_3 En ltac:(lia) Z1 Z2).
  + exact (G 4 65536 (2 ^ 21 - 1) _ _ exu_i_4_4 En ltac:(lia) Z1 Z2).
Qed.
End w.
End u.

(* the statement as the restated texts and the ex_string walk cite it (implicit arguments shown) *)
Set Printing Implicit.
About ex_utf8_run_B.
Check ex_utf8_run_B.
Unset Printing Implicit.
Print Assumptions ex_utf8_run_B.
