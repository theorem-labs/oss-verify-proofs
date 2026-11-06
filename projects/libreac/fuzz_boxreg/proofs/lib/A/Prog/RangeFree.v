(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 725 of its 785 lines of code are new or changed and 309 lines of the source are left out. *)
(* range_free (fuzz_boxreg.asan 0x81430, 61 instructions): the contract of the ASan build's code. range_free is a
   static function of the harness (fuzz/fuzz_boxreg.c:94-102).
   The function takes a 16-byte frame on the machine stack (addi sp,sp,-16; it saves ra there for the call of
   __asan_report_load4) and calls no function on a path that returns. It returns 0 in a0 when base (a1) < 0 or
   base > fabric - nch (a3 - a2). Else it reads the 288-byte table t (a0): n (t + 280), then base (t + 56 i + 8) and
   nch (t + 56 i + 12) of the rows i < n, each 4-byte load after the check of its shadow byte, up to the first row
   whose [base_i, base_i + nch_i) meets [base, base + nch). It returns 0 when a row meets, else 1: 1 exactly when
   Pau's range_free_ok of lib/Prog/range_free_c.v holds, used as it is with the model of lib/Prog/Boxreg.v. It
   writes nothing outside its own frame.
   Where the table lies: every call passes &prev, the harness's local struct reac_boxreg prev (fuzz/fuzz_boxreg.c:210),
   which LLVMFuzzerTestOneInput fills at each loop top with memcpy (&prev, r, sizeof prev) (:211); it is never the
   registry block r. prev is at offset 0x40 of the harness's 416-byte ASan frame block (0x80160 .. 0x80164:
   addi a0,a3,0x40; sd a0,0x78(s1)). The harness poisons its 36 shadow bytes (frame shadow + 8 .. + 0x2b) with 0xf8
   at entry, clears them at each loop top (0x80234 .. 0x802c0) and then calls __asan_memcpy (prev, r, 288) (0x802d0).
   The calls: LLVMFuzzerTestOneInput at 0x80564 (a0 = ld 0x78(s1) at 0x80554) and lowest_free at 0x81574 (its own
   a0, which LLVMFuzzerTestOneInput loads from 0x78(s1) at 0x80928 and 0x80d00). That frame block is the
   __asan_stack_malloc_3 side-stack frame (0x7ffbc), a frame in frames S, so the premise is afobj SEGS B ly S W mem
   t 288 (lib/A/Prog/BoxBase.v; the form of the MAC premise of ReacBoxregFind.v), with the 288 bytes bs of t.
   Hazards.
   (1) The struct is 288 bytes (rows 0..280 with stride 56, n at +280, fabric at +284). The code reads the rows
       i < n without a bound of its own, so n <= 5 (boxreg_B1) keeps every load inside the 288 bytes. range_free
       does not read the table's fabric: it uses its argument fabric.
   (2) afobj holds only on the fake-stack path: when the runtime's detect_stack_use_after_return flag is 0 (or
       __asan_stack_malloc_3 returns 0) the harness takes its fallback (0x7ffc8 .. 0x7ffec: the frame block on the
       machine stack below its own frame), and prev is then in the caller's stack window, which afobj does not
       cover. cgif's model (stack_malloc_progressP) always gives the fake frame.
   (3) fabric - nch (subw at 0x81444) and base + nch (addw at 0x81478) are 32-bit operations; -2^31 <= base < 2^31,
       1 <= nch <= 40 and 1 <= fabric <= 40 keep them exact. base_i + nch_i (addw at 0x814b0) is kept exact by the
       row bounds of boxreg_B3 with boxreg_B2. n is compared as a signed word (blez at 0x81474: n <= 0 returns 1).
   (4) The shadow-checked loads are t + 280 and, for i < n, t + 56 i + 8 and t + 56 i + 12; the branches to
       __asan_report_load4 (0x814f8, 0x81518, 0x81520) are refuted by afobj's range_addressable. The only other
       read is the GOT word of the shadow base (0x8144c .. 0x81454), fixed by AR (AR_const_law).
   (5) No f* or csr instruction occurs in the 61 instructions (measured), so the fixed {fx} is sound.
   (6) The model premises are those of the old walk (a working branch 67b70ae1ec3
       proofs/libreac/fuzz_boxreg/lib/A/Prog/range_free_c.v): the argument ranges and boxreg_B1..B3 of the table.
       The harness meets them from check (r, fabric) on the registry it copied (boxreg_B16), from legal_width
       (2 <= nch <= 40) and from its fabric (1..40); lowest_free meets them from its own premises and its loop
       guard 0 <= base <= fabric - nch.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBRangeFree.v, 0x814e8) adds UBSan checks (alignment of t,
   the row index 5, pointer overflow of t + 56 i, overflow of base_i + nch_i); the result is the same. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg range_free_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Bytes PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 16-byte frame and ESTACK below it for the
   memory-checking runtime (it calls nothing but the error path). *)
Definition A_range_freeP : Z := BASE + AF_range_free.
Definition RANGE_FREE_STK : Z := 16 + ESTACK.
Section h.
Variable B : asyms.
Definition trange_free_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (base nch fabric : Z)
  (bs : list byte) : world SEGS -> config -> Prop :=
apost_base SEGS B RANGE_FREE_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
((range_free_c.range_free_ok bs base nch fabric /\ getr regs' 10 = w64 1) \/
 (~ range_free_c.range_free_ok bs base nch fabric /\ getr regs' 10 = w64 0))).
Definition trange_free_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (t base nch fabric : Z) (bs : list byte),
afn_pre SEGS B RANGE_FREE_STK ly S W regs mem md ch ->
getr regs 10 = w64 t -> getr regs 11 = w64 base -> getr regs 12 = w64 nch -> getr regs 13 = w64 fabric ->
-2 ^ 31 <= base < 2 ^ 31 -> 1 <= nch <= 40 -> 1 <= fabric <= 40 ->
afobj SEGS B ly S W mem t ReacBoxregInit.REG_SIZE -> length bs = 288%nat ->
(forall i, 0 <= i < ReacBoxregInit.REG_SIZE ->
  aview SEGS (w_H W) mem (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
SRr SEGS W (cfg_at SEGS A_range_freeP regs mem md) (trange_free_post regs ly S W mem md base nch fabric bs).
(* The walk. Symbolic frame: atom 32 is the shadow offset (loaded through the GOT word, object 1, from the shadow
   cell, object 12: PALib), atom 33 the row count n (t + 280), atoms 34 + 2i / 35 + 2i the base and nch of row i
   (t + 56i + 8 / + 12); the table is one region at atom 10 (t), its shadow one entry [t, t + 288) from afobj. The loop
   is walked row by row; after row i the two paths that go on (base >= base_i + nch_i, or base_i >= base + nch) meet at
   0x814bc with the same registers and memory, so each row states that join once (rf_join) and both paths use it. At
   the top of each later row the shadow pointer a4, which the code steps by 7, is folded back to
   SB + (t + 8 + 56i) >> 3 (rf_pin, from t mod 8 = 0) so that the shadow checks are recognised. *)
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).

(* 1. byte arithmetic: the four bytes at offset k of the table, read little-endian *)
Definition rvb (bs : list byte) (k : Z) : Z := bytes_le_to_Z (Boxreg.bsub bs k 4).
Lemma rf_nth_firstn : forall (A : Type) (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros n j d H; cbn.
- destruct n; [lia|]. destruct j; reflexivity.
- destruct n; [lia|]. cbn. destruct j; [reflexivity|]. apply IH. lia.
Qed.
Lemma rf_nth_skipn : forall (A : Type) (l : list A) k j d, nth j (skipn k l) d = nth (k + j) l d.
Proof.
intros A l k. revert l. induction k as [|k IH]; intros l j d; [reflexivity|].
destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.
Lemma rf_bsub_nth : forall bs k j d, 0 <= k -> (j < 4)%nat ->
nth j (Boxreg.bsub bs k 4) d = nth (Z.to_nat k + j) bs d.
Proof.
intros bs k j d Hk Hj. unfold Boxreg.bsub.
rewrite rf_nth_firstn by lia. apply rf_nth_skipn.
Qed.
Lemma rf_bsub_len : forall bs k, length bs = 288%nat -> 0 <= k -> k + 4 <= 288 ->
length (Boxreg.bsub bs k 4) = 4%nat.
Proof. intros bs k HL Hk Hk4. rewrite (Boxreg.bsub_length bs k 4) by lia. reflexivity. Qed.
Lemma rf_rvb_range : forall bs k, length bs = 288%nat -> 0 <= k -> k + 4 <= 288 -> 0 <= rvb bs k < 2 ^ 32.
Proof.
intros bs k HL Hk Hk4. unfold rvb. split; [apply PropExec.bytes_le_to_Z_nonneg|].
pose proof (PropExec.bytes_le_to_Z_bound (Boxreg.bsub bs k 4)) as H.
rewrite (rf_bsub_len bs k HL Hk Hk4) in H. exact H.
Qed.
Lemma rf_rvb_rd4 : forall bs k, length bs = 288%nat -> 0 <= k -> k + 4 <= 288 ->
0 <= Boxreg.rd4 bs k -> rvb bs k = Boxreg.rd4 bs k.
Proof.
intros bs k HL Hk Hk4 Hpos. pose proof (rf_rvb_range bs k HL Hk Hk4) as Hr.
unfold Boxreg.rd4 in *. fold (rvb bs k) in *. unfold bv_swrap, bv_wrap in *.
change (bv_half_modulus 32) with 2147483648 in *. change (bv_modulus 32) with 4294967296 in *.
change (2 ^ 32) with 4294967296 in Hr. Z.div_mod_to_equations. lia.
Qed.
Lemma rf_le_byte4 : forall (l : list byte) k, length l = 4%nat -> (k < 4)%nat ->
Z_to_bv 8 (YO0f.le_byte (bytes_le_to_Z l) 4 k) = nth k l (Z_to_bv 8 0).
Proof.
intros l k Hl Hk.
destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 l]]]]]; cbn in Hl; try lia.
rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
destruct k as [|[|[|[|k]]]]; try lia; cbn [nth];
[ change (8 * Z.of_nat 0) with 0 | change (8 * Z.of_nat 1) with 8
| change (8 * Z.of_nat 2) with 16 | change (8 * Z.of_nat 3) with 24 ];
rewrite ?Z.shiftr_0_r, ?Z.shiftr_div_pow2 by lia;
[ change (2 ^ 0) with 1 | change (2 ^ 8) with 256 | change (2 ^ 16) with 65536 | change (2 ^ 24) with 16777216 ];
Z.div_mod_to_equations; lia.
Qed.
Lemma rf_val_mem : forall (H : word -> bool) mem t bs k,
length bs = 288%nat ->
(forall i, 0 <= i < 288 -> aview SEGS H mem (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
0 <= k -> k + 4 <= 288 -> val_mem SEGS (mrestrict H mem) (t + k) 4 (rvb bs k).
Proof.
intros Hh mem t bs k HL HBS Hk Hk4 j Hj.
pose proof (HBS (k + Z.of_nat j) ltac:(lia)) as Ha. unfold aview in Ha.
destruct (mbyte SEGS (mrestrict Hh mem) (t + (k + Z.of_nat j))) as [b|] eqn:Hb; cbn in Ha; [|discriminate].
injection Ha as Ha. replace (t + k + Z.of_nat j) with (t + (k + Z.of_nat j)) by lia. rewrite Hb. f_equal.
unfold rvb. rewrite (rf_le_byte4 (Boxreg.bsub bs k 4) j (rf_bsub_len bs k HL Hk Hk4) Hj).
rewrite rf_bsub_nth by lia. replace (Z.to_nat k + j)%nat with (Z.to_nat (k + Z.of_nat j)) by lia.
apply bv_eq. exact Ha.
Qed.
(* 2. denotations *)
Lemma rf_den : forall E v z, U E v = z mod 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof.
intros E v z Hz. rewrite denot_lit_U, Hz. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma rf_U_off : forall E n v c, ew E n = Z_to_bv 64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
intros E n v c Hn. rewrite U_SOff, Hn, Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma rf_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c Hn. apply rf_den. apply (rf_U_off E n v c Hn). Qed.
Lemma rf_den_off0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v Hn. rewrite (rf_den_off E n v 0 Hn). f_equal. lia.
Qed.
Lemma rf_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z. apply rf_den. rewrite U_SLit. reflexivity. Qed.
Lemma rf_den_add : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
sv_denot E (SAlu ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb. apply rf_den. rewrite U_SAlu. cbn [zalu_raw].
unfold U at 1 2. rewrite Ha, Hb, !Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma rf_mod_sq : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. replace (z mod 2 ^ 64) with (z + - (z / 2 ^ 64) * 2 ^ 32 * 2 ^ 32).
- apply Z_mod_plus_full.
- rewrite (Z.mod_eq z (2 ^ 64)) by lia. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). ring.
Qed.
Lemma rf_den_addw : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
-2 ^ 31 <= x + y < 2 ^ 31 -> sv_denot E (SAluw ALU_ADD a b) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hr. apply rf_den. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
unfold U at 1 2. rewrite Ha, Hb, !Z_to_bv_unsigned.
unfold bv_wrap at 2 3. change (bv_modulus 64) with (2 ^ 64).
rewrite !rf_mod_sq.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31).
Z.div_mod_to_equations. lia.
Qed.
Lemma rf_den_subw : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
-2 ^ 31 <= x - y < 2 ^ 31 -> sv_denot E (SAluw ALU_SUB a b) = Z_to_bv 64 (x - y).
Proof.
intros E a b x y Ha Hb Hr. apply rf_den. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
unfold U at 1 2. rewrite Ha, Hb, !Z_to_bv_unsigned.
unfold bv_wrap at 2 3. change (bv_modulus 64) with (2 ^ 64).
rewrite !rf_mod_sq.
unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31).
Z.div_mod_to_equations. lia.
Qed.
(* 3. branch conditions *)
Lemma rf_lt_t : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
-2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = true -> x < y.
Proof.
intros E a b x y Ha Hb Hx Hy H. rewrite Ha, Hb in H. cbn [branch_taken] in H.
rewrite Boxreg.lts_lit in H by lia. apply Z.ltb_lt. exact H.
Qed.
Lemma rf_lt_f : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
-2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = false -> y <= x.
Proof.
intros E a b x y Ha Hb Hx Hy H. rewrite Ha, Hb in H. cbn [branch_taken] in H.
rewrite Boxreg.lts_lit in H by lia. apply Z.ltb_ge. exact H.
Qed.
Lemma rf_ge_t : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
-2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E a) (sv_denot E b) = true -> y <= x.
Proof.
intros E a b x y Ha Hb Hx Hy H. rewrite Ha, Hb in H. cbn [branch_taken] in H.
rewrite Boxreg.lts_lit in H by lia. apply Z.ltb_ge. apply negb_true_iff in H. exact H.
Qed.
Lemma rf_ge_f : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
-2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E a) (sv_denot E b) = false -> x < y.
Proof.
intros E a b x y Ha Hb Hx Hy H. rewrite Ha, Hb in H. cbn [branch_taken] in H.
rewrite Boxreg.lts_lit in H by lia. apply Z.ltb_lt. apply negb_false_iff in H. exact H.
Qed.
Lemma rf_eq_t : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
-2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = true -> x = y.
Proof.
intros E a b x y Ha Hb Hx Hy H. rewrite Ha, Hb in H. cbn [branch_taken] in H.
unfold bv_eqb in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
change (bv_modulus 64) with (2 ^ 64) in H. apply Z.eqb_eq in H. Z.div_mod_to_equations. lia.
Qed.
Lemma rf_eq_f : forall E a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = false -> x <> y.
Proof.
intros E a b x y Ha Hb H Hxy. rewrite Ha, Hb, Hxy in H. cbn [branch_taken] in H.
unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate.
Qed.
(* 4. facts *)
Lemma rf_afact : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= lo -> lo <= v -> v <= hi -> hi < 2 ^ 64 ->
afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi Hn Hlo Hv Hvh Hh. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.
Lemma rf_facts_drop : forall E ss ms,
st_ok_pi SEGS VAL E ss ms ->
st_ok_pi SEGS VAL E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
  (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms HS. unfold st_ok_pi in *.
destruct ss as [pc sr fr sm rv G].
cbn [ss_facts ss_pc ss_regs ss_fregs ss_mem ss_resv abs_ss setpc] in *.
apply (st_ok_set_facts SEGS E _ ms (mkFacts (f_atoms G) [] (f_alias G)) HS).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & Hc & Hl)).
cbn [ss_facts] in Ha, Hl. split; [exact Ha | split; [exact I | exact Hl]].
Qed.
(* the a4 shadow pointer, re-folded at the top of each row *)
Lemma rf_pin : forall E t k,
ew E 10 = Z_to_bv 64 t -> ew E 32 = Z_to_bv 64 2147450880 ->
0 <= t -> t + 300 < 2 ^ 47 -> t mod 8 = 0 -> 0 <= k <= 240 -> k mod 8 = 0 ->
sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 (k + 56)) (SLit 3)))
= sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 k) (SLit 3))) (SLit 7)).
Proof.
intros E t k H10 H32 Ht0 Ht1 Ht8 Hk Hk8.
assert (Hdiv : (t + (k + 56)) / 8 = (t + k) / 8 + 7) by (Z.div_mod_to_equations; lia).
assert (Hd0 : 0 <= (t + k) / 8 <= t + k) by (Z.div_mod_to_equations; lia).
assert (A1 : U E (SOff 10 (k + 56)) = t + (k + 56))
by (rewrite (rf_U_off E 10 t (k + 56) H10); apply Z.mod_small; lia).
assert (A2 : U E (SOff 10 k) = t + k) by (rewrite (rf_U_off E 10 t k H10); apply Z.mod_small; lia).
assert (A4 : U E (SOff 32 0) = 2147450880) by (rewrite (rf_U_off E 32 _ 0 H32); apply Z.mod_small; lia).
rewrite !denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw].
rewrite A1, A2, A4, !U_SLit. change (zcanon 3) with 3. change (zcanon 7) with 7.
change (Z.land 3 63) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite Hdiv. unfold zcanon, M64. Z.div_mod_to_equations. lia.
Qed.
(* 5. the image and the symbolic frame *)
Definition RF_SB : Z := 0x7fff8000.
Definition RFx : sv := SOff 32 0.
Definition RFspan : Z * Z := (RF_SB, RF_SB + 2 ^ 44 - 1).
Definition rf_rowc (i : nat) : list YP09.chunk :=
[YP09.mkChunk (56 * Z.of_nat i + 8) (CVal 4 (SOff (34 + 2 * i) 0));
 YP09.mkChunk (56 * Z.of_nat i + 12) (CVal 4 (SOff (35 + 2 * i) 0))].
Definition rf_tab : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 288 0 0 (flat_map rf_rowc (seq 0 5) ++ [YP09.mkChunk 280 (CVal 4 (SOff 33 0))]).
Definition rf_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3);
         (32%nat, mkAF RF_SB RF_SB 0); (33%nat, mkAF 0 5 0)] [] [].
Definition rf_ss0 : sstate :=
mkSS AF_range_free sr_atoms [stack_region 16; got_regionP; bcell_regionP 32; rf_tab] None rf_facts0.
Definition rf_SH : list shent := [mkSHE 10 0 288].
Definition rf_extra (bs : list byte) : list word :=
map (Z_to_bv 64) [RF_SB; rvb bs 280;
  rvb bs 8; rvb bs 12; rvb bs 64; rvb bs 68; rvb bs 120; rvb bs 124;
  rvb bs 176; rvb bs 180; rvb bs 232; rvb bs 236].
Definition EC (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (rf_extra bs)).
Lemma rf_ew : forall regs bs i v, nth i (rf_extra bs) (Z_to_bv 64 0) = v -> (i < 12)%nat ->
ew (EC regs bs) (32 + i) = v.
Proof.
intros regs bs i v Hv Hi. unfold EC. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. exact Hv.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
Lemma rf_entry : forall ly S W (regs : bvmap 5 word) mem md ch (t : Z) (bs : list byte),
afn_pre SEGS B RANGE_FREE_STK ly S W regs mem md ch ->
getr regs 10 = w64 t ->
afobj SEGS B ly S W mem t ReacBoxregInit.REG_SIZE -> length bs = 288%nat ->
(forall i, 0 <= i < ReacBoxregInit.REG_SIZE ->
  aview SEGS (w_H W) mem (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs ->
st_ok_pi SEGS VAL (EC regs bs) rf_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_range_freeP) mem (seg_rom SEGS)))
/\ sh_ok SEGS RFx rf_SH (EC regs bs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch t bs HPRE H10 HFO HLEN HBS HB1.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Ht8 & HRA).
change ReacBoxregInit.REG_SIZE with 288 in Hfhi, HRA, HBS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RANGE_FREE_STK = 4112) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfin) as Hfimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (Hn5 : 0 <= rvb bs 280 <= 5).
{ unfold Boxreg.boxreg_B1, Boxreg.bx_n in HB1.
  rewrite (rf_rvb_rd4 bs 280 HLEN ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
rewrite restrict_mkst_fx.
set (E := EC regs bs) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rf_extra bs)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 RF_SB) by (apply (rf_ew regs bs 0%nat); [reflexivity | lia]).
assert (E33 : ew E 33 = Z_to_bv 64 (rvb bs 280)) by (apply (rf_ew regs bs 1%nat); [reflexivity | lia]).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Ht : 4096 <= t /\ t + 288 <= alloc_ceiling) by lia.
split.
- unfold rf_ss0, A_range_freeP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, rf_tab.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RFx RF_SB);
      [cbn [sv_denot RFx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold RF_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat t E10) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc.
      apply in_app_or in Hc as [Hc | Hc].
      -- apply in_flat_map in Hc as (i & Hi & Hc). apply in_seq in Hi.
         unfold rf_rowc in Hc. cbn [In] in Hc.
         assert (Hb : forall k j, 0 <= k -> k + 4 <= 288 -> (j < 12)%nat ->
           nth j (rf_extra bs) (Z_to_bv 64 0) = Z_to_bv 64 (rvb bs k) ->
           YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) t (YP09.mkChunk k (CVal 4 (SOff (32 + j) 0)))).
         { intros k j Hk Hk4 Hj Hnth.
           pose proof (rf_ew regs bs j _ Hnth Hj) as Hw. change (EC regs bs) with E in Hw.
           apply (chunk_ok_val SEGS E _ t k 4 (SOff (32 + j) 0) (rvb bs k));
           [ cbn [sv_denot]; rewrite Hw, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | cbn; pose proof (rf_rvb_range bs k HLEN Hk Hk4); lia | zside |].
           exact (rf_val_mem (w_H W) mem t bs k HLEN HBS Hk Hk4). }
         destruct Hi as [_ Hi5].
         destruct i as [|[|[|[|[|i]]]]]; try lia; cbn [Z.of_nat Z.mul Z.add] in Hc;
         (destruct Hc as [<- | [<- | []]]).
         ++ exact (Hb 8 2%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 12 3%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 64 4%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 68 5%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 120 6%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 124 7%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 176 8%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 180 9%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 232 10%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
         ++ exact (Hb 236 11%nat ltac:(lia) ltac:(lia) ltac:(lia) eq_refl).
      -- cbn [In] in Hc. destruct Hc as [<- | []].
         apply (chunk_ok_val SEGS E _ t 280 4 (SOff 33 0) (rvb bs 280));
         [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | cbn; lia | zside |].
         exact (rf_val_mem (w_H W) mem t bs 280 HLEN HBS ltac:(lia) ltac:(lia)).
  + apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, rf_tab, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat t E10) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hfimg HcellR HgcD HgotR Ht WS Hstk0 Hal16 Hflo Hfhi Hf4096 Hfceil C1.
    clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rf_facts0 f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
            revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; unfold alloc_ceiling; clear; intros;
            repeat split; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia;
            change (2 ^ 3) with 8; revert Ht Ht8 C1; clear; intros; repeat split; lia|].
    split; [exact (rf_afact E 32 RF_SB RF_SB RF_SB E32 ltac:(unfold RF_SB; lia) ltac:(lia) ltac:(lia) ltac:(unfold RF_SB; lia))|].
    split; [exact (rf_afact E 33 (rvb bs 280) 0 5 E33 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact I].
- unfold sh_ok, rf_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E RFx 10 t 288 t 0 288 HRA).
  + unfold U, RFx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold RF_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. revert Happ Hflo Hfhi Hx. clear.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Lemma rf_row_vals : forall bs j, length bs = 288%nat -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
0 <= j -> j < Boxreg.bx_n bs -> j <= 4 ->
rvb bs (56 * j + 8) = Boxreg.bx_base bs j /\ rvb bs (56 * j + 12) = Boxreg.bx_nch bs j /\
0 <= Boxreg.bx_base bs j <= 38 /\ 2 <= Boxreg.bx_nch bs j <= 40 /\
Boxreg.bx_base bs j + Boxreg.bx_nch bs j <= 40.
Proof.
intros bs j HL H2 H3 Hj0 Hjn Hj4.
destruct (Boxreg.B3_bounds bs j H2 H3 ltac:(lia)) as (Hb & Hc & Hbc).
split; [apply rf_rvb_rd4; [exact HL | lia | lia | unfold Boxreg.bx_base in Hb; lia]|].
split; [apply rf_rvb_rd4; [exact HL | lia | lia | unfold Boxreg.bx_nch in Hc; lia]|].
repeat split; lia.
Qed.
Ltac rf_run HS HJ SHOK Us :=
paj_run_tok RUN HS HJ SHOK RFspan; [awr_ok_tac; exact Us |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
idtac.
Ltac rf_runto HS HJ SHOK Us stop :=
paj_run_to_tok RUNTO HS HJ SHOK RFspan stop; [awr_ok_tac; exact Us |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
idtac.
Ltac rf_leafg HS HJ Hra1 Ee1 Hae pick :=
lazymatch goal with
| |- SRr _ ?W0 _ (trange_free_post ?regs0 ?ly0 ?S0 _ _ _ _ _ _ ?bs0) =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msc) =>
    let N1 := fresh "RR1" in let N10 := fresh "RR10" in
    prreg HS (1%bv : bv 5) N1; prreg HS (10%bv : bv 5) N10;
    eapply (RET W0 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros matx;
    unfold trange_free_post, apost_base;
    exists ly0, S0, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite N1, Ee1, Hra1; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs0 (rf_extra bs0) HS);
            [exact Hae | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    pick; split; [| cbn [ms_regs]; rewrite N10; reflexivity]
  end
end.
Ltac rf_leaf_ok HS HJ Hra1 Ee1 Hae := rf_leafg HS HJ Hra1 Ee1 Hae ltac:(left).
Ltac rf_leaf_no HS HJ Hra1 Ee1 Hae := rf_leafg HS HJ Hra1 Ee1 Hae ltac:(right).
Lemma rf_r14ne : (14%bv : bv 5) <> 0%bv.
Proof. intro H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.
Ltac rf_rowfacts HS nb nn Fb Fn Vb Vn :=
let H1 := fresh "HSa" in
pose proof (st_ok_pi_add_fact _ _ _ nb (mkAF 0 38 0) HS
  (rf_afact _ nb _ 0 38 Fb ltac:(lia) ltac:(rewrite Vb; lia) ltac:(rewrite Vb; lia) ltac:(lia))) as H1;
clear HS;
pose proof (st_ok_pi_add_fact _ _ _ nn (mkAF 2 40 0) H1
  (rf_afact _ nn _ 2 40 Fn ltac:(lia) ltac:(rewrite Vn; lia) ltac:(rewrite Vn; lia) ltac:(lia))) as HS;
clear H1.
Ltac rf_pin14 HS E0 t0 kk off Ht80 Fsb F100 :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ss (restrict ?Hh ?ms) =>
  let R14 := fresh "R14" in
  pose proof (st_ok_pi_restrict_reg Hh Ex ss ms (14%bv : bv 5) HS) as R14;
  let e := eval vm_compute in (sr_get (ss_regs ss) (14%bv : bv 5)) in
  change (sr_get (ss_regs ss) (14%bv : bv 5)) with e in R14;
  let H1 := fresh "HSp" in
  pose proof (st_ok_pi_set_reg E0 _ _ (14%bv : bv 5)
     (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 off) (SLit 3))) HS rf_r14ne
     ltac:(cbn [ms_regs restrict mkst]; rewrite R14; symmetry;
           exact (rf_pin E0 t0 kk F100 Fsb ltac:(lia) ltac:(lia) Ht80 ltac:(lia) ltac:(reflexivity)))) as H1;
  clear HS R14; rename H1 into HS
end.
Ltac rf_join HS JN jz :=
lazymatch goal with
| |- SRr _ ?W0 _ (trange_free_post ?regs0 ?ly0 ?S0 ?Wq ?mem0 ?md0 ?base0 ?nch0 ?fabric0 ?bs0) =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ef ?ss (restrict _ _) =>
    let ssj := eval vm_compute in (mkSST 5488 (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
                 (mkFacts (f_atoms (ss_facts ss)) (@nil acond) (f_alias (ss_facts ss)))) in
    assert (JN : (forall i, 0 <= i < jz ->
                    ~ Boxreg.meets base0 nch0 (Boxreg.bx_base bs0 i) (Boxreg.bx_nch bs0 i)) ->
      forall ms2 md2, st_ok_pi SEGS VAL Ef ssj (restrict (w_H W0) ms2) ->
      sh_ok SEGS RFx rf_SH Ef (mrestrict (w_H W0) (ms_mem ms2)) ->
      ajournal SEGS B RANGE_FREE_STK (spZ regs0) [] ly0 S0 W0 mem0 md0 [] ly0 S0 W0 (ms_mem ms2) md2 0 ->
      SRr SEGS W0 (mkCfg ms2 md2) (trange_free_post regs0 ly0 S0 W0 mem0 md0 base0 nch0 fabric0 bs0))
  end
end.

Theorem pb_range_free : trange_free_spec.
Proof.
unfold trange_free_spec.
intros ly S W regs mem md ch t base nch fabric bs HPRE H10 H11 H12 H13 Hbase Hnch Hfab HFO HLEN HBS HB1 HB2 HB3.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rf_entry ly S W regs mem md ch t bs HPRE H10 HFO HLEN HBS HB1) as [HS SHOK].
unfold Boxreg.boxreg_B1 in HB1.
pose proof (ajournal_init SEGS B RANGE_FREE_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Ht8 & HRA).
change ReacBoxregInit.REG_SIZE with 288 in Hfhi.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
assert (Htlo : 4096 <= t) by lia.
assert (Hthi : t + 288 <= alloc_ceiling) by lia.
assert (Htop44 : t + 300 < 2 ^ 47) by (revert Htlo Hthi C1; clear; intros; lia).
remember (EC regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rf_extra bs)) n)
by (intros n Hn; rewrite HE; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 base)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 nch)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 fabric)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (F32 : ew E 32 = Z_to_bv 64 RF_SB) by (rewrite HE; apply (rf_ew regs bs 0%nat); [reflexivity | lia]).
assert (F33 : ew E 33 = Z_to_bv 64 (rvb bs 280)) by (rewrite HE; apply (rf_ew regs bs 1%nat); [reflexivity | lia]).
assert (F34 : ew E 34 = Z_to_bv 64 (rvb bs 8)) by (rewrite HE; apply (rf_ew regs bs 2%nat); [reflexivity | lia]).
assert (F35 : ew E 35 = Z_to_bv 64 (rvb bs 12)) by (rewrite HE; apply (rf_ew regs bs 3%nat); [reflexivity | lia]).
assert (F36 : ew E 36 = Z_to_bv 64 (rvb bs 64)) by (rewrite HE; apply (rf_ew regs bs 4%nat); [reflexivity | lia]).
assert (F37 : ew E 37 = Z_to_bv 64 (rvb bs 68)) by (rewrite HE; apply (rf_ew regs bs 5%nat); [reflexivity | lia]).
assert (F38 : ew E 38 = Z_to_bv 64 (rvb bs 120)) by (rewrite HE; apply (rf_ew regs bs 6%nat); [reflexivity | lia]).
assert (F39 : ew E 39 = Z_to_bv 64 (rvb bs 124)) by (rewrite HE; apply (rf_ew regs bs 7%nat); [reflexivity | lia]).
assert (F40 : ew E 40 = Z_to_bv 64 (rvb bs 176)) by (rewrite HE; apply (rf_ew regs bs 8%nat); [reflexivity | lia]).
assert (F41 : ew E 41 = Z_to_bv 64 (rvb bs 180)) by (rewrite HE; apply (rf_ew regs bs 9%nat); [reflexivity | lia]).
assert (F42 : ew E 42 = Z_to_bv 64 (rvb bs 232)) by (rewrite HE; apply (rf_ew regs bs 10%nat); [reflexivity | lia]).
assert (F43 : ew E 43 = Z_to_bv 64 (rvb bs 236)) by (rewrite HE; apply (rf_ew regs bs 11%nat); [reflexivity | lia]).
assert (HAE : env_agree 32 (Ereg regs (rf_extra bs)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | rewrite HE; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hnn : rvb bs 280 = Boxreg.bx_n bs)
by (apply rf_rvb_rd4; [exact HLEN | lia | lia | unfold Boxreg.boxreg_B1, Boxreg.bx_n in *; lia]).
assert (D11 : sv_denot E (SOff 11 0) = Z_to_bv 64 base) by (apply (rf_den_off0 E 11 base E11)).
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 (Boxreg.bx_n bs))
by (rewrite (rf_den_off0 E 33 _ F33), Hnn; reflexivity).
clear HE EL.
unfold cfg_at, A_range_freeP.
change (w64 (BASE + AF_range_free)) with (Z_to_bv 64 (BASE + AF_range_free)).
change (Z_to_bv 64 (BASE + AF_range_free)) with (Z_to_bv 64 A_range_freeP).
(* 1. base < 0 ? *)
rf_run HS HJ SHOK Usp.
psrr_branch_tok RUN BR HS SHOK RFspan.
{ (* base < 0: nothing is free *)
  pose proof (rf_lt_t E _ _ base 0 D11 (rf_den_lit E 0) ltac:(lia) ltac:(lia) Hc) as Hlt.
  rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
  intros (Hok & _); lia. }
pose proof (rf_lt_f E _ _ base 0 D11 (rf_den_lit E 0) ltac:(lia) ltac:(lia) Hc) as Hge0. clear Hc.
(* 2. fabric - nch < base ? *)
rf_run HS HJ SHOK Usp.
assert (Dsub : sv_denot E (SAluw ALU_SUB (SOff 13 0) (SOff 12 0)) = Z_to_bv 64 (fabric - nch))
by (apply (rf_den_subw E _ _ fabric nch (rf_den_off0 E 13 _ E13) (rf_den_off0 E 12 _ E12)); lia).
psrr_branch_tok RUN BR HS SHOK RFspan.
{ pose proof (rf_lt_t E _ _ (fabric - nch) base Dsub D11 ltac:(lia) ltac:(lia) Hc) as Hlt.
  rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
  intros (Hok & _); lia. }
pose proof (rf_lt_f E _ _ (fabric - nch) base Dsub D11 ltac:(lia) ltac:(lia) Hc) as Hle. clear Hc.
(* 3. n <= 0 ? *)
rf_run HS HJ SHOK Usp.
psrr_branch_tok RUN BR HS SHOK RFspan.
{ pose proof (rf_ge_t E _ _ 0 (Boxreg.bx_n bs) (rf_den_lit E 0) D33 ltac:(lia)
    ltac:(lia) Hc) as Hn0.
  rf_run HS HJ SHOK Usp. rf_leaf_ok HS HJ Hra E1 HAE.
  split; [lia | intros i Hi; lia]. }
pose proof (rf_ge_f E _ _ 0 (Boxreg.bx_n bs) (rf_den_lit E 0) D33 ltac:(lia)
  ltac:(lia) Hc) as Hn0. clear Hc.
(* the five rows: at row j the state is at the loop head with  j < n  known *)
assert (Hj0 : 0 < Boxreg.bx_n bs) by lia.
destruct (rf_row_vals bs 0 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (V0b & V0n & Vb0 & Vn0 & Vbn0).
change (56 * 0 + 8) with 8 in V0b. change (56 * 0 + 12) with 12 in V0n.
rf_rowfacts HS 34%nat 35%nat F34 F35 V0b V0n.
rf_run HS HJ SHOK Usp.
assert (D34 : sv_denot E (SOff 34 0) = Z_to_bv 64 (Boxreg.bx_base bs 0))
by (rewrite (rf_den_off0 E 34 _ F34), V0b; reflexivity).
assert (D35 : sv_denot E (SOff 35 0) = Z_to_bv 64 (Boxreg.bx_nch bs 0))
by (rewrite (rf_den_off0 E 35 _ F35), V0n; reflexivity).
assert (Ds0 : sv_denot E (SAlu ALU_ADD (SOff 34 0) (SOff 35 0))
  = Z_to_bv 64 (Boxreg.bx_base bs 0 + Boxreg.bx_nch bs 0)) by (apply (rf_den_add E _ _ _ _ D34 D35)).
assert (Dnb : sv_denot E (SAluw ALU_ADD (SOff 12 0) (SOff 11 0)) = Z_to_bv 64 (nch + base))
by (apply (rf_den_addw E _ _ nch base (rf_den_off0 E 12 _ E12) D11); lia).
rf_join HS JOIN0 1.
{ (* ---- JOIN 0 ---- *)
intros HNM0 msJ0 mdJ0 HS1 SHOK1 HJ1.
rf_run HS1 HJ1 SHOK1 Usp.
assert (Dn1 : sv_denot E (SOff 33 (-1)) = Z_to_bv 64 (Boxreg.bx_n bs - 1))
by (rewrite (rf_den_off E 33 _ (-1) F33), Hnn; f_equal; lia).
psrr_branch_tok RUN BR HS1 SHOK1 RFspan.
{ pose proof (rf_eq_t E _ _ (Boxreg.bx_n bs - 1) 0 Dn1 (rf_den_lit E 0) ltac:(lia) ltac:(lia) Hc) as Hend. clear Hc.
  rf_run HS1 HJ1 SHOK1 Usp. rf_leaf_ok HS1 HJ1 Hra E1 HAE.
  split; [lia | intros i Hi; apply HNM0; lia]. }
pose proof (rf_eq_f E _ _ (Boxreg.bx_n bs - 1) 0 Dn1 (rf_den_lit E 0) Hc) as Hne0. clear Hc.
assert (Hj1 : 1 < Boxreg.bx_n bs) by lia.
rf_runto HS1 HJ1 SHOK1 Usp 5444.
rf_pin14 HS1 E t 8 64 Ht8 F32 E10.
destruct (rf_row_vals bs 1 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (V1b & V1n & Vb1 & Vn1 & Vbn1).
change (56 * 1 + 8) with 64 in V1b. change (56 * 1 + 12) with 68 in V1n.
rf_rowfacts HS1 36%nat 37%nat F36 F37 V1b V1n.
rf_run HS1 HJ1 SHOK1 Usp.
assert (D36 : sv_denot E (SOff 36 0) = Z_to_bv 64 (Boxreg.bx_base bs 1))
by (rewrite (rf_den_off0 E 36 _ F36), V1b; reflexivity).
assert (D37 : sv_denot E (SOff 37 0) = Z_to_bv 64 (Boxreg.bx_nch bs 1))
by (rewrite (rf_den_off0 E 37 _ F37), V1n; reflexivity).
assert (Ds1 : sv_denot E (SAlu ALU_ADD (SOff 36 0) (SOff 37 0))
  = Z_to_bv 64 (Boxreg.bx_base bs 1 + Boxreg.bx_nch bs 1)) by (apply (rf_den_add E _ _ _ _ D36 D37)).
rf_join HS1 JOIN1 2.
{ (* ---- JOIN 1 ---- *)
intros HNM1 msJ1 mdJ1 HS2 SHOK2 HJ2.
rf_run HS2 HJ2 SHOK2 Usp.
assert (Dn2 : sv_denot E (SOff 33 (-2)) = Z_to_bv 64 (Boxreg.bx_n bs - 2))
by (rewrite (rf_den_off E 33 _ (-2) F33), Hnn; f_equal; lia).
psrr_branch_tok RUN BR HS2 SHOK2 RFspan.
{ pose proof (rf_eq_t E _ _ (Boxreg.bx_n bs - 2) 0 Dn2 (rf_den_lit E 0) ltac:(lia) ltac:(lia) Hc) as Hend. clear Hc.
  rf_run HS2 HJ2 SHOK2 Usp. rf_leaf_ok HS2 HJ2 Hra E1 HAE.
  split; [lia | intros i Hi; apply HNM1; lia]. }
pose proof (rf_eq_f E _ _ (Boxreg.bx_n bs - 2) 0 Dn2 (rf_den_lit E 0) Hc) as Hne1. clear Hc.
assert (Hj2 : 2 < Boxreg.bx_n bs) by lia.
rf_runto HS2 HJ2 SHOK2 Usp 5444.
rf_pin14 HS2 E t 64 120 Ht8 F32 E10.
destruct (rf_row_vals bs 2 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (V2b & V2n & Vb2 & Vn2 & Vbn2).
change (56 * 2 + 8) with 120 in V2b. change (56 * 2 + 12) with 124 in V2n.
rf_rowfacts HS2 38%nat 39%nat F38 F39 V2b V2n.
rf_run HS2 HJ2 SHOK2 Usp.
assert (D38 : sv_denot E (SOff 38 0) = Z_to_bv 64 (Boxreg.bx_base bs 2))
by (rewrite (rf_den_off0 E 38 _ F38), V2b; reflexivity).
assert (D39 : sv_denot E (SOff 39 0) = Z_to_bv 64 (Boxreg.bx_nch bs 2))
by (rewrite (rf_den_off0 E 39 _ F39), V2n; reflexivity).
assert (Ds2 : sv_denot E (SAlu ALU_ADD (SOff 38 0) (SOff 39 0))
  = Z_to_bv 64 (Boxreg.bx_base bs 2 + Boxreg.bx_nch bs 2)) by (apply (rf_den_add E _ _ _ _ D38 D39)).
rf_join HS2 JOIN2 3.
{ (* ---- JOIN 2 ---- *)
intros HNM2 msJ2 mdJ2 HS3 SHOK3 HJ3.
rf_run HS3 HJ3 SHOK3 Usp.
assert (Dn3 : sv_denot E (SOff 33 (-3)) = Z_to_bv 64 (Boxreg.bx_n bs - 3))
by (rewrite (rf_den_off E 33 _ (-3) F33), Hnn; f_equal; lia).
psrr_branch_tok RUN BR HS3 SHOK3 RFspan.
{ pose proof (rf_eq_t E _ _ (Boxreg.bx_n bs - 3) 0 Dn3 (rf_den_lit E 0) ltac:(lia) ltac:(lia) Hc) as Hend. clear Hc.
  rf_run HS3 HJ3 SHOK3 Usp. rf_leaf_ok HS3 HJ3 Hra E1 HAE.
  split; [lia | intros i Hi; apply HNM2; lia]. }
pose proof (rf_eq_f E _ _ (Boxreg.bx_n bs - 3) 0 Dn3 (rf_den_lit E 0) Hc) as Hne2. clear Hc.
assert (Hj3 : 3 < Boxreg.bx_n bs) by lia.
rf_runto HS3 HJ3 SHOK3 Usp 5444.
rf_pin14 HS3 E t 120 176 Ht8 F32 E10.
destruct (rf_row_vals bs 3 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (V3b & V3n & Vb3 & Vn3 & Vbn3).
change (56 * 3 + 8) with 176 in V3b. change (56 * 3 + 12) with 180 in V3n.
rf_rowfacts HS3 40%nat 41%nat F40 F41 V3b V3n.
rf_run HS3 HJ3 SHOK3 Usp.
assert (D40 : sv_denot E (SOff 40 0) = Z_to_bv 64 (Boxreg.bx_base bs 3))
by (rewrite (rf_den_off0 E 40 _ F40), V3b; reflexivity).
assert (D41 : sv_denot E (SOff 41 0) = Z_to_bv 64 (Boxreg.bx_nch bs 3))
by (rewrite (rf_den_off0 E 41 _ F41), V3n; reflexivity).
assert (Ds3 : sv_denot E (SAlu ALU_ADD (SOff 40 0) (SOff 41 0))
  = Z_to_bv 64 (Boxreg.bx_base bs 3 + Boxreg.bx_nch bs 3)) by (apply (rf_den_add E _ _ _ _ D40 D41)).
rf_join HS3 JOIN3 4.
{ (* ---- JOIN 3 ---- *)
intros HNM3 msJ3 mdJ3 HS4 SHOK4 HJ4.
rf_run HS4 HJ4 SHOK4 Usp.
assert (Dn4 : sv_denot E (SOff 33 (-4)) = Z_to_bv 64 (Boxreg.bx_n bs - 4))
by (rewrite (rf_den_off E 33 _ (-4) F33), Hnn; f_equal; lia).
psrr_branch_tok RUN BR HS4 SHOK4 RFspan.
{ pose proof (rf_eq_t E _ _ (Boxreg.bx_n bs - 4) 0 Dn4 (rf_den_lit E 0) ltac:(lia) ltac:(lia) Hc) as Hend. clear Hc.
  rf_run HS4 HJ4 SHOK4 Usp. rf_leaf_ok HS4 HJ4 Hra E1 HAE.
  split; [lia | intros i Hi; apply HNM3; lia]. }
pose proof (rf_eq_f E _ _ (Boxreg.bx_n bs - 4) 0 Dn4 (rf_den_lit E 0) Hc) as Hne3. clear Hc.
assert (Hj4 : 4 < Boxreg.bx_n bs) by lia.
rf_runto HS4 HJ4 SHOK4 Usp 5444.
rf_pin14 HS4 E t 176 232 Ht8 F32 E10.
destruct (rf_row_vals bs 4 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (V4b & V4n & Vb4 & Vn4 & Vbn4).
change (56 * 4 + 8) with 232 in V4b. change (56 * 4 + 12) with 236 in V4n.
rf_rowfacts HS4 42%nat 43%nat F42 F43 V4b V4n.
rf_run HS4 HJ4 SHOK4 Usp.
assert (D42 : sv_denot E (SOff 42 0) = Z_to_bv 64 (Boxreg.bx_base bs 4))
by (rewrite (rf_den_off0 E 42 _ F42), V4b; reflexivity).
assert (D43 : sv_denot E (SOff 43 0) = Z_to_bv 64 (Boxreg.bx_nch bs 4))
by (rewrite (rf_den_off0 E 43 _ F43), V4n; reflexivity).
assert (Ds4 : sv_denot E (SAlu ALU_ADD (SOff 42 0) (SOff 43 0))
  = Z_to_bv 64 (Boxreg.bx_base bs 4 + Boxreg.bx_nch bs 4)) by (apply (rf_den_add E _ _ _ _ D42 D43)).
rf_join HS4 JOIN4 5.
{ (* ---- JOIN 4: the last row; n = 5 here ---- *)
intros HNM4 msJ4 mdJ4 HS5 SHOK5 HJ5.
rf_run HS5 HJ5 SHOK5 Usp.
assert (Dn5 : sv_denot E (SOff 33 (-5)) = Z_to_bv 64 (Boxreg.bx_n bs - 5))
by (rewrite (rf_den_off E 33 _ (-5) F33), Hnn; f_equal; lia).
psrr_branch_tok RUN BR HS5 SHOK5 RFspan.
{ pose proof (rf_eq_t E _ _ (Boxreg.bx_n bs - 5) 0 Dn5 (rf_den_lit E 0) ltac:(lia) ltac:(lia) Hc) as Hend. clear Hc.
  rf_run HS5 HJ5 SHOK5 Usp. rf_leaf_ok HS5 HJ5 Hra E1 HAE.
  split; [lia | intros i Hi; apply HNM4; lia]. }
pose proof (rf_eq_f E _ _ (Boxreg.bx_n bs - 5) 0 Dn5 (rf_den_lit E 0) Hc) as Hne4.
exfalso. lia. }
(* ---- row 4's two branches ---- *)
psrr_branch_tok RUN BR HS4 SHOK4 RFspan.
{ pose proof (rf_ge_t E _ _ base (Boxreg.bx_base bs 4 + Boxreg.bx_nch bs 4) D11 Ds4 ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
  rf_runto HS4 HJ4 SHOK4 Usp 5488.
  pose proof (rf_facts_drop E _ _ HS4) as HSd.
  exact (JOIN4 ltac:(intros i Hi; assert (i = 4 \/ i < 4) as [->|Hlt] by lia;
                     [unfold Boxreg.meets; lia | apply HNM3; lia]) _ _ HSd SHOK4 HJ4). }
pose proof (rf_ge_f E _ _ base (Boxreg.bx_base bs 4 + Boxreg.bx_nch bs 4) D11 Ds4 ltac:(lia) ltac:(lia) Hc) as Hlt4. clear Hc.
rf_run HS4 HJ4 SHOK4 Usp.
psrr_branch_tok RUN BR HS4 SHOK4 RFspan.
{ pose proof (rf_lt_t E _ _ (Boxreg.bx_base bs 4) (nch + base) D42 Dnb ltac:(lia) ltac:(lia) Hc) as Hm. clear Hc.
  rf_run HS4 HJ4 SHOK4 Usp. rf_leaf_no HS4 HJ4 Hra E1 HAE.
  intros (_ & Hall). apply (Hall 4 ltac:(lia)). unfold Boxreg.meets. lia. }
pose proof (rf_lt_f E _ _ (Boxreg.bx_base bs 4) (nch + base) D42 Dnb ltac:(lia) ltac:(lia) Hc) as Hnm. clear Hc.
rf_runto HS4 HJ4 SHOK4 Usp 5488.
pose proof (rf_facts_drop E _ _ HS4) as HSd.
exact (JOIN4 ltac:(intros i Hi; assert (i = 4 \/ i < 4) as [->|Hlt] by lia;
                   [unfold Boxreg.meets; lia | apply HNM3; lia]) _ _ HSd SHOK4 HJ4). }
(* ---- row 3's two branches ---- *)
psrr_branch_tok RUN BR HS3 SHOK3 RFspan.
{ pose proof (rf_ge_t E _ _ base (Boxreg.bx_base bs 3 + Boxreg.bx_nch bs 3) D11 Ds3 ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
  rf_runto HS3 HJ3 SHOK3 Usp 5488.
  pose proof (rf_facts_drop E _ _ HS3) as HSd.
  exact (JOIN3 ltac:(intros i Hi; assert (i = 3 \/ i < 3) as [->|Hlt] by lia;
                     [unfold Boxreg.meets; lia | apply HNM2; lia]) _ _ HSd SHOK3 HJ3). }
pose proof (rf_ge_f E _ _ base (Boxreg.bx_base bs 3 + Boxreg.bx_nch bs 3) D11 Ds3 ltac:(lia) ltac:(lia) Hc) as Hlt3. clear Hc.
rf_run HS3 HJ3 SHOK3 Usp.
psrr_branch_tok RUN BR HS3 SHOK3 RFspan.
{ pose proof (rf_lt_t E _ _ (Boxreg.bx_base bs 3) (nch + base) D40 Dnb ltac:(lia) ltac:(lia) Hc) as Hm. clear Hc.
  rf_run HS3 HJ3 SHOK3 Usp. rf_leaf_no HS3 HJ3 Hra E1 HAE.
  intros (_ & Hall). apply (Hall 3 ltac:(lia)). unfold Boxreg.meets. lia. }
pose proof (rf_lt_f E _ _ (Boxreg.bx_base bs 3) (nch + base) D40 Dnb ltac:(lia) ltac:(lia) Hc) as Hnm. clear Hc.
rf_runto HS3 HJ3 SHOK3 Usp 5488.
pose proof (rf_facts_drop E _ _ HS3) as HSd.
exact (JOIN3 ltac:(intros i Hi; assert (i = 3 \/ i < 3) as [->|Hlt] by lia;
                   [unfold Boxreg.meets; lia | apply HNM2; lia]) _ _ HSd SHOK3 HJ3). }
(* ---- row 2's two branches ---- *)
psrr_branch_tok RUN BR HS2 SHOK2 RFspan.
{ pose proof (rf_ge_t E _ _ base (Boxreg.bx_base bs 2 + Boxreg.bx_nch bs 2) D11 Ds2 ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
  rf_runto HS2 HJ2 SHOK2 Usp 5488.
  pose proof (rf_facts_drop E _ _ HS2) as HSd.
  exact (JOIN2 ltac:(intros i Hi; assert (i = 2 \/ i < 2) as [->|Hlt] by lia;
                     [unfold Boxreg.meets; lia | apply HNM1; lia]) _ _ HSd SHOK2 HJ2). }
pose proof (rf_ge_f E _ _ base (Boxreg.bx_base bs 2 + Boxreg.bx_nch bs 2) D11 Ds2 ltac:(lia) ltac:(lia) Hc) as Hlt2. clear Hc.
rf_run HS2 HJ2 SHOK2 Usp.
psrr_branch_tok RUN BR HS2 SHOK2 RFspan.
{ pose proof (rf_lt_t E _ _ (Boxreg.bx_base bs 2) (nch + base) D38 Dnb ltac:(lia) ltac:(lia) Hc) as Hm. clear Hc.
  rf_run HS2 HJ2 SHOK2 Usp. rf_leaf_no HS2 HJ2 Hra E1 HAE.
  intros (_ & Hall). apply (Hall 2 ltac:(lia)). unfold Boxreg.meets. lia. }
pose proof (rf_lt_f E _ _ (Boxreg.bx_base bs 2) (nch + base) D38 Dnb ltac:(lia) ltac:(lia) Hc) as Hnm. clear Hc.
rf_runto HS2 HJ2 SHOK2 Usp 5488.
pose proof (rf_facts_drop E _ _ HS2) as HSd.
exact (JOIN2 ltac:(intros i Hi; assert (i = 2 \/ i < 2) as [->|Hlt] by lia;
                   [unfold Boxreg.meets; lia | apply HNM1; lia]) _ _ HSd SHOK2 HJ2). }
(* ---- row 1's two branches ---- *)
psrr_branch_tok RUN BR HS1 SHOK1 RFspan.
{ pose proof (rf_ge_t E _ _ base (Boxreg.bx_base bs 1 + Boxreg.bx_nch bs 1) D11 Ds1 ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
  rf_runto HS1 HJ1 SHOK1 Usp 5488.
  pose proof (rf_facts_drop E _ _ HS1) as HSd.
  exact (JOIN1 ltac:(intros i Hi; assert (i = 1 \/ i < 1) as [->|Hlt] by lia;
                     [unfold Boxreg.meets; lia | apply HNM0; lia]) _ _ HSd SHOK1 HJ1). }
pose proof (rf_ge_f E _ _ base (Boxreg.bx_base bs 1 + Boxreg.bx_nch bs 1) D11 Ds1 ltac:(lia) ltac:(lia) Hc) as Hlt1. clear Hc.
rf_run HS1 HJ1 SHOK1 Usp.
psrr_branch_tok RUN BR HS1 SHOK1 RFspan.
{ pose proof (rf_lt_t E _ _ (Boxreg.bx_base bs 1) (nch + base) D36 Dnb ltac:(lia) ltac:(lia) Hc) as Hm. clear Hc.
  rf_run HS1 HJ1 SHOK1 Usp. rf_leaf_no HS1 HJ1 Hra E1 HAE.
  intros (_ & Hall). apply (Hall 1 ltac:(lia)). unfold Boxreg.meets. lia. }
pose proof (rf_lt_f E _ _ (Boxreg.bx_base bs 1) (nch + base) D36 Dnb ltac:(lia) ltac:(lia) Hc) as Hnm. clear Hc.
rf_runto HS1 HJ1 SHOK1 Usp 5488.
pose proof (rf_facts_drop E _ _ HS1) as HSd.
exact (JOIN1 ltac:(intros i Hi; assert (i = 1 \/ i < 1) as [->|Hlt] by lia;
                   [unfold Boxreg.meets; lia | apply HNM0; lia]) _ _ HSd SHOK1 HJ1). }
(* ---- row 0's two branches ---- *)
psrr_branch_tok RUN BR HS SHOK RFspan.
{ pose proof (rf_ge_t E _ _ base (Boxreg.bx_base bs 0 + Boxreg.bx_nch bs 0) D11 Ds0 ltac:(lia) ltac:(lia) Hc) as Hge. clear Hc.
  rf_runto HS HJ SHOK Usp 5488.
  pose proof (rf_facts_drop E _ _ HS) as HSd.
  exact (JOIN0 ltac:(intros i Hi; assert (i = 0) as -> by lia; unfold Boxreg.meets; lia) _ _ HSd SHOK HJ). }
pose proof (rf_ge_f E _ _ base (Boxreg.bx_base bs 0 + Boxreg.bx_nch bs 0) D11 Ds0 ltac:(lia) ltac:(lia) Hc) as Hlt0. clear Hc.
rf_run HS HJ SHOK Usp.
psrr_branch_tok RUN BR HS SHOK RFspan.
{ pose proof (rf_lt_t E _ _ (Boxreg.bx_base bs 0) (nch + base) D34 Dnb ltac:(lia) ltac:(lia) Hc) as Hm. clear Hc.
  rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
  intros (_ & Hall). apply (Hall 0 ltac:(lia)). unfold Boxreg.meets. lia. }
pose proof (rf_lt_f E _ _ (Boxreg.bx_base bs 0) (nch + base) D34 Dnb ltac:(lia) ltac:(lia) Hc) as Hnm. clear Hc.
rf_runto HS HJ SHOK Usp 5488.
pose proof (rf_facts_drop E _ _ HS) as HSd.
exact (JOIN0 ltac:(intros i Hi; assert (i = 0) as -> by lia; unfold Boxreg.meets; lia) _ _ HSd SHOK HJ).
Qed.
End h.
End f.
End d.
