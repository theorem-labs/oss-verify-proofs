(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8n.v:1199-1201
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-202, 358-363, 390-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:207-209 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8k.v:388-389. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_reac_ver_str.v, with its module paths, module names and numbers changed; 552 of its 632 lines of code are new or changed and 994 lines of the source are left out. *)
(* range_free (fuzz_boxreg.asan-ubsan 0x814e8, 76 instructions): the contract of the ASan+UBSan build's code.
   range_free is a static function of the harness (fuzz/fuzz_boxreg.c:94-102).
   The function takes a 16-byte frame on the machine stack (addi sp,sp,-16; it saves ra there for the call of
   __asan_report_load4) and calls no function on a path that returns. It returns 0 in a0 when base (a1) < 0 or
   base > fabric - nch (a3 - a2). Else it checks t (a0) for 4-byte alignment for UBSan and reads the 288-byte table
   t: n (t + 280), then base (t + 56 i + 8) and nch (t + 56 i + 12) of the rows i < n, each 4-byte load after the
   check of its shadow byte, up to the first row whose [base_i, base_i + nch_i) meets [base, base + nch). It returns
   0 when a row meets, else 1: 1 exactly when Pau's range_free_ok of lib/Prog/range_free_c.v holds, used as it is
   with the model of lib/Prog/Boxreg.v. It writes nothing outside its own frame.
   Where the table lies: every call passes &prev, the harness's local struct reac_boxreg prev (fuzz/fuzz_boxreg.c:210),
   which LLVMFuzzerTestOneInput fills at each loop top with memcpy (&prev, r, sizeof prev) (:211); it is never the
   registry block r. prev is at offset 0x40 of the harness's 416-byte ASan frame block (0x801d0: addi s5,a3,0x40,
   a3 = ld 0x18(s1) the frame block; s5 is not written again before the exit). The harness poisons its 36 shadow
   bytes (frame shadow + 8 .. + 0x2b) with 0xf8 at entry, clears them at each loop top (0x802ac .. 0x80338) and then
   calls __asan_memcpy (prev, r, 288) (0x80348). The calls, all with a0 = s5: 0x80568 (case 0, pinned base), and
   0x80940 and 0x80994, the loops of lowest_free, which this build inlines into LLVMFuzzerTestOneInput (case 0 at
   0x80910 .. 0x80950, case 1 at 0x80960 .. 0x809a0). That frame block is the __asan_stack_malloc_3 side-stack frame
   (0x8001c), a frame in frames S, so the premise is afobj SEGS B ly S W mem t 288 (lib/A/Prog/BoxBase.v; the form
   of the MAC premise of BoxBReacBoxregFind.v), with the 288 bytes bs of t.
   Hazards.
   (1) The struct is 288 bytes (rows 0..280 with stride 56, n at +280, fabric at +284). range_free does not read the
       table's fabric: it uses its argument fabric.
   (2) afobj holds only on the fake-stack path: when the runtime's detect_stack_use_after_return flag is 0 (or
       __asan_stack_malloc_3 returns 0) the harness takes its fallback (0x80028 .. 0x8004c: the frame block on the
       machine stack below its own frame), and prev is then in the caller's stack window, which afobj does not
       cover. cgif's model (stack_malloc_progressP) always gives the fake frame.
   (3) Every UBSan check branches to the UBSan trap (the unimp at 0x815f8): the alignment check on t (andi t,3 at
       0x81500) is refuted by afobj's t mod 8 = 0; the row-index check i = 5 (beq at 0x81558) by n <= 5
       (boxreg_B1), as the loop runs i < n; the pointer-overflow check on t + 56 i (bltu ~t, 56 i at 0x8155c) by
       t + 288 <= alloc_ceiling (frames_bounds, lib/Reusable/YCbq.v, for afobj's frame); the overflow check on
       base_i + nch_i (add against addw, bne at 0x81594) by the row bounds of boxreg_B3 with boxreg_B2. fabric - nch
       (subw at 0x814f8) and base + nch (addw at 0x8153c) have no check; -2^31 <= base < 2^31, 1 <= nch <= 40 and
       1 <= fabric <= 40 keep them exact. n is compared as a signed word (blez at 0x8152c: n <= 0 returns 1).
   (4) The shadow-checked loads are t + 280 and, for i < n, t + 56 i + 8 and t + 56 i + 12; the branches to
       __asan_report_load4 (0x815d8, 0x8160c, 0x81614) are refuted by afobj's range_addressable. The only other
       read is the GOT word of the shadow base (0x81508 .. 0x81510), fixed by AR (AR_const_law).
   (5) Apart from the trap word of (3), which is never reached, no f* or csr instruction occurs in the 76
       instructions (measured), so the fixed {fx} is sound.
   (6) The model premises are those of the old walk (a working branch 67b70ae1ec3
       proofs/libreac/fuzz_boxreg/lib/B/Prog/range_free_c.v; its t mod 4 = 0 is afobj's t mod 8 = 0 here): the
       argument ranges and boxreg_B1..B3 of the table. The harness meets them from check (r, fabric) on the registry
       it copied (boxreg_B16), from legal_width (2 <= nch <= 40), from its fabric (1..40) and, in the inlined loops,
       from the loop guard 0 <= base <= fabric - nch.
   Image difference: the asan build (lib/A/Prog/RangeFree.v, 0x81430) has no UBSan checks and a separate
   lowest_free function (lib/A/Prog/LowestFree.v); the result is the same. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg range_free_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 16-byte frame and ESTACK below it for the
   memory-checking runtime (it calls nothing but the error path). *)
Definition AB_range_freeP : Z := BASE + AF_range_free.
Definition RANGE_FREE_STKB : Z := 16 + ESTACK.
Section h.
Variable B : asyms.
Definition tbrange_free_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (base nch fabric : Z)
  (bs : list byte) : world SEGS -> config -> Prop :=
apost_base SEGS B RANGE_FREE_STKB [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
((range_free_c.range_free_ok bs base nch fabric /\ getr regs' 10 = w64 1) \/
 (~ range_free_c.range_free_ok bs base nch fabric /\ getr regs' 10 = w64 0))).
Definition tbrange_free_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (t base nch fabric : Z) (bs : list byte),
afn_pre SEGS B RANGE_FREE_STKB ly S W regs mem md ch ->
getr regs 10 = w64 t -> getr regs 11 = w64 base -> getr regs 12 = w64 nch -> getr regs 13 = w64 fabric ->
-2 ^ 31 <= base < 2 ^ 31 -> 1 <= nch <= 40 -> 1 <= fabric <= 40 ->
afobj SEGS B ly S W mem t BoxBReacBoxregInit.REG_SIZEB -> length bs = 288%nat ->
(forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
  aview SEGS (w_H W) mem (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
SRr SEGS W (cfg_at SEGS AB_range_freeP regs mem md) (tbrange_free_post regs ly S W mem md base nch fabric bs).
(* The walk. The walk layer (BoxBPaLib, YC1h) is loaded through BoxBReacBoxregInit and imported here, below the frozen
   statement prefix (provenance/WALK-INTERFACE.md). *)
Import BoxBPaLib YC1h.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
(* The 4-byte fields of the table, as unsigned words. *)
Definition rfu (bs : list byte) (k : Z) : Z := bytes_le_to_Z (Boxreg.bsub bs k 4).
Lemma rfu_range : forall bs k, 0 <= k -> k + 4 <= Z.of_nat (length bs) -> 0 <= rfu bs k < 2 ^ 32.
Proof. intros bs k Hk H. unfold rfu. apply Boxreg.le4_range. apply Boxreg.bsub_length; lia. Qed.
Lemma rfu_rd4 : forall bs k, 0 <= k -> k + 4 <= Z.of_nat (length bs) -> 0 <= Boxreg.rd4 bs k -> rfu bs k = Boxreg.rd4 bs k.
Proof.
intros bs k Hk H Hp. pose proof (rfu_range bs k Hk H) as R. revert Hp. unfold Boxreg.rd4. fold (rfu bs k).
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
intros Hp. Z.div_mod_to_equations. lia.
Qed.
(* Ported from Prog/BoxregRd.v:9 le_bytes_roundtrip (and Lib/Bytes.v:280 lor_shiftl8_add), which this file does not load. *)
Lemma rf_lor8 : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
assert (H0 : Z.land x (y * 256) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hl | Hh].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small x (2 ^ 8)) by (change (2 ^ 8) with 256; lia). rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite <- (Z.lxor_lor _ _ H0). rewrite <- (Z.add_nocarry_lxor _ _ H0). lia.
Qed.
Lemma rf_le_rt : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
induction l as [|b l IH]; [reflexivity|].
cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg l) as Hl.
rewrite rf_lor8 by lia.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  Z.div_mod_to_equations. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace ((bv_unsigned b + 256 * bytes_le_to_Z l) / 256) with (bytes_le_to_Z l); [exact IH|].
  Z.div_mod_to_equations. lia.
Qed.
Lemma rf_le4 : forall l : list byte, length l = 4%nat -> forall kk, (kk < 4)%nat ->
Z_to_bv 8 (YO0f.le_byte (bytes_le_to_Z l) 4 kk) = nth kk l (Z_to_bv 8 0).
Proof.
intros l HL kk Hk. pose proof (Boxreg.le4_range l HL) as R.
transitivity (nth kk (Z_to_le_bytes 4 (bytes_le_to_Z l)) (Z_to_bv 8 0)).
- set (v := bytes_le_to_Z l) in *. unfold YO0f.le_byte.
  assert (Hm : v mod 2 ^ (8 * Z.of_nat 4) = v) by (apply Z.mod_small; cbn; lia). rewrite Hm.
  destruct kk as [|[|[|[|kk]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth];
  apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
  rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.mod_mod by lia; reflexivity.
- rewrite <- HL at 1. rewrite rf_le_rt. reflexivity.
Qed.
Lemma rf_nth_bsub : forall bs k kk, 0 <= k -> (kk < 4)%nat ->
nth kk (Boxreg.bsub bs k 4) (Z_to_bv 8 0) = nth (Z.to_nat k + kk) bs (Z_to_bv 8 0).
Proof.
intros bs k kk Hk Hkk. unfold Boxreg.bsub. change (Z.to_nat 4) with 4%nat.
assert (F : forall (l : list byte), nth kk (firstn 4 l) (Z_to_bv 8 0) = nth kk l (Z_to_bv 8 0)).
{ intros l. destruct kk as [|[|[|[|kk]]]]; [| | | | lia]; destruct l as [|a [|b [|c [|d l]]]]; reflexivity. }
rewrite F. generalize (Z.to_nat k) as n. clear Hk. intros n. revert bs.
induction n as [|n IH]; intros [|x bs]; cbn [skipn nth Nat.add]; try reflexivity.
- destruct kk; reflexivity.
- apply IH.
Qed.
Lemma rf_val4 : forall (W : world SEGS) mem t bs k, length bs = 288%nat -> 0 <= k -> k + 4 <= 288 ->
(forall i, 0 <= i < 288 -> aview SEGS (w_H W) mem (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
val_mem SEGS (mrestrict (w_H W) mem) (t + k) 4 (rfu bs k).
Proof.
intros W mem t bs k HL Hk Hk4 HM kk Hkk.
pose proof (HM (k + Z.of_nat kk) ltac:(lia)) as Ha. replace (t + (k + Z.of_nat kk)) with (t + k + Z.of_nat kk) in Ha by lia.
unfold aview in Ha. destruct (mbyte SEGS (mrestrict (w_H W) mem) (t + k + Z.of_nat kk)) as [b|] eqn:Hb;
cbn [option_map] in Ha; [|discriminate]. injection Ha as Hbu. f_equal.
unfold rfu. rewrite (rf_le4 _ (Boxreg.bsub_length bs k 4 Hk ltac:(lia) ltac:(rewrite HL; lia)) kk Hkk).
rewrite (rf_nth_bsub bs k kk Hk Hkk). apply bv_eq. rewrite Hbu. f_equal. f_equal. lia.
Qed.
(* The symbolic state at the first slot: atom 32 is n (0 <= n <= 5, boxreg_B1), atoms 33 + 2 j and 34 + 2 j are base and
   nch of row j (j = 0..4; their range facts are added row by row, once j < n is known), atom 43 is the shadow base. *)
Definition RF_SB : Z := 0x7fff8000.
Definition RFx : sv := SOff 43 0.
Definition RFspan : Z * Z := (RF_SB, RF_SB + 2 ^ 44 - 1).
Definition rf_row (j : nat) : list YP09.chunk :=
[YP09.mkChunk (56 * Z.of_nat j + 8) (CVal 4 (SOff (33 + 2 * j) 0));
 YP09.mkChunk (56 * Z.of_nat j + 12) (CVal 4 (SOff (34 + 2 * j) 0))].
Definition rf_chunks : list YP09.chunk := YP09.mkChunk 280 (CVal 4 (SOff 32 0)) :: flat_map rf_row (seq 0 5).
Definition rf_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 43; YP09.mkRegion (Some 10%nat) 0 288 0 0 rf_chunks ].
(* The row facts (base_j <= 38, 2 <= nch_j <= 40, boxreg_B3) hold only for j < n: the walk adds them row by row. *)
Definition rf_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3); (12%nat, mkAF 1 40 0);
(13%nat, mkAF 1 40 0); (32%nat, mkAF 0 5 0); (43%nat, mkAF RF_SB RF_SB 0)] [] [].
Definition ss_rf : sstate := mkSS AF_range_free sr_atoms rf_regions None rf_facts.
Definition rf_SH : list shent := [ mkSHE 10 0 288 ].
Definition rf_extra (bs : list byte) : list word :=
Z_to_bv 64 (rfu bs 280) ::
flat_map (fun j => [Z_to_bv 64 (rfu bs (56 * Z.of_nat j + 8)); Z_to_bv 64 (rfu bs (56 * Z.of_nat j + 12))]) (seq 0 5) ++
[Z_to_bv 64 RF_SB].
Definition ER (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (rf_extra bs)).
Lemma rf_ew : forall regs bs,
ew (ER regs bs) 32 = Z_to_bv 64 (rfu bs 280) /\
(forall j, (j < 5)%nat -> ew (ER regs bs) (33 + 2 * j) = Z_to_bv 64 (rfu bs (56 * Z.of_nat j + 8)) /\
  ew (ER regs bs) (34 + 2 * j) = Z_to_bv 64 (rfu bs (56 * Z.of_nat j + 12))) /\
ew (ER regs bs) 43 = Z_to_bv 64 RF_SB.
Proof.
intros regs bs. split; [reflexivity|]. split; [|reflexivity].
intros j Hj. destruct j as [|[|[|[|[|j]]]]]; [| | | | | lia]; split; reflexivity.
Qed.
Lemma rf_chunks_rows : forall (P : YP09.chunk -> Prop) (l : list nat),
(forall j, In j l -> Forall P (rf_row j)) -> Forall P (flat_map rf_row l).
Proof.
intros P l. induction l as [|j l IH]; intros H; cbn [flat_map]; [constructor|].
apply Forall_app. split; [apply H; left; reflexivity | apply IH; intros j' Hj'; apply H; right; exact Hj'].
Qed.
Lemma rf_afact_val : forall E n v lo hi, ew E n = Z_to_bv 64 v -> lo <= v <= hi -> 0 <= v < 2 ^ 64 ->
afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi H Hv Hv64. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
(* The words the walk reads, as Pau's fields: n at +280, and base / nch of row j < n at +56 j + 8 / +56 j + 12. *)
Lemma rf_n_val : forall bs, length bs = 288%nat -> Boxreg.boxreg_B1 bs -> rfu bs 280 = Boxreg.bx_n bs.
Proof.
intros bs HLEN HB1. unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.bx_n in *.
apply rfu_rd4; [lia | rewrite HLEN; lia | lia].
Qed.
Lemma rf_row_vals : forall bs (j : Z), length bs = 288%nat -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
0 <= j -> j < Boxreg.bx_n bs -> j <= 4 ->
rfu bs (56 * j + 8) = Boxreg.bx_base bs j /\ rfu bs (56 * j + 12) = Boxreg.bx_nch bs j /\
0 <= Boxreg.bx_base bs j <= 38 /\ 2 <= Boxreg.bx_nch bs j <= 40 /\
Boxreg.bx_base bs j + Boxreg.bx_nch bs j <= 40.
Proof.
intros bs j HLEN HB2 HB3 Hj0 Hjn Hj4.
destruct (Boxreg.B3_bounds bs j HB2 HB3 ltac:(lia)) as (Bb & Bn & Be).
unfold Boxreg.bx_base, Boxreg.bx_nch in *.
rewrite !rfu_rd4 by (rewrite ?HLEN; lia). lia.
Qed.
(* The values of the expressions the run stops on. *)
Lemma rf_dn_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma rf_dn_U : forall E x v, U E x = v mod 2 ^ 64 -> sv_denot E x = Z_to_bv 64 v.
Proof. intros E x v H. apply bv_eq. rewrite Z_to_bv_unsigned. exact H. Qed.
Lemma rf_U_atom : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* subw a3,a3,a2 at 0x814f8: fabric + (-1) * nch. *)
Lemma rf_dn_fab : forall E nch fabric, ew E 12 = Z_to_bv 64 nch -> ew E 13 = Z_to_bv 64 fabric ->
1 <= nch <= 40 -> 1 <= fabric <= 40 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SLit (-1))) (SOff 13 0)) = Z_to_bv 64 (fabric - nch).
Proof.
intros E nch fabric H12 H13 Hn Hf. apply rf_dn_U.
rewrite U_SAlu, U_SMd, U_SLit, (rf_U_atom E 12 nch H12), (rf_U_atom E 13 fabric H13). cbn [zalu_raw zmd_raw].
unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite !(Z.mod_small nch) by lia. rewrite !(Z.mod_small fabric) by lia.
Z.div_mod_to_equations. lia.
Qed.
(* add t4,a2,t5 at 0x8158c: base_i + nch_i. *)
Lemma rf_dn_add : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> 0 <= va <= 40 -> 0 <= vb <= 40 ->
sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (va + vb).
Proof.
intros E a b va vb Ha Hb Hva Hvb. apply rf_dn_U.
rewrite U_SAlu, (rf_U_atom E a va Ha), (rf_U_atom E b vb Hb). cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_small va), (Z.mod_small vb) by lia. reflexivity.
Qed.
(* addw t0,a2,a1 at 0x8153c: nch + base, exact for 0 <= base <= 40. *)
Lemma rf_dn_addw : forall E nch base, ew E 12 = Z_to_bv 64 nch -> ew E 11 = Z_to_bv 64 base -> 1 <= nch <= 40 -> 0 <= base <= 40 ->
sv_denot E (SAluw ALU_ADD (SOff 12 0) (SOff 11 0)) = Z_to_bv 64 (nch + base).
Proof.
intros E nch base H12 H11 Hn Hb. transitivity (sv_denot E (SLit (nch + base))); [|reflexivity].
apply S_inj. rewrite S_SAluw, S_SLit, (rf_U_atom E 12 nch H12), (rf_U_atom E 11 base H11).
cbn [zalu_raw]. rewrite !(Z.mod_small _ (2 ^ 64)) by lia. rewrite !(Z.mod_small _ (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 32 / 2) with (2 ^ 31). change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.
(* xori a7,a0,-1 at 0x81538: not t. *)
Lemma rf_dn_not : forall E t, ew E 10 = Z_to_bv 64 t -> 0 <= t < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - t).
Proof.
intros E t H10 Ht. apply rf_dn_U. rewrite U_SAlu, U_SLit, (rf_U_atom E 10 t H10). cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_small t) by lia. change ((-1) mod 2 ^ 64) with (Z.ones 64).
assert (Hx : Z.lxor t (Z.ones 64) = 2 ^ 64 - 1 - t).
{ assert (H0 : Z.land t (Z.lxor t (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.lt_ge_cases k 64) as [Hlo | Hhi].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit t k); reflexivity.
    - assert (Tk : Z.testbit t k = false) by (rewrite <- (Z.mod_small t (2 ^ 64)) by lia; apply Z.mod_pow2_bits_high; lia).
      rewrite Tk. reflexivity. }
  pose proof (Z.add_nocarry_lxor t (Z.lxor t (Z.ones 64)) H0) as Hs.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Hs. change (Z.ones 64) with (2 ^ 64 - 1) in Hs |- *. lia. }
rewrite Hx. reflexivity.
Qed.
(* The branch conditions on literal words. *)
Lemma rf_lt : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. apply Boxreg.lts_lit; lia. Qed.
Lemma rf_ge : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite Boxreg.lts_lit by lia. reflexivity. Qed.
Lemma rf_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. apply Boxreg.ltu_lit; lia. Qed.
Lemma rf_ne : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a =? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. rewrite Boxreg.eqb_lit by lia. reflexivity. Qed.
Lemma rf_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. intros E z. cbn [sv_denot]. reflexivity. Qed.
(* The two paths that leave a row at 0x815a4 (bge taken, or bge and blt not taken) carry one or two branch facts the
   join does not need: they are dropped, so both paths reach the join in the same state. *)
Lemma rf_facts_drop : forall E ss ms, st_ok_pi SEGS VAL E ss ms ->
st_ok_pi SEGS VAL E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
  (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms HS. pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & _ & Hl)).
unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
exact (st_ok_set_facts SEGS E _ ms (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))) HS (conj Ha (conj I Hl))).
Qed.
Lemma rf_entry : forall ly S W (regs : bvmap 5 word) mem md ch (t nch fabric : Z) (bs : list byte),
afn_pre SEGS B RANGE_FREE_STKB ly S W regs mem md ch ->
getr regs 10 = w64 t -> getr regs 12 = w64 nch -> getr regs 13 = w64 fabric -> 1 <= nch <= 40 -> 1 <= fabric <= 40 ->
afobj SEGS B ly S W mem t BoxBReacBoxregInit.REG_SIZEB -> length bs = 288%nat ->
(forall i, 0 <= i < BoxBReacBoxregInit.REG_SIZEB ->
  aview SEGS (w_H W) mem (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs ->
st_ok_pi SEGS VAL (ER regs bs) ss_rf (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_range_freeP) mem (seg_rom SEGS)))
/\ sh_ok SEGS RFx rf_SH (ER regs bs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch t nch fabric bs HPRE H10 H12 H13 Hnch Hfab HFO HLEN HM HB1.
change BoxBReacBoxregInit.REG_SIZEB with 288 in HFO, HM.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Ht8 & HRA).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RANGE_FREE_STKB = 4112) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfin) as Hfimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite restrict_mkst_fx.
destruct (rf_ew regs bs) as (EX32 & EXrow & EX43).
set (E := ER regs bs) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rf_extra bs)) n)
by (intros n Hn; subst E; unfold ER; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 nch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 fabric) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold ER; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold ER; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (FLD : forall k a, 0 <= k -> k + 4 <= 288 -> ew E a = Z_to_bv 64 (rfu bs k) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) t (YP09.mkChunk k (CVal 4 (SOff a 0)))).
{ intros k a Hk Hk4 Ha. apply (chunk_ok_val SEGS E _ t k 4 (SOff a 0) (rfu bs k)).
  - cbn [sv_denot]. rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (rfu_range bs k Hk ltac:(rewrite HLEN; lia)) as R. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  - zside.
  - change (N.to_nat 4) with 4%nat. exact (rf_val4 W mem t bs k HLEN Hk Hk4 HM). }
pose proof (rf_n_val bs HLEN HB1) as RN. unfold Boxreg.boxreg_B1 in HB1.
split.
- unfold ss_rf, AB_range_freeP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute; reflexivity.
  + unfold rf_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RFx RF_SB);
      [cbn [sv_denot RFx]; rewrite EX43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RF_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat t E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold rf_chunks. apply Forall_cons; [apply FLD; [lia | lia | exact EX32]|].
      apply rf_chunks_rows. intros j Hj. apply in_seq in Hj. unfold rf_row.
      constructor; [|constructor; [|constructor]].
      -- apply FLD; [lia | lia | exact (proj1 (EXrow j ltac:(lia)))].
      -- apply FLD; [lia | lia | exact (proj2 (EXrow j ltac:(lia)))].
  + apply pairwise_disjoint_of_extents. unfold rf_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by lia.
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hf4096 Hfceil Hflo Hfhi Hfimg C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold rf_facts. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
      revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia; change (2 ^ 3) with 8;
      revert Hf4096 Hfceil Hflo Hfhi Ht8 C1; clear; intros; repeat split; lia|].
    split; [apply (rf_afact_val E 12 nch); [exact E12 | lia | lia]|].
    split; [apply (rf_afact_val E 13 fabric); [exact E13 | lia | lia]|].
    split; [apply (rf_afact_val E 32 (Boxreg.bx_n bs)); [rewrite EX32, RN; reflexivity | lia | lia]|].
    split; [apply (rf_afact_val E 43 RF_SB); [exact EX43 | lia | unfold RF_SB; lia]|]. exact I.
- unfold sh_ok, rf_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E RFx 10 t 288 t 0 288 HRA).
  + unfold U, RFx. cbn [sv_denot]. rewrite EX43, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold RF_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. revert Happ Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Ltac rf_run HS HJ SHOK Us :=
  paj_run_tok RUN HS HJ SHOK RFspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Us |];
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac rf_runto HS HJ SHOK Us stop :=
  paj_run_to_tok RUNTO HS HJ SHOK RFspan stop; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Us |];
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac rf_rowfacts HS nb nn Fb Fn :=
  let H1 := fresh "HSt" in
  pose proof (st_ok_pi_add_fact _ _ _ nb (mkAF 0 38 0) HS (rf_afact_val _ nb _ 0 38 Fb ltac:(lia) ltac:(lia))) as H1; clear HS;
  pose proof (st_ok_pi_add_fact _ _ _ nn (mkAF 2 40 0) H1 (rf_afact_val _ nn _ 2 40 Fn ltac:(lia) ltac:(lia))) as HS; clear H1.
Ltac rf_add32 HS Dn32 lo hi :=
  let H := fresh "HSt" in
  pose proof (st_ok_pi_add_fact _ _ _ 32%nat (mkAF lo hi 0) HS (rf_afact_val _ 32%nat _ lo hi Dn32 ltac:(lia) ltac:(lia))) as H;
  clear HS; rename H into HS.
Ltac rf_leafg HS HJ Hra1 Ee1 Hae pick :=
lazymatch goal with
| |- SRr _ ?W0 _ (tbrange_free_post ?regs0 ?ly0 ?S0 _ _ _ _ _ _ ?bs0) =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msc) =>
    let N1 := fresh "RR1" in let N10 := fresh "RR10" in let matx := fresh "mat" in
    prreg HS (1%bv : bv 5) N1; prreg HS (10%bv : bv 5) N10;
    eapply (RET W0 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros matx;
    unfold tbrange_free_post, apost_base;
    exists ly0, S0, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite N1, Ee1, Hra1; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs0 (rf_extra bs0) HS); [exact Hae | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
    pick; split; [| cbn [ms_regs]; rewrite N10; reflexivity]
  end
end.
Ltac rf_leaf_ok HS HJ Hra1 Ee1 Hae := rf_leafg HS HJ Hra1 Ee1 Hae ltac:(left).
Ltac rf_leaf_no HS HJ Hra1 Ee1 Hae := rf_leafg HS HJ Hra1 Ee1 Hae ltac:(right).
Ltac rf_join HS JN jz :=
lazymatch goal with
| |- SRr _ ?W0 _ (tbrange_free_post ?regs0 ?ly0 ?S0 ?Wq ?mem0 ?md0 ?base0 ?nch0 ?fabric0 ?bs0) =>
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ef ?ss (restrict _ _) =>
    let ssj := eval vm_compute in (mkSST 5624 (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
                 (mkFacts (f_atoms (ss_facts ss)) (@nil acond) (f_alias (ss_facts ss)))) in
    assert (JN : (forall i, 0 <= i < jz ->
                    ~ Boxreg.meets base0 nch0 (Boxreg.bx_base bs0 i) (Boxreg.bx_nch bs0 i)) ->
      forall ms2 md2, st_ok_pi SEGS VAL Ef ssj (restrict (w_H W0) ms2) ->
      sh_ok SEGS RFx rf_SH Ef (mrestrict (w_H W0) (ms_mem ms2)) ->
      ajournal SEGS B RANGE_FREE_STKB (spZ regs0) [] ly0 S0 W0 mem0 md0 [] ly0 S0 W0 (ms_mem ms2) md2 0 ->
      SRr SEGS W0 (mkCfg ms2 md2) (tbrange_free_post regs0 ly0 S0 W0 mem0 md0 base0 nch0 fabric0 bs0))
  end
end.
(* A branch the run stops on, as a fact on Pau's values (the conditions of 0x814f4, 0x814fc, 0x8155c, 0x8159c, 0x815a0,
   0x815b4). The register facts (atoms 10..13) and the row facts are found in the context by their atom. *)
Ltac rf_hc :=
lazymatch goal with
| Hc : branch_taken _ (sv_denot ?E' _) (sv_denot _ _) = _ |- _ =>
  let rwa n := lazymatch goal with H : ew _ n = Z_to_bv 64 ?v |- _ =>
    rewrite (rf_dn_atom E' n v ltac:(cbn [ew ewset Nat.eqb]; exact H)) in Hc end in
  lazymatch type of Hc with
  | branch_taken BC_LT (sv_denot _ (SOff 11 0)) (sv_denot _ (SLit 0)) = _ =>
    rwa 11%nat; cbn [sv_denot] in Hc; rewrite rf_lt in Hc by lia
  | branch_taken BC_LT (sv_denot _ (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SLit (-1))) (SOff 13 0))) _ = _ =>
    lazymatch goal with H12 : ew _ 12 = Z_to_bv 64 ?vn |- _ => lazymatch goal with H13 : ew _ 13 = Z_to_bv 64 ?vf |- _ =>
    rewrite (rf_dn_fab E' vn vf ltac:(cbn [ew ewset Nat.eqb]; exact H12) ltac:(cbn [ew ewset Nat.eqb]; exact H13)
      ltac:(lia) ltac:(lia)) in Hc end end;
    rwa 11%nat; rewrite rf_lt in Hc by lia
  | branch_taken BC_LTU (sv_denot _ (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))) (sv_denot _ (SLit _)) = _ =>
    lazymatch goal with H10 : ew _ 10 = Z_to_bv 64 ?vt |- _ =>
    rewrite (rf_dn_not E' vt ltac:(cbn [ew ewset Nat.eqb]; exact H10) ltac:(lia)) in Hc end; cbn [sv_denot] in Hc;
    rewrite rf_ltu in Hc by lia
  | branch_taken BC_GE (sv_denot _ (SOff 11 0)) (sv_denot _ (SAlu ALU_ADD (SOff ?a 0) (SOff ?b 0))) = _ =>
    lazymatch goal with Ha : ew _ a = Z_to_bv 64 ?va |- _ => lazymatch goal with Hb : ew _ b = Z_to_bv 64 ?vb |- _ =>
    rewrite (rf_dn_add E' a b va vb ltac:(cbn [ew ewset Nat.eqb]; exact Ha) ltac:(cbn [ew ewset Nat.eqb]; exact Hb)
      ltac:(lia) ltac:(lia)) in Hc end end;
    rwa 11%nat; rewrite rf_ge in Hc by lia
  | branch_taken BC_LT (sv_denot _ (SOff ?a 0)) (sv_denot _ (SAluw ALU_ADD (SOff 12 0) (SOff 11 0))) = _ =>
    lazymatch goal with H12 : ew _ 12 = Z_to_bv 64 ?vn |- _ => lazymatch goal with H11 : ew _ 11 = Z_to_bv 64 ?vb |- _ =>
    rewrite (rf_dn_addw E' vn vb ltac:(cbn [ew ewset Nat.eqb]; exact H12) ltac:(cbn [ew ewset Nat.eqb]; exact H11)
      ltac:(lia) ltac:(lia)) in Hc end end;
    rwa a; rewrite rf_lt in Hc by lia
  | branch_taken BC_NE (sv_denot _ (SOff 32 0)) (sv_denot _ (SLit _)) = _ =>
    rwa 32%nat; cbn [sv_denot] in Hc; rewrite rf_ne in Hc by lia
  end;
  repeat lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff in Hc
  | negb _ = false => apply negb_false_iff in Hc
  end;
  lazymatch type of Hc with
  | (_ <? _) = true => apply Z.ltb_lt in Hc
  | (_ <? _) = false => apply Z.ltb_ge in Hc
  | (_ =? _) = true => apply Z.eqb_eq in Hc
  | (_ =? _) = false => apply Z.eqb_neq in Hc
  end
end.
(* Run to the row's bge (0x8159c), refuting the UBSan pointer check at 0x8155c when the run stops there (rows 1..4). *)
Ltac rf_row_run HS HJ SHOK Us Htb :=
  rf_run HS HJ SHOK Us;
  lazymatch goal with HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM RFx rf_SH ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K RFx RFspan rf_SH (start K RFx RFspan rf_SH ss) end in
    lazymatch why with
    | SR_branch BC_LTU _ _ => psrr_branch_tok RUN BR HS SHOK RFspan;
        [ rf_hc; lazymatch goal with H : 2 ^ 64 - 1 - _ < _ |- _ => exfalso; revert H Htb; clear; intros; lia end
        | match goal with H : branch_taken _ _ _ = _ |- _ => clear H end; rf_run HS HJ SHOK Us ]
    | _ => idtac
    end end.
Theorem pb_brange_free : tbrange_free_spec.
Proof.
unfold tbrange_free_spec.
intros ly S W regs mem md ch t base nch fabric bs HPRE H10 H11 H12 H13 Hbase Hnch Hfab HFO HLEN HM HB1 HB2 HB3.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rf_entry ly S W regs mem md ch t nch fabric bs HPRE H10 H12 H13 Hnch Hfab HFO HLEN HM HB1) as [HS SHOK].
pose proof (ajournal_init SEGS B RANGE_FREE_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & _ & _ & _ & _ & _ & _ & _).
assert (Htb : 4096 <= t /\ t + 288 <= 2 ^ 47).
{ change BoxBReacBoxregInit.REG_SIZEB with 288 in HFO. pose proof HFO as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & _).
  pose proof (asan_consts) as (C1 & _ & _ & _ & _). lia. }
clear HFO HM.
unfold Boxreg.boxreg_B1 in HB1.
remember (ER regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ER; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rf_extra bs)) n)
by (intros n Hn; subst E; unfold ER; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 base) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 nch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 fabric) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (Dn32 : ew E 32 = Z_to_bv 64 (Boxreg.bx_n bs))
by (subst E; rewrite (proj1 (rf_ew regs bs)), (rf_n_val bs HLEN ltac:(unfold Boxreg.boxreg_B1; lia)); reflexivity).
assert (A33 : ew E 33 = Z_to_bv 64 (rfu bs 8)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 0%nat ltac:(lia)) as [H _]; exact H).
assert (A34 : ew E 34 = Z_to_bv 64 (rfu bs 12)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 0%nat ltac:(lia)) as [_ H]; exact H).
assert (A35 : ew E 35 = Z_to_bv 64 (rfu bs 64)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 1%nat ltac:(lia)) as [H _]; exact H).
assert (A36 : ew E 36 = Z_to_bv 64 (rfu bs 68)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 1%nat ltac:(lia)) as [_ H]; exact H).
assert (A37 : ew E 37 = Z_to_bv 64 (rfu bs 120)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 2%nat ltac:(lia)) as [H _]; exact H).
assert (A38 : ew E 38 = Z_to_bv 64 (rfu bs 124)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 2%nat ltac:(lia)) as [_ H]; exact H).
assert (A39 : ew E 39 = Z_to_bv 64 (rfu bs 176)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 3%nat ltac:(lia)) as [H _]; exact H).
assert (A40 : ew E 40 = Z_to_bv 64 (rfu bs 180)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 3%nat ltac:(lia)) as [_ H]; exact H).
assert (A41 : ew E 41 = Z_to_bv 64 (rfu bs 232)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 4%nat ltac:(lia)) as [H _]; exact H).
assert (A42 : ew E 42 = Z_to_bv 64 (rfu bs 236)) by (subst E; destruct (proj1 (proj2 (rf_ew regs bs)) 4%nat ltac:(lia)) as [_ H]; exact H).
assert (HAE : env_agree 32 (Ereg regs (rf_extra bs)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EL.
unfold cfg_at. change (w64 AB_range_freeP) with (Z_to_bv 64 AB_range_freeP).
(* 1. base < 0 ? *)
rf_run HS HJ SHOK Usp.
psrr_branch_tok RUN BR HS SHOK RFspan.
{ rf_hc. rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE. intros (Hok & _); lia. }
rf_hc. rename Hc into Hge0.
(* 2. fabric - nch < base ? *)
rf_run HS HJ SHOK Usp.
psrr_branch_tok RUN BR HS SHOK RFspan.
{ rf_hc. rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE. intros (Hok & _); lia. }
rf_hc. rename Hc into Hle.
(* 3. n <= 0 ? *)
rf_run HS HJ SHOK Usp.
psrr_branch_tok RUN BR HS SHOK RFspan.
{ rewrite (rf_den_lit E 0), (rf_dn_atom E 32 (Boxreg.bx_n bs) Dn32) in Hc; rewrite rf_ge in Hc by lia;
  apply negb_true_iff in Hc; apply Z.ltb_ge in Hc;
  rf_add32 HS Dn32 0 0; rf_run HS HJ SHOK Usp; rf_leaf_ok HS HJ Hra E1 HAE;
  split; [lia | intros i Hi; lia]. }
rewrite (rf_den_lit E 0), (rf_dn_atom E 32 (Boxreg.bx_n bs) Dn32) in Hc; rewrite rf_ge in Hc by lia;
apply negb_false_iff in Hc; apply Z.ltb_lt in Hc. rename Hc into Hpos.
(* ===== ROW 0 ===== *)
assert (Hj0 : 0 < Boxreg.bx_n bs) by lia.
destruct (rf_row_vals bs 0 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (Vb0 & Vn0 & Rb0 & Rn0 & Rbn0).
change (56 * 0 + 8) with 8 in Vb0. change (56 * 0 + 12) with 12 in Vn0.
assert (Db0 : ew E 33 = Z_to_bv 64 (Boxreg.bx_base bs 0)) by (rewrite A33, Vb0; reflexivity).
assert (Dn0 : ew E 34 = Z_to_bv 64 (Boxreg.bx_nch bs 0)) by (rewrite A34, Vn0; reflexivity).
rf_rowfacts HS 33%nat 34%nat Db0 Dn0.
rf_add32 HS Dn32 1 5.
rf_row_run HS HJ SHOK Usp Htb.
rf_join HS JOIN0 1.
{ clear HS SHOK HJ; intros HNM0 msJ0 mdJ0 HS SHOK HJ.
  rf_run HS HJ SHOK Usp.
  psrr_branch_tok RUN BR HS SHOK RFspan.
  { rf_hc. assert (Hj1 : 1 < Boxreg.bx_n bs) by lia.
    destruct (rf_row_vals bs 1 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (Vb1 & Vn1 & Rb1 & Rn1 & Rbn1).
    change (56 * 1 + 8) with 64 in Vb1. change (56 * 1 + 12) with 68 in Vn1.
    assert (Db1 : ew E 35 = Z_to_bv 64 (Boxreg.bx_base bs 1)) by (rewrite A35, Vb1; reflexivity).
    assert (Dn1 : ew E 36 = Z_to_bv 64 (Boxreg.bx_nch bs 1)) by (rewrite A36, Vn1; reflexivity).
    rf_rowfacts HS 35%nat 36%nat Db1 Dn1. rf_add32 HS Dn32 2 5. rf_row_run HS HJ SHOK Usp Htb.
    rf_join HS JOIN1 2.
    { clear HS SHOK HJ; intros HNM1 msJ1 mdJ1 HS SHOK HJ.
      rf_run HS HJ SHOK Usp.
      psrr_branch_tok RUN BR HS SHOK RFspan.
      { rf_hc. assert (Hj2 : 2 < Boxreg.bx_n bs) by lia.
        destruct (rf_row_vals bs 2 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (Vb2 & Vn2 & Rb2 & Rn2 & Rbn2).
        change (56 * 2 + 8) with 120 in Vb2. change (56 * 2 + 12) with 124 in Vn2.
        assert (Db2 : ew E 37 = Z_to_bv 64 (Boxreg.bx_base bs 2)) by (rewrite A37, Vb2; reflexivity).
        assert (Dn2 : ew E 38 = Z_to_bv 64 (Boxreg.bx_nch bs 2)) by (rewrite A38, Vn2; reflexivity).
        rf_rowfacts HS 37%nat 38%nat Db2 Dn2. rf_add32 HS Dn32 3 5. rf_row_run HS HJ SHOK Usp Htb.
        rf_join HS JOIN2 3.
        { clear HS SHOK HJ; intros HNM2 msJ2 mdJ2 HS SHOK HJ.
          rf_run HS HJ SHOK Usp.
          psrr_branch_tok RUN BR HS SHOK RFspan.
          { rf_hc. assert (Hj3 : 3 < Boxreg.bx_n bs) by lia.
            destruct (rf_row_vals bs 3 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (Vb3 & Vn3 & Rb3 & Rn3 & Rbn3).
            change (56 * 3 + 8) with 176 in Vb3. change (56 * 3 + 12) with 180 in Vn3.
            assert (Db3 : ew E 39 = Z_to_bv 64 (Boxreg.bx_base bs 3)) by (rewrite A39, Vb3; reflexivity).
            assert (Dn3 : ew E 40 = Z_to_bv 64 (Boxreg.bx_nch bs 3)) by (rewrite A40, Vn3; reflexivity).
            rf_rowfacts HS 39%nat 40%nat Db3 Dn3. rf_add32 HS Dn32 4 5. rf_row_run HS HJ SHOK Usp Htb.
            rf_join HS JOIN3 4.
            { clear HS SHOK HJ; intros HNM3 msJ3 mdJ3 HS SHOK HJ.
              rf_run HS HJ SHOK Usp.
              psrr_branch_tok RUN BR HS SHOK RFspan.
              { rf_hc. assert (Hj4 : 4 < Boxreg.bx_n bs) by lia.
                destruct (rf_row_vals bs 4 HLEN HB2 HB3 ltac:(lia) ltac:(lia) ltac:(lia)) as (Vb4 & Vn4 & Rb4 & Rn4 & Rbn4).
                change (56 * 4 + 8) with 232 in Vb4. change (56 * 4 + 12) with 236 in Vn4.
                assert (Db4 : ew E 41 = Z_to_bv 64 (Boxreg.bx_base bs 4)) by (rewrite A41, Vb4; reflexivity).
                assert (Dn4 : ew E 42 = Z_to_bv 64 (Boxreg.bx_nch bs 4)) by (rewrite A42, Vn4; reflexivity).
                rf_rowfacts HS 41%nat 42%nat Db4 Dn4. rf_add32 HS Dn32 5 5. rf_row_run HS HJ SHOK Usp Htb.
                rf_join HS JOIN4 5.
                { clear HS SHOK HJ; intros HNM4 msJ4 mdJ4 HS SHOK HJ.
                  rf_run HS HJ SHOK Usp.
                  psrr_branch_tok RUN BR HS SHOK RFspan.
                  { rf_hc. exfalso. lia. }
                  rf_hc. rf_add32 HS Dn32 5 5. rf_run HS HJ SHOK Usp.
                  rf_leaf_ok HS HJ Hra E1 HAE. split; [lia | intros i Hi; apply HNM4; lia]. }
                psrr_branch_tok RUN BR HS SHOK RFspan.
                { rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
                  exact (JOIN4 ltac:(intros i Hi; assert (i = 4 \/ i < 4) as [->|Hlt] by lia;
                    [unfold Boxreg.meets; lia | apply HNM3; lia]) _ _ HSd SHOK HJ). }
                rf_hc. rename Hc into Hbge4. rf_run HS HJ SHOK Usp.
                psrr_branch_tok RUN BR HS SHOK RFspan.
                { rf_hc. rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
                  intros (_ & Hall); apply (Hall 4 ltac:(lia)); unfold Boxreg.meets; lia. }
                rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
                exact (JOIN4 ltac:(intros i Hi; assert (i = 4 \/ i < 4) as [->|Hlt] by lia;
                  [unfold Boxreg.meets; lia | apply HNM3; lia]) _ _ HSd SHOK HJ). }
              rf_hc. rf_add32 HS Dn32 4 4. rf_run HS HJ SHOK Usp.
              rf_leaf_ok HS HJ Hra E1 HAE. split; [lia | intros i Hi; apply HNM3; lia]. }
            psrr_branch_tok RUN BR HS SHOK RFspan.
            { rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
              exact (JOIN3 ltac:(intros i Hi; assert (i = 3 \/ i < 3) as [->|Hlt] by lia;
                [unfold Boxreg.meets; lia | apply HNM2; lia]) _ _ HSd SHOK HJ). }
            rf_hc. rename Hc into Hbge3. rf_run HS HJ SHOK Usp.
            psrr_branch_tok RUN BR HS SHOK RFspan.
            { rf_hc. rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
              intros (_ & Hall); apply (Hall 3 ltac:(lia)); unfold Boxreg.meets; lia. }
            rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
            exact (JOIN3 ltac:(intros i Hi; assert (i = 3 \/ i < 3) as [->|Hlt] by lia;
              [unfold Boxreg.meets; lia | apply HNM2; lia]) _ _ HSd SHOK HJ). }
          rf_hc. rf_add32 HS Dn32 3 3. rf_run HS HJ SHOK Usp.
          rf_leaf_ok HS HJ Hra E1 HAE. split; [lia | intros i Hi; apply HNM2; lia]. }
        psrr_branch_tok RUN BR HS SHOK RFspan.
        { rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
          exact (JOIN2 ltac:(intros i Hi; assert (i = 2 \/ i < 2) as [->|Hlt] by lia;
            [unfold Boxreg.meets; lia | apply HNM1; lia]) _ _ HSd SHOK HJ). }
        rf_hc. rename Hc into Hbge2. rf_run HS HJ SHOK Usp.
        psrr_branch_tok RUN BR HS SHOK RFspan.
        { rf_hc. rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
          intros (_ & Hall); apply (Hall 2 ltac:(lia)); unfold Boxreg.meets; lia. }
        rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
        exact (JOIN2 ltac:(intros i Hi; assert (i = 2 \/ i < 2) as [->|Hlt] by lia;
          [unfold Boxreg.meets; lia | apply HNM1; lia]) _ _ HSd SHOK HJ). }
      rf_hc. rf_add32 HS Dn32 2 2. rf_run HS HJ SHOK Usp.
      rf_leaf_ok HS HJ Hra E1 HAE. split; [lia | intros i Hi; apply HNM1; lia]. }
    psrr_branch_tok RUN BR HS SHOK RFspan.
    { rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
      exact (JOIN1 ltac:(intros i Hi; assert (i = 1 \/ i < 1) as [->|Hlt] by lia;
        [unfold Boxreg.meets; lia | apply HNM0; lia]) _ _ HSd SHOK HJ). }
    rf_hc. rename Hc into Hbge1. rf_run HS HJ SHOK Usp.
    psrr_branch_tok RUN BR HS SHOK RFspan.
    { rf_hc. rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
      intros (_ & Hall); apply (Hall 1 ltac:(lia)); unfold Boxreg.meets; lia. }
    rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
    exact (JOIN1 ltac:(intros i Hi; assert (i = 1 \/ i < 1) as [->|Hlt] by lia;
      [unfold Boxreg.meets; lia | apply HNM0; lia]) _ _ HSd SHOK HJ). }
  rf_hc. rf_add32 HS Dn32 1 1. rf_run HS HJ SHOK Usp.
  rf_leaf_ok HS HJ Hra E1 HAE. split; [lia | intros i Hi; apply HNM0; lia]. }
psrr_branch_tok RUN BR HS SHOK RFspan.
{ rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
  exact (JOIN0 ltac:(intros i Hi; assert (i = 0) as -> by lia; unfold Boxreg.meets; lia) _ _ HSd SHOK HJ). }
rf_hc. rename Hc into Hbge0. rf_run HS HJ SHOK Usp.
psrr_branch_tok RUN BR HS SHOK RFspan.
{ rf_hc. rf_run HS HJ SHOK Usp. rf_leaf_no HS HJ Hra E1 HAE.
  intros (_ & Hall); apply (Hall 0 ltac:(lia)); unfold Boxreg.meets; lia. }
rf_hc. rf_runto HS HJ SHOK Usp 5624. pose proof (rf_facts_drop _ _ _ HS) as HSd.
exact (JOIN0 ltac:(intros i Hi; assert (i = 0) as -> by lia; unfold Boxreg.meets; lia) _ _ HSd SHOK HJ).
Qed.
End h.
End f.
End d.
