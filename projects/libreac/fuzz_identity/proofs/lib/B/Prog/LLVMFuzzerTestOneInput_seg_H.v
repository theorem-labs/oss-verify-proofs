(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/UI3m.v:302-305 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:207-209 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Segment H of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), +0x11c4 .. +0x128c (0x81938 .. 0x81a00):
   the "any firmware value" block. seg_H of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v.

   The code (BASE + 0x11c4 .. BASE + 0x1288), with v = t_any_fw (the 16-bit value in s8 = x24),
   ef = SF + 496 (in s9 = x25) and the counter slot mf + 208 (zero at the start):
     0x81938 .. 0x81948   a0 = v / 1000 by the reciprocal 8389 (slli 48, srli 51, mul, srli 20)
     0x8194c  srli s2,a0,0x14      x18 = v / 1000, kept across the two calls
     0x81950 .. 0x8195c           a0 = ef, a1 = mf + 208, a2 = v / 1000, a3 = 1
     0x81960  jal put_dec          writes DEC (v / 1000) 1 at ef + 0 and the new counter at mf + 208
     0x81964 .. 0x81970           a0 = d1 (the counter), mf + 208 := d1 + 1
     0x81974  bgeu a0,16           UBSan: the index is inside ef (16 bytes); d1 <= 2
     0x81978  not s4,s9            x20 = ~ef, kept to the second check
     0x8197c  bltu s4,a0           UBSan: ef + d1 does not wrap
     0x81980 .. 0x81988           ef[d1] := '.'
     0x8198c .. 0x819a8           a2 = v - 1000 * (v / 1000) truncated to 16 bits = v mod 1000, a3 = 3
     0x819ac  jal put_dec          writes DEC (v mod 1000) 3 at ef + d1 + 1, counter := d1 + 4
     0x819b0 .. 0x819bc           s3 = the counter n2 = d1 + 4; the two UBSan checks again
     0x819c0 .. 0x819c4           x18 = SF + 464 = f
     0x819c8 .. 0x819cc           ef[n2] := 0
     0x819d0 .. 0x819dc  jal reac_identity_fw_str   f := FW v and its NUL, at capacity 8
     0x819e0  ld s6,120(s1)        x22 = the display capacity slot
     0x819e4  bltz a0              the formatter did write (a0 = L v >= 5)
     0x819e8  bne s3,a0            L v = n2
     0x819ec .. 0x819f8  jal bcmp  the n2 + 1 bytes of f and of ef agree
     0x819fc  bnez a0              they do, so the abort is not reached
   The three calls are program calls with no allocator event: put_dec (HPD) twice and
   reac_identity_fw_str (HFWS), plus the bcmp wrapper (ABCMP). The model: ef holds
   SlotModel.t_EF = DEC (v / 1000) 1 ++ [dot] ++ DEC (v mod 1000) 3, and FW v is the same string
   (reac_identity_fw_str_c3), so the compare succeeds.

   `h_core` walks the block on raw facts (no boundary predicate): it is
   LLVMFuzzerTestOneInput_seg_H_hand3_stmt.h_core_stmt given the put_dec call lemma. The three call steps are the
   hand lemmas h_pd_call (LLVMFuzzerTestOneInput_seg_H_hand2.v), h_fw_call and h_bcmp_call
   (LLVMFuzzerTestOneInput_seg_H_hand.v); `seg_H` at the end is the glue h_glue
   (LLVMFuzzerTestOneInput_seg_H_hand3.v) applied to h_core. The kept-memory shape rvs_k and its lemmas are
   reused from lib/B/Prog/reac_identity_reac_ver_str.v (a proved sibling walk), not restated. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_H_hand_stmt LLVMFuzzerTestOneInput_seg_H_hand2_stmt
LLVMFuzzerTestOneInput_seg_H_hand.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
put_dec reac_identity_fw_str reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_H_hand2
LLVMFuzzerTestOneInput_seg_H_hand3_stmt LLVMFuzzerTestOneInput_seg_H_hand3.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import put_dec_c reac_identity_fw_str_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this segment's address arithmetic (shadow_addr, the
   frame's alignment) and the reciprocal need it, so it is turned back on here (as lib/A/Prog/...D6.v does). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model of the block ------------------------------------------------------------- *)
(* d1 = the digits of v / 1000 (1 or 2), n2 = the whole string's length (5 or 6). *)
Definition h_d1 (v : Z) : Z := dec_len (v / 1000) 1.
Definition h_n2 (v : Z) : Z := h_d1 v + 4.
Lemma h_d1_range : forall v, 0 <= v < 65536 -> 1 <= h_d1 v <= 2.
Proof.
intros v Hv. unfold h_d1, dec_len.
rewrite reac_identity_fw_str_dec_h by (Z.div_mod_to_equations; lia).
destruct (10 <=? v / 1000); cbn [app length]; lia.
Qed.
Lemma h_dec3_len : forall f, 0 <= f < 1000 -> dec_len f 3 = 3.
Proof. intros f Hf. unfold dec_len. rewrite reac_identity_fw_str_dec_f by lia. reflexivity. Qed.
(* The bytes ef holds: the plain model's t_EF of the input is the two decimal pieces and the dot. *)
Lemma h_EF : forall inp,
  SlotModel.t_EF inp =
  IdentSpec.DEC (SlotModel.t_any_fw inp / 1000) 1 ++ [SlotModel.dot] ++ IdentSpec.DEC (SlotModel.t_any_fw inp mod 1000) 3.
Proof. intros inp. reflexivity. Qed.
Lemma h_EF_len : forall v, 0 <= v < 65536 ->
  Z.of_nat (length (IdentSpec.DEC (v / 1000) 1 ++ [SlotModel.dot] ++ IdentSpec.DEC (v mod 1000) 3)) = h_n2 v.
Proof.
intros v Hv. rewrite !length_app. cbn [length].
pose proof (h_dec3_len (v mod 1000) ltac:(apply Z.mod_pos_bound; lia)) as E3. unfold dec_len in E3.
unfold h_n2, h_d1, dec_len. lia.
Qed.
(* The formatter's string is the same, with its NUL. *)
Lemma h_FW : forall v, 0 <= v < 65536 ->
  reac_identity_fw_str_c.FW v = IdentSpec.DEC (v / 1000) 1 ++ [SlotModel.dot] ++ IdentSpec.DEC (v mod 1000) 3.
Proof. intros v Hv. exact (reac_identity_fw_str_c3 v Hv). Qed.
Lemma h_L : forall v, 0 <= v < 65536 -> reac_identity_fw_str_c.L v = h_n2 v.
Proof.
intros v Hv. unfold reac_identity_fw_str_c.L. rewrite (h_FW v Hv).
pose proof (h_EF_len v Hv) as H. exact H.
Qed.
Lemma h_fw_n : forall v, 0 <= v < 65536 -> reac_identity_fw_str.fw_n v = h_n2 v + 1.
Proof. intros v Hv. unfold reac_identity_fw_str.fw_n. rewrite (h_L v Hv). reflexivity. Qed.
Lemma h_fw_bytes : forall v, 0 <= v < 65536 ->
  reac_identity_fw_str.fw_bytes v =
  (map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0].
Proof.
intros v Hv. unfold reac_identity_fw_str.fw_bytes. rewrite (h_FW v Hv). rewrite ?map_app. cbn [map].
reflexivity.
Qed.
(* The reciprocal: what the listing computes at 0x81938 .. 0x8194c is v / 1000. *)
Lemma h_recip : forall v, 0 <= v < 65536 -> v / 8 * 8389 / 2 ^ 20 = v / 1000.
Proof.
intros v Hv. apply Z.eqb_eq.
apply (IdentSpec.z_all_spec (fun x => (x / 8 * 8389 / 2 ^ 20 =? x / 1000)) (Z.to_nat 65536) 0
         ltac:(vm_compute; reflexivity) v).
rewrite Z2Nat.id by lia. lia.
Qed.
(* The complement the listing takes at 0x81978 (`not s4,s9`), as a number. *)
Lemma h_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (E2 : 2 ^ 64 - 1 - x = Z.lnot x mod 2 ^ 64).
{ apply (Zmod_unique (Z.lnot x) (2 ^ 64) (-1) (2 ^ 64 - 1 - x)); unfold Z.lnot; lia. }
apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, E2.
replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
- rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.lnot_spec by lia. destruct (Z.testbit x n); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia.
  rewrite (Z.bits_above_log2 x n); [reflexivity | lia |].
  assert (Hl2 : Z.log2 x < 64).
  { destruct (Z.eq_dec x 0) as [-> | Hx0]; [cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))). lia. }
  lia.
Qed.
(* What the listing computes at 0x81938 .. 0x8194c (the reciprocal of 1000) and at
   0x8198c .. 0x8199c (v - 1000 * (v / 1000), truncated to 16 bits). *)
Lemma h_zc : forall z, 0 <= z < 2 ^ 64 -> z mod 2 ^ 64 = z.
Proof. intros z Hz. apply Z.mod_small. exact Hz. Qed.
Lemma h_v1000 : forall v, 0 <= v < 65536 ->
  alu64 ALU_SRL (mul_div M_MUL (alu64 ALU_SRL (alu64 ALU_SLL (Z_to_bv 64 v) (Z_to_bv 64 48)) (Z_to_bv 64 51))
    (Z_to_bv 64 8389)) (Z_to_bv 64 20) = Z_to_bv 64 (v / 1000).
Proof.
intros v Hv.
rewrite !zalu64_sound, zmd64_sound, zalu64_sound.
f_equal. unfold zalu64, zmd64, zcanon, M64. cbn [zalu_raw zmd_raw].
change (Z.land (48 mod 2 ^ 64) 63) with 48. change (Z.land (51 mod 2 ^ 64) 63) with 51.
change (Z.land (20 mod 2 ^ 64) 63) with 20. change (8389 mod 2 ^ 64) with 8389.
rewrite (h_zc v) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite !(h_zc (v * 2 ^ 48)) by lia.
rewrite !Z.shiftr_div_pow2 by lia.
replace (v * 2 ^ 48 / 2 ^ 51) with (v / 8)
  by (change (2 ^ 51) with (2 ^ 48 * 8); rewrite <- Z.div_div by lia; rewrite Z.div_mul by lia; reflexivity).
rewrite !(h_zc (v / 8)) by lia.
rewrite !(h_zc (v / 8 * 8389)) by lia.
rewrite (h_recip v Hv).
apply h_zc. lia.
Qed.
Lemma h_add0 : forall w : word, alu64 ALU_ADD w (Z_to_bv 64 0) = w.
Proof.
intros w. rewrite <- (Z_to_bv_bv_unsigned 64 w). rewrite zalu64_sound. f_equal.
unfold zalu64, zcanon, M64. cbn [zalu_raw]. rewrite Z.add_0_r, !Zmod_mod.
pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R.
apply h_zc. lia.
Qed.
Lemma h_vmod : forall v, 0 <= v < 65536 ->
  alu64 ALU_SRL (alu64 ALU_ADD (alu64 ALU_SLL (Z_to_bv 64 v) (Z_to_bv 64 48))
    (mul_div M_MUL (Z_to_bv 64 (v / 1000)) (Z_to_bv 64 5192296858534827347055519618564096)))
    (Z_to_bv 64 48) = Z_to_bv 64 (v mod 1000).
Proof.
intros v Hv.
rewrite zalu64_sound, zmd64_sound, !zalu64_sound.
f_equal. unfold zalu64, zmd64, zcanon, M64. cbn [zalu_raw zmd_raw].
change (Z.land (48 mod 2 ^ 64) 63) with 48.
rewrite (h_zc v) by lia. rewrite (h_zc (v / 1000)) by lia.
rewrite Z.shiftl_mul_pow2 by lia. rewrite !(h_zc (v * 2 ^ 48)) by lia.
change (5192296858534827347055519618564096 mod 2 ^ 64) with (2 ^ 64 - 1000 * 2 ^ 48).
rewrite !Zmod_mod.
replace ((v * 2 ^ 48 + (v / 1000 * (2 ^ 64 - 1000 * 2 ^ 48)) mod 2 ^ 64) mod 2 ^ 64)
  with ((v mod 1000) * 2 ^ 48).
2:{ rewrite Zplus_mod_idemp_r.
    replace (v * 2 ^ 48 + v / 1000 * (2 ^ 64 - 1000 * 2 ^ 48))
      with ((v mod 1000) * 2 ^ 48 + (v / 1000) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. symmetry. apply h_zc.
    pose proof (Z.mod_pos_bound v 1000 ltac:(lia)). lia. }
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
apply h_zc. pose proof (Z.mod_pos_bound v 1000 ltac:(lia)). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---- the symbolic start state at +0x11c4 ------------------------------------------------------ *)
(* Atoms 0..31 are the registers there (x9 = mf, x24 = v, x25 = ef, x23 = the frame's shadow);
   32 = d1, 33 = ef + d1 (the dot), 34 = n2, 35 = ef + n2 (the NUL), 36 = the value of mf + 120,
   37 = ~ef (the complement the UBSan checks of 0x8197c and 0x819bc compare against).
   The regions: the counter slot mf + 208 (written), the frame-pointer slot mf + 64 and the capacity
   slot mf + 120 (read), and the two bytes the block stores itself. The aliases let the engine see
   ef + d1, ef + n2 and ~ef as atoms, which decides the two UBSan checks by their ranges. *)
Definition h_r208 (c : sv) : YP09.region := YP09.mkRegion (Some 9%nat) 208 216 208 216 [YP09.mkChunk 208 (CVal 8 c)].
Definition h_r64 : YP09.region := YP09.mkRegion (Some 9%nat) 64 72 64 64 [YP09.mkChunk 64 (CVal 8 (SOff 25 (-496)))].
Definition h_r120 : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 36 0))].
Definition h_rdot (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 cs.
Definition h_rnul (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 1 cs.
Definition h_r208ro (c : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 208 216 208 208 [YP09.mkChunk 208 (CVal 8 c)].
Definition h_GA : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (24%nat, mkAF 0 65535 0);
    (25%nat, mkAF 4096 (2 ^ 47) 4); (32%nat, mkAF 1 2 0); (33%nat, mkAF 4097 (2 ^ 47) 0);
    (34%nat, mkAF 5 6 0); (35%nat, mkAF 4101 (2 ^ 47) 0); (36%nat, mkAF 0 (2 ^ 64 - 1) 0);
    (37%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0); (38%nat, mkAF 0 65 0) ].
Definition h_GL : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 25 0) (SOff 32 0), SOff 33 0);
    (SAlu ALU_ADD (SOff 32 0) (SOff 25 0), SOff 33 0);
    (SAlu ALU_ADD (SOff 25 0) (SOff 34 0), SOff 35 0);
    (SAlu ALU_ADD (SOff 34 0) (SOff 25 0), SOff 35 0);
    (SAlu ALU_XOR (SOff 25 0) (SLit (-1)), SOff 37 0) ].
Definition h_ss (pc : Z) (rs : YP09.smem) : sstate := mkSS pc sr_atoms rs None (mkFacts h_GA [] h_GL).
Definition h_extra (ef v cd : Z) : list word :=
  map (Z_to_bv 64) [h_d1 v; ef + h_d1 v; h_n2 v; ef + h_n2 v; cd; 2 ^ 64 - 1 - ef; v / 1000].
Definition h_E (regs : bvmap 5 word) (ef v cd : Z) : env := Eimg (Ereg regs (h_extra ef v cd)).

(* ---- the right to write, and the right to read, the two ranges the calls touch -------------- *)
(* the machine-frame counter slot: the caller's own stack window *)
Lemma h_twr_stack : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mf q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= mf -> mf <= q -> q + n <= sp0 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc mf q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mf q n HJ H1 H2 H3 a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) by (left; lia).
destruct (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Hw)
  as [Hp Ho].
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
assert (Hep : ESTACK = 4096) by reflexivity. lia.
Qed.
(* the entry's own side-stack frame: the caller allocated it (own), so it may write its bytes *)
Lemma h_twr_frame : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mf pos SF q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  own = [(4, pos)] -> frame_addr lyc 4 pos = SF -> In (4, pos) (frames Sc) ->
  SF <= q -> q + n <= SF + 1024 -> alloc_ceiling + ESTACK <= mf ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc mf q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k mf pos SF q n
  HJ Hown HSFa Hin4 H1 H2 Hmf a Ha.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
{ right; right; right. exists 4, pos. split; [rewrite Hown; left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite HSFa, HFB. lia. }
destruct (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Hw)
  as [Hp Ho].
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos (proj1 HJ) Hin4) as (Hf0 & Hfc & _).
rewrite HSFa, HFB in Hfc. rewrite HSFa in Hf0.
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho | lia].
Qed.
(* the machine stack's shadow is zero, so any 8-aligned word of it is addressable and its hull visible *)
Lemma h_stk_sh : forall lyc Sc W memc mdc s,
  AR SEGS B lyc Sc W memc mdc ->
  ly_stk_lo lyc <= 8 * (s - SHADOW_OFF) -> 8 * (s - SHADOW_OFF) + 8 <= ly_stk_hi lyc ->
  aview SEGS (w_H W) memc s = Some 0.
Proof.
intros lyc Sc W memc mdc s HAR Hlo Hhi.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow SEGS B LAWS lyc Sc W memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
unfold zero_shadow in Hz. unfold shadow_of_addr in Hz.
specialize (Hz (s - (SHADOW_OFF + ly_stk_lo lyc / 8)) ltac:(clear - Hlo Hhi Hpal Hpah; lia)).
replace (SHADOW_OFF + ly_stk_lo lyc / 8 + (s - (SHADOW_OFF + ly_stk_lo lyc / 8))) with s in Hz by lia.
exact Hz.
Qed.
Lemma h_ra_stack : forall lyc Sc W memc mdc q n,
  AR SEGS B lyc Sc W memc mdc -> ly_stk_lo lyc + 64 <= q -> q + n + 64 <= ly_stk_hi lyc -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q n /\
  shadow_hull_vis (aview SEGS (w_H W) memc) q n.
Proof.
intros lyc Sc W memc mdc q n HAR Hlo Hhi Hn. split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. apply (h_stk_sh lyc Sc W memc mdc _ HAR); clear - Hlo Hhi Hn Hx; lia.
- intros s Hs. unfold shadow_addr in Hs.
  rewrite (h_stk_sh lyc Sc W memc mdc s HAR ltac:(clear - Hlo Hhi Hn Hs; lia)
    ltac:(clear - Hlo Hhi Hn Hs; lia)). discriminate.
Qed.
(* the value of an 8-byte chunk of the engine's state *)
Lemma h_val_of_chunk : forall E m r p a off (e : sv) z,
  YP09.region_ok SEGS E m r -> YP09.r_base r = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  bv_unsigned (ew E p) = a -> sv_denot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  val_mem SEGS m (a + off) 8 z.
Proof.
intros E m r p a off e z HR Hb Hin Hp He Hz.
destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
change 8%nat with (N.to_nat 8).
eapply val_of_chunk_ok; [exact Hc | exact He | cbn; lia | cbn; lia].
Qed.
(* the n-th region of the engine state, as a region_ok fact (lib/B/Prog/reac_identity_reac_ver_str.v's
   rvs_reg, which is local to its Section) *)
Ltac h_reg HS n HR :=
  let HRok := fresh "HRok" in pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HRok & _);
  lazymatch type of HRok with Forall (YP09.region_ok _ ?Ek ?mx) ?rs =>
    let rs' := eval vm_compute in rs in
    let r := eval vm_compute in (nth n rs' got_regionP) in
    assert (HR : YP09.region_ok SEGS Ek mx r)
      by (apply (proj1 (Forall_forall _ _) HRok); change rs with rs'; cbn [In];
          repeat (first [left; reflexivity | right]))
  end; clear HRok.
(* where a byte of the frame's shadow lies: below the allocation ceiling, outside the machine frame
   and outside the frame itself (the frame is app memory, so it is not in the shadow band) *)
Lemma h_geom : forall SF mf q i,
  4096 <= SF -> SF + 1024 <= alloc_ceiling -> in_app SF 1024 ->
  alloc_ceiling + 2 * ESTACK <= mf -> SF <= q -> 0 <= i -> q + 8 * i + 8 <= SF + 1024 ->
  0 <= shadow_of_addr SHADOW_OFF q + i < 2 ^ 64 /\
  ~ (mf - 2 * ESTACK <= shadow_of_addr SHADOW_OFF q + i < mf) /\
  shadow_of_addr SHADOW_OFF q + i < mf /\
  shadow_addr SF <= shadow_of_addr SHADOW_OFF q + i < shadow_addr SF + 128 /\
  (forall x, SF <= x < SF + 1024 -> shadow_of_addr SHADOW_OFF q + i <> x).
Proof.
intros SF mf q i H1 H2 Happ H3 H4 H5 H6.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold shadow_of_addr, shadow_addr, SHADOW_OFF.
split; [clear - H1 H2 H3 H4 H5 H6 C1 Hes; lia|].
split; [clear - H1 H2 H3 H4 H5 H6 C1 Hes; lia|].
split; [clear - H1 H2 H3 H4 H5 H6 C1 Hes; lia|].
split; [clear - H1 H2 H4 H5 H6 C1; lia|].
intros x Hx. clear - H1 H2 H4 H5 H6 Hx Happ C1. lia.
Qed.
(* reading (and writing) the counter slot: the caller's stack window *)
Lemma h_tsrc_stack : forall lyc Sc W memc mdc STK sp0 mf q n,
  AR SEGS B lyc Sc W memc mdc ->
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a) ->
  alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  ly_stk_lo lyc + 64 <= q -> q + n + 64 <= ly_stk_hi lyc ->
  sp0 - STK <= q -> q + n <= sp0 -> mf <= q -> 0 <= n ->
  tsrc_ok W memc mf q n.
Proof.
intros lyc Sc W memc mdc STK sp0 mf q n HAR Hpres Hclo Hchi Hlo Hhi H1 H2 H3 Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hep : ESTACK = 4096) by reflexivity.
destruct (h_ra_stack lyc Sc W memc mdc q n HAR Hlo Hhi Hn) as [HRA HHU].
split.
{ intros a Ha. split; [apply aview_some_of_apresent; apply Hpres; lia | lia]. }
split; [exact HRA|]. split; [exact HHU|].
split; [unfold amem_range, kHighMemBeg, kHighMemEnd, kLowMemEnd; right; split; lia|].
split; lia.
Qed.
(* reading (and writing) bytes of `ef` (SF + 496, 16 bytes) in the entry's own frame *)
Lemma h_tsrc_frame : forall lyc Sc W memc mdc pos SF mf q n,
  AR SEGS B lyc Sc W memc mdc -> In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SF ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 496) 16 ->
  SF + 496 <= q -> q + n <= SF + 512 -> 0 < n -> alloc_ceiling + ESTACK <= mf ->
  tsrc_ok W memc mf q n.
Proof.
intros lyc Sc W memc mdc pos SF mf q n HAR Hin4 HSFa Zef H1 H2 Hn Hmf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hep : ESTACK = 4096) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (al_frames SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & Happf & HBY & _).
rewrite HSFa, HFB in HSF1, HSFapp, Happf. rewrite HSFa in HSF0, HBY. rewrite HFB in HBY.
assert (HSF8 : (SF + 496) mod 8 = 0).
{ destruct (frame_al64 SEGS B lyc Sc W memc mdc 4 pos HAR Hin4) as (Hal & _ & _).
  rewrite HSFa in Hal. lia. }
split.
{ intros a Ha. split; [apply aview_some_of_apresent; exact (proj1 (HBY a ltac:(lia))) | lia]. }
split.
{ apply (range_addressable_sub (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 496) 16 q n);
  [apply zero_shadow_range; [exact HSF8 | reflexivity | exact Zef] | lia | lia]. }
split.
{ apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memc mdc 4 pos q n HAR Hin4);
  [rewrite HSFa; lia | rewrite HSFa, HFB; lia | exact Hn]. }
split.
{ apply (amem_range_sub_app SF 1024 q n Happf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
split; lia.
Qed.

(* Set register r to the symbolic value e when the machine's register holds e's value
   (lib/B/Prog/reac_identity_reac_ver_str.v's rvs_pin, for any value, not only an atom). *)
Lemma h_pin : forall E ss ms (r : bv 5) (e : sv),
  st_ok_pi SEGS VAL E ss ms -> getr (ms_regs ms) r = sv_denot E e -> bv_eqb r 0 = false ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
  rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
(* the entry's frame is client memory, so no byte of it is in the image *)
Lemma h_frame_not_img : forall lyc Sc W memc mdc pos a,
  AR SEGS B lyc Sc W memc mdc -> In (4, pos) (frames Sc) ->
  frame_addr lyc 4 pos <= a < frame_addr lyc 4 pos + fs_frame_bytes 4 -> ~ in_img SEGS a.
Proof.
intros lyc Sc W memc mdc pos a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR
  (or_intror (or_introl (ex_intro _ 4 (ex_intro _ pos (conj Hin Ha))))))).
Qed.
(* bytes of the frame that a piece did not write are the bytes it found *)
Lemma h_garr8_keep : forall lyc Sc W1 m1 W2 m2 lo hi (E : Z -> Prop) pos a l,
  rvs_k B lyc Sc W1 m1 W2 m2 lo hi E -> In (4, pos) (frames Sc) ->
  frame_addr lyc 4 pos <= a -> a + Z.of_nat (length l) <= frame_addr lyc 4 pos + 1024 ->
  (forall x, a <= x < a + Z.of_nat (length l) -> ~ E x) ->
  garr8 SEGS (mrestrict (w_H W1) m1) a l -> garr8 SEGS (mrestrict (w_H W2) m2) a l.
Proof.
intros lyc Sc W1 m1 W2 m2 lo hi E pos a l HK Hin H1 H2 HE HG.
apply (garr8_frame SEGS _ _ _ _ HG). intros x Hx. apply (mbyte_of_aview SEGS).
destruct HK as (_ & _ & _ & A4 & _).
apply (A4 4 pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd];
  change (fs_frame_bytes 4) with 1024; lia | exact (HE x Hx)].
Qed.
(* the frame's shadow bytes a piece did not write are the bytes it found *)
Lemma h_zsh_keep : forall lyc Sc W1 m1 W2 m2 lo hi (E : Z -> Prop) pos q n,
  rvs_k B lyc Sc W1 m1 W2 m2 lo hi E -> In (4, pos) (frames Sc) ->
  frame_addr lyc 4 pos <= q -> q + n <= frame_addr lyc 4 pos + 1024 -> q mod 8 = 0 ->
  frame_addr lyc 4 pos mod 8 = 0 ->
  (forall x, shadow_addr (frame_addr lyc 4 pos) <= x < shadow_addr (frame_addr lyc 4 pos) + 128 -> ~ E x) ->
  zero_shadow (aview SEGS (w_H W1) m1) SHADOW_OFF q n ->
  zero_shadow (aview SEGS (w_H W2) m2) SHADOW_OFF q n.
Proof.
intros lyc Sc W1 m1 W2 m2 lo hi E pos q n HK Hin H1 H2 Hq8 Hf8 HE HZ i Hi.
destruct HK as (_ & _ & _ & A4 & _).
assert (Hr : shadow_addr (frame_addr lyc 4 pos) <= shadow_of_addr SHADOW_OFF q + i
             < shadow_addr (frame_addr lyc 4 pos) + 128).
{ clear - H1 H2 Hq8 Hf8 Hi. unfold shadow_addr, shadow_of_addr, SHADOW_OFF. lia. }
rewrite (A4 4 pos _ Hin); [exact (HZ i Hi) | right; unfold in_zr; cbn [fst snd];
  change (fs_frame_bytes 4 / 8) with 128; exact Hr | exact (HE _ Hr)].
Qed.
(* a call that changed nothing outside [lo, hi) and lost no byte kept what rvs_k says *)
Lemma h_k_of_keep : forall lyc Sc W memc mdc m1 m2 lo hi,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a) ->
  rvs_k B lyc Sc W m1 W m2 lo hi (fun _ => False).
Proof.
intros lyc Sc W memc mdc m1 m2 lo hi HAR Hlo Hhi KV KP.
pose proof asan_consts as (C1 & _).
split; [intros a Ha Hw He; apply KV; [lia | exact Hw]|].
split.
{ intros b m i Hin Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hcl & _).
  apply KV; lia. }
split.
{ intros a Hi Hns Herr. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. apply KV; lia. }
split.
{ intros cid pos a Hin Hr He.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf0 & _ & _).
  destruct (frame_zone SEGS B LAWS _ _ _ _ _ cid pos a HAR Hin Hr) as (Hza & [(Hz1 & _) | Hz2]);
  (apply KV; [unfold kLowMemEnd in *; lia | lia]). }
intros a Ha Hw Hp. exact (KP a Hp).
Qed.
(* What the block writes: the expected string in ef with its NUL, the formatter's output in f = ef - 32,
   and the counter slot. *)
Definition h_wrote (ef mf v : Z) (a : Z) : Prop :=
  ef <= a < ef + h_n2 v + 1 \/ ef - 32 <= a < ef - 32 + h_n2 v + 1 \/ mf + 208 <= a < mf + 216.
Definition h_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (mf ef v cd : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = cfg_at SEGS (BASE + 0x128c) regs2 mem2 md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
  frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     getr regs2 r = getr regs r) /\
  getr regs2 22 = w64 cd /\
  garr8 SEGS (mrestrict (w_H W2) mem2) ef
    (map (fun b : byte => bv_unsigned b)
       (IdentSpec.DEC (v / 1000) 1 ++ [SlotModel.dot] ++ IdentSpec.DEC (v mod 1000) 3)) /\
  rvs_k B lyc Sc W memc W2 mem2 (mf - 2 * ESTACK) mf (h_wrote ef mf v).

Lemma h_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  pos mf SF v cd,
  LLVMFuzzerTestOneInput_seg_H_hand2_stmt.h_pd_call_stmt B ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  frames Sc = [(4, pos)] -> own = [(4, pos)] -> frame_addr lyc 4 pos = SF ->
  st_nev S + k <= EV_MAX ->
  getr regs 2 = w64 mf -> getr regs 9 = w64 mf ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  mf mod 32 = 0 -> sp0 - 336 <= mf -> mf <= sp0 - 320 -> sp0 - STK <= mf - 2 * ESTACK ->
  getr regs 24 = w64 v -> 0 <= v < 65536 -> getr regs 25 = w64 (SF + 496) ->
  val_mem SEGS (mrestrict (w_H W) memc) (mf + 208) 8 0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (mf + 64) 8 SF ->
  val_mem SEGS (mrestrict (w_H W) memc) (mf + 120) 8 cd -> 0 <= cd < 2 ^ 64 ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 464) 8 ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 496) 16 ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x11c4) regs memc mdc)
    (h_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs mf (SF + 496) v cd).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pos mf SF v cd
  HPDC HJ Hfrs0 Hown HSFa Hnev0 R2 R9 R3 R4 Hmf32 Hmflo Hmfhi HSTKw R24 Hv R25
  V208 V64 V120 Hcd Zf Zef.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs0; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B lyc Sc W memc mdc 4 pos HAR Hin4) as (HSF64 & _ & _).
rewrite HSFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Hmf0 : alloc_ceiling + 2 * ESTACK <= mf) by (clear - Hceil Hslo HSTKw; lia).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
assert (Hclo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Elo; exact Hceil).
assert (Hslo' : ly_stk_lo lyc + STK <= sp0) by (rewrite Elo; exact Hslo).
assert (Hshi' : sp0 <= ly_stk_hi lyc) by (rewrite Ehi; exact Hshi).
assert (Hchi' : ly_stk_hi lyc <= 2 ^ 47) by (rewrite Ehi; exact H47).
pose proof (h_d1_range v Hv) as Hd1.
assert (Hn2 : h_n2 v = h_d1 v + 4) by reflexivity.
assert (Hd1' : 1 <= dec_len (v / 1000) 1 <= 2) by (unfold h_d1 in Hd1; exact Hd1).
(* the environment *)
remember (h_E regs (SF + 496) v cd) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (h_extra (SF + 496) v cd)) n)
  by (intros n Hn; rewrite HE; apply Eimg_low; exact Hn).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite EL by (pose proof (bv_unsigned_in_range 5 r);
        change (bv_modulus 5) with 32 in *; unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (h_d1 v)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SF + 496 + h_d1 v)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (h_n2 v)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (SF + 496 + h_n2 v)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 cd) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (2 ^ 64 - 1 - (SF + 496)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (v / 1000))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (AGE : env_agree 32 (Ereg regs (h_extra (SF + 496) v cd)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small;
      clear - Hmf0 Hmfhi Hshi H47 C1 Hes; lia).
assert (U25 : bv_unsigned (ew E 25) = SF + 496)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (U33 : bv_unsigned (ew E 33) = SF + 496 + h_d1 v)
  by (rewrite E33; apply unsigned_lit_small; clear - HSF0 HSF1 C1 Hd1; lia).
assert (U35 : bv_unsigned (ew E 35) = SF + 496 + h_n2 v)
  by (rewrite E35; apply unsigned_lit_small; clear - HSF0 HSF1 C1 Hd1 Hn2; lia).
assert (U32 : bv_unsigned (ew E 32) = h_d1 v)
  by (rewrite E32; apply unsigned_lit_small; clear - Hd1; lia).
assert (U34 : bv_unsigned (ew E 34) = h_n2 v)
  by (rewrite E34; apply unsigned_lit_small; clear - Hd1 Hn2; lia).
clear HE.
assert (U36 : bv_unsigned (ew E 36) = cd) by (rewrite E36; apply unsigned_lit_small; clear - Hcd; lia).
assert (U37 : bv_unsigned (ew E 37) = 2 ^ 64 - 1 - (SF + 496))
  by (rewrite E37; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (U38 : bv_unsigned (ew E 38) = v / 1000)
  by (rewrite E38; apply unsigned_lit_small; clear - Hv; lia).
assert (U24 : bv_unsigned (ew E 24) = v)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; clear - Hv; lia).
assert (U2 : bv_unsigned (ew E 2) = mf)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small;
      clear - Hmf0 Hmfhi Hshi H47 C1 Hes; lia).
(* the frame's bytes are present and are the client's *)
destruct (al_frames SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hal32 & Happf & HBY & _).
rewrite HSFa in Happf, HBY. rewrite HFB in Happf, HBY.
(* the start state *)
assert (HS : st_ok_pi SEGS VAL E (h_ss 0x11c4 [h_r208ro (SLit 0); h_r64; h_r120])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x11c4)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold h_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold YP09.region_ok, h_r208ro, h_r64, h_r120;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [clear - Hmf0 C1 Hes; lia|]. split; [clear - Hmfhi Hshi H47; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 208 8 (SLit 0) 0);
      [cbn [sv_denot]; reflexivity | clear; lia | clear; lia | exact V208].
    + rewrite U9. split; [clear - Hmf0 C1 Hes; lia|]. split; [clear - Hmfhi Hshi H47; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 64 8 (SOff 25 (-496)) SF);
      [cbn [sv_denot]; rewrite U25; replace (SF + 496 + -496) with SF by (clear; lia); reflexivity
      | clear - HSF0 HSF1 C1; lia | clear; lia | exact V64].
    + rewrite U9. split; [clear - Hmf0 C1 Hes; lia|]. split; [clear - Hmfhi Hshi H47; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 120 8 (SOff 36 0) cd);
      [cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity | clear - Hcd; lia | clear; lia | exact V120].
  - apply pairwise_disjoint_of_extents.
    unfold h_r208ro, h_r64, h_r120, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hmf0 HSF0 HSF1 C1 Hd1 Hn2 Hes. clear. intros. repeat split; try exact I; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias h_GA h_GL atoms_ok conds_ok alias_ok].
    split; [|split].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U2, U9, U24, U25, U32, U33, U34, U35, U36, U37, U38.
      change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      assert (Hef16 : (SF + 496) mod 16 = 0) by (clear - HSF64; lia).
      revert Hmf0 Hmfhi Hshi H47 C1 Hes Hmf32 HSF0 HSF1 Hd1 Hn2 Hv Hcd Hef16. clear.
      intros. repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | clear - Hv; lia].
    + exact I.
    + cbn [alias_ok]. unfold alias_ok.
      assert (Hm1 : (-1) mod 2 ^ 64 = 2 ^ 64 - 1)
        by (symmetry; apply (Zmod_unique (-1) (2 ^ 64) (-1) (2 ^ 64 - 1)); lia).
      assert (Mk : forall a, 0 <= a < 2 ^ 64 -> a mod 2 ^ 64 = a) by (intros; apply Z.mod_small; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I.
      all: apply U_inj; rewrite U_SAlu, ?U_SOff, ?U_SLit; cbn [zalu_raw]; unfold zcanon, M64;
           rewrite ?U25, ?U32, ?U33, ?U34, ?U35, ?U37, ?Hm1, ?Z.add_0_r.
      all: first
        [ rewrite <- Z.add_mod by (clear; lia); first [reflexivity | f_equal; clear - Hd1 Hn2; lia]
        | rewrite (Mk (SF + 496)) by (clear - HSF0 HSF1 C1; lia);
          rewrite (h_xor_m1 (SF + 496)) by (clear - HSF0 HSF1 C1; lia); reflexivity ]. }
(* ---- run 1: 0x81938 .. the first put_dec call (0x81960) ---- *)
unfold cfg_at. change (w64 (BASE + 0x11c4)) with (Z_to_bv 64 (BASE + 0x11c4)).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + 0x11c4)) memc (seg_rom SEGS))) in HJ.
paj_run_shc RUNP RUNC HS HJ.
{ unfold h_ss, h_r208ro, h_r64, h_r120. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_nil. }
(* run 1 wrote nothing: the memory at the call is the one the segment started in *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha.
  apply (kept_of_frame E [h_r208ro (SLit 0); h_r64; h_r120] (w_H W) memc (ms_mem ms)
           (fun _ => False) HFr); [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold h_r208ro, h_r64, h_r120, windows in Hin.
  cbn [map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr; clear - Hr; lia. }
assert (VM1 : forall a (n : nat) z, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W memc) a n z -> val_mem SEGS (rd W (ms_mem ms)) a n z).
{ intros a n z H1 H2 Hv'. apply (val_mem_moved SEGS (w_H W) (w_H W) memc (ms_mem ms) a a n z); [|exact Hv'].
  intros kk Hkk. apply KEEP1. clear - H1 H2 Hkk. lia. }
assert (VMP : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a).
{ intros a (Hh & b & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
  rewrite Hh, Hb in HG. destruct (ms_mem ms (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity]. }
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresR & _).
(* ---- call 1: put_dec (ef, mf + 208, v / 1000, 1) at 0x81960 ---- *)
pmkst HS.
rewrite (PSIG IB_put_dec AF_put_dec eq_refl).
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3. prreg HS (18%bv : bv 5) Rs2.
assert (Ev24 : ew E 24 = Z_to_bv 64 v) by (rewrite <- U24; symmetry; apply Z_to_bv_bv_unsigned).
rewrite (EE 25%nat 25%bv eq_refl), R25 in Ra0. rewrite U9 in Ra1.
rewrite Ev24, h_add0, (h_v1000 v Hv) in Ra2. rewrite Ev24, (h_v1000 v Hv) in Rs2.
rewrite (EE 3%nat 3%bv eq_refl), R3 in Rgp. rewrite (EE 4%nat 4%bv eq_refl), R4 in Rtp.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp; exact U2).
assert (Hv1k : 0 <= v / 1000 < 66) by (clear - Hv; lia).
assert (Esp2 : getr (ms_regs ms) 2 = w64 mf)
  by (rewrite Rsp, <- U2; unfold w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Zef' : zero_shadow (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (SF + 496) 16).
{ intros i Hi. rewrite KEEP1 by (clear - HSF0 HSF1 C1 Hi; unfold shadow_of_addr, SHADOW_OFF; lia).
  exact (Zef i Hi). }
assert (Zf' : zero_shadow (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (SF + 464) 8).
{ intros i Hi. rewrite KEEP1 by (clear - HSF0 HSF1 C1 Hi; unfold shadow_of_addr, SHADOW_OFF; lia).
  exact (Zf i Hi). }
eapply SRr_bind.
{ apply (HPDC LAWS HPD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms)
    (with_vm_backing (m_vm_lazy mdc) mat mdc) k (ms_regs ms) pos mf SF 0 (v / 1000) 1
    HJ Hfrs0 Hown HSFa Hnev0).
  - rewrite Rra. apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - unfold raZ. rewrite Rra, unsigned_lit_small by (clear - HBASE; lia). clear - HBLO; lia.
  - exact Esp2.
  - exact Rgp.
  - exact Rtp.
  - exact Ra0.
  - exact Ra1.
  - rewrite Ra2. unfold w64. apply unsigned_lit_small. clear - Hv1k; lia.
  - exact Ra3.
  - clear - Hv1k; lia.
  - clear; lia.
  - exact Hmf32.
  - exact Hmflo.
  - exact Hmfhi.
  - exact HSTKw.
  - exact Hclo.
  - exact Hchi'.
  - exact Hslo'.
  - exact Hshi'.
  - clear; lia.
  - rewrite Z.add_0_l. clear - Hd1'; lia.
  - apply VM1; [clear - Hmf0 C1 Hes; lia | clear - Hmfhi Hshi H47; lia | exact V208].
  - exact Zef'.
  - exact HpresR. }
cbv beta.
intros W2 c2 _ (lyA & SA & regsA & memA & mdA & -> & HJA & HPA & HfrA & HblA & HtcjA & HgarA & HvalA).
rewrite Rra.
unfold put_dec.EV_PUT_DEC in HJA. rewrite Z.add_0_r in HJA.
rewrite Z.add_0_r in HgarA. rewrite Z.add_0_l in HvalA.
pose proof (proj1 HJA) as HARA.
assert (Hin4A : In (4, pos) (frames SA)) by (rewrite HfrA; exact Hin4).
destruct (rvs_journal_move B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms)
  (with_vm_backing (m_vm_lazy mdc) mat mdc) k lyA SA W2 memA mdA k HJ HJA) as (HfrA2 & HfaA).
assert (HSFaA : frame_addr lyA 4 pos = SF) by (rewrite HfaA; exact HSFa).
destruct (al_frames SEGS B LAWS lyA SA W2 memA mdA 4 pos HARA Hin4A) as (_ & HappfA & HBYA & _).
rewrite HSFaA in HappfA, HBYA. rewrite HFB in HappfA, HBYA.
pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresA & _).
(* the engine state after the call: the two read-only machine-frame slots are kept *)
jafter_call_keep_pi HS 48%nat regsA (mrestrict (w_H W2) memA) HPA [1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U9.
    + intros a Ha. apply (mbyte_of_aview SEGS). destruct HtcjA as (T1 & _). apply T1.
      * clear - Ha Hmf0 Hmfhi Hshi H47 C1 Hes. lia.
      * rewrite Qsp. unfold put_dec.PUT_DEC_STK. clear - Ha Hes. lia.
      * cbv beta. clear - Ha HSF1 C1 Hmf0 Hes Hd1'. lia.
    + intros a Ha. exfalso. clear - Ha. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U9.
    + intros a Ha. apply (mbyte_of_aview SEGS). destruct HtcjA as (T1 & _). apply T1.
      * clear - Ha Hmf0 Hmfhi Hshi H47 C1 Hes. lia.
      * rewrite Qsp. unfold put_dec.PUT_DEC_STK. clear - Ha Hes. lia.
      * cbv beta. clear - Ha HSF1 C1 Hmf0 Hes Hd1'. lia.
    + intros a Ha. exfalso. clear - Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof (img_env_havoc E 48%nat (map (getr regsA) CLOB) HEI ltac:(cbv; lia)) as HEIA.
(* the counter slot holds d1 now; the engine also needs the byte it stores at ef + d1 *)
assert (EH9 : bv_unsigned (ew (havoc E 48%nat (map (getr regsA) CLOB)) 9) = mf)
  by (rewrite ew_havoc_old by (cbv; lia); exact U9).
assert (EH32 : ew (havoc E 48%nat (map (getr regsA) CLOB)) 32 = Z_to_bv 64 (dec_len (v / 1000) 1))
  by (rewrite ew_havoc_old by (cbv; lia); unfold h_d1 in E32; exact E32).
assert (EH33 : bv_unsigned (ew (havoc E 48%nat (map (getr regsA) CLOB)) 33)
               = SF + 496 + dec_len (v / 1000) 1)
  by (rewrite ew_havoc_old by (cbv; lia); unfold h_d1 in U33; exact U33).
assert (ROK208 : YP09.region_ok SEGS (havoc E 48%nat (map (getr regsA) CLOB))
  (mrestrict (w_H W2) memA) (h_r208 (SOff 32 0))).
{ unfold YP09.region_ok, h_r208.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EH9. split; [clear - Hmf0 C1 Hes; lia|]. split; [clear - Hmfhi Hshi H47; lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply HpresA;
          clear - Ho Hmfhi HSTKw Hes; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ mf 208 8 (SOff 32 0) (dec_len (v / 1000) 1));
  [cbn [sv_denot]; rewrite EH32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | clear - Hd1'; lia | clear; lia | exact HvalA]. }
assert (ROKdot : YP09.region_ok SEGS (havoc E 48%nat (map (getr regsA) CLOB))
  (mrestrict (w_H W2) memA) (h_rdot [])).
{ unfold YP09.region_ok, h_rdot.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite EH33. split; [clear - HSF0 Hd1'; lia|]. split; [clear - HSF1 C1 Hd1'; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  exact (proj1 (HBYA (SF + 496 + dec_len (v / 1000) 1 + o) ltac:(clear - Ho Hd1'; lia))). }
pose proof (st_ok_pi_add_region _ _ _ (h_r208 (SOff 32 0)) HS ltac:(vm_compute; reflexivity) ROK208
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, h_r208;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite EH9;
        repeat split; try exact I; clear; lia)) as HS3.
clear HS. rename HS3 into HS.
pose proof (st_ok_pi_add_region _ _ _ (h_rdot []) HS ltac:(vm_compute; reflexivity) ROKdot
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, h_rdot, h_r208;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite EH9, EH33;
        repeat split; try exact I; clear - Hmf0 HSF0 HSF1 C1 Hd1' Hes; lia)) as HS3.
clear HS. rename HS3 into HS.
(* what the segment has kept so far: run 1 wrote nothing, call 1 wrote the counter and ef[0, d1) *)
assert (K1 : rvs_k B lyc Sc W memc W (ms_mem ms) (mf - 2 * ESTACK) mf (fun _ => False)).
{ apply (rvs_k_of_run B LAWS lyc Sc W memc mdc memc (ms_mem ms) (mf - 2 * ESTACK) mf (fun _ => False));
  [exact HAR | clear - Hmf0 Hes; lia | clear - Hmfhi Hshi H47 C1; lia | intros a _ []
  | intros a Ha _ _; apply KEEP1; exact Ha | exact HG]. }
assert (KA : rvs_k B lyc Sc W (ms_mem ms) W2 memA (mf - 2 * ESTACK) mf
  (fun a => mf + 208 <= a < mf + 208 + 8 \/ SF + 496 + 0 <= a < SF + 496 + 0 + dec_len (v / 1000) 1)).
{ pose proof (rvs_k_of_tcj B put_dec.PUT_DEC_STK lyc Sc W (ms_mem ms) W2 memA (spZ (ms_regs ms)) _ HtcjA) as X.
  rewrite Qsp in X. eapply rvs_k_mono;
  [exact X | unfold put_dec.PUT_DEC_STK; clear - Hes; lia | clear; lia | intros a Ha; exact Ha]. }
pose proof (rvs_k_trans B lyc Sc W memc W (ms_mem ms) W2 memA (mf - 2 * ESTACK) mf _ _ K1 KA) as KK1.
(* ---- run 2: 0x81964 .. the second put_dec call (0x819ac) ---- *)
(* x18 keeps v / 1000 across the call (callee-saved); pin it to its atom so the engine's `subw`
   stays an atom expression. *)
prreg HS (18%bv : bv 5) Ps2.
rewrite Ev24, (h_v1000 v Hv) in Ps2.
pose proof (rvs_pin _ _ _ (18%bv : bv 5) 38%nat HS
  ltac:(cbn [ms_regs restrict mkst]; rewrite Ps2; cbn [sv_denot];
        rewrite ew_havoc_old by (cbv; lia); rewrite E38;
        rewrite unsigned_lit_small by (clear - Hv; lia); rewrite Z.add_0_r; reflexivity)
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
clear KEEP1 VM1 VMP Zef' Zf' HpresR Rra Rsp Rgp Rtp Ra0 Ra1 Ra2 Ra3 Rs2 Esp2 Qsp K1 KA.
assert (HfrsA : frames SA = [(4, pos)]) by (rewrite HfrA; exact Hfrs0).
paj_run_shc RUNP RUNC HS HJA.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (SF + 496 + dec_len (v / 1000) 1));
  [ reflexivity | exact EH33
  | cbn [YP09.r_wlo YP09.r_whi h_rdot]; intros a Ha; right; right; right; exists 4, pos;
    split; [rewrite Hown; left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; rewrite HSFaA, HFB; clear - Ha Hd1'; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
  [ reflexivity | cbn [YP09.r_base h_r208]; rewrite EH9; clear; lia
  | cbn [YP09.r_wlo h_r208]; clear - HSTKw Hes; lia
  | cbn [YP09.r_whi h_r208]; clear - Hmfhi; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_nil. }
(* ---- call 2: put_dec (ef, mf + 208, v mod 1000, 3) at 0x819ac ---- *)
(* the counter slot holds d1 + 1 (the store at 0x81970), which the engine's region records *)
h_reg HS 1%nat HR208.
cbn [ms_mem restrict] in HR208.
assert (V208b : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (mf + 208) 8
                  (dec_len (v / 1000) 1 + 1)).
{ apply (h_val_of_chunk _ _ _ 9%nat mf 208 (SOff 32 1) (dec_len (v / 1000) 1 + 1) HR208);
  [ reflexivity | cbn [In]; left; reflexivity
  | cbn [YP09.r_base base_val]; exact EH9
  | cbn [sv_denot]; rewrite EH32, unsigned_lit_small by (clear - Hd1'; lia); reflexivity
  | clear - Hd1'; lia ]. }
(* what run 2 kept: everything outside the counter slot and the dot byte *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (mf + 208 <= a < mf + 216) -> a <> SF + 496 + dec_len (v / 1000) 1 ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) memA a).
{ intros a Ha Hw1 Hw2.
  apply (kept_of_frame _ _ (w_H W2) memA (ms_mem ms0)
    (fun x => (mf + 208 <= x < mf + 216) \/ x = SF + 496 + dec_len (v / 1000) 1) HFr0);
  [| exact Ha | clear - Hw1 Hw2; tauto].
  intros bb wlo whi aa Hin Hr.
  cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi h_rdot h_r208 h_r64 h_r120] in Hin.
  destruct Hin as [Eq | [Eq | [Eq | [Eq | []]]]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [ rewrite EH33 in Hr; right; clear - Hr; lia
  | rewrite EH9 in Hr; left; clear - Hr; lia
  | rewrite EH9 in Hr; exfalso; clear - Hr; lia
  | rewrite EH9 in Hr; exfalso; clear - Hr; lia ]. }
(* ef's and f's shadow are still clear: call 1 kept the frame's shadow, run 2 wrote only bytes *)
assert (ZSH : forall q i, SF <= q -> 0 <= i -> q + 8 * i + 8 <= SF + 1024 ->
  aview SEGS (w_H W2) (ms_mem ms0) (shadow_of_addr SHADOW_OFF q + i)
  = aview SEGS (w_H W) memc (shadow_of_addr SHADOW_OFF q + i)).
{ intros q i Hq1 Hi0 Hq2.
  destruct (h_geom SF mf q i HSF0 HSF1 Happf Hmf0 Hq1 Hi0 Hq2) as (G1 & G2 & G3 & G4 & G5).
  rewrite KEEP2;
  [ | exact G1 | clear - G3; lia | exact (G5 (SF + 496 + dec_len (v / 1000) 1) ltac:(clear - Hd1'; lia)) ].
  destruct KK1 as (_ & _ & _ & A4 & _).
  apply (A4 4 pos (shadow_of_addr SHADOW_OFF q + i) Hin4).
  - right. unfold in_zr. cbn [fst snd]. rewrite HSFa, HFB. change (1024 / 8) with 128. exact G4.
  - cbv beta. intros [[] | [HA | HA]];
    [ clear - HA G3; lia
    | exact (G5 (shadow_of_addr SHADOW_OFF q + i) ltac:(clear - HA Hd1'; lia) eq_refl) ]. }
assert (Zef2 : zero_shadow (aview SEGS (w_H W2) (ms_mem ms0)) SHADOW_OFF (SF + 496) 16).
{ intros i Hi. rewrite (ZSH (SF + 496) i ltac:(clear; lia) ltac:(clear - Hi; lia) ltac:(clear - Hi; lia)).
  exact (Zef i Hi). }
assert (Zf2 : zero_shadow (aview SEGS (w_H W2) (ms_mem ms0)) SHADOW_OFF (SF + 464) 8).
{ intros i Hi. rewrite (ZSH (SF + 464) i ltac:(clear; lia) ltac:(clear - Hi; lia) ltac:(clear - Hi; lia)).
  exact (Zf i Hi). }
(* what run 2 left in ef: the first piece (call 1) and the dot *)
h_reg HS 0%nat HRdot.
cbn [ms_mem restrict] in HRdot.
assert (GDOT : garr8 SEGS (rd W2 (ms_mem ms0)) (SF + 496 + dec_len (v / 1000) 1 + 0) [46]).
{ eapply rvs_byte_reg; [exact HRdot | cbn [base_val]; exact EH33 | cbn [sv_denot]; reflexivity]. }
rewrite Z.add_0_r in GDOT.
assert (GDEC1 : garr8 SEGS (rd W2 (ms_mem ms0)) (SF + 496) (map bv_unsigned (IdentSpec.DEC (v / 1000) 1))).
{ apply (garr8_frame SEGS _ _ _ _ HgarA). intros x Hx. rewrite length_map in Hx.
  apply (mbyte_of_aview SEGS). unfold dec_len in Hd1'.
  apply KEEP2; clear - Hx HSF0 HSF1 C1 Hd1' Hmf0 Hes; unfold dec_len; lia. }
pose proof HJA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresB & _).
pose proof HJA as (_ & HlyA & _).
pose proof HlyA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EloA & EhiA & _).
assert (HcloA : alloc_ceiling <= ly_stk_lo lyA) by (rewrite EloA; exact Hceil).
assert (HchiA : ly_stk_hi lyA <= 2 ^ 47) by (rewrite EhiA; exact H47).
assert (HsloA : ly_stk_lo lyA + STK <= sp0) by (rewrite EloA; exact Hslo).
assert (HshiA : sp0 <= ly_stk_hi lyA) by (rewrite EhiA; exact Hshi).
pmkst HS.
rewrite (PSIG IB_put_dec AF_put_dec eq_refl).
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp2. prreg HS (3%bv : bv 5) Qgp.
prreg HS (4%bv : bv 5) Qtp. prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1.
prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3.
assert (Ev24' : ew (havoc E 48%nat (map (getr regsA) CLOB)) 24 = Z_to_bv 64 v)
  by (rewrite ew_havoc_old by (cbv; lia); exact Ev24).
assert (E38' : ew (havoc E 48%nat (map (getr regsA) CLOB)) 38 = Z_to_bv 64 (v / 1000))
  by (rewrite ew_havoc_old by (cbv; lia); exact E38).
rewrite Ev24, E38, (h_vmod v Hv) in Qa2.
assert (Qef : getr (ms_regs ms0) 10 = w64 (SF + 496)).
{ rewrite Qa0, (EE 25%nat 25%bv eq_refl). exact R25. }
assert (Qp : getr (ms_regs ms0) 11 = w64 (mf + 208)) by (rewrite Qa1, U9; reflexivity).
assert (Qsp' : getr (ms_regs ms0) 2 = w64 mf).
{ rewrite Qsp2, (EE 2%nat 2%bv eq_refl). exact R2. }
assert (Qgp' : getr (ms_regs ms0) 3 = w64 (as_gp B)).
{ rewrite Qgp; try rewrite (EE 3%nat 3%bv eq_refl); exact R3. }
assert (Qtp' : getr (ms_regs ms0) 4 = w64 (as_tp B)).
{ rewrite Qtp; try rewrite (EE 4%nat 4%bv eq_refl); exact R4. }
pose proof (Z.mod_pos_bound v 1000 ltac:(clear; lia)) as Hvm.
lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => set (MDX := md) end.
eapply SRr_bind.
{ apply (HPDC LAWS HPD STK sp0 FP ly S W0 mem0 md0 own lyA SA W2 (ms_mem ms0) MDX
    k (ms_regs ms0) pos mf SF (dec_len (v / 1000) 1 + 1) (v mod 1000) 3
    HJA HfrsA Hown HSFaA Hnev0).
  - rewrite Qra. apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - unfold raZ. rewrite Qra, unsigned_lit_small by (clear - HBASE; lia). clear - HBLO; lia.
  - exact Qsp'.
  - exact Qgp'.
  - exact Qtp'.
  - exact Qef.
  - exact Qp.
  - rewrite Qa2. unfold w64. apply unsigned_lit_small. clear - Hvm; lia.
  - exact Qa3.
  - clear - Hvm; lia.
  - clear; lia.
  - exact Hmf32.
  - exact Hmflo.
  - exact Hmfhi.
  - exact HSTKw.
  - exact HcloA.
  - exact HchiA.
  - exact HsloA.
  - exact HshiA.
  - clear - Hd1'; lia.
  - rewrite (h_dec3_len (v mod 1000) ltac:(clear - Hvm; lia)). clear - Hd1'; lia.
  - exact V208b.
  - exact Zef2.
  - exact HpresB. }
intros W3 c3 _ (lyB & SB & regsB & memB & mdB & -> & HJB & HPB & HfrB & HblB & HtcjB & HgarB & HvalB).
rewrite Qra.
assert (H3l : dec_len (v mod 1000) 3 = 3) by (apply h_dec3_len; clear - Hvm; lia).
unfold put_dec.EV_PUT_DEC in HJB. rewrite Z.add_0_r in HJB.
pose proof (proj1 HJB) as HARB.
assert (HfrsB : frames SB = [(4, pos)]) by (rewrite HfrB; exact HfrsA).
assert (Hin4B : In (4, pos) (frames SB)) by (rewrite HfrsB; left; reflexivity).
destruct (rvs_journal_move B STK sp0 FP ly S W0 mem0 md0 own lyA SA W2 (ms_mem ms0) _ k
  lyB SB W3 memB mdB k HJA HJB) as (HfrB2 & HfaB).
assert (HSFaB : frame_addr lyB 4 pos = SF) by (rewrite HfaB; exact HSFaA).
destruct (al_frames SEGS B LAWS lyB SB W3 memB mdB 4 pos HARB Hin4B) as (_ & HappfB & HBYB & _).
rewrite HSFaB in HappfB, HBYB. rewrite HFB in HappfB, HBYB.
pose proof HJB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresC & _).
assert (QspZ : spZ (ms_regs ms0) = mf).
{ unfold spZ. rewrite Qsp'. unfold w64. apply unsigned_lit_small.
  clear - Hmf0 Hmfhi Hshi H47 C1 Hes. lia. }
(* run 2 and call 2 kept what the block needs *)
assert (K2 : rvs_k B lyc Sc W2 memA W2 (ms_mem ms0) (mf - 2 * ESTACK) mf
  (fun a => (mf + 208 <= a < mf + 216) \/ a = SF + 496 + dec_len (v / 1000) 1)).
{ eapply (rvs_k_move B lyc Sc lyA SA); [| rewrite HblA; apply Permutation_refl | exact HfrA | exact HfaA].
  apply (rvs_k_of_run B LAWS lyA SA W2 memA mdA memA (ms_mem ms0) (mf - 2 * ESTACK) mf _ HARA).
  - clear - Hmf0 Hes; lia.
  - clear - Hmfhi Hshi H47 C1; lia.
  - intros a Himg [Ha | Ha].
    + pose proof (Hsegs a Himg) as Hl. clear - Ha Hl Hmf0 C1 C5 Hes. lia.
    + apply (h_frame_not_img lyA SA W2 memA mdA pos a HARA Hin4A);
      [rewrite HSFaA, HFB; clear - Ha Hd1'; lia | exact Himg].
  - intros a Ha Hlo Hn. apply KEEP2;
    [exact Ha | intros Hc; apply Hn; left; exact Hc | intros Hc; apply Hn; right; exact Hc].
  - exact HG0. }
assert (KB : rvs_k B lyc Sc W2 (ms_mem ms0) W3 memB (mf - 2 * ESTACK) mf
  (fun a => mf + 208 <= a < mf + 208 + 8 \/
            SF + 496 + (dec_len (v / 1000) 1 + 1) <= a
              < SF + 496 + (dec_len (v / 1000) 1 + 1) + dec_len (v mod 1000) 3)).
{ pose proof (rvs_k_of_tcj B put_dec.PUT_DEC_STK lyA SA W2 (ms_mem ms0) W3 memB (spZ (ms_regs ms0)) _ HtcjB) as X.
  rewrite QspZ in X.
  eapply (rvs_k_move B lyc Sc lyA SA); [| rewrite HblA; apply Permutation_refl | exact HfrA | exact HfaA].
  eapply rvs_k_mono; [exact X | unfold put_dec.PUT_DEC_STK; clear - Hes; lia | clear; lia | intros a Ha; exact Ha]. }
pose proof (rvs_k_trans B lyc Sc W memc W2 memA W2 (ms_mem ms0) _ _ _ _ KK1 K2) as KK2.
pose proof (rvs_k_trans B lyc Sc W memc W2 (ms_mem ms0) W3 memB _ _ _ _ KK2 KB) as KK3.
(* ef on memB: the two pieces and the dot *)
assert (HlenD1 : Z.of_nat (length (map bv_unsigned (IdentSpec.DEC (v / 1000) 1))) = dec_len (v / 1000) 1)
  by (rewrite length_map; reflexivity).
assert (HlenD2 : Z.of_nat (length (map bv_unsigned (IdentSpec.DEC (v mod 1000) 3))) = 3)
  by (rewrite length_map; exact (h_dec3_len (v mod 1000) ltac:(clear - Hvm; lia))).
assert (GDEC1B : garr8 SEGS (rd W3 memB) (SF + 496) (map bv_unsigned (IdentSpec.DEC (v / 1000) 1))).
{ apply (h_garr8_keep lyc Sc W2 (ms_mem ms0) W3 memB _ _ _ pos _ _ KB Hin4);
  rewrite ?HlenD1, ?HSFa;
  [ clear; lia | clear - Hd1'; lia
  | intros x Hx [Hc | Hc]; clear - Hx Hc HSF1 C1 Hmf0 Hes Hd1'; lia | exact GDEC1 ]. }
assert (GDOTB : garr8 SEGS (rd W3 memB) (SF + 496 + dec_len (v / 1000) 1) [46]).
{ apply (h_garr8_keep lyc Sc W2 (ms_mem ms0) W3 memB _ _ _ pos _ _ KB Hin4);
  cbn [length Z.of_nat]; rewrite ?HSFa;
  [ clear - Hd1'; lia | clear - Hd1'; lia
  | intros x Hx [Hc | Hc]; clear - Hx Hc HSF1 C1 Hmf0 Hes Hd1'; lia | exact GDOT ]. }
assert (HlenALL : Z.of_nat (length (map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++
                                    map bv_unsigned (IdentSpec.DEC (v mod 1000) 3))) = h_n2 v).
{ rewrite !length_app, !Nat2Z.inj_add, HlenD1, HlenD2. unfold h_n2, h_d1. cbn [length Z.of_nat]. lia. }
assert (G123B : garr8 SEGS (rd W3 memB) (SF + 496)
  (map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3))).
{ apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact GDEC1B|]. rewrite HlenD1.
  apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact GDOTB|]. cbn [length].
  replace (SF + 496 + dec_len (v / 1000) 1 + Z.of_nat 1) with (SF + 496 + (dec_len (v / 1000) 1 + 1)) by (clear; lia).
  exact HgarB. }
(* ---- back to the engine after call 2: keep the two read-only machine-frame slots ---- *)
jafter_call_keep_pi HS 64%nat regsB (mrestrict (w_H W3) memB) HPB [2; 3]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  all: split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EH9;
    [ intros a Ha; apply (mbyte_of_aview SEGS); destruct HtcjB as (T1 & _); apply T1;
      [ clear - Ha Hmf0 Hmfhi Hshi H47 C1 Hes; lia
      | rewrite QspZ; unfold put_dec.PUT_DEC_STK; clear - Ha Hes; lia
      | cbv beta; clear - Ha HSF1 C1 Hmf0 Hes Hd1' H3l; lia ]
    | intros a Ha; exfalso; clear - Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEIB : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (EV3 : forall n, (n < 48)%nat -> ew E2 n = ew E n)
    by (intros n Hn; rewrite !ew_havoc_old by lia; reflexivity) end.
replace (dec_len (v / 1000) 1 + 1 + dec_len (v mod 1000) 3) with (h_n2 v) in HvalB
  by (rewrite (h_dec3_len (v mod 1000) ltac:(clear - Hvm; lia)); unfold h_n2, h_d1; clear; lia).
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (ROK208b : YP09.region_ok SEGS E2 (mrestrict (w_H W3) memB) (h_r208 (SOff 34 0))) end.
{ unfold YP09.region_ok, h_r208.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite ?EV3 by lia. rewrite U9. split; [clear - Hmf0 C1 Hes; lia|]. split; [clear - Hmfhi Hshi H47; lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply HpresC; clear - Ho Hmfhi HSTKw Hes; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ mf 208 8 (SOff 34 0) (h_n2 v));
  [ cbn [sv_denot]; rewrite ?EV3 by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | clear - Hd1 Hn2; lia | clear; lia | exact HvalB ]. }
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (ROKnulb : YP09.region_ok SEGS E2 (mrestrict (w_H W3) memB) (h_rnul [])) end.
{ unfold YP09.region_ok, h_rnul.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite ?EV3 by lia. rewrite U35. split; [clear - HSF0 Hd1 Hn2; lia|].
  split; [clear - HSF1 C1 Hd1 Hn2; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  exact (proj1 (HBYB (SF + 496 + h_n2 v + o) ltac:(clear - Ho Hd1 Hn2; lia))). }
pose proof (st_ok_pi_add_region _ _ _ (h_r208 (SOff 34 0)) HS ltac:(vm_compute; reflexivity) ROK208b
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, h_r208;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?EV3 by lia; rewrite ?U9;
        repeat split; try exact I; clear; lia)) as HS3.
clear HS. rename HS3 into HS.
pose proof (st_ok_pi_add_region _ _ _ (h_rnul []) HS ltac:(vm_compute; reflexivity) ROKnulb
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, h_rnul, h_r208;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?EV3 by lia; rewrite ?U9, ?U35;
        repeat split; try exact I; clear - Hmf0 HSF0 HSF1 C1 Hd1 Hn2 Hes; lia)) as HS3.
clear HS. rename HS3 into HS.
(* ---- run 3: 0x819b0 .. the reac_identity_fw_str call (0x819dc) ---- *)
clear KEEP2 Qra Qsp2 Qgp Qtp Qa0 Qa1 Qa2 Qa3 Qef Qp Qgp' Qtp'.
paj_run_shc RUNP RUNC HS HJB.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 35%nat (SF + 496 + h_n2 v));
  [ reflexivity | rewrite ?EV3 by lia; exact U35
  | cbn [YP09.r_wlo YP09.r_whi h_rnul]; intros a Ha; right; right; right; exists 4, pos;
    split; [rewrite Hown; left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; rewrite HSFaB, HFB; clear - Ha Hd1 Hn2; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
  [ reflexivity | cbn [YP09.r_base h_r208]; rewrite ?EV3 by lia; rewrite U9; clear; lia
  | cbn [YP09.r_wlo h_r208]; clear - HSTKw Hes; lia
  | cbn [YP09.r_whi h_r208]; clear - Hmfhi; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_nil. }
(* the NUL run 3 stored, and what run 3 kept *)
h_reg HS 0%nat HRnul.
cbn [ms_mem restrict] in HRnul.
assert (GNUL : garr8 SEGS (rd W3 (ms_mem ms1)) (SF + 496 + h_n2 v + 0) [0]).
{ eapply rvs_byte_reg; [exact HRnul | cbn [base_val]; rewrite ?EV3 by lia; exact U35 | cbn [sv_denot]; reflexivity]. }
rewrite Z.add_0_r in GNUL.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 208 <= a < mf + 216) -> a <> SF + 496 + h_n2 v ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) memB a).
{ intros a Ha Hw1 Hw2.
  apply (kept_of_frame _ _ (w_H W3) memB (ms_mem ms1)
    (fun x => (mf + 208 <= x < mf + 216) \/ x = SF + 496 + h_n2 v) HFr1);
  [| exact Ha | clear - Hw1 Hw2; tauto].
  intros bb wlo whi aa Hin Hr.
  cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi h_rnul h_r208] in Hin.
  destruct Hin as [Eq | [Eq | [Eq | [Eq | []]]]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  rewrite ?EV3 in Hr by lia;
  [ rewrite U35 in Hr; right; clear - Hr; lia
  | rewrite U9 in Hr; left; clear - Hr; lia
  | rewrite U9 in Hr; exfalso; clear - Hr; lia
  | rewrite U9 in Hr; exfalso; clear - Hr; lia ]. }
assert (K3 : rvs_k B lyc Sc W3 memB W3 (ms_mem ms1) (mf - 2 * ESTACK) mf
  (fun a => (mf + 208 <= a < mf + 216) \/ a = SF + 496 + h_n2 v)).
{ eapply (rvs_k_move B lyc Sc lyB SB);
  [| rewrite HblB, HblA; apply Permutation_refl | rewrite HfrB; exact HfrA
   | intros cid p; rewrite HfaB; apply HfaA].
  apply (rvs_k_of_run B LAWS lyB SB W3 memB mdB memB (ms_mem ms1) (mf - 2 * ESTACK) mf _ HARB).
  - clear - Hmf0 Hes; lia.
  - clear - Hmfhi Hshi H47 C1; lia.
  - intros a Himg [Ha | Ha].
    + pose proof (Hsegs a Himg) as Hl. clear - Ha Hl Hmf0 C1 C5 Hes. lia.
    + apply (h_frame_not_img lyB SB W3 memB mdB pos a HARB Hin4B);
      [rewrite HSFaB, HFB; clear - Ha Hd1 Hn2; lia | exact Himg].
  - intros a Ha Hlo Hn. apply KEEP3;
    [exact Ha | intros Hc; apply Hn; left; exact Hc | intros Hc; apply Hn; right; exact Hc].
  - exact HG1. }
pose proof (rvs_k_trans B lyc Sc W memc W3 memB W3 (ms_mem ms1) _ _ _ _ KK3 K3) as KK4.
assert (G123 : garr8 SEGS (rd W3 (ms_mem ms1)) (SF + 496)
  (map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3))).
{ apply (h_garr8_keep lyc Sc W3 memB W3 (ms_mem ms1) _ _ _ pos _ _ K3 Hin4);
  rewrite ?HlenALL, ?HSFa;
  [ clear; lia | clear - Hd1 Hn2; lia
  | intros x Hx [Hc | Hc]; clear - Hx Hc HSF1 C1 Hmf0 Hes Hd1 Hn2; lia | exact G123B ]. }
assert (GEF : garr8 SEGS (rd W3 (ms_mem ms1)) (SF + 496)
  ((map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0])).
{ apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact G123|]. rewrite HlenALL. exact GNUL. }
(* the frame's shadow is still clear *)
assert (Hsh : forall x, shadow_addr SF <= x < shadow_addr SF + 128 ->
  x < alloc_ceiling /\ (x < SF \/ SF + 1024 <= x)).
{ intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happf.
  unfold shadow_addr, SHADOW_OFF in *. clear - Hx Happf HSF0 HSF1 C1. lia. }
assert (Zf3 : zero_shadow (aview SEGS (w_H W3) (ms_mem ms1)) SHADOW_OFF (SF + 464) 8).
{ apply (h_zsh_keep lyc Sc W memc W3 (ms_mem ms1) _ _ _ pos _ _ KK4 Hin4); rewrite ?HSFa;
  [ clear; lia | clear; lia | clear - HSF64; lia | clear - HSF64; lia | | exact Zf ].
  intros x Hx HE. destruct (Hsh x Hx) as [Hx1 Hx2]. cbv beta in HE.
  repeat match type of HE with _ \/ _ => destruct HE as [HE | HE] end;
  first [contradiction | clear - HE Hx1 Hx2 Hmf0 Hes Hd1 Hn2 Hd1' Hvm H3l; lia]. }
assert (Zef3 : zero_shadow (aview SEGS (w_H W3) (ms_mem ms1)) SHADOW_OFF (SF + 496) 16).
{ apply (h_zsh_keep lyc Sc W memc W3 (ms_mem ms1) _ _ _ pos _ _ KK4 Hin4); rewrite ?HSFa;
  [ clear; lia | clear; lia | clear - HSF64; lia | clear - HSF64; lia | | exact Zef ].
  intros x Hx HE. destruct (Hsh x Hx) as [Hx1 Hx2]. cbv beta in HE.
  repeat match type of HE with _ \/ _ => destruct HE as [HE | HE] end;
  first [contradiction | clear - HE Hx1 Hx2 Hmf0 Hes Hd1 Hn2 Hd1' Hvm H3l; lia]. }
(* ---- the reac_identity_fw_str call at 0x819dc ---- *)
pmkst HS.
rewrite (PSIG IB_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
prreg HS (1%bv : bv 5) Fra. prreg HS (2%bv : bv 5) Fsp. prreg HS (3%bv : bv 5) Fgp.
prreg HS (4%bv : bv 5) Ftp. prreg HS (10%bv : bv 5) Fa0. prreg HS (11%bv : bv 5) Fa1.
prreg HS (12%bv : bv 5) Fa2. prreg HS (18%bv : bv 5) Fs2. prreg HS (19%bv : bv 5) Fs3.
prreg HS (20%bv : bv 5) Fs4.
assert (Fsp' : getr (ms_regs ms1) 2 = w64 mf) by (rewrite Fsp, (EE 2%nat 2%bv eq_refl); exact R2).
assert (Fgp' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Fgp, (EE 3%nat 3%bv eq_refl); exact R3).
assert (Ftp' : getr (ms_regs ms1) 4 = w64 (as_tp B)).
{ rewrite Ftp; try rewrite (EE 4%nat 4%bv eq_refl); exact R4. }
assert (Fv : getr (ms_regs ms1) 10 = w64 v) by (rewrite Fa0, (EE 24%nat 24%bv eq_refl); exact R24).
assert (Ff : getr (ms_regs ms1) 11 = w64 (SF + 464)).
{ rewrite Fa1, U25. unfold w64. f_equal. clear; lia. }
assert (F8 : getr (ms_regs ms1) 12 = w64 8) by (rewrite Fa2; reflexivity).
assert (QspZ1 : spZ (ms_regs ms1) = mf).
{ unfold spZ. rewrite Fsp'. unfold w64. apply unsigned_lit_small.
  clear - Hmf0 Hmfhi Hshi H47 C1 Hes. lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => set (MDF := md) end.
eapply SRr_bind.
{ apply (h_fw_call B LAWS TL HFWS STK sp0 FP ly S W0 mem0 md0 own lyB SB W3 (ms_mem ms1) MDF
    k (ms_regs ms1) pos mf SF v HJB HfrsB Hown HSFaB).
  - rewrite Fra. apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - exact Fsp'.
  - exact Fgp'.
  - exact Ftp'.
  - exact Fv.
  - exact Ff.
  - exact F8.
  - exact Hv.
  - exact Hmf32.
  - exact Hmflo.
  - exact Hmfhi.
  - exact HSTKw.
  - exact Zf3. }
intros W4 c4 _ (lyC & SC & regsC & memC & mdC & -> & HJC & HPC & HfrC & HblC & HIF).
assert (FWW : fw_writes (SF + 464) 8 = true).
{ unfold fw_writes. rewrite (proj2 (Z.eqb_neq (SF + 464) 0)) by (clear - HSF0; lia). reflexivity. }
rewrite FWW in HIF. destruct HIF as (Ha0C & GFW & HtcjC).
rewrite Fra.
pose proof (proj1 HJC) as HARC.
assert (HfrsC : frames SC = [(4, pos)]) by (rewrite HfrC; exact HfrsB).
assert (Hin4C : In (4, pos) (frames SC)) by (rewrite HfrsC; left; reflexivity).
destruct (rvs_journal_move B STK sp0 FP ly S W0 mem0 md0 own lyB SB W3 (ms_mem ms1) _ k
  lyC SC W4 memC mdC k HJB HJC) as (HfrC2 & HfaC).
assert (HSFaC : frame_addr lyC 4 pos = SF) by (rewrite HfaC; exact HSFaB).
assert (HfwN : fw_n v = h_n2 v + 1) by exact (h_fw_n v Hv).
assert (KC : rvs_k B lyc Sc W3 (ms_mem ms1) W4 memC (mf - 2 * ESTACK) mf
  (fun a => SF + 464 <= a < SF + 464 + fw_n v)).
{ pose proof (rvs_k_of_tcj B REAC_IDENTITY_FW_STR_STK lyB SB W3 (ms_mem ms1) W4 memC (spZ (ms_regs ms1)) _ HtcjC) as X.
  rewrite QspZ1 in X.
  eapply (rvs_k_move B lyc Sc lyB SB);
  [| rewrite HblB, HblA; apply Permutation_refl | rewrite HfrB; exact HfrA
   | intros cid p; rewrite HfaB; apply HfaA].
  eapply rvs_k_mono; [exact X | unfold REAC_IDENTITY_FW_STR_STK, FW_FRAME; clear - Hes; lia
  | clear; lia | intros a Ha; exact Ha]. }
pose proof (rvs_k_trans B lyc Sc W memc W3 (ms_mem ms1) W4 memC _ _ _ _ KK4 KC) as KK5.
assert (HlenL : Z.of_nat (length ((map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++
                 map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0])) = h_n2 v + 1).
{ rewrite length_app, Nat2Z.inj_add, HlenALL. cbn [length]. clear; lia. }
assert (GEFC : garr8 SEGS (rd W4 memC) (SF + 496)
  ((map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0])).
{ apply (h_garr8_keep lyc Sc W3 (ms_mem ms1) W4 memC _ _ _ pos _ _ KC Hin4);
  rewrite ?HlenL, ?HSFa;
  [ clear; lia | clear - Hd1 Hn2; lia
  | intros x Hx Hc; cbv beta in Hc; rewrite HfwN in Hc; clear - Hx Hc Hd1 Hn2; lia | exact GEF ]. }
(* ---- back to the engine after reac_identity_fw_str: keep the two read-only slots ---- *)
jafter_call_keep_pi HS 80%nat regsC (mrestrict (w_H W4) memC) HPC [2; 3]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  all: split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EV3 by lia; rewrite ?U9;
    [ intros a Ha; apply (mbyte_of_aview SEGS); destruct HtcjC as (T1 & _); apply T1;
      [ clear - Ha Hmf0 Hmfhi Hshi H47 C1 Hes; lia
      | rewrite QspZ1; unfold REAC_IDENTITY_FW_STR_STK, FW_FRAME; clear - Ha Hes; lia
      | cbv beta; rewrite HfwN; clear - Ha HSF1 C1 Hmf0 Hes Hd1 Hn2; lia ]
    | intros a Ha; exfalso; clear - Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEIC : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (EV4 : forall n, (n < 48)%nat -> ew E2 n = ew E n)
    by (intros n Hn; rewrite !ew_havoc_old by lia; reflexivity) end.
(* a0 = L v = n2, the counter's atom *)
pose proof (rvs_pin _ _ _ (10%bv : bv 5) 34%nat HS
  ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0C, (h_L v Hv); cbn [sv_denot];
        rewrite ?EV4 by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
(* ---- run 4: 0x819e0 .. the bcmp call (0x819f8) ---- *)
clear Fra Fsp Fgp Ftp Fa0 Fa1 Fa2 Fs2 Fs3 Fs4 Fsp' Fgp' Ftp' Fv Ff F8.
paj_run_shc RUNP RUNC HS HJC.
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_nil. }
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem ms2) a = aview SEGS (w_H W4) memC a).
{ intros a Ha.
  apply (kept_of_frame _ _ (w_H W4) memC (ms_mem ms2) (fun _ => False) HFr2); [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr.
  cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; exfalso; clear - Hr; lia. }
pose proof (proj1 HJC) as HARC2.
assert (K4 : rvs_k B lyc Sc W4 memC W4 (ms_mem ms2) (mf - 2 * ESTACK) mf (fun _ => False)).
{ eapply (rvs_k_move B lyc Sc lyC SC);
  [| eapply perm_trans; [exact HblC | rewrite HblB, HblA; apply Permutation_refl]
   | rewrite HfrC, HfrB; exact HfrA
   | intros cid p; rewrite HfaC, HfaB; apply HfaA].
  apply (rvs_k_of_run B LAWS lyC SC W4 memC mdC memC (ms_mem ms2) (mf - 2 * ESTACK) mf _ HARC).
  - clear - Hmf0 Hes; lia.
  - clear - Hmfhi Hshi H47 C1; lia.
  - intros a _ [].
  - intros a Ha _ _. exact (KEEP4 a Ha).
  - exact HG2. }
pose proof (rvs_k_trans B lyc Sc W memc W4 memC W4 (ms_mem ms2) _ _ _ _ KK5 K4) as KK6.
assert (LST : reac_identity_fw_str.fw_bytes v =
  (map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0])
  by exact (h_fw_bytes v Hv).
rewrite LST in GFW.
assert (GFW4 : garr8 SEGS (rd W4 (ms_mem ms2)) (SF + 464)
  ((map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0])).
{ apply (h_garr8_keep lyc Sc W4 memC W4 (ms_mem ms2) _ _ _ pos _ _ K4 Hin4); rewrite ?HlenL, ?HSFa;
  [ clear; lia | clear - Hd1 Hn2; lia | intros x _ [] | exact GFW ]. }
assert (GEF4 : garr8 SEGS (rd W4 (ms_mem ms2)) (SF + 496)
  ((map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0])).
{ apply (h_garr8_keep lyc Sc W4 memC W4 (ms_mem ms2) _ _ _ pos _ _ K4 Hin4); rewrite ?HlenL, ?HSFa;
  [ clear; lia | clear - Hd1 Hn2; lia | intros x _ [] | exact GEFC ]. }
assert (Zf4 : zero_shadow (aview SEGS (w_H W4) (ms_mem ms2)) SHADOW_OFF (SF + 464) 8).
{ apply (h_zsh_keep lyc Sc W memc W4 (ms_mem ms2) _ _ _ pos _ _ KK6 Hin4); rewrite ?HSFa;
  [ clear; lia | clear; lia | clear - HSF64; lia | clear - HSF64; lia | | exact Zf ].
  intros x Hx HE. destruct (Hsh x Hx) as [Hx1 Hx2]. cbv beta in HE.
  repeat match type of HE with _ \/ _ => destruct HE as [HE | HE] end;
  first [contradiction | rewrite ?HfwN in HE; clear - HE Hx1 Hx2 Hmf0 Hes Hd1 Hn2 Hd1' Hvm H3l; lia]. }
assert (Zef4 : zero_shadow (aview SEGS (w_H W4) (ms_mem ms2)) SHADOW_OFF (SF + 496) 16).
{ apply (h_zsh_keep lyc Sc W memc W4 (ms_mem ms2) _ _ _ pos _ _ KK6 Hin4); rewrite ?HSFa;
  [ clear; lia | clear; lia | clear - HSF64; lia | clear - HSF64; lia | | exact Zef ].
  intros x Hx HE. destruct (Hsh x Hx) as [Hx1 Hx2]. cbv beta in HE.
  repeat match type of HE with _ \/ _ => destruct HE as [HE | HE] end;
  first [contradiction | rewrite ?HfwN in HE; clear - HE Hx1 Hx2 Hmf0 Hes Hd1 Hn2 Hd1' Hvm H3l; lia]. }
(* f and ef hold the same n2 + 1 bytes *)
assert (SAME : forall i, 0 <= i < h_n2 v + 1 ->
  aview SEGS (w_H W4) (ms_mem ms2) (SF + 464 + i) = aview SEGS (w_H W4) (ms_mem ms2) (SF + 496 + i)).
{ intros i Hi.
  assert (Hj : (Z.to_nat i < length ((map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46%Z] ++
                 map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) ++ [0%Z]))%nat) by (clear - Hi HlenL; lia).
  unfold aview.
  replace (SF + 464 + i) with (SF + 464 + Z.of_nat (Z.to_nat i)) by (clear - Hi; lia).
  replace (SF + 496 + i) with (SF + 496 + Z.of_nat (Z.to_nat i)) by (clear - Hi; lia).
  rewrite (garr8_mbyte SEGS _ _ _ _ GFW4 Hj), (garr8_mbyte SEGS _ _ _ _ GEF4 Hj). reflexivity. }
(* ---- the bcmp call at 0x819f8 ---- *)
pmkst HS.
prreg HS (1%bv : bv 5) Bra. prreg HS (2%bv : bv 5) Bsp. prreg HS (3%bv : bv 5) Bgp.
prreg HS (4%bv : bv 5) Btp. prreg HS (10%bv : bv 5) Ba0. prreg HS (11%bv : bv 5) Ba1.
prreg HS (12%bv : bv 5) Ba2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ => set (MDB := md) end.
eapply SRr_bind.
{ apply (h_bcmp_call B LAWS ABCMP STK sp0 FP ly S W0 mem0 md0 own lyC SC W4 (ms_mem ms2) MDB k
    (ms_regs ms2) pos mf SF (h_n2 v + 1) _ HJC HfrsC HSFaC Bra).
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite Bsp, (EE 2%nat 2%bv eq_refl). exact R2.
  - rewrite Bgp; try rewrite (EE 3%nat 3%bv eq_refl). exact R3.
  - rewrite Btp; try rewrite (EE 4%nat 4%bv eq_refl). exact R4.
  - rewrite Ba0; try rewrite U25; try rewrite (EE 25%nat 25%bv eq_refl), R25.
    unfold w64. f_equal. clear; lia.
  - rewrite Ba1, (EE 25%nat 25%bv eq_refl). exact R25.
  - rewrite Ba2, U34. unfold w64. f_equal.
  - clear - Hd1 Hn2; lia.
  - exact Hmf32.
  - exact Hmflo.
  - exact Hmfhi.
  - exact HSTKw.
  - exact Zf4.
  - exact Zef4. }
intros W5 c5 _ (-> & regsD & memD & mdD & res & -> & HJD & HPD' & Ha0D & HIFF & HKD & HPRD).
assert (Hres : res = w64 0) by (apply (proj2 HIFF); exact SAME).
rewrite Hres in Ha0D.
assert (KD : rvs_k B lyc Sc W4 (ms_mem ms2) W4 memD (mf - 2 * ESTACK) mf (fun _ => False)).
{ eapply (rvs_k_move B lyc Sc lyC SC);
  [| eapply perm_trans; [exact HblC | rewrite HblB, HblA; apply Permutation_refl]
   | rewrite HfrC, HfrB; exact HfrA
   | intros cid p; rewrite HfaC, HfaB; apply HfaA].
  apply (h_k_of_keep lyC SC W4 (ms_mem ms2) _ (ms_mem ms2) memD (mf - 2 * ESTACK) mf HARC2);
  [ clear - Hmf0 Hes; lia | clear - Hmfhi Hshi H47 C1; lia | exact HKD | exact HPRD ]. }
pose proof (rvs_k_trans B lyc Sc W memc W4 (ms_mem ms2) W4 memD _ _ _ _ KK6 KD) as KK7.
(* ---- back to the engine after bcmp ---- *)
jafter_call_keep_pi HS 96%nat regsD (mrestrict (w_H W4) memD) HPD' [0; 1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  all: split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EV4 by lia; rewrite ?U9;
    [ intros a Ha; apply (mbyte_of_aview SEGS); apply HKD;
      [ clear - Ha Hmf0 Hmfhi Hshi H47 C1 Hes; lia | clear - Ha Hes; lia ]
    | intros a Ha; exfalso; clear - Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
  assert (HEID : img_env VAL A_LIM E2) by (apply img_env_havoc; [assumption | cbv; lia]);
  assert (EV5 : forall n, (n < 48)%nat -> ew E2 n = ew E n)
    by (intros n Hn; rewrite !ew_havoc_old by lia; reflexivity) end.
pose proof (h_pin _ _ _ (10%bv : bv 5) (SLit 0) HS
  ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0D; reflexivity)
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
(* ---- run 5: 0x819fc .. the end of the block (0x81a00) ---- *)
pose proof (proj1 HJD) as HARD.
paj_run_to_sh RUNTOP HS HJD 0x128c.
{ apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|].
  apply awr_ok_nil. }
assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W4) (ms_mem ms3) a = aview SEGS (w_H W4) memD a).
{ intros a Ha.
  apply (kept_of_frame _ _ (w_H W4) memD (ms_mem ms3) (fun _ => False) HFr3); [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr.
  cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; exfalso; clear - Hr; lia. }
assert (K5 : rvs_k B lyc Sc W4 memD W4 (ms_mem ms3) (mf - 2 * ESTACK) mf (fun _ => False)).
{ eapply (rvs_k_move B lyc Sc lyC SC);
  [| eapply perm_trans; [exact HblC | rewrite HblB, HblA; apply Permutation_refl]
   | rewrite HfrC, HfrB; exact HfrA
   | intros cid p; rewrite HfaC, HfaB; apply HfaA].
  apply (rvs_k_of_run B LAWS lyC SC W4 memD mdD memD (ms_mem ms3) (mf - 2 * ESTACK) mf _ HARD).
  - clear - Hmf0 Hes; lia.
  - clear - Hmfhi Hshi H47 C1; lia.
  - intros a _ [].
  - intros a Ha _ _. exact (KEEP5 a Ha).
  - exact HG3. }
pose proof (rvs_k_trans B lyc Sc W memc W4 memD W4 (ms_mem ms3) _ _ _ _ KK7 K5) as KK8.
(* ---- the state at +0x128c ---- *)
assert (G123F : garr8 SEGS (rd W4 (ms_mem ms3)) (SF + 496)
  (map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC (v mod 1000) 3))).
{ apply (h_garr8_keep lyc Sc W4 memD W4 (ms_mem ms3) _ _ _ pos _ _ K5 Hin4); rewrite ?HlenALL, ?HSFa;
  [ clear; lia | clear - Hd1 Hn2; lia | intros x _ [] | ].
  apply (h_garr8_keep lyc Sc W4 (ms_mem ms2) W4 memD _ _ _ pos _ _ KD Hin4); rewrite ?HlenALL, ?HSFa;
  [ clear; lia | clear - Hd1 Hn2; lia | intros x _ [] | ].
  exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) GEF4)). }
assert (KR : forall (r : bv 5) (n : nat), getr (ms_regs ms3) r = ew E n ->
  Z.of_nat n = bv_unsigned r -> getr (ms_regs ms3) r = getr regs r)
  by (intros r n H Hn; rewrite H; apply EE; exact Hn).
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (21%bv : bv 5) P21.
prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27. prreg HS (22%bv : bv 5) P22.
apply SRr_ret.
unfold h_post.
exists lyC, SC, (ms_regs ms3), (ms_mem ms3).
eexists. split; [unfold cfg_at; reflexivity|].
split; [exact HJD|].
split; [rewrite HfrC, HfrB; exact HfrA|].
split; [eapply perm_trans; [exact HblC | rewrite HblB, HblA; apply Permutation_refl]|].
split.
{ intros r Hr. cbn [In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr;
  first [ exact (KR _ _ P2 eq_refl) | exact (KR _ _ P3 eq_refl) | exact (KR _ _ P4 eq_refl)
        | exact (KR _ _ P8 eq_refl) | exact (KR _ _ P9 eq_refl) | exact (KR _ _ P21 eq_refl)
        | exact (KR _ _ P23 eq_refl) | exact (KR _ _ P24 eq_refl) | exact (KR _ _ P25 eq_refl)
        | exact (KR _ _ P26 eq_refl) | exact (KR _ _ P27 eq_refl) ]. }
split.
{ rewrite P22. first [ rewrite E36; reflexivity | rewrite U36, Z.add_0_r; reflexivity
                     | rewrite U36; reflexivity ]. }
split.
{ assert (ML : map (fun b : byte => bv_unsigned b)
                 (IdentSpec.DEC (v / 1000) 1 ++ [SlotModel.dot] ++ IdentSpec.DEC (v mod 1000) 3)
               = map bv_unsigned (IdentSpec.DEC (v / 1000) 1) ++ [46] ++
                 map bv_unsigned (IdentSpec.DEC (v mod 1000) 3)) by (rewrite !map_app; reflexivity).
  rewrite ML. exact G123F. }
eapply rvs_k_mono; [exact KK8 | clear; lia | clear; lia |].
intros a HE. cbv beta in HE. unfold h_wrote.
repeat match type of HE with _ \/ _ => destruct HE as [HE | HE] end;
first [ contradiction
      | rewrite ?HfwN in HE; clear - HE Hd1 Hn2 Hd1' H3l; unfold h_n2, h_d1 in *; lia ].
Qed.
End c.
End b.
End a.

(* ---- seg_H: the glue (LLVMFuzzerTestOneInput_seg_H_hand3.v) around the block's walk h_core -------------- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section w2.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
Section w3.
(* The contract's Section (LLVMFuzzerTestOneInput.v), in its order, as far as seg_H uses it. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Hypothesis HSTK : LLVMFuzzerTestOneInput.STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : LLVMFuzzerTestOneInput.EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis HPD : put_dec.tput_dec_spec B.

Lemma seg_H : @LLVMFuzzerTestOneInput_inv.seg_H_stmt fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
apply (LLVMFuzzerTestOneInput_seg_H_hand3.h_glue B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS LAWS MTL HMT0 HSTK HEV h_anyfw_range).
unfold LLVMFuzzerTestOneInput_seg_H_hand3_stmt.h_core_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pos mf SF v cd.
exact (h_core B LAWS TL PSIG HPD HFWS ABCMP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pos mf SF v cd
  (LLVMFuzzerTestOneInput_seg_H_hand2.h_pd_call B)).
Qed.
Check (seg_H : @LLVMFuzzerTestOneInput_inv.seg_H_stmt fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
End w3.
End w2.
End w.

Print Assumptions seg_H.
