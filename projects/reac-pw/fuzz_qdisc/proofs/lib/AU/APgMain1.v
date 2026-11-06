(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements
   are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc image A (fuzz_qdisc.asan, sha256
   980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgMain3.v (its in_byte, fin_conj and lemma rt_S3, lines 56-60, 85-92 and
   128-236) at origin/ossv/recipes 6ebe35ba632, with its module paths changed, knock's frame arguments (fpos, F,
   EFA3, HpF) dropped because qdisc's harness owns no fake frame (lib/A/QPgRt.v, change Q1), a fourth path added
   (qdisc's loop head also takes rem = 0) and the selector's mod-6 arithmetic added (denot_qd_lead, U_qd_q,
   U_qd_sel). rule 24 (reuse): no function is proved here; this is SEGMENT S1, the input-byte reads of
   LLVMFuzzerTestOneInput's loop body. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QPgMain1.v of this library, for fuzz_qdisc's
   ASan-UBSan image (fuzz_qdisc.asan-ubsan, sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062):
   SEGMENT S1 from ss_L (0x7e728, INV_L fuel) to ss_J (0x7e78c, INV_J fuel), both lib/AU/APgLoop0.v. Written by
   hand from the A file: the lib/AU imports, the asan-ubsan pcs, rem in s10 (x26, the A file's s9), and a join
   one block later, after the table address 0x20c80 + 4 * sel is formed in a0 (x10), which ss_J carries as the
   atom N_fpa = 309 (the A file carried sel itself in a1 as N_sel = 306). The asan-ubsan code adds four UBSan
   tests whose taken side is the trap word `unimp` at 0x7e884; none of them adds a split:
   - `bgeu s5,rX` with rX = cur + 1, cur + 2, cur + 3 (0x7e730, 0x7e750, 0x7e7c8; trap iff cur + k <=u 1): s5 = 1
     is a literal of ss_L and cur is the atom N_cur = 300 with the range [4096, 140737479966720] (ss_L's facts),
     so the engine decides each one not taken (decide_cond2, lib/Reusable/YP0e.v);
   - `bltu s9,a0` at 0x7e800 (trap iff 2 ^ 64 - 1 - 0x20c80 <u 4 * sel, i.e. iff 0x20c80 + 4 * sel wraps): s9 is
     ss_L's literal QD_NFPS; the walk points a0 at the fresh atom 310 holding 4 * (b2 mod 6) (U_qd_sel4) with the
     range [0, 20], and the engine decides the test not taken (20 <= QD_NFPS).
   The slow blocks of the shadow checks have the other polarity than in A (`blt` back to the load, then the
   report); the engine pays each check as one obligation (obl_cur), so no slow block is walked.

   THE CODE, 0x7e728-0x7e810 (capstone 5.0.7 over the pinned image). s0 = cur, s10 = rem, s3 = SB, s5 = 1,
   s6 = 2, s7 = 0x20c80, s8 = 171, s9 = QD_NFPS:
     0x7e728  beqz s10 -> 0x7e784
     0x7e72c  addi a0,s0,1 / bgeu s5,a0 -> 0x7e884    UBSan, cur + 1
     0x7e734-0x7e740  shadow check of cur (slow block 0x7e824-0x7e82c, report 0x7e898-0x7e89c)
     0x7e744  lbu s1,0(s0)                                                         b0
     0x7e748  beq s10,s5 -> 0x7e778
     0x7e74c  addi a1,a0,1 / bgeu s5,a1 -> 0x7e884    UBSan, cur + 2
     0x7e754-0x7e760  shadow check of cur + 1 (slow block 0x7e830-0x7e838, report 0x7e8a0)
     0x7e764  lbu a1,0(a0)                                                         b1
     0x7e768  addi a0,s0,2 / slli a1,a1,8 / or s1,a1,s1                            lead = b1 << 8 | b0
     0x7e774  bne s10,s6 -> 0x7e7c4
     0x7e778  mv s10,zero / mv s0,a0 / j 0x7e788
     0x7e784  mv s1,zero
     0x7e788  mv a0,s7                                                             a0 = 0x20c80
     0x7e7c4  addi a1,a0,1 / bgeu s5,a1 -> 0x7e884    UBSan, cur + 3
     0x7e7cc-0x7e7d8  shadow check of cur + 2 (slow block 0x7e83c-0x7e840, report 0x7e844)
     0x7e7dc  lbu a0,0(a0)                                                         b2
     0x7e7e0  mul a1,a0,s8 / srli a1,a1,0xa / slli a2,a1,3 / slli a1,a1,1 / subw a1,a1,a2 / add a0,a0,a1
     0x7e7f8  andi a0,a0,0xff / slli a0,a0,2                                        a0 = 4 * (b2 mod 6)
     0x7e800  bltu s9,a0 -> 0x7e884                  UBSan, 0x20c80 + 4 * sel
     0x7e804  addi s10,s10,-3 / addi s0,s0,3 / add a0,s7,a0 / j 0x7e78c

   THE FOUR PATHS. cur, rem, c, bud come from INV_L (cur = p + c, c + rem = n); bud and fuel are threaded
   unchanged; b0, b1, b2 are the input bytes at index c, c + 1, c + 2 (PB_at_now), each read through a
   one-byte read-only region based at the cursor atom N_cur (offsets 0, 1, 2). Each path lands at 0x7e78c
   and hands over (cur', rem', lead, sel) with c' the bytes it consumed and a0 = 0x20c80 + 4 * sel:
   P0 rem = 0  -- 0x7e728 `beqz s10` TAKEN (Hc1 : rem = 0). Through 0x7e784.
                  lead = 0, sel = 0, cur' = cur, rem' = 0, c' = c.
   P1 rem = 1  -- Hc1 : rem <> 0, then 0x7e748 `beq s10,s5` TAKEN (Hc2 : rem = 1). Through 0x7e778.
                  lead = b0, sel = 0, cur' = cur + 1, rem' = 0, c' = c + 1.
   P2 rem = 2  -- Hc1, Hc2 : rem <> 1, then 0x7e774 `bne s10,s6` NOT taken (Hc3 : rem = 2). Through 0x7e778.
                  lead = 256 * b1 + b0, sel = 0, cur' = cur + 2, rem' = 0, c' = c + 2.
   P3 rem >= 3 -- Hc1, Hc2, then 0x7e774 `bne s10,s6` TAKEN (Hc3 : rem <> 2). Through 0x7e7c4.
                  lead = 256 * b1 + b0, sel = b2 mod 6, cur' = cur + 3, rem' = rem - 3, c' = c + 3.
   In every path c' + rem' = c + rem = c_n cx. The lead is denot_qd_lead (lor_byte_pair: the two bytes do not
   overlap); the selector is U_qd_sel: (b2 * 171) >> 10 = b2 / 6 (qd_div6), so b2 - 6 * (b2 / 6) = b2 mod 6, at
   most 5 (qd_mod6_range), which the `andi 0xff` keeps and `slli 2` makes 4 * (b2 mod 6) <= 20 (U_qd_sel4). (The
   engine carries `subw` as a 64-bit ALU_SUB here; its denotation is all U_qd_sel uses.) *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt APgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* one input byte at the moving cursor [knock A/APgMain3.v:57-60 in_byte] *)
Ltac s1_in_byte HJ LAWS HAR Hpin Hpin3 Hrq FP0 cx j bj PBj Aj :=
let HJc := fresh "HJc" in pose proof HJ as HJc; rewrite FP0 in HJc;
destruct (PB_at_now _ _ cx _ _ _ _ _ _ _ j LAWS HAR HJc Hpin Hpin3 Hrq ltac:(cbn [c_n]; lia)) as (bj & PBj & Aj);
cbn [c_p] in Aj; clear HJc.
(* the conjuncts of INV_J once its witnesses are given [knock A/APgMain3.v:85-92 fin_conj, without its
   inv_cells arm] *)
Ltac s1_fin :=
repeat match goal with |- _ /\ _ => split end;
first [ eassumption
| lazymatch goal with |- inv_cursor _ _ _ _ =>
  unfold inv_cursor; cbn [c_p c_n]; repeat match goal with |- _ /\ _ => split end; lia end
| lia ].
(* s1 = b1 << 8 | b0 (`slli a1,a1,8 / or s1,a1,s1` at 0x7e76c-0x7e770) *)
Lemma denot_qd_lead : forall E h l bh bl, ew E h = Z_to_bv 64 bh -> ew E l = Z_to_bv 64 bl -> 0 <= bh < 256 -> 0 <= bl < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff h 0) (SLit 8)) (SOff l 0)) = Z_to_bv 64 (256 * bh + bl).
Proof.
intros E h l bh bl Hh Hl Rh Rl. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu, U_SLit, (U_atom E h bh Hh), (U_atom E l bl Hl) by lia. cbn [zalu_raw].
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (bh * 256)) by (unfold M64; lia). rewrite lor_byte_pair by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* q = (b * 171) >> 10 = b / 6 (`mul a1,a0,s8 / srli a1,a1,0xa` at 0x7e7e0-0x7e7e4) *)
Lemma U_qd_q : forall E k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_SRL (SMd M_MUL (SOff k 0) (SLit 171)) (SLit 10)) = b / 6.
Proof.
intros E k b Hk Hb.
rewrite U_SAlu, U_SMd, !U_SLit, (U_atom E k b Hk) by lia. cbn [zalu_raw zmd_raw].
change (zcanon 171) with 171. change (Z.land (zcanon 10) 63) with 10.
rewrite (zcanon_id (b * 171)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 10) with 1024. rewrite (qd_div6 b Hb).
pose proof (Z.div_mod b 6 ltac:(lia)) as D. pose proof (Z.mod_pos_bound b 6 ltac:(lia)) as M.
apply zcanon_id. unfold M64. lia.
Qed.
(* (b + (2q - 8q)) & 0xff = b mod 6 (0x7e7e8-0x7e7f8), the expression the engine builds *)
Lemma U_qd_sel : forall E k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SOff k 0) (SAlu ALU_SUB
      (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff k 0) (SLit 171)) (SLit 10)) (SLit 1))
      (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff k 0) (SLit 171)) (SLit 10)) (SLit 3)))) (SLit 255))
  = b mod 6.
Proof.
intros E k b Hk Hb.
pose proof (U_qd_q E k b Hk Hb) as UQ.
pose proof (Z.div_mod b 6 ltac:(lia)) as D. pose proof (Z.mod_pos_bound b 6 ltac:(lia)) as M.
set (q := b / 6) in *. set (Q := SAlu ALU_SRL (SMd M_MUL (SOff k 0) (SLit 171)) (SLit 10)) in *. clearbody Q q.
rewrite !U_SAlu. rewrite UQ, !U_SLit, (U_atom E k b Hk) by lia. cbn [zalu_raw].
change (Z.land (zcanon 1) 63) with 1. change (Z.land (zcanon 3) 63) with 3. change (zcanon 255) with 255.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 3) with 8.
rewrite (zcanon_id (q * 2)) by (unfold M64; lia). rewrite (zcanon_id (q * 8)) by (unfold M64; lia).
assert (E1 : zcanon (b + zcanon (q * 2 - q * 8)) = b mod 6).
{ unfold zcanon. rewrite Z.add_mod_idemp_r by (unfold M64; lia). replace (b + (q * 2 - q * 8)) with (b mod 6) by lia.
  apply Z.mod_small. unfold M64. lia. }
rewrite E1. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
rewrite (Z.mod_small (b mod 6) 256) by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* a0 = (b mod 6) << 2 (`slli a0,a0,2` at 0x7e7fc), the operand of the UBSan test at 0x7e800 *)
Lemma U_qd_sel4 : forall E k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_ADD (SOff k 0) (SAlu ALU_SUB
      (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff k 0) (SLit 171)) (SLit 10)) (SLit 1))
      (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SOff k 0) (SLit 171)) (SLit 10)) (SLit 3)))) (SLit 255)) (SLit 2))
  = 4 * (b mod 6).
Proof.
intros E k b Hk Hb.
pose proof (U_qd_sel E k b Hk Hb) as US. pose proof (Z.mod_pos_bound b 6 ltac:(lia)) as M.
rewrite U_SAlu. rewrite US, U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FP0 : FP = [].
(* SEGMENT S1: ss_L (0x7e728) -> ss_J (0x7e78c). Byte atoms: 320 = b0, 321 = b1, 322 = b2; 310 = 4 * (b2 mod 6)
   at 0x7e800; the hand-over pins s0 / s10 / s1 / a0 to N_cur2 / N_rem2 / N_lead / N_fpa (303, 304, 305, 309) and
   joins with window RT_JN = 700. *)
Lemma rt_S1 : forall fuel : nat,
  rt_from B MT FP POST ss_J (INV_J B MT fuel) -> rt_from B MT FP POST ss_L (INV_L B MT fuel).
Proof.
intros fuel RT. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & Hpin & Hrq & cur & rem & bud & c & Ecur & Erem & Ebud & HCUR & Hbud & Hfuel).
cbn [c_ly c_S c_p c_n] in HPerm3, Hpin, Hrq, HCUR.
destruct HCUR as (Hcur & Hc0 & Hcn & Hrem0 & Hcur4096 & HcurHi). cbn [c_p c_n] in Hcur, Hcn.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | exact Hpin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hpin3) as (_ & Hp4096 & Hpceil & HinApp & _).
rewrite Hrq in Hpceil, HinApp.
pose proof YM05.alloc_ceiling_val as Hceilv.
pose proof (blk_off_img B _ _ _ _ _ p n (proj1 HJ3) Hpin3) as HoffImg. rewrite Hrq in HoffImg.
(* 0x7e728 beqz s10 *)
br_split HS Hc1.
all: hc_bool Hc1 ltac:(fun H => hc_atom H 301%nat rem Erem ltac:(lia)); hc_prop Hc1.
- (* P0, rem = 0: 0x7e784 *)
  pl_run_to HS HJ3 AG 0x7e78c. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  add_atom_win HS 303%nat (Z_to_bv 64 cur) E303.
  add_atom_win HS 304%nat (Z_to_bv 64 0) E304.
  add_atom_win HS 305%nat (Z_to_bv 64 0) E305.
  add_atom_win HS 309%nat (Z_to_bv 64 (134272 + 4 * 0)) E309.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  pin_by HS (8%bv : bv 5) (SOff 303 0) pin_tac.
  pin_by HS (26%bv : bv 5) (SOff 304 0) pin_tac.
  pin_by HS (9%bv : bv 5) (SOff 305 0) pin_tac.
  pin_by HS (10%bv : bv 5) (SOff 309 0) pin_tac.
  add_fact HS 303%nat 4096 140737479966720 E303 ltac:(lia).
  add_fact HS 304%nat 0 67108863 E304 ltac:(lia).
  add_fact HS 305%nat 0 65535 E305 ltac:(lia).
  add_fact HS 309%nat 134272 134292 E309 ltac:(lia).
  ra_join_win HS ss_J 700%nat ql_deadsJ_bv ltac:(idtac).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RT HS.
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|]. split; [exact Hpin|]. split; [exact Hrq|].
  exists cur, 0, bud, c, 0, 0. s1_fin.
- (* rem <> 0: 0x7e72c-0x7e744, the UBSan test of cur + 1, the check of cur, lbu s1 *)
  s1_in_byte HJ3 LAWS HAR Hpin Hpin3 Hrq FP0 (mkRTCX ly S W regs mem md p n E0 T) c b0 PB0 A0.
  replace (p + c) with (cur + 0) in A0 by lia. pose proof (proj1 PB0) as R0.
  add_atom_win HS 320%nat (Z_to_bv 64 b0) E320.
  add_fact HS 320%nat 0 255 E320 ltac:(lia).
  in_region HS (YP09.mkRegion (Some 300%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 320 0))]) Ecur AG.
  rd_run HS HJ3 AG Ecur E32n Hpin3 Hrq. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  (* 0x7e748 beq s10,s5 *)
  br_split HS Hc2.
  all: hc_bool Hc2 ltac:(fun H => hc_atom H 301%nat rem Erem ltac:(lia)); hc_prop Hc2.
  + (* P1, rem = 1: 0x7e778 *)
    pl_run_to HS HJ3 AG 0x7e78c. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    add_atom_win HS 303%nat (Z_to_bv 64 (cur + 1)) E303.
    add_atom_win HS 304%nat (Z_to_bv 64 0) E304.
    add_atom_win HS 305%nat (Z_to_bv 64 b0) E305.
    add_atom_win HS 309%nat (Z_to_bv 64 (134272 + 4 * 0)) E309.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    pin_by HS (8%bv : bv 5) (SOff 303 0) pin_tac.
    pin_by HS (26%bv : bv 5) (SOff 304 0) pin_tac.
    pin_by HS (9%bv : bv 5) (SOff 305 0) pin_tac.
    pin_by HS (10%bv : bv 5) (SOff 309 0) pin_tac.
    add_fact HS 303%nat 4096 140737479966720 E303 ltac:(lia).
    add_fact HS 304%nat 0 67108863 E304 ltac:(lia).
    add_fact HS 305%nat 0 65535 E305 ltac:(lia).
    add_fact HS 309%nat 134272 134292 E309 ltac:(lia).
    ra_join_win HS ss_J 700%nat ql_deadsJ_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RT HS.
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|]. split; [exact Hpin|]. split; [exact Hrq|].
    exists (cur + 1), 0, bud, (c + 1), b0, 0. s1_fin.
  + (* rem <> 1: 0x7e74c-0x7e770, the UBSan test of cur + 2, the check of cur + 1, lbu a1, lead = b1 << 8 | b0 *)
    s1_in_byte HJ3 LAWS HAR Hpin Hpin3 Hrq FP0 (mkRTCX ly S W regs mem md p n E0 T) (c + 1) b1 PB1 A1.
    replace (p + (c + 1)) with (cur + 1) in A1 by lia. pose proof (proj1 PB1) as R1.
    add_atom_win HS 321%nat (Z_to_bv 64 b1) E321.
    add_fact HS 321%nat 0 255 E321 ltac:(lia).
    in_region HS (YP09.mkRegion (Some 300%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 321 0))]) Ecur AG.
    rd_run HS HJ3 AG Ecur E32n Hpin3 Hrq. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    (* 0x7e774 bne s10,s6 *)
    br_split HS Hc3.
    all: hc_bool Hc3 ltac:(fun H => hc_atom H 301%nat rem Erem ltac:(lia)); hc_prop Hc3.
    * (* P3, rem >= 3: 0x7e7c4-0x7e7fc, the UBSan test of cur + 3, the check of cur + 2, lbu a0,
         a0 = 4 * (b2 mod 6) *)
      s1_in_byte HJ3 LAWS HAR Hpin Hpin3 Hrq FP0 (mkRTCX ly S W regs mem md p n E0 T) (c + 2) b2 PB2 A2.
      replace (p + (c + 2)) with (cur + 2) in A2 by lia. pose proof (proj1 PB2) as R2.
      pose proof (qd_mod6_range b2 R2) as Rsel.
      add_atom_win HS 322%nat (Z_to_bv 64 b2) E322.
      add_fact HS 322%nat 0 255 E322 ltac:(lia).
      in_region HS (YP09.mkRegion (Some 300%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 322 0))]) Ecur AG.
      rd_run_to HS HJ3 AG Ecur E32n Hpin3 Hrq 0x7e800. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      (* 0x7e800 bltu s9,a0: a0 to the atom 310 = 4 * (b2 mod 6) in [0, 20] *)
      add_atom_win HS 310%nat (Z_to_bv 64 (4 * (b2 mod 6))) E310.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      pin_by HS (10%bv : bv 5) (SOff 310 0)
        ltac:(rewrite sv_denot_SOff0, E310, denot_lit_U; f_equal; symmetry; exact (U_qd_sel4 _ 322 b2 E322 R2)).
      add_fact HS 310%nat 0 20 E310 ltac:(lia).
      (* 0x7e800 not taken; 0x7e804-0x7e810 *)
      pl_run_to HS HJ3 AG 0x7e78c. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      add_atom_win HS 303%nat (Z_to_bv 64 (cur + 3)) E303.
      add_atom_win HS 304%nat (Z_to_bv 64 (rem - 3)) E304.
      add_atom_win HS 305%nat (Z_to_bv 64 (256 * b1 + b0)) E305.
      add_atom_win HS 309%nat (Z_to_bv 64 (134272 + 4 * (b2 mod 6))) E309.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      pin_by HS (8%bv : bv 5) (SOff 303 0) pin_tac.
      pin_by HS (26%bv : bv 5) (SOff 304 0) pin_tac.
      pin_by HS (9%bv : bv 5) (SOff 305 0)
        ltac:(rewrite sv_denot_SOff0, E305; symmetry; exact (denot_qd_lead _ 321 320 b1 b0 E321 E320 R1 R0)).
      pin_by HS (10%bv : bv 5) (SOff 309 0) pin_tac.
      add_fact HS 303%nat 4096 140737479966720 E303 ltac:(lia).
      add_fact HS 304%nat 0 67108863 E304 ltac:(lia).
      add_fact HS 305%nat 0 65535 E305 ltac:(lia).
      add_fact HS 309%nat 134272 134292 E309 ltac:(lia).
      ra_join_win HS ss_J 700%nat ql_deadsJ_bv ltac:(idtac).
      rb HS AG E10 E11 E32 E10n E11n E32n.
      rt_hand RT HS.
      split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|]. split; [exact Hpin|]. split; [exact Hrq|].
      exists (cur + 3), (rem - 3), bud, (c + 3), (256 * b1 + b0), (b2 mod 6). s1_fin.
    * (* P2, rem = 2: 0x7e778 *)
      pl_run_to HS HJ3 AG 0x7e78c. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      add_atom_win HS 303%nat (Z_to_bv 64 (cur + 2)) E303.
      add_atom_win HS 304%nat (Z_to_bv 64 0) E304.
      add_atom_win HS 305%nat (Z_to_bv 64 (256 * b1 + b0)) E305.
      add_atom_win HS 309%nat (Z_to_bv 64 (134272 + 4 * 0)) E309.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      pin_by HS (8%bv : bv 5) (SOff 303 0) pin_tac.
      pin_by HS (26%bv : bv 5) (SOff 304 0) pin_tac.
      pin_by HS (9%bv : bv 5) (SOff 305 0)
        ltac:(rewrite sv_denot_SOff0, E305; symmetry; exact (denot_qd_lead _ 321 320 b1 b0 E321 E320 R1 R0)).
      pin_by HS (10%bv : bv 5) (SOff 309 0) pin_tac.
      add_fact HS 303%nat 4096 140737479966720 E303 ltac:(lia).
      add_fact HS 304%nat 0 67108863 E304 ltac:(lia).
      add_fact HS 305%nat 0 65535 E305 ltac:(lia).
      add_fact HS 309%nat 134272 134292 E309 ltac:(lia).
      ra_join_win HS ss_J 700%nat ql_deadsJ_bv ltac:(idtac).
      rb HS AG E10 E11 E32 E10n E11n E32n.
      rt_hand RT HS.
      split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|]. split; [exact Hpin|]. split; [exact Hrq|].
      exists (cur + 2), 0, bud, (c + 2), (256 * b1 + b0), 0. s1_fin.
Qed.
End c.
End b.
