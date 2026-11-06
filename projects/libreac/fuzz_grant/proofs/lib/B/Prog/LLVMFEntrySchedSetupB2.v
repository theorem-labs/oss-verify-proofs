(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupB2), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedSetupB2.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySchedSetupB2.v, ported from a working branch 7c8c67da870 (blob 0f78597c476): image B reads the period's last three bytes in an out-of-line block (0x81e98 .. 0x81f44) that jumps back into 0x81a30 / 0x81a34 / 0x81a38; image B keeps the bytes left in s7 and the bytes left less two in s2 (image A: s8 only), the cursor in s11 and in spill slot 48 (image A: s7 and slot 88), and loads the shadow offset from spill slot 144 before every check (image A: s5); each byte read is preceded by a UBSan pointer-overflow guard whose taken side is the trap 0x81f48; the callee contract is GrantBContracts.v's tb_reac_headamp_tx_set_resweep_spec, which has no bytes_ok premise. *)

(* Segment B2 of the scheduler's setup in fuzz_grant's entry function
   LLVMFuzzerTestOneInput on the ASan+UBSan build (image B; LLVMFEntrySchedSetupDefs.v,
   `sch_segB2_stmt`): from 0x819c0, the return of reac_headamp_tx_arm_scene when two or
   more input bytes were left (`GI_sch1b`), to 0x81a50, the return of
   reac_headamp_tx_set_resweep (`GI_sch2`).

   The block reads the four bytes of the re-assert period that are there (bytes 2..5
   from the cursor of 0x81944; 0 for each one past the end of the input): byte 2 at
   0x819e4, then, in the out-of-line block, byte 3 at 0x81eb4, byte 4 at 0x81eec and
   byte 5 at 0x81f30. Each read is preceded by the UBSan pointer-overflow guard
   `addi aX,s11,1; bgeu 1,aX,0x81f48` (0x819c4..0x819cc, 0x81e98..0x81e9c,
   0x81ecc..0x81ed4, 0x81f14..0x81f18), whose taken side is the trap `unimp` at 0x81f48,
   and by the check of its shadow byte (0x819d0..0x819e0, 0x81ea0..0x81eb0,
   0x81ed8..0x81ee8, 0x81f1c..0x81f2c; the shadow offset is loaded from slot 144 each
   time). The block jumps back to 0x81a30, 0x81a34 or 0x81a38, builds the period with
   slli/or and slliw (0x81a38..0x81a44), and calls reac_headamp_tx_set_resweep
   (t, period) at 0x81a4c. The walk is split on the number of bytes left: 2, 3, 4, 5, or
   6 and more. For 2..5 the bytes left (s7) and the bytes left less two (s2) are known
   numbers and are seated as literals, so the walk engine decides every branch on them;
   for 6 and more they are atoms with interval facts, which decide the branches too.

   The trap guards: the cursor is atom 33 with the interval fact [4096, 2^47 - 2^25],
   so `1 < cursor + k` holds and the engine takes each guard as not taken.

   The error path: each shadow check branches, when its shadow byte is not 0, to the
   slow check at 0x81ff4, 0x82004, 0x82014 or 0x82024, and from there to the report of
   the memory-checking runtime (__asan_report_load1) at 0x82000, 0x82010, 0x82020 or
   0x82030. The shadow entry `b2_SH` (the input bytes from the cursor + 2 on, inside the
   caller's input block) makes the walk engine take each check as passed, so no report
   is reached. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
YC1g YC1h YC1i YC45 YC85 GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySchedSetupDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantModel GrantSlotPlan SlotNeeds_c HeadampSched SegSetModel Seg_sched_setup Seg_sched_lib
NextLemmas reac_headamp_tx_set_resweep_c reac_headamp_tx_arm_scene_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the value the block builds in a1 ---- *)
Lemma b2_lor16 : forall lo hi, 0 <= lo < 65536 -> 0 <= hi -> Z.lor lo (Z.shiftl hi 16) = lo + Z.shiftl hi 16.
Proof.
intros lo hi Hlo Hhi. pose proof (Seg_sched_setup.land_low_high lo hi Hlo) as H0.
rewrite <- (Z.lxor_lor lo _ H0), <- (Z.add_nocarry_lxor lo _ H0). reflexivity.
Qed.

Lemma b2_zcanon32 : forall z, zcanon z mod 4294967296 = z mod 4294967296.
Proof. intros z. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. apply GrantModel.mod64_mod32. Qed.

(* lo | (hi << 8), two bytes. *)
Lemma b2_U_lo : forall E (n1 n0 : nat) b0 b1,
  ew E n0 = Z_to_bv 64 b0 -> ew E n1 = Z_to_bv 64 b1 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0)) = b0 + 256 * b1.
Proof.
intros E n1 n0 b0 b1 H0 H1 R0 R1.
rewrite !U_SAlu, (U_atom E n1 b1 H1), (U_atom E n0 b0 H0), (U_lit E 8) by lia. cbn [zalu_raw].
change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b1 * 256)) by (unfold M64; lia).
replace (b1 * 256) with (256 * b1) by lia. rewrite Seg_sched_setup.lor256 by lia.
apply zcanon_id. unfold M64. lia.
Qed.

(* Three bytes left: a1 = b2 (0x819e4, then 0x81a30 .. 0x81a44). *)
Lemma b2_U3 : forall E b2, ew E 34 = Z_to_bv 64 b2 -> 0 <= b2 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SLit 0) (SOff 34 0)) (SLit 0)) = b2.
Proof.
intros E b2 H2 R2. rewrite !U_SAlu, (U_lit E 0), (U_atom E 34 b2 H2) by lia. cbn [zalu_raw].
rewrite Z.lor_0_l, (zcanon_id b2) by (unfold M64; lia). rewrite Z.lor_0_r. apply zcanon_id. unfold M64. lia.
Qed.

(* Four bytes left: a1 = b2 + 256 b3 (0x81eb4, then 0x81a38 .. 0x81a44). *)
Lemma b2_U4 : forall E b2 b3, ew E 34 = Z_to_bv 64 b2 -> ew E 35 = Z_to_bv 64 b3 ->
  0 <= b2 < 256 -> 0 <= b3 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 34 0)) (SLit 0)) = b2 + 256 * b3.
Proof.
intros E b2 b3 H2 H3 R2 R3. rewrite U_SAlu, (b2_U_lo E 35 34 b2 b3 H2 H3 R2 R3), (U_lit E 0) by lia.
cbn [zalu_raw]. rewrite Z.lor_0_r. apply zcanon_id. unfold M64. lia.
Qed.

(* Five bytes left: a1 = b2 + 256 b3 + 65536 b4 (the slliw of a byte is a slli). *)
Lemma b2_U5 : forall E b2 b3 b4, ew E 34 = Z_to_bv 64 b2 -> ew E 35 = Z_to_bv 64 b3 -> ew E 36 = Z_to_bv 64 b4 ->
  0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 34 0))
         (SAlu ALU_SLL (SAlu ALU_OR (SLit 0) (SOff 36 0)) (SLit 16))) = b2 + 256 * b3 + 65536 * b4.
Proof.
intros E b2 b3 b4 H2 H3 H4 R2 R3 R4. rewrite U_SAlu, (b2_U_lo E 35 34 b2 b3 H2 H3 R2 R3).
rewrite !U_SAlu, (U_lit E 0), (U_lit E 16), (U_atom E 36 b4 H4) by lia. cbn [zalu_raw].
rewrite Z.lor_0_l, (zcanon_id b4) by (unfold M64; lia). change (Z.land 16 63) with 16.
rewrite (zcanon_id (Z.shiftl b4 16)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite b2_lor16 by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* Six bytes or more: a1 = (b2 | b3 << 8) | slliw (b4 | b5 << 8, 16), of which the callee
   reads the low four bytes (Seg_sched_setup.lor_per). *)
Lemma b2_U6 : forall E b2 b3 b4 b5,
  ew E 34 = Z_to_bv 64 b2 -> ew E 35 = Z_to_bv 64 b3 -> ew E 36 = Z_to_bv 64 b4 -> ew E 37 = Z_to_bv 64 b5 ->
  0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 34 0))
         (SAluw ALU_SLL (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 36 0)) (SLit 16))) mod 4294967296
  = (b2 + 256 * b3 + 65536 * (b4 + 256 * b5)) mod 4294967296.
Proof.
intros E b2 b3 b4 b5 H2 H3 H4 H5 R2 R3 R4 R5.
rewrite U_SAlu, b2_zcanon32, (b2_U_lo E 35 34 b2 b3 H2 H3 R2 R3).
rewrite U_of_S, S_SAluw, (b2_U_lo E 37 36 b4 b5 H4 H5 R4 R5), (U_lit E 16) by lia. cbn [zalu_raw].
change (Z.land (16 mod 2 ^ 32) 31) with 16.
rewrite (Z.mod_small (b4 + 256 * b5) (2 ^ 32)) by lia.
unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite Seg_sched_setup.lor_per by lia; try (f_equal; lia).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* ---- the model: the period, and the table the call leaves ---- *)
(* The period as fuzz_grant's plain walk reads it (GrantSlotPlan.sched_rd, bytes 2..5
   from the cursor of 0x81944, 0 past the end). *)
Definition sch_per (cx : ecx) : Z :=
  sch_b cx 2 + 256 * sch_b cx 3 + 65536 * (sch_b cx 4 + 256 * sch_b cx 5).

Lemma b2_sch_b_out : forall cx j, sch_L cx <= Z.of_nat j -> sch_b cx j = 0.
Proof. intros cx j H. unfold sch_b, sbat. apply Seg_sched_setup.bat_out. unfold sch_L, c_n in H. lia. Qed.

Lemma b2_T_sched0 : forall cx, GrantSlotPlan.T_sched0 (c_pl cx) =
  reac_headamp_tx_set_resweep_c.set_resweep_T (sch_T1 cx) (Z_to_bv 64 (sch_per cx)).
Proof.
intros cx. unfold GrantSlotPlan.T_sched0, sch_T1, sch_per, sch_b, sbat.
pose proof (Seg_sched_setup.sched_rd_bat (c_pl cx)) as H.
destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] f] p4].
destruct H as (-> & -> & -> & _). rewrite Nat.add_0_r. reflexivity.
Qed.

(* reac_headamp_tx_set_resweep stores the low four bytes of a1 only. *)
Lemma b2_rsw_eq : forall T (a : word) per, bv_unsigned a mod 4294967296 = per mod 4294967296 ->
  reac_headamp_tx_set_resweep_c.set_resweep_T T a = reac_headamp_tx_set_resweep_c.set_resweep_T T (Z_to_bv 64 per).
Proof.
intros T a per H. unfold reac_headamp_tx_set_resweep_c.set_resweep_T. f_equal. f_equal.
rewrite <- (Step.Z_to_bv_lit_self a). apply NextLemmas.le4_eqm. exact H.
Qed.

(* ---- the symbolic state at 0x819c0 ---- *)
(* Atoms: 0..31 the registers at the cut, 32 SHADOW_OFF (spill slot 144), 33 the input
   cursor of 0x81944 (spill slot 48), 34..37 the four bytes of the period (0 past the
   end of the input). s11 is the cursor past the scene's two bytes; s7 (atom 23) holds
   the bytes left and s2 (atom 18) the bytes left less two. *)
Definition b2_x (cx : ecx) : list word :=
  map (Z_to_bv 64) [SHADOW_OFF; SCH_P cx; sch_b cx 2; sch_b cx 3; sch_b cx 4; sch_b cx 5].
Definition b2_E (cx : ecx) (regs : bvmap 5 word) : env := Eimg (Ereg regs (b2_x cx)).
(* The spill slots 48 (the cursor) and 144 (the shadow offset), read only. *)
Definition b2_Rsp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 152 0 0
    [YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 144 (CVal 8 (SOff 32 0))].
(* The input bytes 2 .. m - 1 from the cursor, read only. *)
Definition b2_rin (m : nat) : YP09.region :=
  YP09.mkRegion (Some 33%nat) 2 (Z.of_nat m) 0 0
    (map (fun j => YP09.mkChunk (2 + Z.of_nat j) (CVal 1 (SOff (34 + j) 0))) (seq 0 (m - 2))).
(* s7 (the bytes left) lies in [lo, hi], s2 in [lo - 2, hi - 2]. *)
Definition b2_G (lo hi : Z) : facts :=
  mkFacts [ (18%nat, mkAF (lo - 2) (hi - 2) 0); (23%nat, mkAF lo hi 0);
            (32%nat, mkAF SCH_SB SCH_SB 0); (33%nat, mkAF 4096 140737479966720 0);
            (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0) ] [] [].
Definition b2_sr : list sv := sr_set sr_atoms 27%bv (SOff 33 2).
Definition b2_ss (m : nat) (lo hi : Z) : sstate := mkSS GP_sch1b b2_sr [b2_Rsp; b2_rin m] None (b2_G lo hi).
(* The shadow entry: the input bytes 2 .. m - 1 from the cursor are addressable. *)
Definition b2_SH (m : nat) : list shent := [mkSHE 33 2 (Z.of_nat m)].

(* A run over regions with no write window leaves the memory as it was. *)
Lemma b2_frame_ro : forall E rs (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hr & Hw).
rewrite forallb_forall in Hro. specialize (Hro r Hr). apply Z.leb_le in Hro. lia.
Qed.

(* When the bytes left are a known number l, s2 and s7 are seated as the literals l - 2
   and l, so that the engine decides the branches on them. *)
Lemma b2_pin : forall E ss ms (l : Z),
  st_ok_pi SEGS VAL E ss ms ->
  getr (ms_regs ms) 18 = Z_to_bv 64 (l - 2) -> getr (ms_regs ms) 23 = Z_to_bv 64 l ->
  st_ok_pi SEGS VAL E
    (mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) 18%bv (SLit (l - 2))) 23%bv (SLit l))
       (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l HS H18 H23.
pose proof (st_ok_pi_pin_reg' E ss ms 18%bv (l - 2) HS H18 eq_refl) as H1.
exact (st_ok_pi_pin_reg' E _ ms 23%bv l H1 H23 eq_refl).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis RSW : tb_reac_headamp_tx_set_resweep_spec B.
Let RUN := paj_run B LAWS.

(* The shadow entry the walk uses: the bytes q + lo .. q + hi - 1 inside one block of the
   heap are addressable, so each shadow-byte check on them passes. *)
Lemma b2_shent : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex sch_Bx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS sch_Bx Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex n q b sz lo hi HAR Hin HB Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

(* ---- the seat ---- *)
Lemma b2_seat : forall cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 (m : nat) (lo hi : Z),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  GI_sch1b B MT cx fp k acc ly3 S3 W3 ms3 md3 ->
  (m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6)%nat -> Z.of_nat m <= sch_L cx -> lo <= sch_L cx <= hi -> 2 <= lo ->
  st_ok_pi SEGS VAL (b2_E cx (ms_regs ms3)) (b2_ss m lo hi) (restrict (w_H W3) ms3) /\
  sh_ok SEGS sch_Bx (b2_SH m) (b2_E cx (ms_regs ms3)) (mrestrict (w_H W3) (ms_mem ms3)) /\
  4096 <= SCH_P cx /\ SCH_P cx + sch_L cx <= 140737479966720.
Proof.
intros cx fp k acc ly3 S3 W3 ms3 md3 m lo hi HB HJ HFR HI Hm HmL Hlohi Hlo.
destruct HI as (t & HC & HL2 & R20 & R21 & R24 & R27 & R18 & R23 & HTAB).
destruct HC as (HBODY & Hk & Hacc & HBLK & HCN & R19 & R22 & S8 & S40 & S48 & S64 & S72 & S96 & S112 &
  S128 & S136 & S144 & S152 & HWS & HST & HREL & HI1).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL & Hlen & HIN).
pose proof HB as (HPRE & H10 & H11 & Hpn & _).
pose proof HJ as (HAR & _).
pose proof (ge_sp_facts B MT cx HB) as (Hal16 & Hslo & Hshi & Hsp1).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (Seg_sched_setup.pos_raw_le (c_pl cx)) as Hpr.
assert (Hn0 : 0 < c_n cx) by (unfold sch_L, c_n in *; lia).
assert (HLn : sch_L cx <= c_n cx) by (unfold sch_L; lia).
assert (Hin0 : In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))
  by (destruct Hpn as [(Hz & _) | (_ & Hin0)]; [lia | exact Hin0]).
assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
  by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos' (c_n cx) ltac:(lia)) as [_ Hrq].
assert (HPL : SCH_P cx + sch_L cx = c_p cx + c_n cx) by (unfold SCH_P, sch_L; lia).
assert (HP0 : 4096 <= SCH_P cx) by (unfold SCH_P; lia).
assert (HP1 : SCH_P cx + sch_L cx <= 140737479966720) by lia.
assert (Hms : restrict (w_H W3) ms3 =
  mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_sch1b)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (B2r : 0 <= sch_b cx 2 < 256) by apply sbat_range.
assert (B3r : 0 <= sch_b cx 3 < 256) by apply sbat_range.
assert (B4r : 0 <= sch_b cx 4 < 256) by apply sbat_range.
assert (B5r : 0 <= sch_b cx 5 < 256) by apply sbat_range.
set (E := b2_E cx (ms_regs ms3)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold E, b2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (b2_x cx) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, b2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (E18 : ew E 18 = Z_to_bv 64 (sch_L cx - 2)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E23 : ew E 23 = Z_to_bv 64 (sch_L cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (SCH_P cx)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (sch_b cx 2)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (sch_b cx 3)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (sch_b cx 4)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (sch_b cx 5)) by exact (EX 5%nat ltac:(lia)).
assert (EB : forall j, (j < 4)%nat -> ew E (34 + j) = Z_to_bv 64 (sch_b cx (2 + j))).
{ intros j Hj. destruct j as [|[|[|[|j]]]]; [exact E34 | exact E35 | exact E36 | exact E37 | lia]. }
assert (HS0 : st_ok_pi SEGS VAL E (mkSS GP_sch1b sr_atoms [b2_Rsp; b2_rin m] None (b2_G lo hi))
                (restrict (w_H W3) ms3)).
{ rewrite Hms. apply pa_entry_st_ok_full.
  - unfold E, b2_E. apply regs_ok_Eimg_Ereg.
  - destruct Hm as [->|[->|[->|[->| ->]]]]; vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold YP09.region_ok, b2_Rsp.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 48 8 (SOff 33 0) (SCH_P cx)).
        -- rewrite ge_sv_SOff0, E33. reflexivity.
        -- cbn. lia.
        -- cbn. lia.
        -- exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S48).
      * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 144 8 (SOff 32 0) SHADOW_OFF).
        -- rewrite ge_sv_SOff0, E32. reflexivity.
        -- cbn. unfold SHADOW_OFF. lia.
        -- cbn. lia.
        -- exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S144).
    + unfold YP09.region_ok, b2_rin.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite E33, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      apply (chunk_ok_val SEGS E _ (SCH_P cx) (2 + Z.of_nat j) 1 (SOff (34 + j) 0) (sch_b cx (2 + j))).
      * rewrite ge_sv_SOff0, (EB j ltac:(lia)). reflexivity.
      * pose proof (sbat_range (c_pl cx) (2 + j)). unfold sch_b. change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      * cbn. lia.
      * set (pr := GrantSlotPlan.pos_raw (c_pl cx)) in *.
        assert (Hj' : (pr + (2 + j) < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
          by (rewrite length_map; unfold sch_L, c_n in *; lia).
        destruct (HIN (pr + (2 + j))%nat Hj') as [Hv _].
        unfold SCH_P. fold pr.
        replace (c_p cx + Z.of_nat pr + (2 + Z.of_nat j)) with (c_p cx + Z.of_nat (pr + (2 + j))) by lia.
        replace (sch_b cx (2 + j)) with (nth (pr + (2 + j)) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0);
          [exact Hv|].
        unfold sch_b, sbat. fold pr. rewrite Seg_sched_setup.bat_in by (rewrite length_map in Hj'; exact Hj').
        unfold GrantSlotPlan.pbz. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hj'.
        apply (map_nth (fun b : byte => bv_unsigned b)).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split.
    unfold YP09.extent_disjoint, b2_Rsp, b2_rin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
    rewrite E9, E33, !unsigned_lit_small by lia. right. lia.
  - split; [|split; exact I].
    unfold b2_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, E23, E32, E33, E34, E35, E36, E37.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SCH_SB, SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (HS1 : st_ok_pi SEGS VAL E (b2_ss m lo hi) (restrict (w_H W3) ms3)).
{ apply (st_ok_pi_set_reg E _ _ 27%bv (SOff 33 2) HS0).
  - intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
  - cbn [restrict ms_regs sv_denot]. rewrite E33, unsigned_lit_small by lia. exact R27. }
split; [exact HS1|].
split; [|split; [exact HP0 | exact HP1]].
unfold sh_ok, b2_SH. apply Forall_cons; [|apply Forall_nil].
apply (b2_shent ly3 S3 W3 (ms_mem ms3) md3 E 33 (SCH_P cx) (c_p cx) (c_n cx) 2 (Z.of_nat m) HAR Hin).
- unfold sch_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
- apply (U_atom E 33 (SCH_P cx) E33). lia.
- unfold SCH_P. lia.
- lia.
- lia.
Qed.

(* ---- the call of reac_headamp_tx_set_resweep and the cut at its return ---- *)
Lemma b2_pres : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

(* acallee_saved of a register named by its number. *)
Ltac b2_cs :=
  unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end;
  lia.

(* At the call (pc = reac_headamp_tx_set_resweep, ra = 0x81a50) with the memory of the
   cut 0x819c0 and the registers the block leaves, the run reaches POST. *)
Lemma b2_call : forall POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) md3 t (regs : bvmap 5 word) mem md,
  ge_from B MT POST (GI_sch2 B MT) ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  sch_common B MT cx fp GP_sch1b GSH_c k acc ly3 S3 W3 ms3 t ->
  gtab B cx ly3 S3 W3 ms3 t (sch_T1 cx) ->
  (forall x, mem x = ms_mem ms3 x) ->
  getr regs 1 = Z_to_bv 64 (BASE + GP_sch2) ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 10 = w64 t ->
  bv_unsigned (getr regs 11) mod 4294967296 = sch_per cx mod 4294967296 ->
  getr regs 19 = w64 (gSH cx fp) -> getr regs 20 = w64 t -> getr regs 21 = w64 (sch_b cx 0) ->
  getr regs 22 = w64 (gF cx fp + GO_CH) -> getr regs 23 = w64 (Z.max (sch_L cx - 6) 0) ->
  getr regs 24 = w64 (sch_b cx 1) ->
  (6 <= sch_L cx -> getr regs 27 = w64 (SCH_P cx + 6)) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_set_resweep)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
intros POST cx fp k acc ly3 S3 W3 ms3 md3 t regs mem md H2 HB HJ HJm HFR HMO HC HT1 HM
  R1 R2 R8 R9 R3 R4 R10 R11 R19 R20 R21 R22 R23 R24 R27.
assert (HAG : forall a, aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a)
  by (intros a; unfold aview, YP09.mbyte, mrestrict; rewrite HM; reflexivity).
pose proof HC as (HBODY & Hk & Hacc & HBLK & HCN & _ & _ & S8 & S40 & S48 & S64 & S72 & S96 & S112 &
  S128 & S136 & S144 & S152 & HWS & HST & HREL & HI1).
pose proof HBODY as (_ & _ & _ & _ & _ & _ & _ & HSV & HSH & HFL & Hlen & HIN).
pose proof HT1 as (Htin & Ht0 & HTl & _).
pose proof (proj1 HJm) as HARm.
pose proof HSV as (Sra & Ssv).
pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (_ & Lws & Lst & _).
assert (HFPt : forall a, inFP [(t + 452, t + 460)] a -> t <= a < t + 460)
  by (intros a (r & [<-|[]] & Hr); cbn [fst snd] in Hr; lia).
assert (HT1m : gtab B cx ly3 S3 W3 (mkst regs (Z_to_bv 64 0) mem (seg_rom SEGS)) t (sch_T1 cx)).
{ destruct HT1 as (T1 & T2 & T3 & T4). split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
  intros i Hi H438 H439 H451. cbn [ms_mem mkst]. rewrite HAG. exact (T4 i Hi H438 H439 H451). }
eapply (gcall B MT LAWS STK_reac_headamp_tx_set_resweep [(t + 452, t + 460)]
  (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
     obj_at SEGS (mrestrict (w_H W3) mem') t LAY_TX
       (tx_vals (reac_headamp_tx_set_resweep_c.set_resweep_T (sch_T1 cx) (getr regs 11))))
  _ GP_sch2 POST cx fp k ly3 S3 W3 regs mem md HB HJm R2 R8 R3 R4 R1).
- unfold GP_sch2. lia.
- reflexivity.
- rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) mem) _ (fun j _ => HAG _)). exact Sra.
- rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) mem) _ (fun j _ => HAG _)).
  specialize (Ssv 0 ltac:(lia)). rewrite Z.mul_0_r, Z.sub_0_r in Ssv. rewrite Ssv. unfold s0Z.
  do 3 f_equal; apply bv_eq; reflexivity.
- unfold STK_reac_headamp_tx_set_resweep, ESTACK. lia.
- intros a Ha. exists t, 460. split; [exact Htin|].
  split; [exact (sch_notin_base B LAWS cx ly3 S3 W3 mem md t HARm HBLK)|].
  pose proof (HFPt a Ha). change (req_size 460) with 460. lia.
- intros HPRE.
  exact (RSW ly3 S3 W3 regs mem md (gch cx) t (sch_T1 cx) HPRE R10 Htin HTl
           (gtab_obj B cx ly3 S3 W3 _ t (sch_T1 cx) HT1m)).
- intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & Hobj2).
  assert (HK0 : ge_keep cx fp W3 [] (ms_mem ms3) mem2).
  { apply (ge_keep_trans cx fp W3 [] (ms_mem ms3) mem mem2).
    - intros a _. exact (HAG a).
    - exact (sch_keep_call B MT LAWS cx fp W3 ms3 ly3 S3 md3 k t STK_reac_headamp_tx_set_resweep
        [(t + 452, t + 460)] mem md mem2 md2 0 HB HJ HFR HBLK HARm HFPt HJc). }
  assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r)
    by (intros r Hr; exact (b2_pres regs regs2 r HP Hr)).
  apply (H2 cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + GP_sch2)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
  set (ms := mkst regs2 (Z_to_bv 64 (BASE + GP_sch2)) mem2 (seg_rom SEGS)).
  assert (MR : ms_regs ms = regs2) by reflexivity.
  assert (KS : forall off v, 0 <= off <= 184 -> gslot cx W3 ms3 off v -> gslot cx W3 ms off v)
    by (intros off v Hoff Hv; exact (ge_gslot_keep B MT cx fp W3 HB [] ms3 ms off v HK0 ltac:(lia) ltac:(lia) Hv)).
  exists t. unfold sch_common. rewrite MR.
  split.
  { split.
    { unfold ge_body. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split.
      { unfold gregs. rewrite MR.
        rewrite (PR 2%bv), (PR 8%bv), (PR 9%bv), (PR 3%bv), (PR 4%bv) by b2_cs.
        split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R3 | exact R4]. }
      split; [exact (ge_gsaved_keep B MT cx fp W3 HB [] ms3 ms HK0 HSV)|].
      split; [refine (ge_gshadow_keep cx fp W3 [] ms3 ms GSH_c HK0 _ HSH);
              rewrite Hlen; unfold GE_NSH; change (fs_frame_bytes GE_CID) with 1024; lia|].
      split; [exact (ge_flag_keep cx fp W3 [] ms3 ms HK0 HFL)|].
      split; [exact Hlen|].
      exact (ge_input_keep cx fp W3 [] ms3 ms HK0 HIN). }
    split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact HCN|].
    split; [rewrite (PR 19%bv) by b2_cs; exact R19|].
    split; [rewrite (PR 22%bv) by b2_cs; exact R22|].
    split; [exact (KS 8 _ ltac:(lia) S8)|].
    split; [exact (KS 40 _ ltac:(lia) S40)|].
    split; [exact (KS 48 _ ltac:(lia) S48)|].
    split; [exact (KS 64 _ ltac:(lia) S64)|].
    split; [exact (KS 72 _ ltac:(lia) S72)|].
    split; [exact (KS 96 _ ltac:(lia) S96)|].
    split; [exact (KS 112 _ ltac:(lia) S112)|].
    split; [exact (KS 128 _ ltac:(lia) S128)|].
    split; [exact (KS 136 _ ltac:(lia) S136)|].
    split; [exact (KS 144 _ ltac:(lia) S144)|].
    split; [exact (KS 152 _ ltac:(lia) S152)|].
    split; [refine (ge_gfarr_keep cx fp W3 [] ms3 ms GO_WAS _ HK0 _ _ HWS);
            [unfold GO_WAS; lia | rewrite Lws; change (fs_frame_bytes GE_CID) with 1024; unfold GO_WAS; lia]|].
    split; [refine (ge_gfarr_keep cx fp W3 [] ms3 ms GO_SET _ HK0 _ _ HST);
            [unfold GO_SET; lia | rewrite Lst; change (fs_frame_bytes GE_CID) with 1024; unfold GO_SET; lia]|].
    split; [exact HREL | exact HI1]. }
  split; [rewrite (PR 20%bv) by b2_cs; exact R20|].
  split; [rewrite (PR 21%bv) by b2_cs; exact R21|].
  split; [rewrite (PR 24%bv) by b2_cs; exact R24|].
  split; [rewrite (PR 23%bv) by b2_cs; exact R23|].
  split; [intros H6; rewrite (PR 27%bv) by b2_cs; exact (R27 H6)|].
  rewrite (b2_rsw_eq _ _ _ R11), <- b2_T_sched0 in Hobj2.
  exact (obj_gtab B cx ly3 S3 W3 ms t _ Htin Ht0 (proj2 (HeadampSched.sched0_ok (c_pl cx))) Hobj2).
Qed.

(* ---- the walk ---- *)
(* The write windows of the walk: none. *)
Ltac b2_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Ltac b2_reg HS r := let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q.

(* At the call: the memory is the cut's (the walk writes nothing), the registers are
   read off the symbolic state; b2_call takes over. Leaves the goals for a1, s7 and s11,
   with X34 .. X37 the four bytes in the run's environment. *)
Ltac b2_land ms3 H2 HB HJ0 HFR HMO HC HTAB HS HJ EE G2 G8 G9 G3 G4 R19 R20 R21 R22 R24 E34 E35 E36 E37 :=
  lazymatch type of HS with st_ok _ ?E1 ?ss1 (restrict _ ?ms) =>
    let HM := fresh "HM" in
    assert (HM : forall x, ms_mem ms x = ms_mem ms3 x)
      by (intros x;
          repeat match goal with
            | Hf : frame_of _ ?rs (ms_mem ?m1) (ms_mem ?m2) |- ms_mem ?m2 x = ms_mem ms3 x =>
                rewrite (b2_frame_ro _ rs _ _ ltac:(vm_compute; reflexivity) Hf x)
            end;
          reflexivity);
    let v34 := lazymatch type of E34 with _ = ?v => v end in
    let v35 := lazymatch type of E35 with _ = ?v => v end in
    let v36 := lazymatch type of E36 with _ = ?v => v end in
    let v37 := lazymatch type of E37 with _ = ?v => v end in
    assert (X34 : ew E1 34%nat = v34) by (cbn [ew ewset Nat.eqb]; exact E34);
    assert (X35 : ew E1 35%nat = v35) by (cbn [ew ewset Nat.eqb]; exact E35);
    assert (X36 : ew E1 36%nat = v36) by (cbn [ew ewset Nat.eqb]; exact E36);
    assert (X37 : ew E1 37%nat = v37) by (cbn [ew ewset Nat.eqb]; exact E37);
    let Q11 := fresh "Q11" in
    pose proof (st_ok_restrict_reg _ _ E1 ss1 ms 11%bv HS) as Q11;
    let e := eval vm_compute in (sr_get (ss_regs ss1) 11%bv) in change (sr_get (ss_regs ss1) 11%bv) with e in Q11;
    cbn [ms_regs restrict mkst] in Q11;
    pmkst HS; rewrite pa_sigma_reac_headamp_tx_set_resweep;
    eapply (b2_call _ _ _ _ _ _ _ _ ms3 _ _ (ms_regs ms) (ms_mem ms) _ H2 HB HJ0 HJ HFR HMO HC HTAB HM);
    [ b2_reg HS (1%bv : bv 5); reflexivity
    | b2_reg HS (2%bv : bv 5); rewrite (EE 2%nat 2%bv eq_refl); exact G2
    | b2_reg HS (8%bv : bv 5); rewrite (EE 8%nat 8%bv eq_refl); exact G8
    | b2_reg HS (9%bv : bv 5); rewrite (EE 9%nat 9%bv eq_refl); exact G9
    | b2_reg HS (3%bv : bv 5); rewrite (EE 3%nat 3%bv eq_refl); exact G3
    | b2_reg HS (4%bv : bv 5); rewrite (EE 4%nat 4%bv eq_refl); exact G4
    | b2_reg HS (10%bv : bv 5); rewrite (EE 20%nat 20%bv eq_refl); exact R20
    | rewrite Q11
    | b2_reg HS (19%bv : bv 5); rewrite (EE 19%nat 19%bv eq_refl); exact R19
    | b2_reg HS (20%bv : bv 5); rewrite (EE 20%nat 20%bv eq_refl); exact R20
    | b2_reg HS (21%bv : bv 5); rewrite (EE 21%nat 21%bv eq_refl); exact R21
    | b2_reg HS (22%bv : bv 5); rewrite (EE 22%nat 22%bv eq_refl); exact R22
    | b2_reg HS (23%bv : bv 5)
    | b2_reg HS (24%bv : bv 5); rewrite (EE 24%nat 24%bv eq_refl); exact R24
    | intros ?; b2_reg HS (27%bv : bv 5) ]
  end.

(* Seat the cut for a known number of bytes left l (2 .. 5): s2 and s7 as literals. *)
Ltac b2_seat_pin cx fp k acc ly3 S3 W3 ms3 md3 l HB HJ HFR HI R18 R23 HL :=
  let HS0 := fresh "HS0" in let SHOK := fresh "SHOK" in let HP0 := fresh "HP0" in let HP1 := fresh "HP1" in
  destruct (b2_seat cx fp k acc ly3 S3 W3 ms3 md3 l (Z.of_nat l) (Z.of_nat l) HB HJ HFR HI
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (HS0 & SHOK & HP0 & HP1);
  let HS := fresh "HS" in
  pose proof (b2_pin _ _ _ (Z.of_nat l) HS0
                ltac:(cbn [restrict ms_regs]; rewrite R18, HL; reflexivity)
                ltac:(cbn [restrict ms_regs]; rewrite R23, HL; reflexivity)) as HS;
  clear HS0;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ =>
    let v := eval vm_compute in ss3 in change ss3 with v in HS end.

Theorem sch_segB2 : forall POST, sch_segB2_stmt B MT POST.
Proof.
intros POST H2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
pose proof HI as HI0. destruct HI0 as (t & HC & HL2 & R20 & R21 & R24 & R27 & R18 & R23 & HTAB).
pose proof HC as (HBODY & Hk & Hacc & HBLK & HCN & R19 & R22 & _).
pose proof HBODY as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & _).
assert (B2r : 0 <= sch_b cx 2 < 256) by apply sbat_range.
assert (B3r : 0 <= sch_b cx 3 < 256) by apply sbat_range.
assert (B4r : 0 <= sch_b cx 4 < 256) by apply sbat_range.
assert (B5r : 0 <= sch_b cx 5 < 256) by apply sbat_range.
assert (HLn : sch_L cx < 2 ^ 26) by (unfold sch_L, c_n in *; lia).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (b2_E cx (ms_regs ms3)) n = getr (ms_regs ms3) r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  unfold b2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 6)%nat -> ew (b2_E cx (ms_regs ms3)) (32 + j) = nth j (b2_x cx) (Z_to_bv 64 0)).
{ intros j Hj. unfold b2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E23 : ew (b2_E cx (ms_regs ms3)) 23 = Z_to_bv 64 (sch_L cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E33 : ew (b2_E cx (ms_regs ms3)) 33 = Z_to_bv 64 (SCH_P cx)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew (b2_E cx (ms_regs ms3)) 34 = Z_to_bv 64 (sch_b cx 2)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew (b2_E cx (ms_regs ms3)) 35 = Z_to_bv 64 (sch_b cx 3)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew (b2_E cx (ms_regs ms3)) 36 = Z_to_bv 64 (sch_b cx 4)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew (b2_E cx (ms_regs ms3)) 37 = Z_to_bv 64 (sch_b cx 5)) by exact (EX 5%nat ltac:(lia)).
pose proof HJ as HJ0.
assert (HLc : sch_L cx = 2 \/ sch_L cx = 3 \/ sch_L cx = 4 \/ sch_L cx = 5 \/ 6 <= sch_L cx) by lia.
destruct HLc as [HL|[HL|[HL|[HL|HL]]]].
- (* two bytes left: beqz s2 at 0x819c0 is taken (0x81a24); the period is 0 *)
  b2_seat_pin cx fp k acc ly3 S3 W3 ms3 md3 2%nat HB HJ HFR HI R18 R23 HL.
  remember (b2_E cx (ms_regs ms3)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  paj_run_tok RUN HS HJ SHOK sch_span; [b2_awr|].
  b2_land ms3 H2 HB HJ0 HFR HMO HC HTAB HS HJ EE G2 G8 G9 G3 G4 R19 R20 R21 R22 R24 E34 E35 E36 E37.
  + unfold sch_per.
    rewrite (b2_sch_b_out cx 2), (b2_sch_b_out cx 3), (b2_sch_b_out cx 4), (b2_sch_b_out cx 5) by lia.
    cbn [sv_denot]. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Z.max_r by lia. reflexivity.
  + exfalso. lia.
- (* three bytes left: 0x819e4 reads byte 2; bne s2,1 at 0x819f4 is not taken (0x819f8) *)
  b2_seat_pin cx fp k acc ly3 S3 W3 ms3 md3 3%nat HB HJ HFR HI R18 R23 HL.
  remember (b2_E cx (ms_regs ms3)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  paj_run_tok RUN HS HJ SHOK sch_span; [b2_awr|].
  b2_land ms3 H2 HB HJ0 HFR HMO HC HTAB HS HJ EE G2 G8 G9 G3 G4 R19 R20 R21 R22 R24 E34 E35 E36 E37.
  + pose proof (b2_U3 _ _ X34 B2r) as HX. unfold U in HX. rewrite HX. unfold sch_per.
    rewrite (b2_sch_b_out cx 3), (b2_sch_b_out cx 4), (b2_sch_b_out cx 5) by lia. f_equal. lia.
  + rewrite Z.max_r by lia. reflexivity.
  + exfalso. lia.
- (* four bytes left: 0x81eb4 reads byte 3; beqz a4 at 0x81ec8 is taken (0x81f08) *)
  b2_seat_pin cx fp k acc ly3 S3 W3 ms3 md3 4%nat HB HJ HFR HI R18 R23 HL.
  remember (b2_E cx (ms_regs ms3)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  paj_run_tok RUN HS HJ SHOK sch_span; [b2_awr|].
  b2_land ms3 H2 HB HJ0 HFR HMO HC HTAB HS HJ EE G2 G8 G9 G3 G4 R19 R20 R21 R22 R24 E34 E35 E36 E37.
  + pose proof (b2_U4 _ _ _ X34 X35 B2r B3r) as HX. unfold U in HX. rewrite HX. unfold sch_per.
    rewrite (b2_sch_b_out cx 4), (b2_sch_b_out cx 5) by lia. f_equal. lia.
  + rewrite Z.max_r by lia. reflexivity.
  + exfalso. lia.
- (* five bytes left: 0x81eec reads byte 4; bne a4,a5 at 0x81efc is not taken (0x81f00) *)
  b2_seat_pin cx fp k acc ly3 S3 W3 ms3 md3 5%nat HB HJ HFR HI R18 R23 HL.
  remember (b2_E cx (ms_regs ms3)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  paj_run_tok RUN HS HJ SHOK sch_span; [b2_awr|].
  b2_land ms3 H2 HB HJ0 HFR HMO HC HTAB HS HJ EE G2 G8 G9 G3 G4 R19 R20 R21 R22 R24 E34 E35 E36 E37.
  + pose proof (b2_U5 _ _ _ _ X34 X35 X36 B2r B3r B4r) as HX. unfold U in HX. rewrite HX. unfold sch_per.
    rewrite (b2_sch_b_out cx 5) by lia. f_equal. lia.
  + rewrite Z.max_r by lia. reflexivity.
  + exfalso. lia.
- (* six bytes or more: 0x81f30 reads byte 5; s7 drops by 6 (0x81f34) *)
  destruct (b2_seat cx fp k acc ly3 S3 W3 ms3 md3 6 6 (2 ^ 26) HB HJ HFR HI ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia)) as (HS & SHOK & HP0 & HP1).
  remember (b2_E cx (ms_regs ms3)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  paj_run_tok RUN HS HJ SHOK sch_span; [b2_awr|].
  b2_land ms3 H2 HB HJ0 HFR HMO HC HTAB HS HJ EE G2 G8 G9 G3 G4 R19 R20 R21 R22 R24 E34 E35 E36 E37.
  + pose proof (b2_U6 _ _ _ _ _ X34 X35 X36 X37 B2r B3r B4r B5r) as HX. unfold U in HX. exact HX.
  + rewrite E23, unsigned_lit_small by lia.
    rewrite Z.max_l by lia; try (unfold w64; f_equal; lia).
  + rewrite E33, unsigned_lit_small by lia; try reflexivity.
Qed.

End c.
End b.
End a.
