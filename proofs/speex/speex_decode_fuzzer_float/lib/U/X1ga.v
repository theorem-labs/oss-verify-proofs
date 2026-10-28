(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pw X0qn X0px X0qc X0qp X0pv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fr X1fl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g5 X1fd X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1nt X1rg X1ri X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation rsegs := X1gj.rsegs.

Definition A_calloc_p : Z := 0x31788.
Definition A_memcpy_p : Z := 0x39c5c.
Definition A_fprintf_p : Z := 0x34aac.
Definition A_MAGIC : Z := 0x10526.
Definition A_MSG_TOO_SMALL : Z := 0x1052f.
Definition A_MSG_BAD_MODE : Z := 0x104ff.
Definition P2H_LOOP : Z := 0x1da8c.
Definition P2H_ALLOC : Z := 0x1dac0.
Definition P2H_EXIT : Z := 0x1dbec.
Definition P2H_RET : Z := 0x1dbf0.
Definition P2H_STR_TOP : Z := 0x20000.
Definition P2H_GOT_STDERR : Z := 0x3c020.
Definition P2H_STDERR_VAR : Z := 0x3bfd0.

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.

Lemma s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros x. unfold s32. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Definition w4 (b0 b1 b2 b3 : byte) : Z := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Lemma w4_range : forall b0 b1 b2 b3, 0 <= w4 b0 b1 b2 b3 < 2^32.
Proof.
intros. unfold w4.
pose proof (bv_unsigned_in_range 8 b0). pose proof (bv_unsigned_in_range 8 b1).
pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3).
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.
Lemma byte_of_Z : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
intros b z E. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. exact E.
Qed.
Lemma le4_w4 : forall b0 b1 b2 b3, le4 (Z_to_bv 64 (w4 b0 b1 b2 b3)) = [b0; b1; b2; b3].
Proof.
intros.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le4. rewrite unsigned_lit64 by (unfold w4; lia). cbn [Z_to_le_bytes].
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia.
unfold w4.
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal; [apply byte_of_Z; Z.div_mod_to_equations; nia|].
f_equal. apply byte_of_Z; Z.div_mod_to_equations; nia.
Qed.
Lemma s32_eqm : forall x, (s32 x) mod 2^32 = x mod 2^32.
Proof.
intros x. unfold s32.
pose proof (Z.div_mod (x + 2^31) (2^32) ltac:(lia)) as E.
set (q := (x + 2 ^ 31) / 2 ^ 32) in E.
replace ((x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) with (x + (- q) * 2 ^ 32) by lia.
apply Z.mod_add. lia.
Qed.
Lemma le4_s32_w4 : forall b0 b1 b2 b3, le4 (Z_to_bv 64 (s32 (w4 b0 b1 b2 b3))) = [b0; b1; b2; b3].
Proof. intros. rewrite <- le4_w4. apply le4_lit_eqm. apply s32_eqm. Qed.
Lemma s32_small_id : forall x, 0 <= x < 2^31 -> s32 x = x.
Proof. intros x H. unfold s32. rewrite Z.mod_small by lia. lia. Qed.
Lemma s32_big : forall x, 2^31 <= x < 2^32 -> s32 x = x - 2^32.
Proof. intros x H. unfold s32. replace (x + 2^31) with ((x - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. Qed.

Lemma sx32_w : forall u, 0 <= u < 2^32 -> sx32 (Z_to_bv 64 u) = Z_to_bv 64 (s32 u).
Proof.
intros u Hu. unfold sx32. f_equal. rewrite unsigned_lit64 by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, s32.
change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31). reflexivity.
Qed.

Lemma lit64_neg_wrap : forall v, -2^63 <= v < 0 -> Z_to_bv 64 v = Z_to_bv 64 (v + 2^64).
Proof.
intros v Hv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
replace (v + 2^64) with (v + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma lts_zero_lit : forall c, -2^63 <= c < 2^63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 c) = (0 <? c).
Proof. intros c Hc. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.

Definition hb (pb : list byte) (i : nat) : byte := nth i pb (Z_to_bv 8 0).
Definition fw (pb : list byte) (i : nat) : Z := w4 (hb pb i) (hb pb (i + 1)) (hb pb (i + 2)) (hb pb (i + 3)).
Lemma skipn_hb : forall (pb : list byte) i, (i < length pb)%nat -> skipn i pb = hb pb i :: skipn (S i) pb.
Proof.
intros pb i Hi. unfold hb. revert i Hi. induction pb as [|x pb IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|].
apply IH. lia.
Qed.
Lemma le32_at_fw : forall (pb : list byte) (i : nat), (i + 4 <= length pb)%nat ->
le32_at (map bv_unsigned pb) (Z.of_nat i) = fw pb i.
Proof.
intros pb i Hi. unfold le32_at, zslice, ztake, zdrop. rewrite Nat2Z.id.
rewrite skipn_map.
rewrite (skipn_hb pb i), (skipn_hb pb (S i)), (skipn_hb pb (S (S i))), (skipn_hb pb (S (S (S i)))) by lia.
change (Z.to_nat 4) with 4%nat.
cbn [map firstn le_val]. rewrite firstn_O. cbn [le_val]. unfold fw, w4.
replace (i + 1)%nat with (S i) by lia. replace (i + 2)%nat with (S (S i)) by lia. replace (i + 3)%nat with (S (S (S i))) by lia.
lia.
Qed.
Lemma firstn_S_hb : forall (pb : list byte) i, (i < length pb)%nat -> firstn (S i) pb = firstn i pb ++ [hb pb i].
Proof.
intros pb i Hi. rewrite <- (firstn_skipn i pb) at 1. rewrite firstn_app, length_firstn, firstn_firstn.
replace (Nat.min (S i) i) with i by lia. replace (S i - Nat.min i (length pb))%nat with 1%nat by lia.
rewrite (skipn_hb pb i Hi). cbn. reflexivity.
Qed.
Lemma firstn_plus4 : forall (pb : list byte) n i, (n = i + 4)%nat -> (n <= length pb)%nat ->
firstn n pb = firstn i pb ++ [hb pb i; hb pb (i + 1); hb pb (i + 2); hb pb (i + 3)].
Proof.
intros pb n i -> Hi.
replace (i + 4)%nat with (S (S (S (S i)))) by lia.
rewrite (firstn_S_hb pb (S (S (S i)))) by lia. rewrite (firstn_S_hb pb (S (S i))) by lia.
rewrite (firstn_S_hb pb (S i)) by lia. rewrite (firstn_S_hb pb i) by lia.
rewrite <- !app_assoc. cbn. replace (i + 1)%nat with (S i) by lia. replace (i + 2)%nat with (S (S i)) by lia.
replace (i + 3)%nat with (S (S (S i))) by lia. reflexivity.
Qed.
Definition hdr_cells (pb : list byte) (c48 : word) : list cell :=
[CB 28 (firstn 28 pb); C4 (Z_to_bv 64 (fw pb 28)); C4 (Z_to_bv 64 (fw pb 32)); C4 (Z_to_bv 64 (fw pb 36));
C4 (Z_to_bv 64 (fw pb 40)); C4 (Z_to_bv 64 (fw pb 44)); C4 c48;
C4 (Z_to_bv 64 (fw pb 52)); C4 (Z_to_bv 64 (fw pb 56)); C4 (Z_to_bv 64 (fw pb 60)); C4 (Z_to_bv 64 (fw pb 64));
C4 (Z_to_bv 64 (fw pb 68)); C4 (Z_to_bv 64 (fw pb 72)); C4 (Z_to_bv 64 (fw pb 76))].
Lemma le4_fw : forall pb i, le4 (Z_to_bv 64 (fw pb i)) = [hb pb i; hb pb (i + 1); hb pb (i + 2); hb pb (i + 3)].
Proof. intros. unfold fw. apply le4_w4. Qed.

Lemma hdr_cells_bytes : forall pb, (80 <= length pb)%nat ->
cells_bytes (hdr_cells pb (Z_to_bv 64 (fw pb 48))) = firstn 80 pb.
Proof.
intros pb L. unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_fw, app_nil_r.
rewrite (firstn_plus4 pb 80 76), (firstn_plus4 pb 76 72), (firstn_plus4 pb 72 68), (firstn_plus4 pb 68 64) by lia.
rewrite (firstn_plus4 pb 64 60), (firstn_plus4 pb 60 56), (firstn_plus4 pb 56 52), (firstn_plus4 pb 52 48) by lia.
rewrite (firstn_plus4 pb 48 44), (firstn_plus4 pb 44 40), (firstn_plus4 pb 40 36), (firstn_plus4 pb 36 32) by lia.
rewrite (firstn_plus4 pb 32 28) by lia.
cbn [Nat.add]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma hdr_cells_wf : forall pb c48, (80 <= length pb)%nat -> cells_wf (hdr_cells pb c48).
Proof. intros pb c48 L. unfold hdr_cells. cbn. rewrite length_firstn. repeat split; try lia; exact I. Qed.
Lemma header_fields : forall pb, (80 <= length pb)%nat ->
let h := header_of_bytes (map bv_unsigned pb) in
hd_speex_version_id h = s32 (fw pb 28) /\ hd_header_size h = s32 (fw pb 32) /\ hd_rate h = s32 (fw pb 36)
/\ hd_mode h = s32 (fw pb 40) /\ hd_mode_bitstream_version h = s32 (fw pb 44) /\ hd_nb_channels h = s32 (fw pb 48)
/\ hd_frames_per_packet h = s32 (fw pb 64) /\ hd_extra_headers h = s32 (fw pb 68).
Proof.
intros pb L. cbn [header_of_bytes hd_speex_version_id hd_header_size hd_rate hd_mode hd_mode_bitstream_version hd_nb_channels
hd_frames_per_packet hd_extra_headers].
unfold s32_at.
change 28 with (Z.of_nat 28). change 32 with (Z.of_nat 32). change 36 with (Z.of_nat 36). change 40 with (Z.of_nat 40).
change 44 with (Z.of_nat 44). change 48 with (Z.of_nat 48). change 64 with (Z.of_nat 64). change 68 with (Z.of_nat 68).
rewrite !le32_at_fw by lia. repeat split; reflexivity.
Qed.

Lemma fw_range : forall pb i, 0 <= fw pb i < 2^32.
Proof. intros. unfold fw. apply w4_range. Qed.

Definition MAGIC_BYTES : list byte := map (fun z => Z_to_bv 8 z) SPEEX_MAGIC.
Lemma MAGIC_BYTES_eq : MAGIC_BYTES = [Z_to_bv 8 83; Z_to_bv 8 112; Z_to_bv 8 101; Z_to_bv 8 101; Z_to_bv 8 120; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32].
Proof. reflexivity. Qed.
Lemma MAGIC_unsigned : map bv_unsigned MAGIC_BYTES = SPEEX_MAGIC.
Proof. vm_compute. reflexivity. Qed.
Lemma magic_ro : forall m, mem_inv rsegs m -> u8ro rsegs m A_MAGIC MAGIC_BYTES.
Proof.
intros m MI. unfold u8ro. apply ro_string_at; [exact MI| vm_compute; reflexivity| unfold A_MAGIC; lia| cbn; unfold A_MAGIC; lia].
Qed.

Definition SLACK_TOO_SMALL : list byte := map (fun z => Z_to_bv 8 z) [99; 108].
Definition SLACK_BAD_MODE : list byte := map (fun z => Z_to_bv 8 z) [83; 112].
Lemma cstr_too_small : forall m lo spv, mem_inv rsegs m -> BITS_GLOBALS_TOP <= lo ->
bits_cstr_arg P2H_STR_TOP m (Z_to_bv 64 A_MSG_TOO_SMALL) MSG_HEADER_TOO_SMALL lo spv.
Proof.
intros m lo spv MI GLO. unfold bits_cstr_arg, A_MSG_TOO_SMALL, BITS_GLOBALS_TOP, BITS_INT_MAX, P2H_STR_TOP in *.
exists SLACK_TOO_SMALL. rewrite unsigned_lit64 by lia.
split; [apply ro_string_at; [exact MI| vm_compute; reflexivity| lia| cbn; lia]|].
split; [unfold MSG_HEADER_TOO_SMALL; cbn; repeat (constructor; [lia|]); constructor|].
unfold zlength, MSG_HEADER_TOO_SMALL, SLACK_TOO_SMALL. cbn [length str_bytes map Z.of_nat]. cbn. lia.
Qed.
Lemma cstr_bad_mode : forall m lo spv, mem_inv rsegs m -> BITS_GLOBALS_TOP <= lo ->
bits_cstr_arg P2H_STR_TOP m (Z_to_bv 64 A_MSG_BAD_MODE) MSG_INVALID_MODE_HEADER lo spv.
Proof.
intros m lo spv MI GLO. unfold bits_cstr_arg, A_MSG_BAD_MODE, BITS_GLOBALS_TOP, BITS_INT_MAX, P2H_STR_TOP in *.
exists SLACK_BAD_MODE. rewrite unsigned_lit64 by lia.
split; [apply ro_string_at; [exact MI| vm_compute; reflexivity| lia| cbn; lia]|].
split; [unfold MSG_INVALID_MODE_HEADER; cbn; repeat (constructor; [lia|]); constructor|].
unfold zlength, MSG_INVALID_MODE_HEADER, SLACK_BAD_MODE. cbn [length str_bytes map Z.of_nat]. cbn. lia.
Qed.

Lemma got_stderr_cell : forall m, rtables_pristine m -> rw_cells rsegs m P2H_GOT_STDERR [C8 (Z_to_bv 64 P2H_STDERR_VAR)].
Proof. intros m TP. apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, P2H_GOT_STDERR; lia| unfold P2H_GOT_STDERR, RTABLES_HI; cbn; lia| vm_compute; reflexivity]. Qed.
Lemma stderr_var_cell : forall m, rtables_pristine m -> rw_cells rsegs m P2H_STDERR_VAR [C8 (Z_to_bv 64 BITS_RSTDERR)].
Proof. intros m TP. apply rw_cells_of_pristine; [exact TP| cbn; tauto| unfold RTABLES_LO, P2H_STDERR_VAR; lia| unfold P2H_STDERR_VAR, RTABLES_HI; cbn; lia| vm_compute; reflexivity]. Qed.

Lemma rw_cells_C8_func : forall m A (v1 v2 : word), rw_cells rsegs m A [C8 v1] -> rw_cells rsegs m A [C8 v2] -> v1 = v2.
Proof.
intros m A v1 v2 [[_ B1] _] [[_ B2] _]. cbn [cells_bytes cbytes] in B1, B2. rewrite app_nil_r in B1, B2.
destruct B1 as (_ & _ & R1). destruct B2 as (_ & _ & R2).
assert (E : le8 v1 = le8 v2).
{ apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
- rewrite <- (R1 i) by (rewrite length_le8; exact Hi). rewrite <- (R2 i) by (rewrite length_le8; exact Hi). reflexivity.
- rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_le8; lia). reflexivity. }
rewrite <- (le_bytes_to_word_le8 v1), <- (le_bytes_to_word_le8 v2), E. reflexivity.
Qed.

Lemma stderr_wfile_kept' : forall m m', range_kept m m' BITS_RSTDERR (BITS_RSTDERR + 232) -> stderr_wfile m -> stderr_wfile m'.
Proof.
intros m m' RK sfH_; first [ sf_destruct 7%nat sfH_ as flags mode e wend tail FC FL | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & FC & FL) ]. first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [|exact FL].
eapply (pres_except_rw_cells rsegs (fun a => BITS_RSTDERR <= a < BITS_RSTDERR + 232) []); [| exact FC|].
- intros a Ha Hc _. exact (RK a Ha Hc).
- intros a Ha. split; [|intros X; exact X]. cbn in Ha. unfold BITS_RSTDERR. lia.
Qed.

Lemma rheap_ssp' {RCEIL : RunCeiling} : forall s LB m, RHEAP s LB m -> ssp_cells m run_canary.
Proof.
intros s LB m sfH_; first [ sf_destruct 6%nat sfH_ as st LB0 _ _ MR _ | sf_fb; destruct sfH_ as (st & LB0 & _ & _ & MR & _) ]. first [ sf_destruct 4%nat MR as _ _ G _ | sf_fb; destruct MR as (_ & _ & G & _) ]. first [ sf_destruct 5%nat G as _ _ _ G4 G5 | sf_fb; destruct G as (_ & _ & _ & G4 & G5) ].
unfold ssp_cells, got_ssp, ssp_guard. split; [exact G4| exact G5].
Qed.
Lemma canary_zero {RCEIL : RunCeiling} : forall s LB m c, RHEAP s LB m -> ssp_cells m c -> c = run_canary.
Proof.
intros s LB m c HP [_ SC]. destruct (rheap_ssp' _ _ _ HP) as [_ S0]. exact (rw_cells_C8_func _ _ _ _ SC S0).
Qed.

Definition memcpy_postz (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(Dst, Dst + N)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at rsegs m' Src src.
Lemma memcpy_callz : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
(Src + N <= Dst \/ Dst + N <= Src) -> 0 <= N < 2^64 -> 0 <= Src < 2^64 -> 0 <= Dst < 2^64 -> mem_inv rsegs m ->
evt rsegs (memcpy_postz ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_memcpy_p) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros BA LEN DC SEP HN HS HD MI. unfold A_memcpy_p.
assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit64; lia).
assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit64; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit64; lia).
eapply evt_mono. { eapply X1fd.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
intros ms' Q. unfold X1fd.memcpy_post, memcpy_postz in *. rewrite ED, ES, EN in Q. exact Q.
Qed.

Lemma land3_mod4 : forall v, Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?land3_mod4 in K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac nt := first [ if_false_x | ntk ].
Ltac ltb_fix := repeat match goal with |- context [?x <? ?y] =>
first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
| replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ] end.
Ltac ee_pos p := lazymatch p with xH => idtac | xO ?q => ee_pos q | xI ?q => ee_pos q end.
Ltac ee_zlit z := lazymatch z with Z0 => idtac | Zpos ?p => ee_pos p | Zneg ?p => ee_pos p end.
Ltac lit_fold := repeat match goal with |- context [Z_to_bv 64 ?e] =>
tryif ee_zlit e then fail else (let v := eval vm_compute in e in ee_zlit v; change e with v) end.

Section Magic.
Context {RCEIL : RunCeiling}.
Variables (P : Z) (pbytes : list byte) (m : mem).
Variables (ra sp gp tp t0 t1 t2 s0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis PK : u8ro rsegs m P pbytes.
Hypothesis L8 : (8 <= length pbytes)%nat.
Hypothesis MG : u8ro rsegs m A_MAGIC MAGIC_BYTES.
Hypothesis P0 : 0 < P.

Definition magic_post : machine_state -> Prop := fun ms' =>
exists a0' a1' a2' a3' a4' a5' a6' : word,
(ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_EXIT) fc None m (seg_rom rsegs)
/\ firstn 8 pbytes <> MAGIC_BYTES)
\/ (ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 P) a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_ALLOC) fc None m (seg_rom rsegs)
/\ firstn 8 pbytes = MAGIC_BYTES).

#[using="PK L8 MG P0"] Lemma magic_loop : forall (k i : nat) (kz iz : Z) (a5 a6 : word),
(i + k = 8)%nat -> (0 < k)%nat -> kz = Z.of_nat k -> iz = Z.of_nat i ->
firstn i pbytes = firstn i MAGIC_BYTES ->
evt rsegs magic_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 P) (Z_to_bv 64 kz) (Z_to_bv 64 (66854 + iz)) (Z_to_bv 64 1) (Z_to_bv 64 (P + iz))
(Z_to_bv 64 (P + iz)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 P2H_LOOP) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i kz iz a5 a6 Hik Hk -> -> PRE; [lia|].
pose proof (bytes_at_bound _ _ _ _ PK) as BX. pose proof (bytes_at_bound _ _ _ _ MG) as BY.
rewrite MAGIC_BYTES_eq in BY. cbn [length] in BY. unfold A_MAGIC in BY.
assert (LM : length MAGIC_BYTES = 8%nat) by reflexivity.
set (x := hb pbytes i). set (y := hb MAGIC_BYTES i).
pose proof (u8ro_read rsegs m P pbytes (Z.of_nat i) x (wa (P + Z.of_nat i)) PK
ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) eq_refl) as RX.
pose proof (u8ro_read rsegs m A_MAGIC MAGIC_BYTES (Z.of_nat i) y (wa (66854 + Z.of_nat i)) MG
ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) ltac:(unfold A_MAGIC; reflexivity)) as RY.
unfold P2H_LOOP. zstep. nt.
zstep. zstep. ltb_fix. lit_fold. zstep. nt.
zstep. nt.
zstep. zstep. clear RX RY.
zstep. if_cases K; zify_cond K.
-
apply evt_done. unfold magic_post, P2H_EXIT. sf_eexists 7%nat. left. split; [reflexivity|].
intros E. apply K.
enough (Exy : x = y) by (rewrite Exy; reflexivity).
subst x y. unfold hb. rewrite <- E. rewrite nth_firstn. replace (i <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
- assert (Exy : x = y) by (apply bv_eq; exact K).
zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
+
destruct k as [|k']; [exfalso; cbn [Z.of_nat] in K2; rewrite ?unsigned_lit64 in K2 by lia; lia|].
replace (66854 + Z.of_nat i + 1) with (66854 + Z.of_nat (S i)) by lia.
replace (P + Z.of_nat i + 1) with (P + Z.of_nat (S i)) by lia.
apply (IH (S i) (Z.of_nat (S (S k')) + -1) (Z.of_nat (S i))); [lia| lia| lia| reflexivity|].
rewrite (firstn_S_hb pbytes i), (firstn_S_hb MAGIC_BYTES i) by lia. rewrite PRE. fold x. fold y. rewrite Exy. reflexivity.
+
destruct k as [|k']; [| exfalso; rewrite ?unsigned_lit64 in K2 by lia; lia].
apply evt_done. unfold magic_post, P2H_ALLOC. sf_eexists 7%nat. right. split; [reflexivity|].
replace 8%nat with (S i) by lia.
rewrite <- (firstn_all2 (n := S i) MAGIC_BYTES) by lia.
rewrite (firstn_S_hb pbytes i), (firstn_S_hb MAGIC_BYTES i) by lia. rewrite PRE. fold x. fold y. rewrite Exy. reflexivity.
Qed.
End Magic.

Section F.
Context {RCEIL : RunCeiling}.
Hypothesis HC : bits_calloc_stmt.
Hypothesis HF : rfree_stmt.
Hypothesis HN : bits_notify_stmt s_notify stderr_wfile ssp_cells P2H_STR_TOP.
Hypothesis HFR : rheap_frame_stmt.
Hypothesis HBR : rheap_block_range_stmt.
Hypothesis HBD : rheap_blocks_disjoint_stmt.
Hypothesis HBN : rheap_blocks_nodup_stmt.

#[using="Type"] Lemma p2h_fail_tail :
forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(raj s0j s1j t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
(m m1 : mem) (s s' : PState) (LB : list block) (AB lo : Z) (canary errv' : word) (fr8 : list byte),
frm0 fc' -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -32) ->
rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 fr8; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv'] -> rauxv_ok m1 AB ->
pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m1 ->
stderr_wfile m1 -> ssp_cells m1 canary -> ps_so s' = ps_so s -> RHEAP s' LB m1 ->
lo + 32 <= bv_unsigned sp ->
evt rsegs (rspx_packet_to_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo canary m None s')
(MS (mkR raj (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0j s1j a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 P2H_EXIT) fc' None m1 (seg_rom rsegs)).
Proof.
intros until fr8. intros FRM MI ST FR ERR AUX PX SE SSP SO HP LOF.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64) with (2^64) in Rq.
pose proof ST as ST0. destruct ST0 as (LO0 & _).
pose proof (rw_cells_bound _ _ _ _ FR) as GB. cbn [cells_size csize Nat.add length] in GB.
unfold P2H_EXIT. do 7 step.
release_frame FR ST (bv_unsigned sp).
unfold rspx_packet_to_header_post, wz. apply evt_done. sf_eexists 19%nat. split; [reflexivity|].
split; [exact FRM|]. split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact AUX|].
split; [exact PX|]. split; [exact SE|]. split; [exact SSP|]. split; [exact SO|]. split; [reflexivity| exact HP].
Qed.

#[using="Type"] Lemma le4_s32_fw : forall pb i, le4 (Z_to_bv 64 (s32 (fw pb i))) = le4 (Z_to_bv 64 (fw pb i)).
Proof. intros. apply le4_lit_eqm. apply s32_eqm. Qed.

#[using="Type"] Lemma hdr_cells_post : forall m3 A pb cv, (80 <= length pb)%nat ->
rw_cells rsegs m3 A (hdr_cells pb (Z_to_bv 64 cv)) ->
rw_cells rsegs m3 A (spx_header_cells (firstn 28 pb) (set_nb_channels (header_of_bytes (map bv_unsigned pb)) cv)
(Z_to_bv 64 (fw pb 52)) (Z_to_bv 64 (fw pb 56)) (Z_to_bv 64 (fw pb 60)) (Z_to_bv 64 (fw pb 72)) (Z_to_bv 64 (fw pb 76))).
Proof.
intros m3 A pb cv L HDR.
pose proof (header_fields pb L) as HFS. cbv zeta in HFS. first [ sf_destruct 8%nat HFS as E28 E32 E36 E40 E44 E48 E64 E68 | sf_fb; destruct HFS as (E28 & E32 & E36 & E40 & E44 & E48 & E64 & E68) ].
unfold spx_header_cells, wz.
cbn [set_nb_channels hd_speex_version_id hd_header_size hd_rate hd_mode hd_mode_bitstream_version hd_nb_channels hd_frames_per_packet hd_extra_headers].
rewrite E28, E32, E36, E40, E44, E64, E68.
eapply rw_cells_samebytes; [exact HDR| | |].
- cbn. rewrite length_firstn. repeat split; try lia; exact I.
- unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_s32_fw. reflexivity.
- cbn. reflexivity.
Qed.

#[using="Type"] Lemma p2h_ok_join :
forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(raj t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
(m m3 : mem) (s s' : PState) (LB : list block) (p : bptr) (A0 P AB lo cv : Z) (errv' : word) (fr8 pbytes : list byte),
frm0 fc' -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -32) ->
rw_cells rsegs m3 (bv_unsigned sp + -32) [CB 8 fr8; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 AB ->
pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m3 ->
stderr_wfile m3 -> ps_so s' = ps_so s -> RHEAP s' ((p, A0, 80) :: LB) m3 -> rblock_range A0 80 ->
rw_cells rsegs m3 A0 (hdr_cells pbytes (Z_to_bv 64 cv)) -> (80 <= length pbytes)%nat ->
0 <= s32 (fw pbytes 40) < 3 -> cv = clamp_channels (s32 (fw pbytes 48)) ->
alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> tp = Z_to_bv 64 RATP -> bv_unsigned sp <= AB ->
evt rsegs (rspx_packet_to_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo run_canary m
(Some (p, set_nb_channels (header_of_bytes (map bv_unsigned pbytes)) (clamp_channels (hd_nb_channels (header_of_bytes (map bv_unsigned pbytes)))))) s')
(MS (mkR raj (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A0) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 P2H_RET) fc' None m3 (seg_rom rsegs)).
Proof.
intros until pbytes. intros FRM MI ST FR ERR AUX PX SE SO HP BR HDR L80 GOOD CV CEIL LOF TP SPB.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64) with (2^64) in Rq.
pose proof ST as ST0. destruct ST0 as (LO0 & _).
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ]. unfold alloc_ceiling in BR4.
pose proof (header_fields pbytes L80) as HFS. cbv zeta in HFS. first [ sf_destruct 8%nat HFS as E28 E32 E36 E40 E44 E48 E64 E68 | sf_fb; destruct HFS as (E28 & E32 & E36 & E40 & E44 & E48 & E64 & E68) ].
assert (ERRA : errno_addr tp = 316332) by (subst tp; rewrite unsigned_lit64 by (unfold RATP; lia); reflexivity).
rewrite ERRA in ERR.
unfold P2H_RET.
do 6 step.
release_frame FR ST (bv_unsigned sp).
unfold rspx_packet_to_header_post, wz. apply evt_done. sf_eexists 19%nat. split; [reflexivity|].
split; [exact FRM|]. split; [assumption|]. split; [exact ST|]. split; [rewrite ERRA; eassumption|].
split; [exact AUX|]. split; [exact PX|]. split; [exact SE|].
split; [eapply rheap_ssp'; exact HP|]. split; [exact SO|].
first [ unshelve sf_eexists 7%nat; [ exact (A0) | exact ((firstn 28 pbytes)) | exact ((Z_to_bv 64 (fw pbytes 52))) | exact ((Z_to_bv 64 (fw pbytes 56))) | exact ((Z_to_bv 64 (fw pbytes 60))) | exact ((Z_to_bv 64 (fw pbytes 72))) | exact ((Z_to_bv 64 (fw pbytes 76))) | ] | sf_fb; exists A0, (firstn 28 pbytes), (Z_to_bv 64 (fw pbytes 52)), (Z_to_bv 64 (fw pbytes 56)), (Z_to_bv 64 (fw pbytes 60)), (Z_to_bv 64 (fw pbytes 72)), (Z_to_bv 64 (fw pbytes 76)) ].
split; [reflexivity|]. split; [exact BR|]. split; [exact HP|].
rewrite E48.
split. { rewrite <- CV. apply hdr_cells_post; [exact L80|]. exact HDR. }
cbn [hd_nb_channels hd_speex_version_id hd_rate hd_mode hd_mode_bitstream_version hd_frames_per_packet hd_extra_headers set_nb_channels].
rewrite E28, E36, E40, E44, E64, E68, <- CV.
pose proof (s32_range (fw pbytes 28)). pose proof (s32_range (fw pbytes 36)). pose proof (s32_range (fw pbytes 44)).
pose proof (s32_range (fw pbytes 48)). pose proof (s32_range (fw pbytes 64)). pose proof (s32_range (fw pbytes 68)).
unfold X1rh.SPEEX_NB_MODES. unfold clamp_channels in CV.
destruct (2 <? s32 (fw pbytes 48)) eqn:C1; [|destruct (s32 (fw pbytes 48) <? 1) eqn:C2]; repeat split; lia.
Qed.

#[using="HFR"] Lemma p2h_ok_tail :
forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(raj t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
(m m3 : mem) (s s' : PState) (LB : list block) (p : bptr) (A0 P AB lo cv : Z) (errv' : word) (fr8 pbytes : list byte),
frm0 fc' -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -32) ->
rw_cells rsegs m3 (bv_unsigned sp + -32) [CB 8 fr8; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 AB ->
pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m3 ->
stderr_wfile m3 -> ps_so s' = ps_so s -> RHEAP s' ((p, A0, 80) :: LB) m3 -> rblock_range A0 80 ->
(forall a', rclient_addr LB (bv_unsigned sp) a' -> ~ (A0 <= a' < A0 + 80)) ->
(forall x, In x LB -> rblock_range (blk_addr x) (blk_size x)) ->
rw_cells rsegs m3 A0 (hdr_cells pbytes (Z_to_bv 64 (fw pbytes 48))) -> (80 <= length pbytes)%nat ->
0 <= s32 (fw pbytes 40) < 3 -> cv = clamp_channels (s32 (fw pbytes 48)) ->
alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> tp = Z_to_bv 64 RATP -> bv_unsigned sp <= AB ->
evt rsegs (rspx_packet_to_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo run_canary m
(Some (p, set_nb_channels (header_of_bytes (map bv_unsigned pbytes)) (clamp_channels (hd_nb_channels (header_of_bytes (map bv_unsigned pbytes)))))) s')
(MS (mkR raj (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A0) (Z_to_bv 64 P) (Z_to_bv 64 (A0 + 48)) (Z_to_bv 64 cv) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0x1db98) fc' None m3 (seg_rom rsegs)).
Proof.
intros until pbytes. intros FRM MI ST FR ERR AUX PX SE SO HP BR HPRIV HBRc HDR L80 GOOD CV CEIL LOF TP SPB.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64) with (2^64) in Rq.
pose proof ST as ST0. destruct ST0 as (LO0 & _).
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ]. unfold alloc_ceiling in BR4.
assert (ERRA : errno_addr tp = 316332) by (subst tp; rewrite unsigned_lit64 by (unfold RATP; lia); reflexivity).
rewrite ERRA in ERR.
pose proof (munch_refl [(A0, A0 + 80); (bv_unsigned sp + -32, bv_unsigned sp)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
unfold hdr_cells in HDR.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AUX4 : rauxv_ok mx AB) by (eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]);
assert (PX4 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m mx) by
(eapply pres_except_trans; [exact PX|];
eapply (pres_except_of_munch_client LB (bv_unsigned sp) lo); [exact HBRc| exact CEIL| lia| exact MU| exact WM|];
constructor; [right; right; cbn [fst snd]; exact HPRIV|]; constructor; [left; cbn; lia| constructor]);
assert (SE4 : stderr_wfile mx) by
(eapply stderr_wfile_kept'; [|exact SE]; eapply range_kept_of_munch; [exact MU| exact WM|];
intros a Ha; unfold BITS_RSTDERR in Ha; cbn; lia);
assert (HP4 : RHEAP s' ((p, A0, 80) :: LB) mx) by
(eapply HFR; [exact HP| exact MU| exact WM|];
constructor; [right; right; eexists; split; [left; reflexivity| cbn; lia]|];
constructor; [left; cbn; lia| constructor])
end.
eapply (p2h_ok_join ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (cv := cv) (pbytes := pbytes) (P := P);
try eassumption; try reflexivity; try lia.
rewrite ERRA. eassumption.
Qed.

#[using="HF HN HFR HBR HBN"] Lemma p2h_badmode_tail :
forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(raj t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
(m m3 : mem) (s s' : PState) (LB : list block) (p : bptr) (A0 P AB lo : Z) (errv' : word) (fr8 : list byte),
frm0 fc' -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -32) ->
rw_cells rsegs m3 (bv_unsigned sp + -32) [CB 8 fr8; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 AB ->
pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m3 ->
stderr_wfile m3 -> ps_so s' = ps_so s -> RHEAP s' ((p, A0, 80) :: LB) m3 ->
rw_cells rsegs m3 P2H_GOT_STDERR [C8 (Z_to_bv 64 P2H_STDERR_VAR)] -> rw_cells rsegs m3 P2H_STDERR_VAR [C8 (Z_to_bv 64 BITS_RSTDERR)] ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp - PKT2HDR_STACK -> bv_unsigned sp < 2^63 -> tp = Z_to_bv 64 RATP -> bv_unsigned sp <= AB ->
implM rsegs (X1qx.mbind (s_notify MSG_INVALID_MODE_HEADER) (fun _ => X1qx.mbind (raw_free p) (fun _ => X1qx.mret (@None (bptr * spx_header)))))
s' (rspx_packet_to_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo run_canary m)
(MS (mkR raj (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A0) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0x1dbc4) fc' None m3 (seg_rom rsegs)).
Proof.
intros until fr8. intros FRM MI ST FR ERR AUX PX SE SO HP G1 G2 CEIL LO SP63 TP SPB.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64) with (2^64) in Rq.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold PKT2HDR_STACK in LO.
unfold P2H_GOT_STDERR, P2H_STDERR_VAR in G1, G2.
assert (ERRA : errno_addr tp = 316332) by (subst tp; rewrite unsigned_lit64 by (unfold RATP; lia); reflexivity).
rewrite ERRA in ERR.
pose proof (HBN _ _ _ HP) as ND.
assert (NI : ~ In p (map blk_id LB)).
{ cbn [map] in ND. inversion ND as [|x l NI' ND' E1]; subst. exact NI'. }
assert (HBRc : forall x, In x LB -> rblock_range (blk_addr x) (blk_size x)).
{ intros x Hx. exact (HBR _ _ _ _ HP (or_intror Hx)). }
pose proof (rw_cells_bound _ _ _ _ FR) as GB. cbn [cells_size csize Nat.add length] in GB.
unfold implM. iprefix.
do 8 step.
apply evt_done.
eapply (implM_bind rsegs).
{ eapply HN with (lo := lo); try reflexivity; try exact SE; try exact MI; try exact FRM.
all: rewrite ?unsigned_lit64 by lia.
- apply cstr_bad_mode; [assumption| unfold BITS_GLOBALS_TOP; lia].
- exact ST.
- unfold BITS_FPRINTF_DEPTH. lia.
- unfold BITS_GLOBALS_TOP. lia.
- lia.
- eapply rheap_ssp'. exact HP. }
cbv beta. intros [] st4 ms4 PN.
first [ sf_destruct 28%nat PN as x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 Ft2 fc2 m4 -> MUn WMn MI4 FRM4 HFt4 ST4 SE4 SSP4 -> | sf_fb; destruct PN as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & Ft2 & fc2 & m4 & -> & MUn & WMn & MI4 & FRM4 & HFt4 & ST4 & SE4 & SSP4 & ->) ].
rewrite !unsigned_lit64 in MUn, ST4 by lia.
replace (ret_pc (Z_to_bv 64 121828)) with (Z_to_bv 64 121828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FR MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as FR4.
pose proof (rw_cells_transport rsegs _ m3 m4 _ _ ERR MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as ERR4.
assert (AUX4 : rauxv_ok m4 AB).
{ eapply rauxv_ok_frame; [exact AUX| exact MUn| exact WMn|]. unfold BITS_RSTDERR.
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]. }
assert (HP4 : RHEAP s' ((p, A0, 80) :: LB) m4).
{ eapply HFR; [exact HP| exact MUn| exact WMn|]. unfold BITS_RSTDERR.
constructor; [left; cbn; lia|]. constructor; [|constructor].
right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. cbn. lia. }
assert (PX4 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m4).
{ eapply pres_except_trans; [exact PX|].
eapply (pres_except_of_munch_client LB (bv_unsigned sp) lo); [exact HBRc| exact CEIL| lia| exact MUn| exact WMn|].
constructor; [left; cbn; lia|]. constructor; [right; left; left; reflexivity| constructor]. }
clear FR ERR AUX SE PX MI G1 G2.

unfold implM. iprefix.
step. step.
apply evt_done.
eapply (implM_bind rsegs).
{ eapply HF with (LB := (p, A0, 80) :: LB) (p := p) (A := A0) (n := 80) (lo := lo) (B := AB) (errv := errv');
try reflexivity; try exact HP4; try exact AUX4; try exact MI4; try exact TP.
all: rewrite ?unsigned_lit64 by lia.
- left. reflexivity.
- lia.
- exact ST4.
- exact CEIL.
- unfold RFREE_STACK. lia.
- rewrite ERRA. exact ERR4. }
cbv beta. intros [] st5 ms5 PF.
first [ sf_destruct 25%nat PF as z0 z1 z2 w0 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m5 -> MI5 ST5 ERR5 AUX5 PRES5 FA5 SO5 HP5 | sf_fb; destruct PF as (z0 & z1 & z2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m5 & -> & MI5 & ST5 & ERR5 & AUX5 & PRES5 & FA5 & SO5 & HP5) ].
rewrite !unsigned_lit64 in ST5, PRES5 by lia. rewrite ERRA in ERR5.
rewrite lb_remove_cons in HP5, PRES5. cbn [blk_id fst snd] in HP5, PRES5.
rewrite (proj2 (bptr_eqb_true p p) eq_refl) in HP5, PRES5. rewrite (lb_remove_notin _ _ NI) in HP5, PRES5.
replace (ret_pc (Z_to_bv 64 121836)) with (Z_to_bv 64 121836) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -32) [CB 8 fr8; C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact PRES5| exact FR4| left; cbn; lia]. }
assert (SE5 : stderr_wfile m5).
{ eapply stderr_wfile_kept'; [|exact SE4]. eapply range_kept_of_rheap_pres; [exact PRES5|].
intros a Ha. unfold BITS_RSTDERR in Ha. right; left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
assert (PX5 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m5).
{ eapply pres_except_trans; [exact PX4|]. eapply pres_except_of_rheap_pres; [exact PRES5| lia]. }
apply implM_ret. change (Z_to_bv 64 121836) with (Z_to_bv 64 P2H_EXIT).
eapply p2h_fail_tail; try eassumption; try lia.
- rewrite ERRA. exact ERR5.
- eapply rheap_ssp'. exact HP5.
- rewrite SO5. exact SO.
Qed.

#[using="HC HF HN HFR HBR HBD HBN"] Lemma speex_packet_to_header_proof : rspx_packet_to_header_stmt.
Proof.
unfold rspx_packet_to_header_stmt.
intros until canary. intros HP HIN PB1 PB2 PK Hsz Hsz31 TPR SE SSP AUX SPB ABB ST CEIL LO SP63 ERR MI FRM TP Ha0 Ha1 PM4.
unfold wz in *. subst a0 a1.
unfold A_speex_packet_to_header, PKT2HDR_STACK in *.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64) with (2^64) in Rq.
pose proof (bytes_at_bound _ _ _ _ PK) as PBB.
pose proof (HBR _ _ _ _ HP HIN) as BRP. pose proof BRP as sfP_; first [ sf_destruct 5%nat sfP_ as BP1 BP2 BP3 BP4 BP5 | sf_fb; destruct sfP_ as (BP1 & BP2 & BP3 & BP4 & BP5) ]. unfold alloc_ceiling in BP4.
assert (ERRA : errno_addr tp = 316332) by (subst tp; rewrite unsigned_lit64 by (unfold RATP; lia); reflexivity).
rewrite ERRA in ERR.
pose proof (canary_zero _ _ _ _ HP SSP) as Ecan. subst canary.
pose proof (got_stderr_cell m TPR) as G1. pose proof (stderr_var_cell m TPR) as G2.
unfold P2H_GOT_STDERR, P2H_STDERR_VAR in G1, G2.
unfold implM. iprefix.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 32%nat ST.
do 4 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
assert (HP1 : RHEAP s LB m1).
{ eapply HFR; [exact HP| exact MU| exact WM|]. constructor; [|constructor]. left. cbn. lia. }
assert (AUX1 : rauxv_ok m1 AB).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
assert (SE1 : stderr_wfile m1).
{ eapply stderr_wfile_kept'; [|exact SE]. eapply range_kept_of_munch; [exact MU| exact WM|]. intros a Ha. unfold BITS_RSTDERR in Ha. cbn. lia. }
assert (PX1 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m1).
{ eapply (pres_except_of_munch_client LB (bv_unsigned sp) lo); [ | exact CEIL| lia| exact MU| exact WM|].
+ intros x Hx. exact (HBR _ _ _ _ HP Hx).
+ constructor; [left; cbn; lia| constructor]. }
pose proof (rheap_ssp' _ _ _ HP1) as SSP1.
step. step. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; rewrite ?unsigned_lit64 in K by lia.
-
do 8 step.
apply evt_done. unfold speex_packet_to_header.
replace (size <? SIZEOF_SPEEX_HEADER) with true by (symmetry; apply Z.ltb_lt; unfold SIZEOF_SPEEX_HEADER; lia).
unfold io_notify.
eapply (implM_bind rsegs).
{ eapply HN with (lo := lo); try reflexivity; try exact SE1; try exact MI; try exact FRM.
all: rewrite ?unsigned_lit64 by lia.
- apply cstr_too_small; [assumption| unfold BITS_GLOBALS_TOP; lia].
- exact ST.
- unfold BITS_FPRINTF_DEPTH. lia.
- unfold BITS_GLOBALS_TOP. lia.
- lia.
- exact SSP1. }
cbv beta. intros [] s2_ ms2 PN.
first [ sf_destruct 28%nat PN as x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 Ft fc2 m2 -> MUn WMn MI2 FRM2 HFt2 ST2 SE2 SSP2 -> | sf_fb; destruct PN as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & Ft & fc2 & m2 & -> & MUn & WMn & MI2 & FRM2 & HFt2 & ST2 & SE2 & SSP2 & ->) ].
rewrite !unsigned_lit64 in MUn, ST2 by lia.
replace (ret_pc (Z_to_bv 64 121792)) with (Z_to_bv 64 121792) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as FR2.
pose proof (rw_cells_transport rsegs _ m1 m2 _ _ ERR MUn WMn ltac:(cbn; unfold BITS_RSTDERR; lia)) as ERR2.
assert (AUX2 : rauxv_ok m2 AB).
{ eapply rauxv_ok_frame; [exact AUX1| exact MUn| exact WMn|]. unfold BITS_RSTDERR.
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]. }
assert (HP2 : RHEAP s LB m2).
{ eapply HFR; [exact HP1| exact MUn| exact WMn|]. unfold BITS_RSTDERR.
constructor; [left; cbn; lia|]. constructor; [|constructor].
right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. cbn. lia. }
assert (PX2 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m2).
{ eapply pres_except_trans; [exact PX1|].
eapply (pres_except_of_munch_client LB (bv_unsigned sp) lo); [ | exact CEIL| lia| exact MUn| exact WMn|].
+ intros x Hx. exact (HBR _ _ _ _ HP Hx).
+ constructor; [left; cbn; lia|]. constructor; [right; left; left; reflexivity| constructor]. }
apply implM_ret. unfold implM.
step.
eapply p2h_fail_tail; try eassumption; try reflexivity; try lia.
rewrite ERRA. exact ERR2.
-
assert (L80 : (80 <= length pbytes)%nat) by lia.
do 7 zstep. ltb_fix. lit_fold.
replace (Z_to_bv 64 66854) with (Z_to_bv 64 (66854 + 0)) by (f_equal; lia).
replace (Z_to_bv 64 P) with (Z_to_bv 64 (P + 0)) at 2 3 by (f_equal; lia).
eapply evt_cut.
{ eapply (magic_loop P pbytes m1) with (k := 8%nat) (i := 0%nat); [exact PK| lia| apply magic_ro; exact MI| lia| reflexivity| lia| reflexivity| reflexivity| reflexivity]. }
cbv beta. intros ms' sfH_; first [ sf_destruct 8%nat sfH_ as a0' a1' a2' a3' a4' a5' a6' [[-> NE]|[-> EQ]] | sf_fb; destruct sfH_ as (a0' & a1' & a2' & a3' & a4' & a5' & a6' & [[-> NE]|[-> EQ]]) ].
+
apply evt_done. unfold speex_packet_to_header.
replace (size <? SIZEOF_SPEEX_HEADER) with false by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
replace (list_eqb (ztake 8 (map bv_unsigned pbytes)) SPEEX_MAGIC) with false.
2:{ symmetry. destruct (list_eqb (ztake 8 (map bv_unsigned pbytes)) SPEEX_MAGIC) eqn:E; [|reflexivity]. exfalso. apply NE.
apply list_eqb_eq in E. unfold ztake in E. change (Z.to_nat 8) with 8%nat in E. rewrite firstn_map, <- MAGIC_unsigned in E.
apply byte_list_eq. exact E. }
cbn [negb]. apply implM_ret.
eapply p2h_fail_tail; try eassumption; try reflexivity; try lia.
rewrite ERRA. exact ERR.
+
do 3 step.
apply evt_done. unfold speex_packet_to_header.
replace (size <? SIZEOF_SPEEX_HEADER) with false by (symmetry; apply Z.ltb_ge; unfold SIZEOF_SPEEX_HEADER; lia).
replace (list_eqb (ztake 8 (map bv_unsigned pbytes)) SPEEX_MAGIC) with true.
2:{ symmetry. apply list_eqb_eq. unfold ztake. change (Z.to_nat 8) with 8%nat. rewrite firstn_map, EQ. exact MAGIC_unsigned. }
cbn [negb].
eapply (implM_bind rsegs).
{ eapply HC with (s := s) (LB := LB) (m0 := SIZEOF_SPEEX_HEADER) (n0 := 1) (lo := lo) (B := AB) (errv := errv);
try reflexivity; try exact HP1; try exact AUX1; try exact MI.
all: rewrite ?unsigned_lit64 by lia.
all: try (unfold SIZEOF_SPEEX_HEADER, RSMALL_MAX in *; lia).
all: try (rewrite ERRA; exact ERR); try exact TP; try exact ST; unfold BITS_CALLOC_STACK; lia. }
cbv beta. intros r s' ms' POST.
first [ sf_destruct 26%nat POST as x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m2 errv2 -> MI2 ST2 ERR2 AUX2 PRES FA SO RES | sf_fb; destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & PRES & FA & SO & RES) ].
rewrite !unsigned_lit64 in ST2, PRES by lia. rewrite ERRA in ERR2.
replace (ret_pc (Z_to_bv 64 121548)) with (Z_to_bv 64 121548) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) [CB 8 (take 8 (take 16 (take 24 junk))); C8 s1; C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact PRES| exact FR| left; cbn; lia]. }
assert (PK2 : u8ro rsegs m2 P pbytes).
{ unfold u8ro. eapply rheap_pres_bytes_at; [exact PRES| exact PK|]. right; right. exists pblk. split; [exact HIN| lia]. }
assert (G1' : rw_cells rsegs m2 245792 [C8 (Z_to_bv 64 245712)]).
{ eapply rheap_pres_rw_cells; [exact PRES| exact G1|]. right; left. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. cbn. lia. }
assert (G2' : rw_cells rsegs m2 245712 [C8 (Z_to_bv 64 BITS_RSTDERR)]).
{ eapply rheap_pres_rw_cells; [exact PRES| exact G2|]. right; left. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. cbn. lia. }
assert (SE2 : stderr_wfile m2).
{ eapply stderr_wfile_kept'; [|exact SE1]. eapply range_kept_of_rheap_pres; [exact PRES|].
intros a Ha. unfold BITS_RSTDERR in Ha. right; left. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
assert (PX2 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m2).
{ eapply pres_except_trans; [exact PX1|]. eapply pres_except_of_rheap_pres; [exact PRES| lia]. }
clear FR G1 G2 MU WM ST HP1 AUX1 SE1 SSP1 PX1 MI ERR AUX.
destruct r as [p|].
*
first [ sf_destruct 7%nat RES as A0 -> BR HP2 BLK EXP SMALL | sf_fb; destruct RES as (A0 & -> & BR & HP2 & BLK & EXP & SMALL) ].
change (Z.to_nat (1 * SIZEOF_SPEEX_HEADER)) with 80%nat in BLK. change (1 * SIZEOF_SPEEX_HEADER) with 80 in HP2, BR.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ]. unfold alloc_ceiling in BR4.
pose proof (HBN _ _ _ HP2) as ND2.
assert (DJ : P + Z.of_nat (length pbytes) <= A0 \/ A0 + 80 <= P).
{ assert (NE2 : blk_id (p, A0, 80) <> blk_id pblk).
{ cbn [map] in ND2. inversion ND2 as [|x l NI ND' E1]; subst. intros E. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. apply in_map. exact HIN. }
pose proof (HBD _ _ _ _ _ HP2 (or_introl eq_refl) (or_intror HIN) NE2) as DJ. cbn [blk_addr blk_size fst snd] in DJ. lia. }
assert (HPRIV : forall a', rclient_addr LB (bv_unsigned sp) a' -> ~ (A0 <= a' < A0 + 80)).
{ intros a' Ha'. eapply (head_block_private HBD s'); [exact HP2| exact ND2| exact BR| exact CEIL| | exact Ha']. lia. }
assert (HBRc : forall x, In x LB -> rblock_range (blk_addr x) (blk_size x)).
{ intros x Hx. exact (HBR _ _ _ _ HP Hx). }
pose proof (header_fields pbytes L80) as HFS. cbv zeta in HFS. first [ sf_destruct 8%nat HFS as E28 E32 E36 E40 E44 E48 E64 E68 | sf_fb; destruct HFS as (E28 & E32 & E36 & E40 & E44 & E48 & E64 & E68) ].
pose proof (s32_range (fw pbytes 40)) as R40. pose proof (fw_range pbytes 40) as U40.
cbv beta iota zeta. rewrite E40.
pose proof (munch_refl [(A0, A0 + 80); (bv_unsigned sp + -32, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
unfold implM. iprefix.

zstep. zstep. zstep. rewrite ?(lor_al4 A0 P) by lia. zstep. nt.
do 4 step.

pose proof PK2 as PK80. unfold u8ro in PK80. rewrite <- (firstn_skipn 80 pbytes) in PK80.
apply (proj1 (bytes_at_app rsegs m2 P (firstn 80 pbytes) (skipn 80 pbytes))) in PK80. destruct PK80 as [PK80 _].
eapply evt_cut.
{ eapply memcpy_callz with (src := firstn 80 pbytes) (junk := repeat (Z_to_bv 8 0) 80);
[exact PK80| rewrite length_firstn; lia| exact BLK| lia| lia| lia| lia| exact MI2]. }
clear BLK PK80.
cbv beta. intros ms'' PM.
first [ sf_destruct 21%nat PM as q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 m3 -> MU3 WM3 MI3 DST SRC3 | sf_fb; destruct PM as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m3 & -> & MU3 & WM3 & MI3 & DST & SRC3) ].
replace (ret_pc (Z_to_bv 64 121580)) with (Z_to_bv 64 121580) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
pose proof (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn; lia)) as FR3.
pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
pose proof (rw_cells_transport rsegs _ m2 m3 _ _ G1' MU3 WM3 ltac:(cbn; lia)) as G1_3.
pose proof (rw_cells_transport rsegs _ m2 m3 _ _ G2' MU3 WM3 ltac:(cbn; lia)) as G2_3.
pose proof (stk_transport rsegs _ m2 m3 _ _ ST2 MU3 WM3 ltac:(cbn; lia)) as ST3.
assert (AUX3 : rauxv_ok m3 AB).
{ eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
assert (HP3 : RHEAP s' ((p, A0, 80) :: LB) m3).
{ eapply HFR; [exact HP2| exact MU3| exact WM3|].
constructor; [right; right; eexists; split; [left; reflexivity| cbn; lia]| constructor]. }
assert (SE3 : stderr_wfile m3).
{ eapply stderr_wfile_kept'; [|exact SE2]. eapply range_kept_of_munch; [exact MU3| exact WM3|]. intros a Ha. unfold BITS_RSTDERR in Ha. cbn. lia. }
assert (PX3 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(BITS_RSTDERR, BITS_RSTDERR + 232)] m m3).
{ eapply pres_except_trans; [exact PX2|].
eapply (pres_except_of_munch_client LB (bv_unsigned sp) lo); [exact HBRc| exact CEIL| lia| exact MU3| exact WM3|].
constructor; [right; right; cbn [fst snd]; exact HPRIV| constructor]. }
assert (HDR : rw_cells rsegs m3 A0 (hdr_cells pbytes (Z_to_bv 64 (fw pbytes 48)))).
{ eapply rw_cells_samebytes; [exact DST| apply hdr_cells_wf; exact L80| | cbn; reflexivity].
rewrite (hdr_cells_bytes pbytes L80). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity. }
clear DST FR2 ERR2 G1' G2' ST2 AUX2 SE2 PX2 MU WM MU3 WM3 MI2 SRC3.
pose proof (munch_refl [(A0, A0 + 80); (bv_unsigned sp + -32, bv_unsigned sp)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
pose proof HDR as HDRc. unfold hdr_cells in HDRc.
zstep. nt.
do 11 (zstep; zstep; zstep; nt).
step. rewrite sx32_w by exact U40.
step.
assert (CASES : 0 <= s32 (fw pbytes 40) < 3 \/ ~ (0 <= s32 (fw pbytes 40) < 3)) by lia.
destruct CASES as [GOOD|BAD].
--
step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit64 in K3 by lia; [exfalso; lia|]. clear K3.
pose proof (s32_range (fw pbytes 48)) as R48. pose proof (fw_range pbytes 48) as U48.
step. rewrite sx32_w by exact U48.
step. if_cases K4; zify_cond K4; rewrite ?signed_lit_small in K4 by lia.
++
step. rewrite (lts_zero_lit (s32 (fw pbytes 48))) by lia. if_cases K5; zify_cond K5.
**
apply evt_done.
replace ((SPEEX_NB_MODES <=? s32 (fw pbytes 40)) || (s32 (fw pbytes 40) <? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.leb_gt; unfold SPEEX_NB_MODES; lia| apply Z.ltb_ge; lia]).
apply implM_ret.
assert (HDRj : rw_cells rsegs m3 A0 (hdr_cells pbytes (Z_to_bv 64 (s32 (fw pbytes 48))))).
{ eapply rw_cells_samebytes; [exact HDR| | |].
- cbn. rewrite length_firstn. repeat split; try lia; exact I.
- unfold hdr_cells. cbn [cells_bytes cbytes]. rewrite !le4_s32_fw. reflexivity.
- cbn. reflexivity. }
eapply (p2h_ok_join ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (cv := s32 (fw pbytes 48)) (pbytes := pbytes);
try eassumption; try reflexivity; try lia.
+++ rewrite ERRA. exact ERR3.
+++ unfold clamp_channels. replace (2 <? s32 (fw pbytes 48)) with false by (symmetry; apply Z.ltb_ge; lia).
replace (s32 (fw pbytes 48) <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
**
step.
apply evt_done.
replace ((SPEEX_NB_MODES <=? s32 (fw pbytes 40)) || (s32 (fw pbytes 40) <? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.leb_gt; unfold SPEEX_NB_MODES; lia| apply Z.ltb_ge; lia]).
apply implM_ret.
eapply p2h_ok_tail; try eassumption; try reflexivity; try lia.
+++ rewrite ERRA. exact ERR3.
+++ unfold clamp_channels. replace (2 <? s32 (fw pbytes 48)) with false by (symmetry; apply Z.ltb_ge; lia).
replace (s32 (fw pbytes 48) <? 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
++
step. step.
apply evt_done.
replace ((SPEEX_NB_MODES <=? s32 (fw pbytes 40)) || (s32 (fw pbytes 40) <? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.leb_gt; unfold SPEEX_NB_MODES; lia| apply Z.ltb_ge; lia]).
apply implM_ret.
eapply p2h_ok_tail; try eassumption; try reflexivity; try lia.
+++ rewrite ERRA. exact ERR3.
+++ unfold clamp_channels. replace (2 <? s32 (fw pbytes 48)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
--
assert (TAKEN : exists u, Z_to_bv 64 (s32 (fw pbytes 40)) = Z_to_bv 64 u /\ 3 <= u < 2^64).
{ destruct (Z_lt_le_dec (s32 (fw pbytes 40)) 0) as [NEG|NN].
- exists (s32 (fw pbytes 40) + 2^64). split; [apply lit64_neg_wrap; lia| lia].
- exists (s32 (fw pbytes 40)). split; [reflexivity| lia]. }
destruct TAKEN as (u & Eu & Hu). rewrite Eu.
step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit64 in K3 by lia; [| exfalso; lia]. clear K3.
apply evt_done.
replace ((SPEEX_NB_MODES <=? s32 (fw pbytes 40)) || (s32 (fw pbytes 40) <? 0)) with true.
2:{ symmetry. destruct (Z_lt_le_dec (s32 (fw pbytes 40)) 0) as [NEG|NN].
- rewrite (proj2 (Z.ltb_lt _ _) NEG). apply orb_true_r.
- unfold SPEEX_NB_MODES. rewrite (proj2 (Z.leb_le 3 (s32 (fw pbytes 40))) ltac:(lia)). reflexivity. }
cbv iota. unfold io_notify.
eapply p2h_badmode_tail; try eassumption; try reflexivity; try lia.
rewrite ERRA. exact ERR3.
*
apply implM_unr.
Qed.
End F.
