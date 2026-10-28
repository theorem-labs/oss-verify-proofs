(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1nq X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].
Ltac sgn := repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_sign_lit x) by lia end.

Definition cdbk_bytes (base : Z) (n : nat) : list byte :=
match image_bytes rsegs base n with Some bs => bs | None => [] end.

Lemma cdbk_ro : forall m base n, mem_inv rsegs m ->
ro_bytes_b rsegs base (cdbk_bytes base n) = true -> 0 <= base -> base + Z.of_nat (length (cdbk_bytes base n)) <= 2^64 ->
u8ro rsegs m base (cdbk_bytes base n).
Proof.
intros m base n MI RB H0 HL. unfold u8ro.
pose proof (ro_cells_bytes_at rsegs m base _ (ro_cells_image rsegs m base _ MI RB H0 HL)) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.

Ltac cdbk_ro_tac base n :=
let m := fresh "m" in let MI := fresh "MI" in let L := fresh "L" in
intros m MI; exists (cdbk_bytes base n);
assert (L : length (cdbk_bytes base n) = n) by (vm_compute; reflexivity);
split; [| exact L]; apply cdbk_ro; [exact MI| vm_compute; reflexivity| lia| rewrite L; lia].

Lemma cdbk_nb_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x113a8 CD /\ length CD = 640%nat.
Proof. cdbk_ro_tac 0x113a8 640%nat. Qed.
Lemma cdbk_nb_low1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11628 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x11628 320%nat. Qed.
Lemma cdbk_nb_low2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11768 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x11768 320%nat. Qed.
Lemma cdbk_nb_high1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x118a8 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x118a8 320%nat. Qed.
Lemma cdbk_nb_high2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x119e8 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x119e8 320%nat. Qed.
Lemma high_lsp_cdbk_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11b28 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 0x11b28 512%nat. Qed.
Lemma high_lsp_cdbk2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11d28 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 0x11d28 512%nat. Qed.

Lemma rodata_ro : forall x, 0x10000 <= x < 0x1b000 -> ro_addr rsegs (wa x) = true.
Proof.
intros x Hx. unfold ro_addr. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
cbn [find_segment Ubsan.M.loaded_segments Ubsan_loaded_segments Ubsan_segment_000 seg_base seg_size].
replace (Z.of_N 0x10000 <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x + 1 <=? Z.of_N 0x10000 + Z.of_N 0xb000) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. reflexivity.
Qed.

Lemma wr_at_apart_ro : forall m q k c n, mem_inv rsegs m -> wr_at rsegs m q k -> 0 < k -> 0 < n ->
0x10000 <= c -> c + n <= 0x1b000 ->
q + k <= c \/ c + n <= q.
Proof.
intros m q k c n MI [Hq0 [Hqk W]] Hk Hn Hc0 Hc1.
destruct (Z_lt_dec q (c + n)); [|lia]. destruct (Z_lt_dec c (q + k)); [|lia]. exfalso.
set (x := Z.max q c).
assert (Hx1 : q <= x < q + k) by lia. assert (Hx2 : c <= x < c + n) by lia.
specialize (W (x - q) ltac:(lia)). replace (q + (x - q)) with x in W by lia.
pose proof (rodata_ro x ltac:(lia)) as RO.
destruct (m (wa x)) eqn:E.
- pose proof (mem_inv_ro _ _ MI _ _ E). congruence.
- pose proof (wview_not_ro rsegs m (wa x) W E). congruence.
Qed.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma unpack_pair : forall b n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

#[using="Type"] Lemma nb_loop0 : forall (k : nat) (i qlsp cnt pa : Z) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 10 - i -> 0 <= i < 10 -> cnt = 10 - i -> pa = qlsp + 4 * i -> 0 < qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp y0 y1 y2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2ab34) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 cnt) (Z_to_bv 64 1) (Z_to_bv 64 pa) (Z_to_bv 64 pa) a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2aafc) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp cnt pa cur m0
ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> -> Q0 QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
zstep. if_false_z.
zstep. zstep. zstep. if_false_z.
zstep. if_false_z.
do 5 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur i v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep. zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp _ _ _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
do 15 eexists. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma nb_loop1 : forall (k : nat) (i qlsp CDB row cnt pa : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 10 - i -> 0 <= i < 10 -> cnt = 10 - i -> pa = qlsp + 4 * (0 + i) -> 0 < qlsp -> 0 < CDB ->
0 <= row -> row + 10 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp y0 y1 y2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2abfc) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 CDB) (Z_to_bv 64 i) (Z_to_bv 64 cnt) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 row) (Z_to_bv 64 pa) (Z_to_bv 64 pa) (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2ab88) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row cnt pa CD cur m0
ra sp gp tp t0 t1 t2 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> -> Q0 CB0 R0 R1 R2 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. if_false_z.
zstep. zstep. zstep. if_false_z.
zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. nswrap. zstep. if_false_z.
zstep. nswrap. zstep. zstep. if_false_z.
zstep. zstep. sgn. zstep. zstep. zstep. sgn. if_false_z.
zstep. zstep. clear RD RD' Hnth.
zstep. nswrap. zstep. zstep.
do 4 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (0 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
do 15 eexists. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma nb_loop2 : forall (k : nat) (i qlsp CDB row off : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> off = 4 * (0 + i) -> 0 < qlsp -> 0 < CDB ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp y0 y1 y2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2aca0) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 CDB) (Z_to_bv 64 off) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 row) (Z_to_bv 64 20) a6 a7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2ac40) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row off CD cur m0
ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> Q0 CB0 R0 R1 R2 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. nswrap. zstep. if_false_z.
zstep. nswrap. zstep. zstep. if_false_z.
zstep. zstep. sgn. zstep. zstep. zstep. sgn. if_false_z.
zstep.
zstep. zstep. clear RD RD' Hnth.
zstep.
do 4 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (0 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep. nswrap.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
do 15 eexists. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma nb_loop3 : forall (k : nat) (i qlsp CDB row off : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> off = 4 * (0 + i) -> 0 < qlsp -> 0 < CDB ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp y0 y1 y2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2ad40) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 CDB) (Z_to_bv 64 off) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 row) (Z_to_bv 64 20) a6 a7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2ace0) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row off CD cur m0
ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> Q0 CB0 R0 R1 R2 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. nswrap. zstep. if_false_z.
zstep. nswrap. zstep. zstep. if_false_z.
zstep. zstep. sgn. zstep. zstep. zstep. sgn. if_false_z.
zstep.
zstep. zstep. clear RD RD' Hnth.
zstep.
do 4 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (0 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep. nswrap.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
do 15 eexists. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma nb_loop4 : forall (k : nat) (i qlsp CDB row off : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> off = 4 * (5 + i) -> 0 < qlsp -> 0 < CDB ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp y0 y1 y2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2add8) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 CDB) (Z_to_bv 64 i) (Z_to_bv 64 off) (Z_to_bv 64 0) (Z_to_bv 64 row) (Z_to_bv 64 40) a6 a7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2ad78) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row off CD cur m0
ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> Q0 CB0 R0 R1 R2 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (5 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. nswrap. zstep. if_false_z.
zstep. nswrap. zstep. zstep. if_false_z.
zstep. zstep. sgn. zstep. zstep. zstep. sgn. if_false_z.
zstep.
zstep. zstep. clear RD RD' Hnth.
zstep.
do 4 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (5 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (5 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep. nswrap.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
do 15 eexists. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma nb_loop5 : forall (k : nat) (i qlsp CDB row off : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> off = 4 * (5 + i) -> 0 < qlsp -> 0 < CDB ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp y0 y1 y2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2ae70) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 CDB) (Z_to_bv 64 i) (Z_to_bv 64 off) (Z_to_bv 64 0) (Z_to_bv 64 row) (Z_to_bv 64 40) a6 a7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2ae10) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row off CD cur m0
ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> Q0 CB0 R0 R1 R2 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (5 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. nswrap. zstep. if_false_z.
zstep. nswrap. zstep. zstep. if_false_z.
zstep. zstep. sgn. zstep. zstep. zstep. sgn. if_false_z.
zstep.
zstep. zstep. clear RD RD' Hnth.
zstep.
do 4 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (5 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (5 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep. nswrap.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
do 15 eexists. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

Ltac rebits R A D bb rj Lrj OBJ bs DAT Hbs SIDE :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (R : bits_rep rsegs mc A D bb)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
clear OBJ DAT
end.

Ltac after_unpack b0 bb n rj Lrj OBJ bs DAT Hbs SIDE OKp OKn Hv Lbs :=
try rename MI0 into MI; rewrite (unpack_pair bb n) in *; cbn [fst snd] in *;
lazymatch goal with H : bits_rep _ _ _ _ (ub bb n) |- _ =>
destruct H as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE); unfold bits_cells in OBJ end;
lazymatch goal with H : ?v = Z_to_bv 64 (uv bb n) |- _ => subst v end;
pose proof (speex_bits_unpack_unsigned_ok bb n _ _ OKp ltac:(lia) (unpack_pair bb n)) as (OKn & Hv & _);
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b0)
by (let X := fresh in pose proof OKn as X; unfold bits_ok in X; rewrite Hbs, zlength_map_unsigned, ?ub_size in X; lia).

#[using="Type"] Lemma lsp_unquant_nb_proof : @lsp_unquant_stmt ptr LspUnquantNb.
Proof.
unfold lsp_unquant_stmt. intros until m. intros REP OK CG QC LQ STK LO GLO GLQ GLA AQ1 AQ2 AQ3 AQ4 AQ5 -> -> -> MI FRM Q0 Q4.
change (lsp_order LspUnquantNb) with 10 in *. change (4 * 10) with 40 in *.
unfold lsp_entry, A_lsp_unquant_nb, LSPQ_DEPTH, NB_GLOBALS_TOP in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ. clear REP.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ QC) as GQ. rewrite cells_size_f32, LQ in GQ.

pose proof QC as [_ WQ]. rewrite cells_size_f32, LQ in WQ. change (4 * Z.of_nat 10) with 40 in WQ.
pose proof (wr_at_apart_ro m qlsp 40 0x113a8 640 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA1.
pose proof (wr_at_apart_ro m qlsp 40 0x11628 320 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA2.
pose proof (wr_at_apart_ro m qlsp 40 0x11768 320 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA3.
pose proof (wr_at_apart_ro m qlsp 40 0x118a8 320 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA4.
pose proof (wr_at_apart_ro m qlsp 40 0x119e8 320 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA5.
clear WQ.
destruct CG as [CG1 CG2]. unfold NB_GOT_LSP_HIGH, NB_GOT_LSP_NB in CG1, CG2.
pose proof (munch_refl [(lo, bv_unsigned sp); (qlsp, qlsp + 40); (A, A + BITS_SIZEOF)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold apart in AQ1, AQ2, AQ3, AQ4, AQ5.
carve_frame 64%nat STK.

do 11 zstep.
zstep. if_false_x.
do 8 zstep. cond_prep. rewrite ?Q4. cond_prep.

pose proof (u32arr_of_f32 rsegs _ _ _ QC) as QA. clear QC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (nb_loop0 10%nat 0 qlsp _ _ old mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML LQ; try clear QA.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

do 4 zstep.
rebits REP A D b rj Lrj OBJ bs DAT Hbs SIDE.
zstep. call (speex_bits_unpack_unsigned_spec A D b 6); [exact REP | exact OK | lia | exact MI |]. clear REP.
after_unpack b b 6 rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1 OK OK1 Hv1 Lbs1.

do 4 zstep.
zstep. zstep. nswrap.
zstep. zstep.
zstep. rewrite ?Z.lxor_nilpotent.
zstep. zstep. zstep. nswrap.
zstep. zstep. cond_prep.
destruct (cdbk_nb_ro _ MI) as (CD1 & RO1 & LC1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (nb_loop1 10%nat 0 qlsp 0x113a8 _ _ _ CD1 _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (rewrite LC1; lia).
clear MUL WML LQ LC1; try clear QA; try clear RO1; try clear CD1.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

zstep. zstep.
rebits REP A D (ub b 6) rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1.
zstep. call (speex_bits_unpack_unsigned_spec A D (ub b 6) 6); [exact REP | exact OK1 | lia | exact MI |]. clear REP.
after_unpack b (ub b 6) 6 rj2 Lrj2 OBJ2 bs2 DAT2 Hbs2 SIDE2 OK1 OK2 Hv2 Lbs2.

zstep. zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
zstep. rewrite zb_lxor_ones by lia.
zstep. zstep. zstep. nswrap.
zstep. zstep. zstep.
zstep. rewrite ?Z.lxor_nilpotent.
zstep. zstep. nswrap.
zstep. cond_prep.
destruct (cdbk_nb_low1_ro _ MI) as (CD2 & RO2 & LC2).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (nb_loop2 5%nat 0 qlsp 0x11628 _ _ CD2 _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (rewrite LC2; lia).
clear MUL WML LQ LC2; try clear QA; try clear RO2; try clear CD2.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

zstep. zstep.
rebits REP A D (ub (ub b 6) 6) rj2 Lrj2 OBJ2 bs2 DAT2 Hbs2 SIDE2.
zstep. call (speex_bits_unpack_unsigned_spec A D (ub (ub b 6) 6) 6); [exact REP | exact OK2 | lia | exact MI |]. clear REP.
after_unpack b (ub (ub b 6) 6) 6 rj3 Lrj3 OBJ3 bs3 DAT3 Hbs3 SIDE3 OK2 OK3 Hv3 Lbs3.

zstep. zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
zstep. zstep. zstep. nswrap.
zstep. zstep. zstep.
zstep. rewrite ?Z.lxor_nilpotent.
zstep. zstep. nswrap.
zstep. cond_prep.
destruct (cdbk_nb_low2_ro _ MI) as (CD3 & RO3 & LC3).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (nb_loop3 5%nat 0 qlsp 0x11768 _ _ CD3 _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (rewrite LC3; lia).
clear MUL WML LQ LC3; try clear QA; try clear RO3; try clear CD3.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

zstep. zstep.
rebits REP A D (ub (ub (ub b 6) 6) 6) rj3 Lrj3 OBJ3 bs3 DAT3 Hbs3 SIDE3.
zstep. call (speex_bits_unpack_unsigned_spec A D (ub (ub (ub b 6) 6) 6) 6); [exact REP | exact OK3 | lia | exact MI |]. clear REP.
after_unpack b (ub (ub (ub b 6) 6) 6) 6 rj4 Lrj4 OBJ4 bs4 DAT4 Hbs4 SIDE4 OK3 OK4 Hv4 Lbs4.

zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
zstep. zstep. zstep. zstep. nswrap.
zstep.
zstep. rewrite ?Z.lxor_nilpotent.
zstep. zstep. nswrap.
zstep. cond_prep.
destruct (cdbk_nb_high1_ro _ MI) as (CD4 & RO4 & LC4).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (nb_loop4 5%nat 0 qlsp 0x118a8 _ _ CD4 _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (rewrite LC4; lia).
clear MUL WML LQ LC4; try clear QA; try clear RO4; try clear CD4.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

zstep. zstep.
rebits REP A D (ub (ub (ub (ub b 6) 6) 6) 6) rj4 Lrj4 OBJ4 bs4 DAT4 Hbs4 SIDE4.
zstep. call (speex_bits_unpack_unsigned_spec A D (ub (ub (ub (ub b 6) 6) 6) 6) 6); [exact REP | exact OK4 | lia | exact MI |]. clear REP.
after_unpack b (ub (ub (ub (ub b 6) 6) 6) 6) 6 rj5 Lrj5 OBJ5 bs5 DAT5 Hbs5 SIDE5 OK4 OK5 Hv5 Lbs5.

zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
zstep. zstep. zstep. zstep. nswrap.
zstep.
zstep. rewrite ?Z.lxor_nilpotent.
zstep. zstep. nswrap.
zstep. cond_prep.
destruct (cdbk_nb_high2_ro _ MI) as (CD5 & RO5 & LC5).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (nb_loop5 5%nat 0 qlsp 0x119e8 _ _ CD5 _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (rewrite LC5; lia).
clear MUL WML LQ LC5; try clear QA; try clear RO5; try clear CD5.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

do 8 zstep.
release_frame FR STK (bv_unsigned sp).
zstep.
apply evt_done. unfold lsp_unquant_post. cbn [lsp_bits lsp_order].
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _.
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact STK|].
split; [apply f32_of_u32arr; exact QA|]. split; [exact LQ|].
split; [| exact OK5].
split; [exists rj5; split; [exact Lrj5| unfold bits_cells; exact OBJ5]| split; [exists bs5; split; [exact DAT5| exact Hbs5]| exact SIDE5]].
Qed.
End F.
