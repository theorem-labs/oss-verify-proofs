(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
induction k as [|k next]; intros i qlsp cnt pa cur m0 ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Kfuel Irng Ecnt Epa Qpos Qarr Qlen Fp Wv MI Rnd; [lia|].
subst cnt pa.
destruct (u32arr_bound _ _ _ _ Qarr) as [Qlo Qhi]. rewrite Qlen in Qhi.
zstep. if_false_z.
do 3 zstep. if_false_z.
zstep. if_false_z.
do 5 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i _ Qarr ltac:(lia) eq_refl) as Sok.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur i v Qarr ltac:(lia)) as Qupd end.
clear Qarr. store_done.
lazymatch type of Qupd with u32arr _ _ _ ?l => assert (Qlen1 : length l = 10%nat) by (rewrite upd_length; exact Qlen) end.
do 3 zstep.
if_cases Kc; zify_cond Kc; cycle 1.
- apply evt_done. do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact Qlen1.
- eapply (next (i + 1) qlsp (10 - i + -1) (qlsp + 4 * i + 4));
  [lia | lia | lia | lia | exact Qpos | exact Qupd | exact Qlen1 | exact Fp | exact Wv | exact MI | eassumption].
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
induction k as [|k next]; intros i qlsp CDB row cnt pa CD cur m0 ra sp gp tp t0 t1 t2 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Kfuel Irng Ecnt Epa Qpos Cpos Rpos Rfit Lfit Cro Csep Qarr Qlen Fp Wv MI Rnd; [lia|].
subst cnt pa.
destruct (u32arr_bound _ _ _ _ Qarr) as [Qlo Qhi]. rewrite Qlen in Qhi.
destruct (bytes_at_bound _ _ _ _ Cro) as [Clo Chi].
assert (Nth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0)))
  by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Cro Nth ltac:(lia) eq_refl) as Ld8.
pose proof (u32arr_read_nth rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Qarr ltac:(lia) eq_refl) as Ld32.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i _ Qarr ltac:(lia) eq_refl) as Sok.
zstep. if_false_z.
do 3 zstep. if_false_z.
zstep. if_false_z.
zstep. if_false_z.
do 3 zstep. rewrite (swrap32_small (row + i)) by lia. if_false_z.
zstep. rewrite swrap32_small by lia.
do 2 zstep. if_false_z.
do 5 zstep. sgn. if_false_z.
do 3 zstep. rewrite swrap32_small by lia.
do 7 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur i v Qarr ltac:(lia)) as Qupd end.
clear Qarr. store_done.
lazymatch type of Qupd with u32arr _ _ _ ?l => assert (Qlen1 : length l = 10%nat) by (rewrite upd_length; exact Qlen) end.
do 2 zstep.
if_cases Kc; zify_cond Kc; cycle 1.
- apply evt_done. do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact Qlen1.
- eapply (next (i + 1) qlsp CDB row (10 - i + -1) (qlsp + 4 * (0 + i) + 4));
  [lia | lia | lia | lia | exact Qpos | exact Cpos | exact Rpos | exact Rfit | exact Lfit | exact Cro | exact Csep
  | exact Qupd | exact Qlen1 | exact Fp | exact Wv | exact MI | eassumption].
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
induction k as [|k next]; intros i qlsp CDB row off CD cur m0 ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Kfuel Irng Eoff Qpos Cpos Rpos Rfit Lfit Cro Csep Qarr Qlen Fp Wv MI Rnd; [lia|].
subst off.
destruct (u32arr_bound _ _ _ _ Qarr) as [Qlo Qhi]. rewrite Qlen in Qhi.
destruct (bytes_at_bound _ _ _ _ Cro) as [Clo Chi].
assert (Nth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0)))
  by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Cro Nth ltac:(lia) eq_refl) as Ld8.
pose proof (u32arr_read_nth rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Qarr ltac:(lia) eq_refl) as Ld32.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i _ Qarr ltac:(lia) eq_refl) as Sok.
zstep. if_false_z.
zstep. if_false_z.
do 3 zstep. rewrite (swrap32_small (row + i)) by lia. if_false_z.
zstep. rewrite swrap32_small by lia.
do 2 zstep. if_false_z.
do 5 zstep. sgn. if_false_z.
do 9 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur i v Qarr ltac:(lia)) as Qupd end.
clear Qarr. store_done.
lazymatch type of Qupd with u32arr _ _ _ ?l => assert (Qlen1 : length l = 10%nat) by (rewrite upd_length; exact Qlen) end.
zstep. rewrite swrap32_small by lia. zstep.
if_cases Kc; zify_cond Kc; cycle 1.
- apply evt_done. do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact Qlen1.
- eapply (next (i + 1) qlsp CDB row (4 * (0 + i) + 4));
  [lia | lia | lia | exact Qpos | exact Cpos | exact Rpos | exact Rfit | exact Lfit | exact Cro | exact Csep
  | exact Qupd | exact Qlen1 | exact Fp | exact Wv | exact MI | eassumption].
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
induction k as [|k next]; intros i qlsp CDB row off CD cur m0 ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Kfuel Irng Eoff Qpos Cpos Rpos Rfit Lfit Cro Csep Qarr Qlen Fp Wv MI Rnd; [lia|].
subst off.
destruct (u32arr_bound _ _ _ _ Qarr) as [Qlo Qhi]. rewrite Qlen in Qhi.
destruct (bytes_at_bound _ _ _ _ Cro) as [Clo Chi].
assert (Nth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0)))
  by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Cro Nth ltac:(lia) eq_refl) as Ld8.
pose proof (u32arr_read_nth rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Qarr ltac:(lia) eq_refl) as Ld32.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i _ Qarr ltac:(lia) eq_refl) as Sok.
zstep. if_false_z.
zstep. if_false_z.
do 3 zstep. rewrite (swrap32_small (row + i)) by lia. if_false_z.
zstep. rewrite swrap32_small by lia.
do 2 zstep. if_false_z.
do 5 zstep. sgn. if_false_z.
do 9 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur i v Qarr ltac:(lia)) as Qupd end.
clear Qarr. store_done.
lazymatch type of Qupd with u32arr _ _ _ ?l => assert (Qlen1 : length l = 10%nat) by (rewrite upd_length; exact Qlen) end.
zstep. rewrite swrap32_small by lia. zstep.
if_cases Kc; zify_cond Kc; cycle 1.
- apply evt_done. do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact Qlen1.
- eapply (next (i + 1) qlsp CDB row (4 * (0 + i) + 4));
  [lia | lia | lia | exact Qpos | exact Cpos | exact Rpos | exact Rfit | exact Lfit | exact Cro | exact Csep
  | exact Qupd | exact Qlen1 | exact Fp | exact Wv | exact MI | eassumption].
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
induction k as [|k next]; intros i qlsp CDB row off CD cur m0 ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Kfuel Irng Eoff Qpos Cpos Rpos Rfit Lfit Cro Csep Qarr Qlen Fp Wv MI Rnd; [lia|].
subst off.
destruct (u32arr_bound _ _ _ _ Qarr) as [Qlo Qhi]. rewrite Qlen in Qhi.
destruct (bytes_at_bound _ _ _ _ Cro) as [Clo Chi].
assert (Nth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0)))
  by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Cro Nth ltac:(lia) eq_refl) as Ld8.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (5 + i) (wa (qlsp + 4 * (5 + i))) Qarr ltac:(lia) eq_refl) as Ld32.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (5 + i) _ Qarr ltac:(lia) eq_refl) as Sok.
zstep. if_false_z.
zstep. if_false_z.
do 3 zstep. rewrite (swrap32_small (row + i)) by lia. if_false_z.
zstep. rewrite swrap32_small by lia.
do 2 zstep. if_false_z.
do 5 zstep. sgn. if_false_z.
do 9 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur (5 + i) v Qarr ltac:(lia)) as Qupd end.
clear Qarr. store_done.
lazymatch type of Qupd with u32arr _ _ _ ?l => assert (Qlen1 : length l = 10%nat) by (rewrite upd_length; exact Qlen) end.
zstep. rewrite swrap32_small by lia. zstep.
if_cases Kc; zify_cond Kc; cycle 1.
- apply evt_done. do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact Qlen1.
- eapply (next (i + 1) qlsp CDB row (4 * (5 + i) + 4));
  [lia | lia | lia | exact Qpos | exact Cpos | exact Rpos | exact Rfit | exact Lfit | exact Cro | exact Csep
  | exact Qupd | exact Qlen1 | exact Fp | exact Wv | exact MI | eassumption].
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
induction k as [|k next]; intros i qlsp CDB row off CD cur m0 ra sp gp tp t0 t1 t2 s1 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Kfuel Irng Eoff Qpos Cpos Rpos Rfit Lfit Cro Csep Qarr Qlen Fp Wv MI Rnd; [lia|].
subst off.
destruct (u32arr_bound _ _ _ _ Qarr) as [Qlo Qhi]. rewrite Qlen in Qhi.
destruct (bytes_at_bound _ _ _ _ Cro) as [Clo Chi].
assert (Nth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0)))
  by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Cro Nth ltac:(lia) eq_refl) as Ld8.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (5 + i) (wa (qlsp + 4 * (5 + i))) Qarr ltac:(lia) eq_refl) as Ld32.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (5 + i) _ Qarr ltac:(lia) eq_refl) as Sok.
zstep. if_false_z.
zstep. if_false_z.
do 3 zstep. rewrite (swrap32_small (row + i)) by lia. if_false_z.
zstep. rewrite swrap32_small by lia.
do 2 zstep. if_false_z.
do 5 zstep. sgn. if_false_z.
do 9 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur (5 + i) v Qarr ltac:(lia)) as Qupd end.
clear Qarr. store_done.
lazymatch type of Qupd with u32arr _ _ _ ?l => assert (Qlen1 : length l = 10%nat) by (rewrite upd_length; exact Qlen) end.
zstep. rewrite swrap32_small by lia. zstep.
if_cases Kc; zify_cond Kc; cycle 1.
- apply evt_done. do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact Qlen1.
- eapply (next (i + 1) qlsp CDB row (4 * (5 + i) + 4));
  [lia | lia | lia | exact Qpos | exact Cpos | exact Rpos | exact Rfit | exact Lfit | exact Cro | exact Csep
  | exact Qupd | exact Qlen1 | exact Fp | exact Wv | exact MI | eassumption].
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
unfold lsp_unquant_stmt, lsp_unquant_post.
intros A D b qlsp old lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
  Brep Bok Got Qold Qlen Stk Room Lglo Qglo Aglo QSdj ASdj DSdj QAdj QDdj -> -> -> MI Rnd Qpos Qal.
cbn [lsp_order lsp_entry lsp_bits] in *.
unfold A_lsp_unquant_nb, LSPQ_DEPTH, NB_GLOBALS_TOP, BITS_SIZEOF, apart in *.
unfold lsp_cdbk_got, NB_GOT_LSP_HIGH, NB_GOT_LSP_NB in Got. destruct Got as [GotHi GotNb].
change (Z.to_nat 10) with 10%nat in Qlen.
pose proof (u32arr_of_f32 rsegs m qlsp old Qold) as Qarr. clear Qold.
destruct (u32arr_bound _ _ _ _ Qarr) as [Qlo Qhi]. rewrite Qlen in Qhi. change (Z.of_nat 10) with 10 in Qhi.
pose proof (bv_unsigned_in_range 64 sp) as SPrange. unfold bv_modulus in SPrange.
destruct Brep as ((pad & PadLen & Bcells) & (buf & Bbuf & Bdata) & Bside). unfold bits_cells in Bcells.
assert (BufLen : Z.of_nat (length buf) = sb_buf_size b)
  by (pose proof Bok as Bk; unfold bits_ok in Bk; rewrite Bdata, zlength_map_unsigned in Bk; lia).
pose proof (munch_refl [(lo, bv_unsigned sp); (qlsp, qlsp + 4 * 10); (A, A + 48)] m) as Fp.
pose proof (wmono_refl rsegs m) as Wv.
carve_frame 64%nat Stk.
do 8 zstep.
do 4 zstep. if_false_z.
do 8 zstep.
cond_prep. rewrite ?Qal. cond_prep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (nb_loop0 10 0 qlsp 10 qlsp old mc);
  [lia | lia | lia | lia | lia | exact Qarr | exact Qlen | apply munch_refl | apply wmono_refl | exact MI | exact Rnd | ] end.
try rename MI0 into MI.
do 5 zstep.
rebits Brep0 A D b pad PadLen Bcells buf Bbuf Bdata Bside.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  eapply evt_cut; [eapply (speex_bits_unpack_unsigned_spec A D b 6); [exact Brep0 | exact Bok | lia | exact MI]
  | unfold speex_bits_unpack_unsigned_post, BITS_SIZEOF; post_call rsegs mc] end.
after_unpack b b 6 pad1 PadLen1 Bcells1 buf1 Bbuf1 Bdata1 Bside1 Bok Bok1 Vr1 BufLen1.
repeat match goal with Hdj : sf_dj _ _ _ _ |- _ => clear Hdj end.
clear Brep0 Bdata Bside pad PadLen buf BufLen.
change (2 ^ 6) with 64 in Vr1.
do 14 zstep.
rewrite ?Z.add_0_r, !(swrap32_small (uv b 6 * 10)) by lia.
rewrite Z.mod_small, Z.lxor_nilpotent by lia. cond_prep.
destruct (cdbk_nb_ro _ MI) as (CDa & CDaro & CDalen).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (nb_loop1 10 0 qlsp 0x113a8 (uv b 6 * 10) 10 qlsp CDa _ mc);
  [lia | lia | lia | lia | lia | lia | lia | rewrite CDalen; lia | rewrite CDalen; lia | exact CDaro
  | right; rewrite CDalen; lia | eassumption | eassumption | apply munch_refl | apply wmono_refl | exact MI | eassumption | ] end.
try rename MI0 into MI.
do 3 zstep.
rebits Brep1 A D (ub b 6) pad1 PadLen1 Bcells1 buf1 Bbuf1 Bdata1 Bside1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  eapply evt_cut; [eapply (speex_bits_unpack_unsigned_spec A D (ub b 6) 6); [exact Brep1 | exact Bok1 | lia | exact MI]
  | unfold speex_bits_unpack_unsigned_post, BITS_SIZEOF; post_call rsegs mc] end.
after_unpack b (ub b 6) 6 pad2 PadLen2 Bcells2 buf2 Bbuf2 Bdata2 Bside2 Bok1 Bok2 Vr2 BufLen2.
repeat match goal with Hdj : sf_dj _ _ _ _ |- _ => clear Hdj end.
clear Brep1 Bdata1 Bside1 pad1 PadLen1 buf1 BufLen1.
change (2 ^ 6) with 64 in Vr2.
do 3 zstep. rewrite Z.shiftl_mul_pow2 by lia.
zstep. rewrite zb_lxor_ones by lia.
do 3 zstep. rewrite swrap32_small by lia.
do 7 zstep.
rewrite Z.lxor_nilpotent, Z.add_0_r, swrap32_small by lia. cond_prep.
destruct (cdbk_nb_low1_ro _ MI) as (CDb & CDbro & CDblen).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (nb_loop2 5 0 qlsp 0x11628 (uv (ub b 6) 6 * 4 + uv (ub b 6) 6) 0 CDb _ mc);
  [lia | lia | lia | lia | lia | lia | rewrite CDblen; lia | rewrite CDblen; lia | exact CDbro
  | right; rewrite CDblen; lia | eassumption | eassumption | apply munch_refl | apply wmono_refl | exact MI | eassumption | ] end.
try rename MI0 into MI.
do 3 zstep.
rebits Brep2 A D (ub (ub b 6) 6) pad2 PadLen2 Bcells2 buf2 Bbuf2 Bdata2 Bside2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  eapply evt_cut; [eapply (speex_bits_unpack_unsigned_spec A D (ub (ub b 6) 6) 6); [exact Brep2 | exact Bok2 | lia | exact MI]
  | unfold speex_bits_unpack_unsigned_post, BITS_SIZEOF; post_call rsegs mc] end.
after_unpack b (ub (ub b 6) 6) 6 pad3 PadLen3 Bcells3 buf3 Bbuf3 Bdata3 Bside3 Bok2 Bok3 Vr3 BufLen3.
repeat match goal with Hdj : sf_dj _ _ _ _ |- _ => clear Hdj end.
clear Brep2 Bdata2 Bside2 pad2 PadLen2 buf2 BufLen2.
change (2 ^ 6) with 64 in Vr3.
do 3 zstep. rewrite Z.shiftl_mul_pow2 by lia.
do 3 zstep. rewrite swrap32_small by lia.
do 7 zstep.
rewrite Z.lxor_nilpotent, Z.add_0_r, swrap32_small by lia. cond_prep.
destruct (cdbk_nb_low2_ro _ MI) as (CDc & CDcro & CDclen).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (nb_loop3 5 0 qlsp 0x11768 (uv (ub (ub b 6) 6) 6 * 4 + uv (ub (ub b 6) 6) 6) 0 CDc _ mc);
  [lia | lia | lia | lia | lia | lia | rewrite CDclen; lia | rewrite CDclen; lia | exact CDcro
  | right; rewrite CDclen; lia | eassumption | eassumption | apply munch_refl | apply wmono_refl | exact MI | eassumption | ] end.
try rename MI0 into MI.
do 3 zstep.
rebits Brep3 A D (ub (ub (ub b 6) 6) 6) pad3 PadLen3 Bcells3 buf3 Bbuf3 Bdata3 Bside3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  eapply evt_cut; [eapply (speex_bits_unpack_unsigned_spec A D (ub (ub (ub b 6) 6) 6) 6); [exact Brep3 | exact Bok3 | lia | exact MI]
  | unfold speex_bits_unpack_unsigned_post, BITS_SIZEOF; post_call rsegs mc] end.
after_unpack b (ub (ub (ub b 6) 6) 6) 6 pad4 PadLen4 Bcells4 buf4 Bbuf4 Bdata4 Bside4 Bok3 Bok4 Vr4 BufLen4.
repeat match goal with Hdj : sf_dj _ _ _ _ |- _ => clear Hdj end.
clear Brep3 Bdata3 Bside3 pad3 PadLen3 buf3 BufLen3.
change (2 ^ 6) with 64 in Vr4.
do 2 zstep. rewrite Z.shiftl_mul_pow2 by lia.
do 4 zstep. rewrite swrap32_small by lia.
do 5 zstep.
rewrite Z.lxor_nilpotent, Z.add_0_r, swrap32_small by lia. cond_prep.
destruct (cdbk_nb_high1_ro _ MI) as (CDd & CDdro & CDdlen).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (nb_loop4 5 0 qlsp 0x118a8 (uv (ub (ub (ub b 6) 6) 6) 6 * 4 + uv (ub (ub (ub b 6) 6) 6) 6) 20 CDd _ mc);
  [lia | lia | lia | lia | lia | lia | rewrite CDdlen; lia | rewrite CDdlen; lia | exact CDdro
  | right; rewrite CDdlen; lia | eassumption | eassumption | apply munch_refl | apply wmono_refl | exact MI | eassumption | ] end.
try rename MI0 into MI.
do 3 zstep.
rebits Brep4 A D (ub (ub (ub (ub b 6) 6) 6) 6) pad4 PadLen4 Bcells4 buf4 Bbuf4 Bdata4 Bside4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  eapply evt_cut; [eapply (speex_bits_unpack_unsigned_spec A D (ub (ub (ub (ub b 6) 6) 6) 6) 6); [exact Brep4 | exact Bok4 | lia | exact MI]
  | unfold speex_bits_unpack_unsigned_post, BITS_SIZEOF; post_call rsegs mc] end.
after_unpack b (ub (ub (ub (ub b 6) 6) 6) 6) 6 pad5 PadLen5 Bcells5 buf5 Bbuf5 Bdata5 Bside5 Bok4 Bok5 Vr5 BufLen5.
repeat match goal with Hdj : sf_dj _ _ _ _ |- _ => clear Hdj end.
clear Brep4 Bdata4 Bside4 pad4 PadLen4 buf4 BufLen4.
change (2 ^ 6) with 64 in Vr5.
do 2 zstep. rewrite Z.shiftl_mul_pow2 by lia.
do 4 zstep. rewrite swrap32_small by lia.
do 5 zstep.
rewrite Z.lxor_nilpotent, Z.add_0_r, swrap32_small by lia. cond_prep.
destruct (cdbk_nb_high2_ro _ MI) as (CDe & CDero & CDelen).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  call (nb_loop5 5 0 qlsp 0x119e8 (uv (ub (ub (ub (ub b 6) 6) 6) 6) 6 * 4 + uv (ub (ub (ub (ub b 6) 6) 6) 6) 6) 20 CDe _ mc);
  [lia | lia | lia | lia | lia | lia | rewrite CDelen; lia | rewrite CDelen; lia | exact CDero
  | right; rewrite CDelen; lia | eassumption | eassumption | apply munch_refl | apply wmono_refl | exact MI | eassumption | ] end.
try rename MI0 into MI.
do 9 zstep.
release_frame FR Stk (bv_unsigned sp).
rebits Brep5 A D (ub (ub (ub (ub (ub b 6) 6) 6) 6) 6) pad5 PadLen5 Bcells5 buf5 Bbuf5 Bdata5 Bside5.
apply evt_done.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _.
split; [reflexivity|].
split; [exact Fp|]. split; [exact Wv|]. split; [exact MI|]. split; [eassumption|]. split; [exact Stk|].
split; [apply f32_of_u32arr; eassumption|]. split; [eassumption|]. split; [exact Brep5| exact Bok5].
Qed.
End F.
