(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1nq X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

Lemma lbr_lxor_sign : forall x, 0 <= x < 2^64 -> Z.lxor x 9223372036854775808 = (x + 2^63) mod 2^64.
Proof. intros x Hx. change 9223372036854775808 with (2^63). apply zb_lxor_sign. exact Hx. Qed.

Ltac lx := repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lbr_lxor_sign x) by mlia end.
Ltac pof := lx; cond_prep; lx; if_false_z.
Ltac sxw := first [ rewrite sx32_small by (unfold int31; lia) | nswrap ].

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
Proof. cdbk_ro_tac 70568 640%nat. Qed.
Lemma cdbk_nb_low1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11628 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 71208 320%nat. Qed.
Lemma cdbk_nb_low2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11768 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 71528 320%nat. Qed.
Lemma cdbk_nb_high1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x118a8 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 71848 320%nat. Qed.
Lemma cdbk_nb_high2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x119e8 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 72168 320%nat. Qed.
Lemma high_lsp_cdbk_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11b28 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 72488 512%nat. Qed.
Lemma high_lsp_cdbk2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11d28 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 73000 512%nat. Qed.

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

#[using="Type"] Lemma lbr_loop0 : forall (k : nat) (i qlsp cnt pa pb : Z) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 10 - i -> 0 <= i < 10 -> cnt = 10 - i -> pa = qlsp + 4 * i -> pb = qlsp + 4 * i -> 0 < qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2b1f8) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 cnt) (Z_to_bv 64 1) (Z_to_bv 64 pa) (Z_to_bv 64 pb) a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2b1c0) fc1 None m1 (seg_rom rsegs)).
Proof.
intros k; induction k as [|n Step];
intros i qlsp cnt pa pb cur m0 ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Fuel Rng Cnt Pa Pb QPos Arr Len Foot Mono Inv Rnd; [lia|].
subst cnt pa pb.
assert (Slot : 0 <= i < Z.of_nat (length cur)) by (rewrite Len; lia).
pose proof (u32arr_bound _ _ _ _ Arr) as Room. rewrite Len in Room.
zstep. if_false_z.
do 3 zstep. if_false_z.
zstep. if_false_z.
do 5 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Arr Slot eq_refl) as Wok.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur i v Arr Slot) as Arr' end.
clear Arr. store_done.
do 3 zstep.
destruct (Z.eq_dec i 9) as [Last|More].
- subst i. if_false_x. finish.
  + exact Arr'.
  + rewrite upd_length. exact Len.
- if_true_x.
  eapply Step; try eassumption; try lia.
  rewrite upd_length. exact Len.
Qed.

#[using="Type"] Lemma lbr_loop1 : forall (k : nat) (i qlsp CDB row cnt pa pb : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 10 - i -> 0 <= i < 10 -> cnt = 10 - i -> pa = qlsp + 4 * i -> pb = qlsp + 4 * i -> 0 < qlsp -> 0 < CDB ->
0 <= row -> row + 10 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (y0 y1 x0 x1 x2 x3 x4 x5 x6 x7 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp y0 y1 t2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2b2ac) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 cnt) (Z_to_bv 64 CDB) (Z_to_bv 64 1) (Z_to_bv 64 row) (Z_to_bv 64 pa) (Z_to_bv 64 pb) a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2b23c) fc1 None m1 (seg_rom rsegs)).
Proof.
intros k; induction k as [|n Step];
intros i qlsp CDB row cnt pa pb CD cur m0 ra sp gp tp t0 t1 t2 s1 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Fuel Rng Cnt Pa Pb QPos CdPos RowPos RowFit CdSmall Tab Sep Arr Len Foot Mono Inv Rnd; [lia|].
subst cnt pa pb.
assert (Slot : 0 <= i < Z.of_nat (length cur)) by (rewrite Len; lia).
pose proof (u32arr_bound _ _ _ _ Arr) as Room. rewrite Len in Room.
pose proof (bytes_at_bound _ _ _ _ Tab) as TabRoom.
zstep. zstep. sxw. zstep. if_false_z.
zstep. sxw. zstep. zstep. if_false_z.
do 5 zstep. pof.
zstep. if_false_z.
do 3 zstep. if_false_z.
zstep. if_false_z.
assert (Cell : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Tab Cell ltac:(lia) eq_refl) as Rd8.
zstep.
pose proof (u32arr_read_nth rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Arr Slot eq_refl) as Rd32.
zstep. zstep. sxw.
do 6 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Arr Slot eq_refl) as Wok.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur i v Arr Slot) as Arr' end.
clear Arr. store_done.
zstep. zstep.
destruct (Z.eq_dec i 9) as [Last|More].
- subst i. if_false_x. finish.
  + exact Arr'.
  + rewrite upd_length. exact Len.
- if_true_x.
  eapply Step; try eassumption; try lia.
  rewrite upd_length. exact Len.
Qed.

#[using="Type"] Lemma lbr_loop2 : forall (k : nat) (i qlsp CDB row off : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> off = 4 * i -> 0 < CDB ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2b348) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 off) (Z_to_bv 64 CDB) (Z_to_bv 64 row) (Z_to_bv 64 20) a5 a6 a7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2b2ec) fc1 None m1 (seg_rom rsegs)).
Proof.
intros k; induction k as [|n Step];
intros i qlsp CDB row off CD cur m0 ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Fuel Rng Off CdPos RowPos RowFit CdSmall Tab Sep Arr Len Foot Mono Inv Rnd; [lia|].
subst off.
assert (Slot : 0 <= i < Z.of_nat (length cur)) by (rewrite Len; lia).
pose proof (u32arr_bound _ _ _ _ Arr) as Room. rewrite Len in Room.
pose proof (bytes_at_bound _ _ _ _ Tab) as TabRoom.
zstep. zstep. sxw. zstep. if_false_z.
zstep. sxw. zstep. zstep. if_false_z.
do 5 zstep. pof.
zstep. if_false_z.
zstep.
assert (Cell : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Tab Cell ltac:(lia) eq_refl) as Rd8.
zstep.
pose proof (u32arr_read_nth rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Arr Slot eq_refl) as Rd32.
do 6 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i (wa (qlsp + 4 * i)) Arr Slot eq_refl) as Wok.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur i v Arr Slot) as Arr' end.
clear Arr. store_done.
zstep. sxw. zstep.
destruct (Z.eq_dec i 4) as [Last|More].
- subst i. if_false_x. finish.
  + exact Arr'.
  + rewrite upd_length. exact Len.
- if_true_x.
  eapply Step; try eassumption; try lia.
  rewrite upd_length. exact Len.
Qed.

#[using="Type"] Lemma lbr_loop3 : forall (k : nat) (i qlsp CDB row off : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> off = 20 + 4 * i -> 0 < CDB ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> Z.of_nat (length CD) < 2^31 -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (x0 x1 x2 x3 x4 x5 x6 x7 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2b3d8) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 qlsp) s1 (Z_to_bv 64 i) (Z_to_bv 64 CDB) (Z_to_bv 64 off) (Z_to_bv 64 row) (Z_to_bv 64 40) a5 a6 a7 (Z_to_bv 64 (18446744073709551615 - qlsp)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2b37c) fc1 None m1 (seg_rom rsegs)).
Proof.
intros k; induction k as [|n Step];
intros i qlsp CDB row off CD cur m0 ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
  Fuel Rng Off CdPos RowPos RowFit CdSmall Tab Sep Arr Len Foot Mono Inv Rnd; [lia|].
subst off.
assert (Slot : 0 <= 5 + i < Z.of_nat (length cur)) by (rewrite Len; lia).
pose proof (u32arr_bound _ _ _ _ Arr) as Room. rewrite Len in Room.
pose proof (bytes_at_bound _ _ _ _ Tab) as TabRoom.
zstep. zstep. sxw. zstep. if_false_z.
zstep. sxw. zstep. zstep. if_false_z.
do 5 zstep. pof.
zstep. if_false_z.
zstep.
assert (Cell : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ (wa (CDB + (row + i))) Tab Cell ltac:(lia) eq_refl) as Rd8.
zstep.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (5 + i) (wa (qlsp + 4 * (5 + i))) Arr Slot eq_refl) as Rd32.
do 6 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (5 + i) (wa (qlsp + 4 * (5 + i))) Arr Slot eq_refl) as Wok.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
  pose proof (u32arr_write rsegs m1 qlsp cur (5 + i) v Arr Slot) as Arr' end.
clear Arr. store_done.
zstep. sxw. zstep.
destruct (Z.eq_dec i 4) as [Last|More].
- subst i. if_false_x. finish.
  + exact Arr'.
  + rewrite upd_length. exact Len.
- if_true_x.
  eapply Step; try eassumption; try lia.
  rewrite upd_length. exact Len.
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

#[using="Type"] Lemma lsp_unquant_lbr_proof : @lsp_unquant_stmt ptr LspUnquantLbr.
Proof.
intros A D b qlsp old lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
  Rep Ok Got Old LenOld Stk Deep LoTop QTop ATop QvsStk AvsStk DvsStk QvsA QvsD Ea0 Ea1 Ea2 Inv Rnd QPos QAl.
subst a0 a1 a2.
unfold lsp_unquant_post. cbn [lsp_entry lsp_order lsp_bits] in *.
unfold A_lsp_unquant_lbr, LSPQ_DEPTH, NB_GLOBALS_TOP, BITS_SIZEOF in *.
pose proof (munch_refl [(lo, bv_unsigned sp); (qlsp, qlsp + 40); (A, A + 48)] m) as Foot.
pose proof (wmono_refl rsegs m) as Mono.
pose proof (u32arr_of_f32 rsegs m qlsp old Old) as Lsp. clear Old.
pose proof (u32arr_bound _ _ _ _ Lsp) as QRoom. rewrite LenOld in QRoom. change (Z.of_nat (Z.to_nat 10)) with 10 in QRoom.
destruct Rep as ((pad & PadLen & Hdr) & (buf & Buf & Dmap) & Side). unfold bits_cells in Hdr.
assert (BufLen : Z.of_nat (length buf) = sb_buf_size b)
  by (pose proof Ok as Sz; unfold bits_ok in Sz; rewrite Dmap, zlength_map_unsigned in Sz; lia).
destruct Got as (GotHi & GotNb). unfold NB_GOT_LSP_HIGH, NB_GOT_LSP_NB in GotHi, GotNb.
carve_frame 48%nat Stk.
assert (Bsz : BITS_SIZEOF = 48) by reflexivity.
do 12 zstep. if_false_z.
do 7 zstep. cond_prep.
eapply evt_cut;
  [ eapply (lbr_loop0 10 0 qlsp 10 qlsp qlsp old m1); first [ lia | eassumption | apply munch_refl | apply wmono_refl ]
  | post_call rsegs m1 ].
clear Rnd LenOld.
lazymatch goal with Q : u32arr rsegs _ qlsp ?w, L : length ?w = 10%nat, R : frm0 _ |- _ =>
  rename w into lsp1, Q into Lsp, L into LspLen, R into Rnd end.
do 3 zstep.
rebits Rep0 A D b pad PadLen Hdr buf Buf Dmap Side.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply (speex_bits_unpack_unsigned_spec A D b 6); [ exact Rep0 | exact Ok | lia | assumption ]
  | post_call rsegs mm ] end.
clear Rep0.
after_unpack b b 6 pad1 PadLen1 Hdr1 buf1 Buf1 Dmap1 Side1 Ok Ok1 Id1 BufLen1.
zstep. zstep. zstep. sxw. zstep. if_false_z.
destruct (cdbk_nb_ro _ MI) as (CD1 & Tab1 & LenCD1).
do 10 zstep. cond_prep. sxw.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply (lbr_loop1 10 0 qlsp 70568 (uv b 6 * 10) 10 qlsp qlsp CD1 lsp1 mm);
    first [ lia | eassumption | apply munch_refl | apply wmono_refl ]
  | post_call rsegs mm ] end.
clear Rnd LspLen Tab1.
lazymatch goal with Q : u32arr rsegs _ qlsp ?w, L : length ?w = 10%nat, R : frm0 _ |- _ =>
  rename w into lsp2, Q into Lsp, L into LspLen, R into Rnd end.
do 3 zstep.
rebits Rep1 A D (ub b 6) pad1 PadLen1 Hdr1 buf1 Buf1 Dmap1 Side1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply (speex_bits_unpack_unsigned_spec A D (ub b 6) 6); [ exact Rep1 | exact Ok1 | lia | assumption ]
  | post_call rsegs mm ] end.
clear Rep1.
after_unpack b (ub b 6) 6 pad2 PadLen2 Hdr2 buf2 Buf2 Dmap2 Side2 Ok1 Ok2 Id2 BufLen2.
do 3 zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zsimp. sxw. zstep. if_false_z.
destruct (cdbk_nb_low1_ro _ MI) as (CD2 & Tab2 & LenCD2).
do 9 zstep. sxw. rewrite zb_lxor_ones by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply (lbr_loop2 5 0 qlsp 71208 _ 0 CD2 lsp2 mm);
    first [ lia | eassumption | apply munch_refl | apply wmono_refl ]
  | post_call rsegs mm ] end.
clear Rnd LspLen Tab2.
lazymatch goal with Q : u32arr rsegs _ qlsp ?w, L : length ?w = 10%nat, R : frm0 _ |- _ =>
  rename w into lsp3, Q into Lsp, L into LspLen, R into Rnd end.
do 3 zstep.
rebits Rep2 A D (ub (ub b 6) 6) pad2 PadLen2 Hdr2 buf2 Buf2 Dmap2 Side2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply (speex_bits_unpack_unsigned_spec A D (ub (ub b 6) 6) 6); [ exact Rep2 | exact Ok2 | lia | assumption ]
  | post_call rsegs mm ] end.
clear Rep2.
after_unpack b (ub (ub b 6) 6) 6 pad3 PadLen3 Hdr3 buf3 Buf3 Dmap3 Side3 Ok2 Ok3 Id3 BufLen3.
do 3 zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zsimp. sxw. zstep. if_false_z.
destruct (cdbk_nb_high1_ro _ MI) as (CD3 & Tab3 & LenCD3).
do 6 zstep. sxw.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply evt_cut;
  [ eapply (lbr_loop3 5 0 qlsp 71848 _ 20 CD3 lsp3 mm);
    first [ lia | eassumption | apply munch_refl | apply wmono_refl ]
  | post_call rsegs mm ] end.
clear Rnd LspLen Tab3.
lazymatch goal with Q : u32arr rsegs _ qlsp ?w, L : length ?w = 10%nat, R : frm0 _ |- _ =>
  rename w into lsp4, Q into Lsp, L into LspLen, R into Rnd end.
do 8 zstep.
release_frame FR Stk (bv_unsigned sp).
rebits Rep3 A D (ub (ub (ub b 6) 6) 6) pad3 PadLen3 Hdr3 buf3 Buf3 Dmap3 Side3.
apply evt_done.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, lsp4.
split; [reflexivity|].
split; [exact Foot|]. split; [exact Mono|]. split; [assumption|]. split; [exact Rnd|]. split; [exact Stk|].
split; [apply f32_of_u32arr; exact Lsp|]. split; [rewrite LspLen; reflexivity|].
split; [exact Rep3 | exact Ok3].
Qed.
End F.
