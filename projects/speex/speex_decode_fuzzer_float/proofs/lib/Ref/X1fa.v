(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hu X1nq X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

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

Lemma cdbk_nb_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x113b0 CD /\ length CD = 640%nat.
Proof. cdbk_ro_tac 0x113b0 640%nat. Qed.
Lemma cdbk_nb_low1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11630 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x11630 320%nat. Qed.
Lemma cdbk_nb_low2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11770 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x11770 320%nat. Qed.
Lemma cdbk_nb_high1_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x118b0 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x118b0 320%nat. Qed.
Lemma cdbk_nb_high2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x119f0 CD /\ length CD = 320%nat.
Proof. cdbk_ro_tac 0x119f0 320%nat. Qed.
Lemma high_lsp_cdbk_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11b30 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 0x11b30 512%nat. Qed.
Lemma high_lsp_cdbk2_ro : forall m, mem_inv rsegs m -> exists CD, u8ro rsegs m 0x11d30 CD /\ length CD = 512%nat.
Proof. cdbk_ro_tac 0x11d30 512%nat. Qed.

Lemma rodata_ro : forall x, 0x10000 <= x < 0x1b000 -> ro_addr rsegs (wa x) = true.
Proof.
intros x Hx. unfold ro_addr. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
cbn [find_segment Plain.M.loaded_segments Plain_loaded_segments Plain_segment_000 seg_base seg_size].
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

#[using="Type"] Lemma lbr_loop0 : forall (k : nat) (i qlsp pa pend : Z) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 10 - i -> 0 <= i < 10 -> pa = qlsp + 4 * i -> pend = qlsp + 40 ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (10)) (Z_to_bv 64 (pend)) (Z_to_bv 64 (pend)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x25b4c) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (i)) (Z_to_bv 64 (pend)) (Z_to_bv 64 (pa)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x25b30) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp pa pend cur m0
ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> -> QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
zstep. zstep. zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur i _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur i v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep. zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp _ _ _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
sf_eexists 4%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma lbr_loop1 : forall (k : nat) (i qlsp CDB row pt pa pend : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 10 - i -> 0 <= i < 10 -> pt = CDB + row + i -> pend = CDB + row + 10 -> pa = qlsp + 4 * (0 + i) ->
0 <= row -> row + 10 <= Z.of_nat (length CD) -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xb : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pend)) (Z_to_bv 64 (pend)) (Z_to_bv 64 (qlsp + 40)) xb a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x25ba4) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pt)) (Z_to_bv 64 (pend)) (Z_to_bv 64 (pa)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x25b7c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row pt pa pend CD cur m0
ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> -> -> R0 R1 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. zstep. clear RD RD' Hnth.
do 5 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (0 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ _ _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
sf_eexists 5%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma lbr_loop2 : forall (k : nat) (i qlsp CDB row pt pa pend : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> pt = CDB + row + i -> pend = CDB + row + 5 -> pa = qlsp + 4 * (0 + i) ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xb : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pend)) (Z_to_bv 64 (pend)) (Z_to_bv 64 (qlsp + 20)) xb a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x25bfc) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pt)) (Z_to_bv 64 (pend)) (Z_to_bv 64 (pa)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x25bd4) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row pt pa pend CD cur m0
ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> -> -> R0 R1 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. zstep. clear RD RD' Hnth.
do 5 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (0 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (0 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ _ _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
sf_eexists 5%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact Lcur.
Qed.

#[using="Type"] Lemma lbr_loop3 : forall (k : nat) (i qlsp CDB row pt pa pend : Z) (CD : list byte) (cur : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = 5 - i -> 0 <= i < 5 -> pt = CDB + row + i -> pend = CDB + row + 5 -> pa = qlsp + 4 * (5 + i) ->
0 <= row -> row + 5 <= Z.of_nat (length CD) -> u8ro rsegs m1 CDB CD ->
qlsp + 40 <= CDB \/ CDB + Z.of_nat (length CD) <= qlsp ->
u32arr rsegs m1 qlsp cur -> length cur = 10%nat ->
munch [(qlsp, qlsp + 40)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xb : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (qlsp + 40)) s1 (Z_to_bv 64 (pend)) (Z_to_bv 64 (pend)) xb a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x25c4c) fc2 None m2 (seg_rom rsegs)
/\ munch [(qlsp, qlsp + 40)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 qlsp cur' /\ length cur' = 10%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (pa)) s1 (Z_to_bv 64 (pt)) (Z_to_bv 64 (pend)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x25c24) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i qlsp CDB row pt pa pend CD cur m0
ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hi -> -> -> R0 R1 RO AP QA Lcur MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ QA) as BQ. rewrite Lcur in BQ.
pose proof RO as RO'. destruct RO' as [C0 [C1 _]].
assert (Hnth : nth_error CD (Z.to_nat (row + i)) = Some (nth (Z.to_nat (row + i)) CD (Z_to_bv 8 0))).
{ apply nth_error_nth'. lia. }
pose proof (u8ro_read rsegs m1 CDB CD (row + i) _ _ RO Hnth ltac:(lia) ltac:(f_equal; lia)) as RD.
pose proof (u32arr_read_nth rsegs m1 qlsp cur (5 + i) _ QA ltac:(lia) eq_refl) as RD'.
zstep. zstep. clear RD RD' Hnth.
do 5 zstep.
pose proof (u32arr_store_ok rsegs m1 qlsp cur (5 + i) _ QA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 qlsp cur (5 + i) v QA ltac:(lia)) as QA' end.
clear QA. store_done. try clear SOK.
zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) qlsp CDB row _ _ _ CD _ m0); try eassumption; try lia. rewrite upd_length; exact Lcur.
- apply evt_done.
sf_eexists 5%nat. split; [ms_eq|].
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

#[using="Type"] Lemma lsp_unquant_lbr_proof : @lsp_unquant_stmt ptr LspUnquantLbr.
Proof.
unfold lsp_unquant_stmt. intros until m. intros REP OK CG QC LQ STK LO GLO GLQ GLA AQ1 AQ2 AQ3 AQ4 AQ5 -> -> -> MI FRM.
change (lsp_order LspUnquantLbr) with 10 in *. change (4 * 10) with 40 in *.
unfold lsp_entry, A_lsp_unquant_lbr, LSPQ_DEPTH, NB_GLOBALS_TOP in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
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
pose proof (wr_at_apart_ro m qlsp 40 0x113b0 640 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA1.
pose proof (wr_at_apart_ro m qlsp 40 0x11630 320 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA2.
pose proof (wr_at_apart_ro m qlsp 40 0x118b0 320 MI WQ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA3.
clear WQ.
destruct CG as [CG1 CG2]. unfold NB_GOT_LSP_HIGH, NB_GOT_LSP_NB in CG1, CG2.
pose proof (munch_refl [(lo, bv_unsigned sp); (qlsp, qlsp + 40); (A, A + BITS_SIZEOF)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
carve_frame 32%nat STK.

do 7 zstep.
zstep. if_false_x.
do 6 zstep. change (Z.shiftl 10 2) with 40.

pose proof (u32arr_of_f32 rsegs _ _ _ QC) as QA. clear QC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (lbr_loop0 10%nat 0 qlsp _ _ old mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML LQ; try clear QA.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

zstep. zstep.
rebits REP A D b rj Lrj OBJ bs DAT Hbs SIDE.
zstep. call (speex_bits_unpack_unsigned_spec A D b 6); [exact REP | exact OK | lia | exact MI |]. clear REP.
after_unpack b b 6 rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1 OK OK1 Hv1 Lbs1.

zstep. zstep. zstep. zstep. zstep.
zstep. nswrap.
zstep. zstep. zstep.
destruct (cdbk_nb_ro _ MI) as (CD1 & RO1 & LC1).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (lbr_loop1 10%nat 0 qlsp 0x113b0 (uv b 6 * 10) _ _ _ CD1 _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (rewrite LC1; lia).
clear MUL WML LQ LC1; try clear QA; try clear RO1; try clear CD1.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

zstep. zstep.
rebits REP A D (ub b 6) rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1.
zstep. call (speex_bits_unpack_unsigned_spec A D (ub b 6) 6); [exact REP | exact OK1 | lia | exact MI |]. clear REP.
after_unpack b (ub b 6) 6 rj2 Lrj2 OBJ2 bs2 DAT2 Hbs2 SIDE2 OK1 OK2 Hv2 Lbs2.

zstep. zstep. zstep. zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
zstep. nswrap.
zstep. zstep. zstep.
destruct (cdbk_nb_low1_ro _ MI) as (CD2 & RO2 & LC2).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (lbr_loop2 5%nat 0 qlsp 0x11630 (uv (ub b 6) 6 * 5) _ _ _ CD2 _ mc) end.
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
zstep. nswrap.
zstep. zstep. zstep.
destruct (cdbk_nb_high1_ro _ MI) as (CD3 & RO3 & LC3).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(qlsp, qlsp + 40)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (lbr_loop3 5%nat 0 qlsp 0x118b0 (uv (ub (ub b 6) 6) 6 * 5) _ _ _ CD3 _ mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (rewrite LC3; lia).
clear MUL WML LQ LC3; try clear QA; try clear RO3; try clear CD3.
lazymatch goal with H : u32arr rsegs _ qlsp ?c, L : length ?c = 10%nat |- _ => rename H into QA; rename L into LQ end.
try rename MI0 into MI.

do 5 zstep.
release_frame FR STK (bv_unsigned sp).
zstep.
apply evt_done. unfold lsp_unquant_post. cbn [lsp_bits lsp_order].
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _.
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact STK|].
split; [apply f32_of_u32arr; exact QA|]. split; [exact LQ|].
split; [| exact OK3].
split; [exists rj3; split; [exact Lrj3| unfold bits_cells; exact OBJ3]| split; [exists bs3; split; [exact DAT3| exact Hbs3]| exact SIDE3]].
Qed.
End F.
