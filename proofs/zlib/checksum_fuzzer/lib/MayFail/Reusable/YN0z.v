(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0z.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma hwe_stop_ge : forall f c u, 4 * c <= u -> halve_while_even (S f) c u = c.
Proof. intros f c u H. cbn [halve_while_even]. replace (u <? 4 * c) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity. Qed.
Lemma hwe_stop_odd : forall f c u, Z.even c = false -> halve_while_even f c u = c.
Proof. intros [|f] c u H; cbn [halve_while_even]; [reflexivity|]. rewrite H. reflexivity. Qed.
Lemma hwe_step : forall f c h u, c = 2 * h -> u < 4 * c -> halve_while_even (S f) c u = halve_while_even f h u.
Proof.
intros f c h u -> Hu. cbn [halve_while_even]. replace (Z.even (2 * h)) with true by (symmetry; rewrite Z.even_mul; reflexivity).
replace (u <? 4 * (2 * h)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma hwe_zero : forall c u, halve_while_even 0 c u = c.
Proof. reflexivity. Qed.
Lemma hwb_stop : forall f c size, size * c < 2 ^ 20 -> halve_while_big (S f) c size = c.
Proof. intros f c size H. cbn [halve_while_big]. replace (65536 * UNIT <=? size * c) with false by (symmetry; apply Z.leb_gt; unfold UNIT; lia). reflexivity. Qed.
Lemma hwb_step : forall f c h size, c = 2 * h -> 2 ^ 20 <= size * c -> halve_while_big (S f) c size = halve_while_big f h size.
Proof.
intros f c h size -> H. cbn [halve_while_big]. replace (65536 * UNIT <=? size * (2 * h)) with true by (symmetry; apply Z.leb_le; unfold UNIT; lia).
rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma small_tab_range : forall r c, (r < 9)%nat -> (c < 3)%nat -> 4 <= nth c (nth r small_cnt_tab []) 0 <= 31.
Proof.
intros r c Hr Hc.
do 9 (destruct r as [|r]; [destruct c as [|[|[|c]]]; [cbn; lia | cbn; lia | cbn; lia | lia] |]). lia.
Qed.
Lemma ic_small : forall sc u i, 0 <= sc <= 8 ->
let row := nth (Z.to_nat sc) small_cnt_tab [] in
(i = 0%nat /\ 4 * znth 0 row <= u \/ i = 1%nat /\ u < 4 * znth 0 row /\ 4 * znth 1 row <= u \/ i = 2%nat /\ u < 4 * znth 0 row /\ u < 4 * znth 1 row) ->
initial_cnt sc u = znth (Z.of_nat i) row.
Proof.
intros sc u i Hsc row Hi.
assert (R : forall c, (c < 3)%nat -> 4 <= znth (Z.of_nat c) row <= 31).
{ intros c Hc. unfold znth. rewrite Nat2Z.id. apply small_tab_range; [| exact Hc]. subst row. lia. }
unfold initial_cnt. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia).
assert (E : small_cnt sc u = znth (Z.of_nat i) row).
{ unfold small_cnt. fold row. destruct Hi as [[-> H]|[(-> & H1 & H2)|(-> & H1 & H2)]].
- replace (u <? 4 * znth 0 row) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- replace (u <? 4 * znth 0 row) with true by (symmetry; apply Z.ltb_lt; lia). replace (u <? 4 * znth 1 row) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- replace (u <? 4 * znth 0 row) with true by (symmetry; apply Z.ltb_lt; lia). replace (u <? 4 * znth 1 row) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
rewrite E. pose proof (R i ltac:(destruct Hi as [[-> _]|[[-> _]|[-> _]]]; lia)) as Ri.
replace (znth (Z.of_nat i) row =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
Lemma ic_med : forall sc u c, 9 <= sc ->
halve_while_big 8%nat (halve_while_even 8%nat (znth (Z.land sc 3) med_cnt_tab) u) (class_size sc) = c ->
initial_cnt sc u = (if (c =? 1) && (class_size sc * c + UNIT <=? PGSZ / 2) then 2 else c).
Proof.
intros sc u c Hsc H. unfold initial_cnt. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia). rewrite H. reflexivity.
Qed.
Lemma den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma den_off0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H. pose proof (u64_range (Z_to_bv 64 v)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma bt_use_lit : forall E u k (b : bool), ew E 56 = Z_to_bv 64 u -> 0 <= u < 2 ^ 48 -> 0 <= k < 2 ^ 62 ->
branch_taken BC_GEU (sv_denot E (SOff 56 0)) (sv_denot E (SLit k)) = b -> if b then k <= u else u < k.
Proof.
intros E u k b E56 Hu Hk H. rewrite (den_off0 E 56 u E56), den_lit, branch_geu, !lit64_small in H by lia.
destruct b; [destruct (u <? k) eqn:X; [discriminate | apply Z.ltb_ge in X; lia] | destruct (u <? k) eqn:X; [apply Z.ltb_lt in X; lia | discriminate]].
Qed.
Lemma bt_use_tab : forall E u t tv (b : bool), ew E 56 = Z_to_bv 64 u -> 0 <= u < 2 ^ 48 -> ew E t = Z_to_bv 64 tv -> 0 <= tv <= 255 ->
branch_taken BC_GEU (sv_denot E (SOff 56 0)) (sv_denot E (SAlu ALU_SLL (SOff t 0) (SLit 2))) = b -> if b then 4 * tv <= u else u < 4 * tv.
Proof.
intros E u t tv b E56 Hu Et Htv H. rewrite (den_off0 E 56 u E56), branch_geu, lit64_small in H by lia.
cbn [sv_denot] in H. rewrite Et, alu64_sll in H. rewrite (lit64_small tv) in H by lia. rewrite Z.add_0_r, (lit64_small tv), (lit64_small 2) in H by lia. change (2 mod 64) with 2 in H.
rewrite sll64_small in H by (change (2 ^ 2) with 4; lia). change (2 ^ 2) with 4 in H.
destruct b; [destruct (u <? tv * 4) eqn:X; [discriminate | apply Z.ltb_ge in X; lia] | destruct (u <? tv * 4) eqn:X; [apply Z.ltb_lt in X; lia | discriminate]].
Qed.
Lemma den_l2 : forall E n c, ew E 35 = Z_to_bv 64 n -> 1 <= n <= 8191 -> 0 <= c <= 64 ->
bv_unsigned (sv_denot E (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit c)) (SLit 20))) = (16 * n * c) / 2 ^ 20.
Proof.
intros E n c E35 Hn Hc. cbn [sv_denot]. rewrite E35, alu64_srl, mul64_unsigned, alu64_sll. rewrite (lit64_small n) by lia. rewrite Z.add_0_r, (lit64_small n), (lit64_small 4), (lit64_small 20), (lit64_small c) by lia.
change (4 mod 64) with 4. change (20 mod 64) with 20. rewrite sll64_small by (change (2 ^ 4) with 16; lia). change (2 ^ 4) with 16.
rewrite mul64_small by nia. rewrite Z.shiftr_div_pow2 by lia. f_equal. lia.
Qed.
Lemma bt_l2 : forall E n c (b : bool), ew E 35 = Z_to_bv 64 n -> 1 <= n <= 8191 -> 0 <= c <= 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit c)) (SLit 20))) (sv_denot E (SLit 0)) = b ->
if b then 2 ^ 20 <= 16 * n * c else 16 * n * c < 2 ^ 20.
Proof.
intros E n c b E35 Hn Hc H. rewrite branch_ne, (den_l2 E n c E35 Hn Hc), den_lit, lit64_small in H by lia.
pose proof (Z_div_mod_eq_full (16 * n * c) (2 ^ 20)) as P1. pose proof (Z.mod_pos_bound (16 * n * c) (2 ^ 20) ltac:(lia)) as P2.
pose proof (Z.div_pos (16 * n * c) (2 ^ 20) ltac:(lia) ltac:(lia)) as P3.
destruct b; destruct (16 * n * c / 2 ^ 20 =? 0) eqn:X; try discriminate; [apply Z.eqb_neq in X | apply Z.eqb_eq in X]; nia.
Qed.
Lemma bt_l2_small : forall E n c, ew E 35 = Z_to_bv 64 n -> 1 <= n <= 8191 -> 0 <= c <= 8 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit c)) (SLit 20))) (sv_denot E (SLit 0)) = true -> False.
Proof. intros E n c E35 Hn Hc H. pose proof (bt_l2 E n c true E35 Hn ltac:(lia) H) as X. cbn in X. nia. Qed.
Lemma den_special : forall E n, ew E 35 = Z_to_bv 64 n -> 1 <= n <= 8191 ->
sv_denot E (SAlu ALU_SUB (SLit 2) (SAlu ALU_SLTU (SLit 2048) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)))) =
Z_to_bv 64 (if 16 * n * 1 + UNIT <=? PGSZ / 2 then 2 else 1).
Proof.
intros E n E35 Hn. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E35, alu64_sub, alu64_sltu, alu64_add, alu64_sll. rewrite (lit64_small n) by lia.
rewrite Z.add_0_r, (lit64_small n), (lit64_small 2), (lit64_small 2048), (lit64_small 4), (lit64_small 16) by lia. change (4 mod 64) with 4. rewrite sll64_small by (change (2 ^ 4) with 16; lia). change (2 ^ 4) with 16.
rewrite add64_small by lia. unfold sltu, UNIT, PGSZ. change (4096 / 2) with 2048.
destruct (2048 <? n * 16 + 16) eqn:X; [apply Z.ltb_lt in X | apply Z.ltb_ge in X].
- replace (16 * n * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia). rewrite sub64_small, lit64_small by lia. reflexivity.
- replace (16 * n * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia). rewrite sub64_small, lit64_small by lia. reflexivity.
Qed.
Lemma den_prod : forall E n e K, ew E 35 = Z_to_bv 64 n -> 1 <= n <= 8191 -> sv_denot E e = Z_to_bv 64 K -> 0 <= K <= 64 ->
sv_denot E (SMd M_MUL (SAlu ALU_SLL (SOff 35 0) (SLit 4)) e) = Z_to_bv 64 (16 * n * K).
Proof.
intros E n e K E35 Hn He HK. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite He, E35, mul64_unsigned, alu64_sll. rewrite (lit64_small n) by lia.
rewrite Z.add_0_r, (lit64_small n), (lit64_small 4), (lit64_small K), (lit64_small (16 * n * K)) by nia. change (4 mod 64) with 4. rewrite sll64_small by (change (2 ^ 4) with 16; lia). change (2 ^ 4) with 16.
rewrite mul64_small by nia. lia.
Qed.
Lemma ctx_word_gen : forall L1 A1 m1 md1 off v, midrep B L1 A1 m1 md1 -> In (MCell (LCtx off) 8 v) (ctx_cells A1) -> (forall z, v <> VLo5 z) ->
word_mem src0segs m1 (CTX + off) (sval_num L1 v).
Proof.
intros L1 A1 m1 md1 off v MID1 Hin Hv. pose proof (memrep_cell B L1 A1 m1 _ (mid_mem _ _ _ _ _ MID1) ltac:(unfold image; apply in_app_iff; left; exact Hin)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr] in C. rewrite (mid_ctx _ _ _ _ _ MID1) in C. change (ms_ctx B) with CTX in C.
destruct v as [z|p|z|]; try exact C. exfalso. exact (Hv z eq_refl).
Qed.
Lemma usage_word : forall L1 A1 m1 md1 c, midrep B L1 A1 m1 md1 -> 0 <= c < 48 ->
word_mem src0segs m1 (LOCK + 8 * c + 472) (usage_of A1 c).
Proof.
intros L1 A1 m1 md1 c MID1 Hc.
replace (LOCK + 8 * c + 472) with (CTX + (CTX_usage + 8 * Z.of_nat (Z.to_nat c))) by (unfold LOCK, CTX, CTX_usage, src0_D_malloc_lock, src0_D_malloc_context; lia).
replace (usage_of A1 c) with (sval_num L1 (VZ (nth (Z.to_nat c) (st_usage A1) 0))) by (unfold usage_of, znth; reflexivity).
apply (ctx_word_gen L1 A1 m1 md1); [exact MID1 | | intros z; discriminate].
unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat c). split; [reflexivity | apply in_seq; lia].
Qed.
Lemma small_cnt_byte : forall L1 A1 m1 md1 r c, midrep B L1 A1 m1 md1 -> (r < 9)%nat -> (c < 3)%nat ->
mbyte src0segs m1 (SCNT + Z.of_nat (3 * r + c)) = Some (Z_to_bv 8 (nth c (nth r small_cnt_tab []) 0)).
Proof.
intros L1 A1 m1 md1 r c MID1 Hr Hc. pose proof (mid_statics _ _ _ _ _ MID1) as ST. pose proof (mid_syms _ _ _ _ _ MID1) as SO.
destruct (so_small_cnt _ SO r c Hr Hc) as (b & Hb & Hv). cbn [ms_segs ms_small_cnt src0_msyms] in Hb.
rewrite (st_tables _ _ ST) by (unfold table_addr; cbn [ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms]; unfold SCNT, src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_size_classes, src0_D_debruijn32; lia).
change (ms_segs B) with src0segs. unfold SCNT. rewrite Hb. f_equal. rewrite <- Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma med_cnt_byte : forall L1 A1 m1 md1 c, midrep B L1 A1 m1 md1 -> (c < 4)%nat ->
exists b, seg_rom src0segs (Z_to_bv 64 (MCNT + Z.of_nat c)) = Some b /\ mbyte src0segs m1 (MCNT + Z.of_nat c) = Some b /\ bv_unsigned b = nth c med_cnt_tab 0.
Proof.
intros L1 A1 m1 md1 c MID1 Hc. pose proof (mid_statics _ _ _ _ _ MID1) as ST. pose proof (mid_syms _ _ _ _ _ MID1) as SO.
destruct (so_med_cnt _ SO c Hc) as (b & Hb & Hv). cbn [ms_segs ms_med_cnt src0_msyms] in Hb. unfold w64 in Hb.
exists b. split; [exact Hb|]. split; [| exact Hv].
rewrite (st_tables _ _ ST) by (unfold table_addr; cbn [ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms]; unfold MCNT, src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_size_classes, src0_D_debruijn32; lia).
change (ms_segs B) with src0segs. unfold w64, MCNT. exact Hb.
Qed.
Section j.
Variables (X : list sptr) (U : Z -> Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (sc n stk : Z).
Hypothesis HI : Inv X None U A.
Hypothesis XR : rawX X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis RSV : rsv_ok A.
Hypothesis SPOK : span_ok A.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis MID : midrep B L A mem md.
Hypothesis AUXP : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem.
Hypothesis PRE : callee_pre B regs mem stk.
Hypothesis Hstk : ASF <= stk <= AS_STACK.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis AMH : alloc_meta_hyp B.
Variable g : Z.
Hypothesis Hg : word_mem src0segs mem GUARD g.
Variables (j1 j2 : Z).
Let sp : Z := bv_unsigned (getr regs 2).
Local Notation csn := (cs L A sc g j1 j2).
Local Notation E00 := (E0 regs csn).
Local Notation WSn := (WS regs).
Let agree_cs' := agree_cs L A regs sc g j1 j2.
Let sv_cs' := sv_cs L A regs sc g j1 j2.
Let agree_reg' := agree_reg L A regs sc g j1 j2.
Let cs_facts' := cs_facts X U L A regs mem md sc HI Hsc MID g j1 j2.
Let pre_facts' := pre_facts regs mem stk PRE.
Let nu : Z := cs L A sc g j1 j2 35.
Lemma nu_facts : 1 <= nu <= 8191 /\ class_size sc = 16 * nu.
Proof. destruct cs_facts' as (_ & _ & _ & C35 & _ & _ & _ & CS). subst nu. split; [exact C35 | exact CS]. Qed.
Section GB.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model) (E1 : env).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis BND1 : bounded s1.
Hypothesis HA1 : env_agree 40 E00 E1.
Hypothesis E1_40 : ew E1 40 = Z_to_bv 64 (ptr_addr L1 m).
Hypothesis Mh1 : m_halted md1 = None.
Hypothesis Mlz1 : m_vm_lazy md1 = [].
Let usage : Z := usage_of s1 sc.
Let K : Z := initial_cnt sc usage.
Definition FRM1 (mm : word -> option byte) : Prop := forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> mm (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x).
Definition CW (E : env) (ss : sstate) (c : config) : Prop := exists ms, c = mkCfg ms md1 /\ st_ok src0segs E ss ms /\ FRM1 (ms_mem ms).
Lemma usage_range : 0 <= usage < 2 ^ 48.
Proof. subst usage. exact (proj1 BND1 sc). Qed.
Lemma K_facts : 1 <= K <= 32 /\ class_size sc * K < 2 ^ 20 /\ (sc <= 26 -> 2 <= K).
Proof. subst K. exact (initial_cnt_facts sc usage Hsc). Qed.
Lemma FRM1_run : forall E rs mm mm', env_agree 40 E00 E -> FRM1 mm -> frame_of E rs mm mm' -> wsub rs SKS = true -> FRM1 mm'.
Proof.
intros E rs mm mm' HA HF Hfr Hs x Hx Hnw. rewrite <- (HF x Hx Hnw). apply (frame_of_at E rs mm mm' x Hfr Hx).
intros Hw. destruct (in_wrange_wsub regs E rs SKS x Hs Hw) as (b & lo & hi & Hin & Hbx). apply Hnw.
unfold SKS in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <-.
cbn [base_val] in Hbx. rewrite (agree_reg' E 2 HA ltac:(lia)) in Hbx. replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) in Hbx by (apply bv_eq; reflexivity). unfold WS. lia.
Qed.
Lemma cw_node : forall E ss ss' c a b (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL PS_GC ss = (ss', RS_stopped (SR_branch c a b)) -> wsub (ss_mem ss) SKS = true -> env_agree 40 E00 E ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true -> forall cfg, CW E (add_cond ss' (mkAC c a b)) cfg -> SR src0segs cfg Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false -> forall cfg, CW E (add_cond ss' (mkAC (neg_bc c) a b)) cfg -> SR src0segs cfg Q) ->
forall cfg, CW E ss cfg -> SR src0segs cfg Q.
Proof.
intros E ss ss' c a b Q RUN WSB HA KT KF cfg (ms & -> & HS & HF).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_GC E ss ss'); [exact Mh1 | exact Mlz1 | exact HS | exact RUN |].
intros ms' HS' Hfr. pose proof (FRM1_run E _ _ _ HA HF Hfr WSB) as HF'.
apply (SR_sym_branch src0segs E ss' ms' md1 Q c a b HS').
- intros Hb HSb. apply (KT Hb). exists ms'. split; [reflexivity|]. split; [exact HSb | exact HF'].
- intros Hb HSb. apply (KF Hb). exists ms'. split; [reflexivity|]. split; [exact HSb | exact HF'].
Qed.
Lemma cw_leaf : forall E ss ss' (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL PS_GC ss = (ss', RS_running) -> wsub (ss_mem ss) SKS = true -> env_agree 40 E00 E ->
(forall cfg, CW E ss' cfg -> SR src0segs cfg Q) ->
forall cfg, CW E ss cfg -> SR src0segs cfg Q.
Proof.
intros E ss ss' Q RUN WSB HA KQ cfg (ms & -> & HS & HF).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_GC E ss ss'); [exact Mh1 | exact Mlz1 | exact HS | exact RUN |].
intros ms' HS' Hfr. apply KQ. exists ms'. split; [reflexivity|]. split; [exact HS' | exact (FRM1_run E _ _ _ HA HF Hfr WSB)].
Qed.
Definition GCpost (c : config) : Prop :=
exists E ms, c = mkCfg ms md1 /\ st_ok src0segs E ss_GC ms /\ env_agree 40 E00 E /\ ew E 40 = Z_to_bv 64 (ptr_addr L1 m) /\
ew E 56 = Z_to_bv 64 usage /\ ew E 61 = Z_to_bv 64 K /\ ew E 62 = Z_to_bv 64 (16 * nu * K) /\ FRM1 (ms_mem ms).
Lemma gc_finish : forall E ss Kv, gc_check ss = true -> env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew E 56 = Z_to_bv 64 usage ->
ew E 35 = Z_to_bv 64 nu -> facts_ok E (ss_facts ss_S3) ->
sv_denot E (sr_get (ss_regs ss) 19) = Z_to_bv 64 Kv -> Kv = K ->
forall cfg, CW E ss cfg -> SR src0segs cfg GCpost.
Proof.
intros E ss Kv CK HA E40 E56 E35 HF3 D19 EK cfg (ms & -> & HS & HF). subst Kv.
pose proof K_facts as (K1 & K2 & K3). pose proof nu_facts as [N1 N2].
unfold gc_check in CK. apply andb_prop in CK as [CK MG]. apply andb_prop in CK as [AT E14]. apply sv_eqb_eq in E14.
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) GC_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs GC_JUNK 61 E ss ms HS AT NZ) as (E' & HA' & HS').
assert (D14 : sv_denot E (sr_get (ss_regs ss) 14) = Z_to_bv 64 (16 * nu * K)) by (rewrite E14; exact (den_prod E nu _ K E35 N1 D19 ltac:(lia))).
assert (R19 : sr_get (ss_regs (junk_regs GC_JUNK 61 ss)) 19 = SOff 61 0).
{ unfold GC_JUNK. cbn [junk_regs ss_regs]. rewrite sr_get_set_other by (intros H; discriminate). rewrite sr_get_set_other by (intros H; discriminate). apply sr_get_set_same. reflexivity. }
assert (R14 : sr_get (ss_regs (junk_regs GC_JUNK 61 ss)) 14 = SOff 62 0).
{ unfold GC_JUNK. cbn [junk_regs ss_regs]. rewrite sr_get_set_other by (intros H; discriminate). apply sr_get_set_same. reflexivity. }
assert (E61 : ew E' 61 = Z_to_bv 64 K).
{ pose proof (st_ok_regs_ok _ E' _ ms HS' 19%bv) as X1. pose proof (st_ok_regs_ok _ E _ ms HS 19%bv) as X2. rewrite R19 in X1. rewrite D19 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
assert (E62 : ew E' 62 = Z_to_bv 64 (16 * nu * K)).
{ pose proof (st_ok_regs_ok _ E' _ ms HS' 14%bv) as X1. pose proof (st_ok_regs_ok _ E _ ms HS 14%bv) as X2. rewrite R14 in X1. rewrite D14 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
destruct HA' as [X' D'].
assert (HFG : facts_ok E' facts_GC).
{ assert (AT3 : facts_atoms_lt 61 (ss_facts ss_S3) = true) by (vm_compute; reflexivity).
pose proof (facts_ok_agree 61 E E' (ss_facts ss_S3) (conj X' D') AT3 HF3) as (Y1 & Y2 & Y3).
unfold facts_GC. split; [| split; [exact Y2 | exact I]]. cbn [f_atoms atoms_ok]. split; [| split; [| exact Y1]].
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E61, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r.
- unfold afact_ok. cbn [af_lo af_hi af_al2]. assert (16 <= 16 * nu * K <= 4194304) by nia. rewrite E62, lit64_small by lia. split; [lia|]. split; [| lia].
change (2 ^ 4) with 16. rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult. }
apply SR_ret. exists E', ms. split; [reflexivity|]. split.
{ exact (st_ok_merge src0segs E' ss_GC (setfacts facts_GC (junk_regs GC_JUNK 61 ss)) ms (st_ok_setfacts src0segs E' _ ms facts_GC HS' HFG) MG). }
split; [split; [intros k Hk; rewrite (X' k) by lia; apply (proj1 HA); exact Hk | rewrite D'; apply (proj2 HA)] |].
split; [rewrite (X' 40%nat) by lia; exact E40|]. split; [rewrite (X' 56%nat) by lia; exact E56|]. split; [exact E61|]. split; [exact E62|]. exact HF.
Qed.
Lemma cw_station : forall E E' ss ss' ssS st (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL PS_GC ss = (ss', RS_stopped st) -> wsub (ss_mem ss) SKS = true -> env_agree 40 E00 E ->
(forall ms, st_ok src0segs E ss' ms -> FRM1 (ms_mem ms) -> st_ok src0segs E' ssS ms) ->
(forall cfg, CW E' ssS cfg -> SR src0segs cfg Q) ->
forall cfg, CW E ss cfg -> SR src0segs cfg Q.
Proof.
intros E E' ss ss' ssS st Q RUN WSB HA ST KQ cfg (ms & -> & HS & HF).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_GC E ss ss'); [exact Mh1 | exact Mlz1 | exact HS | exact RUN |].
intros ms' HS' Hfr. pose proof (FRM1_run E _ _ _ HA HF Hfr WSB) as HF'. apply KQ. exists ms'. split; [reflexivity|]. split; [exact (ST ms' HS' HF') | exact HF'].
Qed.
Lemma ctx_not_WS : forall x, CTX <= x < CTX + CTX_SIZE -> ~ WSn x.
Proof. intros x Hx HW. unfold WS in HW. pose proof (proj1 alloc_ceiling_val). destruct pre_facts' as (_ & _ & P3 & _). unfold CTX_SIZE in Hx. lits. lia. Qed.
Lemma tab_not_WS : forall x, 0 <= x < 2 ^ 20 -> ~ WSn x.
Proof. intros x Hx HW. unfold WS in HW. pose proof (proj1 alloc_ceiling_val). destruct pre_facts' as (_ & _ & P3 & _). lia. Qed.
Lemma station_S3 : forall E ms, st_ok src0segs E ss_g1 ms -> env_agree 40 E00 E -> FRM1 (ms_mem ms) ->
st_ok src0segs (ewset E 56 (Z_to_bv 64 usage)) ss_S3 ms.
Proof.
intros E ms HS HA HF. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts' as (C33 & C33m & _). pose proof usage_range as UR.
set (E' := ewset E 56 (Z_to_bv 64 usage)).
assert (HA' : env_agree 40 E00 E') by (eapply env_agree_trans; [exact HA | eapply env_agree_le; [| apply env_agree_ewset]; lia]).
assert (E33 : ew E' 33 = Z_to_bv 64 (csn 33)) by (apply (agree_cs' E' 33 HA'); lia).
assert (HS0 : st_ok src0segs E' ss_g1 ms) by (eapply (st_ok_agree src0segs 56 E E'); [exact HS | apply env_agree_ewset | exact (proj1 atoms_g1)]).
assert (HS2 : st_ok src0segs E' (mkSS (ss_pc ss_g1) (ss_regs ss_g1) (R_use :: ss_mem ss_g1) (ss_resv ss_g1) (ss_facts ss_g1)) ms).
{ apply (st_ok_add_region src0segs E' _ ms R_use HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_use]; rewrite E33, (u64_of_Z (csn 33)) by (lits; lia); [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E' (ms_mem ms) (csn 33) 472 _ usage).
+ apply den_off0. subst E'. apply ew_ewset_same.
+ apply (word_mem_ext1 mem1).
* intros k Hk. apply HF; [lits; lia|]. apply ctx_not_WS. cbn [cs]. unfold CTX_SIZE. lits. lia.
* cbn [cs]. exact (usage_word L1 s1 mem1 md1 sc MID1 Hsc).
- apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite sk_g1 in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_use]. change (base_val E' (Some 33%nat)) with (bv_unsigned (ew E' 33)). rewrite E33, (u64_of_Z (csn 33)) by (lits; lia).
cbn [In] in Hr. destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?(agree_reg' E' 2 HA') by lia; try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); lits; lia. }
apply (st_ok_add_fact src0segs E' _ ms 56 F_use) in HS2. 2:{ unfold afact_ok, F_use. cbn [af_lo af_hi af_al2]. subst E'. rewrite ew_ewset_same, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
exact HS2.
Qed.
Lemma wsub_part1 : wsub (ss_mem ss_R1) SKS = true /\ wsub (ss_mem ss_S3) SKS = true /\ wsub (ss_mem (add_cond ss_g2 C_sc8)) SKS = true /\ wsub (ss_mem (add_cond ss_g2 C_sc9)) SKS = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Let E2 : env := ewset E1 56 (Z_to_bv 64 usage).
Lemma E2_facts : env_agree 40 E00 E2 /\ ew E2 40 = Z_to_bv 64 (ptr_addr L1 m) /\ ew E2 56 = Z_to_bv 64 usage /\ ew E2 35 = Z_to_bv 64 nu /\ ew E2 10 = Z_to_bv 64 sc.
Proof.
assert (HA2 : env_agree 40 E00 E2) by (eapply env_agree_trans; [exact HA1 | eapply env_agree_le; [| apply env_agree_ewset]; lia]).
split; [exact HA2|]. split; [subst E2; rewrite ew_ewset_other by lia; exact E1_40|]. split; [subst E2; apply ew_ewset_same|].
split; [exact (agree_cs' E2 35 HA2 ltac:(lia))|]. rewrite (agree_reg' E2 10 HA2) by lia. exact R10.
Qed.
Lemma reach_S3 : forall rg1, st_ok src0segs E1 ss_R1 (mkst rg1 (Z_to_bv 64 PS_RAM) mem1 (seg_rom src0segs)) ->
SR src0segs (mkCfg (mkst rg1 (Z_to_bv 64 PS_RAM) mem1 (seg_rom src0segs)) md1) (fun c => CW E2 ss_S3 c /\ exists ms, c = mkCfg ms md1 /\ facts_ok E2 (ss_facts ss_S3)).
Proof.
intros rg1 HS.
assert (C0 : CW E1 ss_R1 (mkCfg (mkst rg1 (Z_to_bv 64 PS_RAM) mem1 (seg_rom src0segs)) md1)).
{ eexists. split; [reflexivity|]. split; [exact HS|]. intros x Hx Hnw. reflexivity. }
revert C0. apply (cw_station E1 E2 ss_R1 ss_g1 ss_S3 _ _ grun_R1 (proj1 wsub_part1) HA1).
- intros ms HS' HF'. exact (station_S3 E1 ms HS' HA1 HF').
- intros cfg (ms & -> & HS3 & HF3). apply SR_ret. split; [exists ms; split; [reflexivity|]; split; assumption|]. exists ms. split; [reflexivity|].
destruct HS3 as (_ & _ & _ & _ & _ & _ & _ & _ & H9). exact H9.
Qed.
Let row : list Z := nth (Z.to_nat sc) small_cnt_tab [].
Let E3 : env := ewset (ewset (ewset (ewset E2 57 (Z_to_bv 64 (SCNT + 3 * sc))) 58 (Z_to_bv 64 (znth 0 row))) 59 (Z_to_bv 64 (znth 1 row))) 60 (Z_to_bv 64 (znth 2 row)).
Lemma E3_agree : env_agree 57 E2 E3.
Proof.
split; [| reflexivity]. intros k Hk. subst E3. rewrite !ew_ewset_other by lia. reflexivity.
Qed.
Lemma E3_facts : env_agree 40 E00 E3 /\ ew E3 40 = Z_to_bv 64 (ptr_addr L1 m) /\ ew E3 56 = Z_to_bv 64 usage /\ ew E3 35 = Z_to_bv 64 nu /\ ew E3 10 = Z_to_bv 64 sc /\
ew E3 57 = Z_to_bv 64 (SCNT + 3 * sc) /\ ew E3 58 = Z_to_bv 64 (znth 0 row) /\ ew E3 59 = Z_to_bv 64 (znth 1 row) /\ ew E3 60 = Z_to_bv 64 (znth 2 row).
Proof.
destruct E2_facts as (A1 & A2 & A3 & A4 & A5). destruct E3_agree as [Y _].
split; [eapply env_agree_trans; [exact A1 | eapply env_agree_le; [| exact E3_agree]; lia]|].
split; [rewrite Y by lia; exact A2|]. split; [rewrite Y by lia; exact A3|]. split; [rewrite Y by lia; exact A4|]. split; [rewrite Y by lia; exact A5|].
subst E3. rewrite !ew_ewset_other, ew_ewset_same by lia. split; [reflexivity|]. split; [rewrite !ew_ewset_other, ew_ewset_same by lia; reflexivity|].
split; [rewrite ew_ewset_other, ew_ewset_same by lia; reflexivity|]. apply ew_ewset_same.
Qed.
Lemma row_range : sc <= 8 -> forall c, 0 <= c < 3 -> 4 <= znth c row <= 31.
Proof. intros H8 c Hc. unfold znth. subst row. apply small_tab_range; lia. Qed.
Lemma station_S4 : sc <= 8 -> forall ms, st_ok src0segs E2 ss_c0 ms -> FRM1 (ms_mem ms) -> st_ok src0segs E3 ss_S4 ms.
Proof.
intros H8 ms HS HF. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts' as (C33 & C33m & _). destruct E3_facts as (HA3 & _ & _ & _ & E10 & E57 & E58 & E59 & E60).
pose proof (row_range H8 0 ltac:(lia)) as R0. pose proof (row_range H8 1 ltac:(lia)) as R1. pose proof (row_range H8 2 ltac:(lia)) as R2.
assert (E33 : ew E3 33 = Z_to_bv 64 (csn 33)) by (apply (agree_cs' E3 33 HA3); lia).
assert (HS0 : st_ok src0segs E3 ss_c0 ms) by (eapply (st_ok_agree src0segs 57 E2 E3); [exact HS | exact E3_agree | exact (proj2 atoms_g1)]).
assert (HS1 : st_ok src0segs E3 (mkSS (ss_pc ss_c0) (sr_set (ss_regs ss_c0) 12 (SOff 57 0)) (ss_mem ss_c0) (ss_resv ss_c0) (ss_facts ss_c0)) ms).
{ apply (st_ok_regs src0segs E3 ss_c0 ms). exact HS0. intros r.
destruct (decide (r = 12%bv)) as [Er|Er].
- subst r. rewrite sr_get_set_same by reflexivity. rewrite (proj1 c0_a2).
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E57, E10, alu64_add, mul64_unsigned. rewrite (lit64_small sc) by lia.
rewrite !Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite (lit64_small sc), (lit64_small 3), (lit64_small (SCNT + 3 * sc)) by (lits; lia). rewrite (lit64_small SCNT) by (lits; lia).
rewrite mul64_small by lia. rewrite add64_small by (lits; lia). lia.
- rewrite sr_get_set_other by exact Er. reflexivity. }
assert (HS2 : st_ok src0segs E3 (mkSS (ss_pc ss_c0) (sr_set (ss_regs ss_c0) 12 (SOff 57 0)) (R_scnt :: ss_mem ss_c0) (ss_resv ss_c0) (ss_facts ss_c0)) ms).
{ apply (st_ok_add_region src0segs E3 _ ms R_scnt HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_scnt]; rewrite E57, (u64_of_Z (SCNT + 3 * sc)) by (lits; lia); [lits; lia | lits; lia | intros o Ho; lia |].
assert (BY : forall c, (c < 3)%nat -> mbyte src0segs (ms_mem ms) (SCNT + 3 * sc + Z.of_nat c) = Some (Z_to_bv 8 (znth (Z.of_nat c) row))).
{ intros c Hc. rewrite (mbyte_ext1 mem1).
- replace (SCNT + 3 * sc + Z.of_nat c) with (SCNT + Z.of_nat (3 * Z.to_nat sc + c)) by lia. unfold znth. rewrite Nat2Z.id. subst row.
exact (small_cnt_byte L1 s1 mem1 md1 (Z.to_nat sc) c MID1 ltac:(lia) Hc).
- apply HF; [lits; lia|]. apply tab_not_WS. lits. lia. }
assert (LB : forall v, 0 <= v < 256 -> Z_to_bv 8 v = Z_to_bv 8 (le_byte v 1 0)).
{ intros v Hv. f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. symmetry. apply Z.mod_small. lia. }
repeat apply Forall_cons; [| | | apply Forall_nil];
(eapply (chunk_ok_cval src0segs E3 (ms_mem ms) (SCNT + 3 * sc) _ 1); [apply den_off0; eassumption | lia |]);
(intros k Hk; destruct k as [|k]; [| lia]); rewrite <- LB by lia.
+ replace (SCNT + 3 * sc + 0 + Z.of_nat 0) with (SCNT + 3 * sc + Z.of_nat 0) by lia. exact (BY 0%nat ltac:(lia)).
+ replace (SCNT + 3 * sc + 1 + Z.of_nat 0) with (SCNT + 3 * sc + Z.of_nat 1) by lia. exact (BY 1%nat ltac:(lia)).
+ replace (SCNT + 3 * sc + 2 + Z.of_nat 0) with (SCNT + 3 * sc + Z.of_nat 2) by lia. exact (BY 2%nat ltac:(lia)).
- apply Forall_forall. intros r Hr. cbn [ss_mem] in Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite sk_c0 in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_scnt]. change (base_val E3 (Some 57%nat)) with (bv_unsigned (ew E3 57)). rewrite E57, (u64_of_Z (SCNT + 3 * sc)) by (lits; lia).
cbn [In] in Hr. destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[]]]]]]; apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?(agree_reg' E3 2 HA3), ?E33 by lia; rewrite ?(u64_of_Z (csn 33)) by (lits; lia);
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); lits; lia. }
apply (st_ok_add_fact src0segs E3 _ ms 60 F_tab) in HS2. 2:{ unfold afact_ok, F_tab. cbn [af_lo af_hi af_al2]. rewrite E60, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
apply (st_ok_add_fact src0segs E3 _ ms 59 F_tab) in HS2. 2:{ unfold afact_ok, F_tab. cbn [af_lo af_hi af_al2]. rewrite E59, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
apply (st_ok_add_fact src0segs E3 _ ms 58 F_tab) in HS2. 2:{ unfold afact_ok, F_tab. cbn [af_lo af_hi af_al2]. rewrite E58, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
apply (st_ok_add_fact src0segs E3 _ ms 57 F_scnt) in HS2. 2:{ unfold afact_ok, F_scnt. cbn [af_lo af_hi af_al2]. rewrite E57, lit64_small by (lits; lia). split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
exact HS2.
Qed.
Lemma station_S5 : forall r, 9 <= sc -> Z.land sc 3 = r -> forall ms, st_ok src0segs E2 ss_g3 ms -> FRM1 (ms_mem ms) -> st_ok src0segs E2 (ss_M r) ms.
Proof.
intros r H9 Hr ms HS HF. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts' as (C33 & C33m & _). destruct E2_facts as (HA2 & _ & _ & _ & E10).
assert (R4 : 0 <= r < 4) by (subst r; split; [apply Z.land_nonneg; lia | change 3 with (Z.ones 2); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia]).
assert (E33 : ew E2 33 = Z_to_bv 64 (csn 33)) by (apply (agree_cs' E2 33 HA2); lia).
assert (HS1 : st_ok src0segs E2 (mkSS (ss_pc ss_g3) (sr_set (ss_regs ss_g3) 12 (SLit (MCNT + r))) (ss_mem ss_g3) (ss_resv ss_g3) (ss_facts ss_g3)) ms).
{ apply (st_ok_regs src0segs E2 ss_g3 ms). exact HS. intros rr.
destruct (decide (rr = 12%bv)) as [Er|Er].
- subst rr. rewrite sr_get_set_same by reflexivity. rewrite (proj2 c0_a2).
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E10, !alu64_add, alu64_and. rewrite (lit64_small sc) by lia.
rewrite !Z.add_0_r, ?Z_to_bv_bv_unsigned. rewrite (lit64_small sc), (lit64_small 3), (lit64_small MCNT), (lit64_small (MCNT + r)) by (lits; lia). rewrite Hr. rewrite add64_small by (lits; lia). reflexivity.
- rewrite sr_get_set_other by exact Er. reflexivity. }
assert (HS2 : st_ok src0segs E2 (mkSS (ss_pc ss_g3) (sr_set (ss_regs ss_g3) 12 (SLit (MCNT + r))) (R_mcnt :: ss_mem ss_g3) (ss_resv ss_g3) (ss_facts ss_g3)) ms).
{ apply (st_ok_add_region src0segs E2 _ ms R_mcnt HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_mcnt]; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. intros i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
destruct (med_cnt_byte L1 s1 mem1 md1 (Z.to_nat i) MID1 ltac:(lia)) as (b & Hb1 & Hb2 & _). rewrite Z2Nat.id in Hb1, Hb2 by lia.
exists b. split; [unfold img_byte; rewrite Z.add_0_l; exact Hb1|]. rewrite Z.add_0_l. rewrite (mbyte_ext1 mem1); [exact Hb2|]. apply HF; [lits; lia|]. apply tab_not_WS. lits. lia.
- rewrite sk_g3. apply Forall_forall. intros rr Hr'. cbn [ss_mem] in Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite sk_c0 in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_mcnt base_val].
cbn [In] in Hr'. destruct Hr' as [Hr'|[Hr'|[Hr'|[Hr'|[Hr'|[]]]]]]; apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr'; cbn in Hr'; injection Hr' as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?(agree_reg' E2 2 HA2), ?E33 by lia; rewrite ?(u64_of_Z (csn 33)) by (lits; lia);
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); lits; lia. }
exact HS2.
Qed.
Lemma tree_c : sc <= 8 -> facts_ok E3 (ss_facts ss_S3) -> forall cfg, CW E3 ss_S4 cfg -> SR src0segs cfg GCpost.
Proof.
intros H8 HF3. pose proof E3_facts as (HA & E40 & E56 & E35 & E10 & E57 & E58 & E59 & E60). pose proof usage_range as UR. pose proof nu_facts as [NU CS].
pose proof (row_range H8 0 ltac:(lia)) as R0. pose proof (row_range H8 1 ltac:(lia)) as R1. pose proof (row_range H8 2 ltac:(lia)) as R2.
assert (Erow : nth (Z.to_nat sc) small_cnt_tab [] = row) by reflexivity.
assert (W_r : wsub (ss_mem ss_c_) SKS = true) by (vm_compute; reflexivity).
assert (W_T : wsub (ss_mem ss_c_T) SKS = true) by (vm_compute; reflexivity).
assert (W_F : wsub (ss_mem ss_c_F) SKS = true) by (vm_compute; reflexivity).
assert (W_FT : wsub (ss_mem ss_c_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_FF : wsub (ss_mem ss_c_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_src : wsub (ss_mem ss_S4) SKS = true) by (vm_compute; reflexivity).
apply (cw_node E3 _ _ _ _ _ _ grun_c_ W_src HA); intros B0.
- pose proof (bt_use_tab E3 usage 58 _ true E56 UR E58 ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_leaf E3 _ _ _ grun_c_T W_r HA).
assert (R19 : sr_get (ss_regs ss_c_T) 19 = SOff 58 0) by (vm_compute; reflexivity).
apply (gc_finish E3 ss_c_T (znth 0 row) gc_c_T HA E40 E56 E35 HF3); [rewrite R19; apply den_off0; exact E58 |].
subst K. symmetry. apply (ic_small sc usage 0%nat ltac:(lia)). cbv zeta. rewrite !Erow. left; split; [reflexivity | lia].
- pose proof (bt_use_tab E3 usage 58 _ false E56 UR E58 ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E3 _ _ _ _ _ _ grun_c_F W_r HA); intros B1.
+ pose proof (bt_use_tab E3 usage 59 _ true E56 UR E59 ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_leaf E3 _ _ _ grun_c_FT W_F HA).
assert (R19 : sr_get (ss_regs ss_c_FT) 19 = SOff 59 0) by (vm_compute; reflexivity).
apply (gc_finish E3 ss_c_FT (znth 1 row) gc_c_FT HA E40 E56 E35 HF3); [rewrite R19; apply den_off0; exact E59 |].
subst K. symmetry. apply (ic_small sc usage 1%nat ltac:(lia)). cbv zeta. rewrite !Erow. right; left; split; [reflexivity | lia].
+ pose proof (bt_use_tab E3 usage 59 _ false E56 UR E59 ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_leaf E3 _ _ _ grun_c_FF W_F HA).
assert (R19 : sr_get (ss_regs ss_c_FF) 19 = SOff 60 0) by (vm_compute; reflexivity).
apply (gc_finish E3 ss_c_FF (znth 2 row) gc_c_FF HA E40 E56 E35 HF3); [rewrite R19; apply den_off0; exact E60 |].
subst K. symmetry. apply (ic_small sc usage 2%nat ltac:(lia)). cbv zeta. rewrite !Erow. right; right; split; [reflexivity | lia].
Qed.
Lemma tree_m0 : 9 <= sc -> Z.land sc 3 = 0 -> facts_ok E2 (ss_facts ss_S3) -> forall cfg, CW E2 (ss_M 0) cfg -> SR src0segs cfg GCpost.
Proof.
intros H9 Hr HF3. pose proof E2_facts as (HA & E40 & E56 & E35 & E10). pose proof usage_range as UR. pose proof nu_facts as [NU CS].
assert (W_r : wsub (ss_mem ss_m0_) SKS = true) by (vm_compute; reflexivity).
assert (W_T : wsub (ss_mem ss_m0_T) SKS = true) by (vm_compute; reflexivity).
assert (W_TT : wsub (ss_mem ss_m0_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTT : wsub (ss_mem ss_m0_TTT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTTF : wsub (ss_mem ss_m0_TTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TTF : wsub (ss_mem ss_m0_TTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TF : wsub (ss_mem ss_m0_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_F : wsub (ss_mem ss_m0_F) SKS = true) by (vm_compute; reflexivity).
assert (W_FT : wsub (ss_mem ss_m0_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTT : wsub (ss_mem ss_m0_FTT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTTF : wsub (ss_mem ss_m0_FTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FTF : wsub (ss_mem ss_m0_FTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FF : wsub (ss_mem ss_m0_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFF : wsub (ss_mem ss_m0_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_src : wsub (ss_mem (ss_M 0)) SKS = true) by (vm_compute; reflexivity).
apply (cw_node E2 _ _ _ _ _ _ grun_m0_ W_src HA); intros B0.
- pose proof (bt_use_lit E2 usage 112 true E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m0_T W_r HA); intros B1.
+ pose proof (bt_l2 E2 nu 28 true E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m0_TT W_T HA); intros B2.
* pose proof (bt_l2 E2 nu 14 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m0_TTT W_TT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 7 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 7 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m0_TTTF W_TTT HA).
assert (R19 : sr_get (ss_regs ss_m0_TTTF) 19 = SLit 7) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m0_TTTF 7 gc_m0_TTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 7 H9); [reflexivity|]. rewrite Hr, CS. change (znth 0 med_cnt_tab) with 28.
rewrite (hwe_stop_ge 7 28 usage) by lia.
rewrite (hwb_step 7 28 14 (16 * nu) eq_refl) by lia.
rewrite (hwb_step 6 14 7 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 5 7 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 14 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m0_TTF W_TT HA).
assert (R19 : sr_get (ss_regs ss_m0_TTF) 19 = SLit 14) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m0_TTF 14 gc_m0_TTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 14 H9); [reflexivity|]. rewrite Hr, CS. change (znth 0 med_cnt_tab) with 28.
rewrite (hwe_stop_ge 7 28 usage) by lia.
rewrite (hwb_step 7 28 14 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 14 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_l2 E2 nu 28 false E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_leaf E2 _ _ _ grun_m0_TF W_T HA).
assert (R19 : sr_get (ss_regs ss_m0_TF) 19 = SLit 28) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m0_TF 28 gc_m0_TF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 28 H9); [reflexivity|]. rewrite Hr, CS. change (znth 0 med_cnt_tab) with 28.
rewrite (hwe_stop_ge 7 28 usage) by lia.
rewrite (hwb_stop 7 28 (16 * nu)) by lia.
reflexivity.
- pose proof (bt_use_lit E2 usage 112 false E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m0_F W_r HA); intros B1.
+ pose proof (bt_use_lit E2 usage 56 true E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m0_FT W_F HA); intros B2.
* pose proof (bt_l2 E2 nu 14 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m0_FTT W_FT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 7 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 7 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m0_FTTF W_FTT HA).
assert (R19 : sr_get (ss_regs ss_m0_FTTF) 19 = SLit 7) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m0_FTTF 7 gc_m0_FTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 7 H9); [reflexivity|]. rewrite Hr, CS. change (znth 0 med_cnt_tab) with 28.
rewrite (hwe_step 7 28 14 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 14 usage) by lia.
rewrite (hwb_step 7 14 7 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 7 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 14 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m0_FTF W_FT HA).
assert (R19 : sr_get (ss_regs ss_m0_FTF) 19 = SLit 14) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m0_FTF 14 gc_m0_FTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 14 H9); [reflexivity|]. rewrite Hr, CS. change (znth 0 med_cnt_tab) with 28.
rewrite (hwe_step 7 28 14 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 14 usage) by lia.
rewrite (hwb_stop 7 14 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_use_lit E2 usage 56 false E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m0_FF W_F HA); intros B2.
* exfalso. exact (bt_l2_small E2 nu 7 E35 NU ltac:(lia) B2).
* pose proof (bt_l2 E2 nu 7 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m0_FFF W_FF HA).
assert (R19 : sr_get (ss_regs ss_m0_FFF) 19 = SLit 7) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m0_FFF 7 gc_m0_FFF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 7 H9); [reflexivity|]. rewrite Hr, CS. change (znth 0 med_cnt_tab) with 28.
rewrite (hwe_step 7 28 14 usage eq_refl) by lia.
rewrite (hwe_step 6 14 7 usage eq_refl) by lia.
rewrite (hwe_stop_odd 6 7 usage eq_refl).
rewrite (hwb_stop 7 7 (16 * nu)) by lia.
reflexivity.
Qed.
Lemma tree_m1 : 9 <= sc -> Z.land sc 3 = 1 -> facts_ok E2 (ss_facts ss_S3) -> forall cfg, CW E2 (ss_M 1) cfg -> SR src0segs cfg GCpost.
Proof.
intros H9 Hr HF3. pose proof E2_facts as (HA & E40 & E56 & E35 & E10). pose proof usage_range as UR. pose proof nu_facts as [NU CS].
assert (W_r : wsub (ss_mem ss_m1_) SKS = true) by (vm_compute; reflexivity).
assert (W_T : wsub (ss_mem ss_m1_T) SKS = true) by (vm_compute; reflexivity).
assert (W_TT : wsub (ss_mem ss_m1_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTT : wsub (ss_mem ss_m1_TTT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTTF : wsub (ss_mem ss_m1_TTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TTF : wsub (ss_mem ss_m1_TTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TF : wsub (ss_mem ss_m1_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_F : wsub (ss_mem ss_m1_F) SKS = true) by (vm_compute; reflexivity).
assert (W_FT : wsub (ss_mem ss_m1_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTT : wsub (ss_mem ss_m1_FTT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTTF : wsub (ss_mem ss_m1_FTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FTF : wsub (ss_mem ss_m1_FTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FF : wsub (ss_mem ss_m1_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFT : wsub (ss_mem ss_m1_FFT) SKS = true) by (vm_compute; reflexivity).
assert (W_FFTF : wsub (ss_mem ss_m1_FFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFF : wsub (ss_mem ss_m1_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFF : wsub (ss_mem ss_m1_FFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_src : wsub (ss_mem (ss_M 1)) SKS = true) by (vm_compute; reflexivity).
apply (cw_node E2 _ _ _ _ _ _ grun_m1_ W_src HA); intros B0.
- pose proof (bt_use_lit E2 usage 96 true E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_T W_r HA); intros B1.
+ pose proof (bt_l2 E2 nu 24 true E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_TT W_T HA); intros B2.
* pose proof (bt_l2 E2 nu 12 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_TTT W_TT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 6 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 6 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m1_TTTF W_TTT HA).
assert (R19 : sr_get (ss_regs ss_m1_TTTF) 19 = SLit 6) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m1_TTTF 6 gc_m1_TTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 6 H9); [reflexivity|]. rewrite Hr, CS. change (znth 1 med_cnt_tab) with 24.
rewrite (hwe_stop_ge 7 24 usage) by lia.
rewrite (hwb_step 7 24 12 (16 * nu) eq_refl) by lia.
rewrite (hwb_step 6 12 6 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 5 6 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 12 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m1_TTF W_TT HA).
assert (R19 : sr_get (ss_regs ss_m1_TTF) 19 = SLit 12) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m1_TTF 12 gc_m1_TTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 12 H9); [reflexivity|]. rewrite Hr, CS. change (znth 1 med_cnt_tab) with 24.
rewrite (hwe_stop_ge 7 24 usage) by lia.
rewrite (hwb_step 7 24 12 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 12 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_l2 E2 nu 24 false E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_leaf E2 _ _ _ grun_m1_TF W_T HA).
assert (R19 : sr_get (ss_regs ss_m1_TF) 19 = SLit 24) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m1_TF 24 gc_m1_TF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 24 H9); [reflexivity|]. rewrite Hr, CS. change (znth 1 med_cnt_tab) with 24.
rewrite (hwe_stop_ge 7 24 usage) by lia.
rewrite (hwb_stop 7 24 (16 * nu)) by lia.
reflexivity.
- pose proof (bt_use_lit E2 usage 96 false E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_F W_r HA); intros B1.
+ pose proof (bt_use_lit E2 usage 48 true E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_FT W_F HA); intros B2.
* pose proof (bt_l2 E2 nu 12 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_FTT W_FT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 6 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 6 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m1_FTTF W_FTT HA).
assert (R19 : sr_get (ss_regs ss_m1_FTTF) 19 = SLit 6) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m1_FTTF 6 gc_m1_FTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 6 H9); [reflexivity|]. rewrite Hr, CS. change (znth 1 med_cnt_tab) with 24.
rewrite (hwe_step 7 24 12 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 12 usage) by lia.
rewrite (hwb_step 7 12 6 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 6 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 12 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m1_FTF W_FT HA).
assert (R19 : sr_get (ss_regs ss_m1_FTF) 19 = SLit 12) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m1_FTF 12 gc_m1_FTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 12 H9); [reflexivity|]. rewrite Hr, CS. change (znth 1 med_cnt_tab) with 24.
rewrite (hwe_step 7 24 12 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 12 usage) by lia.
rewrite (hwb_stop 7 12 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_use_lit E2 usage 48 false E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_FF W_F HA); intros B2.
* pose proof (bt_use_lit E2 usage 24 true E56 UR ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_FFT W_FF HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 6 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 6 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m1_FFTF W_FFT HA).
assert (R19 : sr_get (ss_regs ss_m1_FFTF) 19 = SLit 6) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m1_FFTF 6 gc_m1_FFTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 6 H9); [reflexivity|]. rewrite Hr, CS. change (znth 1 med_cnt_tab) with 24.
rewrite (hwe_step 7 24 12 usage eq_refl) by lia.
rewrite (hwe_step 6 12 6 usage eq_refl) by lia.
rewrite (hwe_stop_ge 5 6 usage) by lia.
rewrite (hwb_stop 7 6 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_use_lit E2 usage 24 false E56 UR ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m1_FFF W_FF HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 3 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 3 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m1_FFFF W_FFF HA).
assert (R19 : sr_get (ss_regs ss_m1_FFFF) 19 = SLit 3) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m1_FFFF 3 gc_m1_FFFF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 3 H9); [reflexivity|]. rewrite Hr, CS. change (znth 1 med_cnt_tab) with 24.
rewrite (hwe_step 7 24 12 usage eq_refl) by lia.
rewrite (hwe_step 6 12 6 usage eq_refl) by lia.
rewrite (hwe_step 5 6 3 usage eq_refl) by lia.
rewrite (hwe_stop_odd 5 3 usage eq_refl).
rewrite (hwb_stop 7 3 (16 * nu)) by lia.
reflexivity.
Qed.
Lemma tree_m2 : 9 <= sc -> Z.land sc 3 = 2 -> facts_ok E2 (ss_facts ss_S3) -> forall cfg, CW E2 (ss_M 2) cfg -> SR src0segs cfg GCpost.
Proof.
intros H9 Hr HF3. pose proof E2_facts as (HA & E40 & E56 & E35 & E10). pose proof usage_range as UR. pose proof nu_facts as [NU CS].
assert (W_r : wsub (ss_mem ss_m2_) SKS = true) by (vm_compute; reflexivity).
assert (W_T : wsub (ss_mem ss_m2_T) SKS = true) by (vm_compute; reflexivity).
assert (W_TT : wsub (ss_mem ss_m2_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTT : wsub (ss_mem ss_m2_TTT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTTF : wsub (ss_mem ss_m2_TTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TTF : wsub (ss_mem ss_m2_TTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TF : wsub (ss_mem ss_m2_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_F : wsub (ss_mem ss_m2_F) SKS = true) by (vm_compute; reflexivity).
assert (W_FT : wsub (ss_mem ss_m2_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTT : wsub (ss_mem ss_m2_FTT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTTF : wsub (ss_mem ss_m2_FTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FTF : wsub (ss_mem ss_m2_FTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FF : wsub (ss_mem ss_m2_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFF : wsub (ss_mem ss_m2_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_src : wsub (ss_mem (ss_M 2)) SKS = true) by (vm_compute; reflexivity).
apply (cw_node E2 _ _ _ _ _ _ grun_m2_ W_src HA); intros B0.
- pose proof (bt_use_lit E2 usage 80 true E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m2_T W_r HA); intros B1.
+ pose proof (bt_l2 E2 nu 20 true E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m2_TT W_T HA); intros B2.
* pose proof (bt_l2 E2 nu 10 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m2_TTT W_TT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 5 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 5 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m2_TTTF W_TTT HA).
assert (R19 : sr_get (ss_regs ss_m2_TTTF) 19 = SLit 5) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m2_TTTF 5 gc_m2_TTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 5 H9); [reflexivity|]. rewrite Hr, CS. change (znth 2 med_cnt_tab) with 20.
rewrite (hwe_stop_ge 7 20 usage) by lia.
rewrite (hwb_step 7 20 10 (16 * nu) eq_refl) by lia.
rewrite (hwb_step 6 10 5 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 5 5 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 10 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m2_TTF W_TT HA).
assert (R19 : sr_get (ss_regs ss_m2_TTF) 19 = SLit 10) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m2_TTF 10 gc_m2_TTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 10 H9); [reflexivity|]. rewrite Hr, CS. change (znth 2 med_cnt_tab) with 20.
rewrite (hwe_stop_ge 7 20 usage) by lia.
rewrite (hwb_step 7 20 10 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 10 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_l2 E2 nu 20 false E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_leaf E2 _ _ _ grun_m2_TF W_T HA).
assert (R19 : sr_get (ss_regs ss_m2_TF) 19 = SLit 20) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m2_TF 20 gc_m2_TF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 20 H9); [reflexivity|]. rewrite Hr, CS. change (znth 2 med_cnt_tab) with 20.
rewrite (hwe_stop_ge 7 20 usage) by lia.
rewrite (hwb_stop 7 20 (16 * nu)) by lia.
reflexivity.
- pose proof (bt_use_lit E2 usage 80 false E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m2_F W_r HA); intros B1.
+ pose proof (bt_use_lit E2 usage 40 true E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m2_FT W_F HA); intros B2.
* pose proof (bt_l2 E2 nu 10 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m2_FTT W_FT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 5 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 5 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m2_FTTF W_FTT HA).
assert (R19 : sr_get (ss_regs ss_m2_FTTF) 19 = SLit 5) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m2_FTTF 5 gc_m2_FTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 5 H9); [reflexivity|]. rewrite Hr, CS. change (znth 2 med_cnt_tab) with 20.
rewrite (hwe_step 7 20 10 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 10 usage) by lia.
rewrite (hwb_step 7 10 5 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 5 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 10 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m2_FTF W_FT HA).
assert (R19 : sr_get (ss_regs ss_m2_FTF) 19 = SLit 10) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m2_FTF 10 gc_m2_FTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 10 H9); [reflexivity|]. rewrite Hr, CS. change (znth 2 med_cnt_tab) with 20.
rewrite (hwe_step 7 20 10 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 10 usage) by lia.
rewrite (hwb_stop 7 10 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_use_lit E2 usage 40 false E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m2_FF W_F HA); intros B2.
* exfalso. exact (bt_l2_small E2 nu 5 E35 NU ltac:(lia) B2).
* pose proof (bt_l2 E2 nu 5 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m2_FFF W_FF HA).
assert (R19 : sr_get (ss_regs ss_m2_FFF) 19 = SLit 5) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m2_FFF 5 gc_m2_FFF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 5 H9); [reflexivity|]. rewrite Hr, CS. change (znth 2 med_cnt_tab) with 20.
rewrite (hwe_step 7 20 10 usage eq_refl) by lia.
rewrite (hwe_step 6 10 5 usage eq_refl) by lia.
rewrite (hwe_stop_odd 6 5 usage eq_refl).
rewrite (hwb_stop 7 5 (16 * nu)) by lia.
reflexivity.
Qed.
Lemma tree_m3 : 9 <= sc -> Z.land sc 3 = 3 -> facts_ok E2 (ss_facts ss_S3) -> forall cfg, CW E2 (ss_M 3) cfg -> SR src0segs cfg GCpost.
Proof.
intros H9 Hr HF3. pose proof E2_facts as (HA & E40 & E56 & E35 & E10). pose proof usage_range as UR. pose proof nu_facts as [NU CS].
assert (W_r : wsub (ss_mem ss_m3_) SKS = true) by (vm_compute; reflexivity).
assert (W_T : wsub (ss_mem ss_m3_T) SKS = true) by (vm_compute; reflexivity).
assert (W_TT : wsub (ss_mem ss_m3_TT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTT : wsub (ss_mem ss_m3_TTT) SKS = true) by (vm_compute; reflexivity).
assert (W_TTTF : wsub (ss_mem ss_m3_TTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TTF : wsub (ss_mem ss_m3_TTF) SKS = true) by (vm_compute; reflexivity).
assert (W_TF : wsub (ss_mem ss_m3_TF) SKS = true) by (vm_compute; reflexivity).
assert (W_F : wsub (ss_mem ss_m3_F) SKS = true) by (vm_compute; reflexivity).
assert (W_FT : wsub (ss_mem ss_m3_FT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTT : wsub (ss_mem ss_m3_FTT) SKS = true) by (vm_compute; reflexivity).
assert (W_FTTF : wsub (ss_mem ss_m3_FTTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FTF : wsub (ss_mem ss_m3_FTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FF : wsub (ss_mem ss_m3_FF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFT : wsub (ss_mem ss_m3_FFT) SKS = true) by (vm_compute; reflexivity).
assert (W_FFTF : wsub (ss_mem ss_m3_FFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFF : wsub (ss_mem ss_m3_FFF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFT : wsub (ss_mem ss_m3_FFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFTF : wsub (ss_mem ss_m3_FFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFF : wsub (ss_mem ss_m3_FFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFFT : wsub (ss_mem ss_m3_FFFFT) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFFTF : wsub (ss_mem ss_m3_FFFFTF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFFF : wsub (ss_mem ss_m3_FFFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_FFFFFF : wsub (ss_mem ss_m3_FFFFFF) SKS = true) by (vm_compute; reflexivity).
assert (W_src : wsub (ss_mem (ss_M 3)) SKS = true) by (vm_compute; reflexivity).
apply (cw_node E2 _ _ _ _ _ _ grun_m3_ W_src HA); intros B0.
- pose proof (bt_use_lit E2 usage 128 true E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_T W_r HA); intros B1.
+ pose proof (bt_l2 E2 nu 32 true E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_TT W_T HA); intros B2.
* pose proof (bt_l2 E2 nu 16 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_TTT W_TT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 8 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 8 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m3_TTTF W_TTT HA).
assert (R19 : sr_get (ss_regs ss_m3_TTTF) 19 = SLit 8) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_TTTF 8 gc_m3_TTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 8 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_stop_ge 7 32 usage) by lia.
rewrite (hwb_step 7 32 16 (16 * nu) eq_refl) by lia.
rewrite (hwb_step 6 16 8 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 5 8 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 16 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m3_TTF W_TT HA).
assert (R19 : sr_get (ss_regs ss_m3_TTF) 19 = SLit 16) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_TTF 16 gc_m3_TTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 16 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_stop_ge 7 32 usage) by lia.
rewrite (hwb_step 7 32 16 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 16 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_l2 E2 nu 32 false E35 NU ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_leaf E2 _ _ _ grun_m3_TF W_T HA).
assert (R19 : sr_get (ss_regs ss_m3_TF) 19 = SLit 32) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_TF 32 gc_m3_TF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 32 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_stop_ge 7 32 usage) by lia.
rewrite (hwb_stop 7 32 (16 * nu)) by lia.
reflexivity.
- pose proof (bt_use_lit E2 usage 128 false E56 UR ltac:(lia) B0) as F0; cbv iota in F0.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_F W_r HA); intros B1.
+ pose proof (bt_use_lit E2 usage 64 true E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FT W_F HA); intros B2.
* pose proof (bt_l2 E2 nu 16 true E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FTT W_FT HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 8 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 8 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m3_FTTF W_FTT HA).
assert (R19 : sr_get (ss_regs ss_m3_FTTF) 19 = SLit 8) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_FTTF 8 gc_m3_FTTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 8 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_step 7 32 16 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 16 usage) by lia.
rewrite (hwb_step 7 16 8 (16 * nu) eq_refl) by lia.
rewrite (hwb_stop 6 8 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_l2 E2 nu 16 false E35 NU ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_leaf E2 _ _ _ grun_m3_FTF W_FT HA).
assert (R19 : sr_get (ss_regs ss_m3_FTF) 19 = SLit 16) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_FTF 16 gc_m3_FTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 16 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_step 7 32 16 usage eq_refl) by lia.
rewrite (hwe_stop_ge 6 16 usage) by lia.
rewrite (hwb_stop 7 16 (16 * nu)) by lia.
reflexivity.
+ pose proof (bt_use_lit E2 usage 64 false E56 UR ltac:(lia) B1) as F1; cbv iota in F1.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FF W_F HA); intros B2.
* pose proof (bt_use_lit E2 usage 32 true E56 UR ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FFT W_FF HA); intros B3.
-- exfalso. exact (bt_l2_small E2 nu 8 E35 NU ltac:(lia) B3).
-- pose proof (bt_l2 E2 nu 8 false E35 NU ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_leaf E2 _ _ _ grun_m3_FFTF W_FFT HA).
assert (R19 : sr_get (ss_regs ss_m3_FFTF) 19 = SLit 8) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_FFTF 8 gc_m3_FFTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 8 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_step 7 32 16 usage eq_refl) by lia.
rewrite (hwe_step 6 16 8 usage eq_refl) by lia.
rewrite (hwe_stop_ge 5 8 usage) by lia.
rewrite (hwb_stop 7 8 (16 * nu)) by lia.
reflexivity.
* pose proof (bt_use_lit E2 usage 32 false E56 UR ltac:(lia) B2) as F2; cbv iota in F2.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FFF W_FF HA); intros B3.
-- pose proof (bt_use_lit E2 usage 16 true E56 UR ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FFFT W_FFF HA); intros B4.
++ exfalso. exact (bt_l2_small E2 nu 4 E35 NU ltac:(lia) B4).
++ pose proof (bt_l2 E2 nu 4 false E35 NU ltac:(lia) B4) as F4; cbv iota in F4.
apply (cw_leaf E2 _ _ _ grun_m3_FFFTF W_FFFT HA).
assert (R19 : sr_get (ss_regs ss_m3_FFFTF) 19 = SLit 4) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_FFFTF 4 gc_m3_FFFTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 4 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_step 7 32 16 usage eq_refl) by lia.
rewrite (hwe_step 6 16 8 usage eq_refl) by lia.
rewrite (hwe_step 5 8 4 usage eq_refl) by lia.
rewrite (hwe_stop_ge 4 4 usage) by lia.
rewrite (hwb_stop 7 4 (16 * nu)) by lia.
reflexivity.
-- pose proof (bt_use_lit E2 usage 16 false E56 UR ltac:(lia) B3) as F3; cbv iota in F3.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FFFF W_FFF HA); intros B4.
++ pose proof (bt_use_lit E2 usage 8 true E56 UR ltac:(lia) B4) as F4; cbv iota in F4.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FFFFT W_FFFF HA); intros B5.
** exfalso. exact (bt_l2_small E2 nu 2 E35 NU ltac:(lia) B5).
** pose proof (bt_l2 E2 nu 2 false E35 NU ltac:(lia) B5) as F5; cbv iota in F5.
apply (cw_leaf E2 _ _ _ grun_m3_FFFFTF W_FFFFT HA).
assert (R19 : sr_get (ss_regs ss_m3_FFFFTF) 19 = SLit 2) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_FFFFTF 2 gc_m3_FFFFTF HA E40 E56 E35 HF3); [rewrite R19; apply den_lit |].
subst K. symmetry. rewrite (ic_med sc usage 2 H9); [reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_step 7 32 16 usage eq_refl) by lia.
rewrite (hwe_step 6 16 8 usage eq_refl) by lia.
rewrite (hwe_step 5 8 4 usage eq_refl) by lia.
rewrite (hwe_step 4 4 2 usage eq_refl) by lia.
rewrite (hwe_stop_ge 3 2 usage) by lia.
rewrite (hwb_stop 7 2 (16 * nu)) by lia.
reflexivity.
++ pose proof (bt_use_lit E2 usage 8 false E56 UR ltac:(lia) B4) as F4; cbv iota in F4.
apply (cw_node E2 _ _ _ _ _ _ grun_m3_FFFFF W_FFFF HA); intros B5.
** exfalso. exact (bt_l2_small E2 nu 1 E35 NU ltac:(lia) B5).
** pose proof (bt_l2 E2 nu 1 false E35 NU ltac:(lia) B5) as F5; cbv iota in F5.
apply (cw_leaf E2 _ _ _ grun_m3_FFFFFF W_FFFFF HA).
assert (R19 : sr_get (ss_regs ss_m3_FFFFFF) 19 = SAlu ALU_SUB (SLit 2) (SAlu ALU_SLTU (SLit 2048) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)))) by (vm_compute; reflexivity).
apply (gc_finish E2 ss_m3_FFFFFF (if 16 * nu * 1 + UNIT <=? PGSZ / 2 then 2 else 1) gc_m3_FFFFFF HA E40 E56 E35 HF3); [rewrite R19; exact (den_special E2 nu E35 NU) |].
subst K. symmetry. rewrite (ic_med sc usage 1 H9); [rewrite CS; reflexivity|]. rewrite Hr, CS. change (znth 3 med_cnt_tab) with 32.
rewrite (hwe_step 7 32 16 usage eq_refl) by lia.
rewrite (hwe_step 6 16 8 usage eq_refl) by lia.
rewrite (hwe_step 5 8 4 usage eq_refl) by lia.
rewrite (hwe_step 4 4 2 usage eq_refl) by lia.
rewrite (hwe_step 3 2 1 usage eq_refl) by lia.
rewrite (hwe_stop_odd 3 1 usage eq_refl).
rewrite (hwb_stop 7 1 (16 * nu)) by lia.
reflexivity.
Qed.
Lemma bt_sc : forall E (b : bool), ew E 10 = Z_to_bv 64 sc ->
branch_taken BC_LT (sv_denot E (SLit 8)) (sv_denot E (SOff 10 0)) = b -> if b then 9 <= sc else sc <= 8.
Proof.
intros E b E10 H. rewrite (den_off0 E 10 sc E10), den_lit, branch_lt, !lit64_small in H by lia.
unfold s64 in H. replace (8 <? 2 ^ 63) with true in H by reflexivity. replace (sc <? 2 ^ 63) with true in H by (symmetry; apply Z.ltb_lt; lia).
destruct b; [destruct (8 <? sc) eqn:Y; [apply Z.ltb_lt in Y; lia | discriminate] | destruct (8 <? sc) eqn:Y; [discriminate | apply Z.ltb_ge in Y; lia]].
Qed.
Theorem reach_GC : forall rg1, st_ok src0segs E1 ss_R1 (mkst rg1 (Z_to_bv 64 PS_RAM) mem1 (seg_rom src0segs)) ->
SR src0segs (mkCfg (mkst rg1 (Z_to_bv 64 PS_RAM) mem1 (seg_rom src0segs)) md1) GCpost.
Proof.
intros rg1 HS. pose proof E2_facts as (HA2 & _ & _ & _ & E10).
eapply SR_bind; [exact (reach_S3 rg1 HS)|]. intros c [C3 (ms3 & -> & HF3)]. revert C3.
apply (cw_node E2 _ _ _ _ _ _ grun_S3 (proj1 (proj2 wsub_part1)) HA2); intros B0.
- pose proof (bt_sc E2 true E10 B0) as H9. cbv iota in H9.
assert (HR : exists r, Z.land sc 3 = r /\ (r = 0 \/ r = 1 \/ r = 2 \/ r = 3)).
{ exists (Z.land sc 3). split; [reflexivity|].
assert (0 <= Z.land sc 3 < 4) by (split; [apply Z.land_nonneg; lia | change 3 with (Z.ones 2); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia]). lia. }
destruct HR as (r & Hr & Rc).
apply (cw_station E2 E2 _ _ (ss_M r) _ _ grun_sc9 (proj2 (proj2 (proj2 wsub_part1))) HA2); [intros ms HS' HF'; exact (station_S5 r H9 Hr ms HS' HF') |].
destruct Rc as [-> | [-> | [-> | ->]]]; [exact (tree_m0 H9 Hr HF3) | exact (tree_m1 H9 Hr HF3) | exact (tree_m2 H9 Hr HF3) | exact (tree_m3 H9 Hr HF3)].
- pose proof (bt_sc E2 false E10 B0) as H8. cbv iota in H8.
apply (cw_station E2 E3 _ _ ss_S4 _ _ grun_sc8 (proj1 (proj2 (proj2 wsub_part1))) HA2); [intros ms HS' HF'; exact (station_S4 H8 ms HS' HF') |].
apply (tree_c H8). eapply (facts_ok_agree 57 E2 E3); [exact E3_agree | vm_compute; reflexivity | exact HF3].
Qed.
Definition G4post (nested : bool) (c : config) : Prop :=
exists E ms, c = mkCfg ms md1 /\ st_ok src0segs E (add_cond ss_g4 (if nested then C_nest else C_mm)) ms /\ env_agree 40 E00 E /\
ew E 40 = Z_to_bv 64 (ptr_addr L1 m) /\ ew E 56 = Z_to_bv 64 usage /\ ew E 61 = Z_to_bv 64 K /\ ew E 62 = Z_to_bv 64 (16 * nu * K) /\ FRM1 (ms_mem ms).
Lemma wsub_GC : wsub (ss_mem ss_GC) SKS = true. Proof. vm_compute. reflexivity. Qed.
Lemma reach_g4 : forall c, GCpost c -> SR src0segs c (G4post (class_size sc * K + UNIT <=? PGSZ / 2)).
Proof.
intros c (E & ms & -> & HS & HA & E40 & E56 & E61 & E62 & HF). pose proof K_facts as (K1 & K2 & _). pose proof nu_facts as [N1 N2].
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_GC ss_g4); [exact Mh1 | exact Mlz1 | exact HS | apply run_GC |].
intros ms' HS' Hfr. pose proof (FRM1_run E _ _ _ HA HF Hfr wsub_GC) as HF'.
assert (D62 : bv_unsigned (sv_denot E (SOff 62 16)) = 16 * nu * K + 16).
{ cbn [sv_denot]. rewrite E62. rewrite (lit64_small (16 * nu * K)) by nia. apply lit64_small. nia. }
apply (SR_sym_branch src0segs E ss_g4 ms' md1 _ BC_GEU (SLit 2048) (SOff 62 16) HS').
- intros Hb HSb. rewrite branch_geu, den_lit, lit64_small, D62 in Hb by lia.
destruct (2048 <? 16 * nu * K + 16) eqn:Y; [discriminate|]. apply Z.ltb_ge in Y.
replace (class_size sc * K + UNIT <=? PGSZ / 2) with true by (symmetry; apply Z.leb_le; rewrite N2; unfold UNIT, PGSZ; change (4096 / 2) with 2048; lia).
apply SR_ret. exists E, ms'. split; [reflexivity|]. split; [exact HSb|]. repeat (split; [assumption|]). exact HF'.
- intros Hb HSb. rewrite branch_geu, den_lit, lit64_small, D62 in Hb by lia.
destruct (2048 <? 16 * nu * K + 16) eqn:Y; [|discriminate]. apply Z.ltb_lt in Y.
replace (class_size sc * K + UNIT <=? PGSZ / 2) with false by (symmetry; apply Z.leb_gt; rewrite N2; unfold UNIT, PGSZ; change (4096 / 2) with 2048; lia).
apply SR_ret. exists E, ms'. split; [reflexivity|]. split; [exact HSb|]. repeat (split; [assumption|]). exact HF'.
Qed.
End GB.
Definition am_facts (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model) : Prop :=
(Qam X U A (Some m, s1) /\ (rawX X s1 /\ as_keep X A s1)) /\ layout_le A L L1 /\ midrep B L1 s1 mem1 md1 /\ ama_ok s1 /\ bounded s1 /\
(exists vm', md1 = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L1 s1 x ->
mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem1 a).
Definition SEG_mm_at : Prop :=
forall m s1 L1 mem1 md1 c, am_facts m s1 L1 mem1 md1 -> G4post m s1 L1 mem1 md1 false c ->
PGSZ / 2 < class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT ->
mreal src0segs c (ibind (mm_body sc n m s1) KS) (POST X L A regs mem md sc stk g).
Definition SEG_nest_at (fuel : nat) : Prop :=
forall m s1 L1 mem1 md1 c, am_facts m s1 L1 mem1 md1 -> G4post m s1 L1 mem1 md1 true c ->
class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT <= PGSZ / 2 ->
mreal src0segs c (ibind (nest_body fuel sc n m s1) KS) (POST X L A regs mem md sc stk g).
Theorem group_split : forall fuel, SEG_mm_at -> SEG_nest_at fuel -> SEG_group_body X U L A regs mem md sc n stk g j1 j2 fuel.
Proof.
intros fuel SM SN m s1 c1 [[Q [RX1 AK1]] (L1 & mem1 & md1 & E1 & LE1 & MID1 & AMA1 & BND1 & VM1 & FR1 & ERRW1 & HA1 & Ec & E1_40 & HS1)]. cbn [fst snd] in *.
destruct c1 as [ms1 mdx]. cbn [cfg_ms cfg_model] in *. injection Ec as Ems Emd. subst mdx.
pose proof Q as (_ & _ & HI1 & _).
pose proof (mid_md _ _ _ _ _ MID1) as (Mh1 & Mlz1 & _).
assert (AF : am_facts m s1 L1 mem1 md1) by (split; [exact (conj Q (conj RX1 AK1))|]; split; [exact LE1|]; split; [exact MID1|]; split; [exact AMA1|]; split; [exact BND1|]; split; [exact VM1|]; split; [exact FR1 | exact ERRW1]).
assert (HS1' : st_ok src0segs E1 ss_R1 (mkst (ms_regs ms1) (Z_to_bv 64 PS_RAM) mem1 (seg_rom src0segs))) by (rewrite <- Ems; exact HS1).
rewrite Ems. eapply mreal_SR_pre.
- eapply SR_bind; [eapply (reach_GC m s1 L1 mem1 md1 E1); eassumption |].
intros c2 H2. eapply (reach_g4 m s1 L1 mem1 md1); try eassumption.
- intros c3 H3. cbv beta in H3. rewrite group_body_arms.
destruct (class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT <=? PGSZ / 2) eqn:Y.
+ apply Z.leb_le in Y. replace (PGSZ / 2 <? _) with false by (symmetry; apply Z.ltb_ge; lia). exact (SN m s1 L1 mem1 md1 c3 AF H3 Y).
+ apply Z.leb_gt in Y. replace (PGSZ / 2 <? _) with true by (symmetry; apply Z.ltb_lt; lia). exact (SM m s1 L1 mem1 md1 c3 AF H3 Y).
Qed.
End j.
Definition SEG_mm : Prop :=
forall X U L A regs mem md sc n stk g j1 j2,
Inv X None U A -> rawX X A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD ->
midrep B L A mem md -> (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) -> callee_pre B regs mem stk -> ASF <= stk <= AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n -> word_mem src0segs mem GUARD g ->
(forall k, U k = 0) -> as_budget sc <= stk ->
SEG_mm_at X U L A regs mem md sc n stk g j1 j2.
Definition SEG_nest_c (fuel : nat) : Prop :=
forall X U L A regs mem md sc n stk g j1 j2,
Inv X None U A -> rawX X A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD ->
midrep B L A mem md -> (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) -> callee_pre B regs mem stk -> ASF <= stk <= AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n -> word_mem src0segs mem GUARD g ->
(forall k, U k = 0) -> as_budget sc <= stk -> (need sc <= S (S fuel))%nat ->
SEG_nest_at X U L A regs mem md sc n stk g j1 j2 fuel.
Definition SEG_nest : Prop := forall fuel, ASH fuel -> SEG_nest_c fuel.
Theorem SEG_group_from_arms : SEG_mm -> SEG_nest -> forall fuel, ASH fuel -> SEG_group_at fuel.
Proof.
intros SM SN fuel IH X U L A regs mem md sc n stk g j1 j2 HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB HN.
eapply (group_split X U L A regs mem md sc n stk); try eassumption. Unshelve. all: try exact j1; try exact j2.
- eapply SM; eassumption.
- eapply (SN fuel IH); eassumption.
Qed.
Theorem alloc_slot_ind : alloc_meta_hyp B -> (forall fuel, SEG_group_at fuel -> SEG_head_at fuel) -> SEG_mm -> SEG_nest ->
forall fuel f, (f <= fuel)%nat -> ASH f.
Proof.
intros AMH SH SM SN fuel. induction fuel as [|fuel IH]; intros f Hf.
- intros X U L A regs mem md sc n stk g HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB HN. pose proof (need_ge2 sc). lia.
- destruct (Nat.eq_dec f (S fuel)) as [->|NE]; [| apply IH; lia].
intros X U L A regs mem md sc n stk g HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB HN.
pose proof (need_ge2 sc) as N2. destruct fuel as [|f]; [lia|].
assert (IHf : ASH f) by (apply IH; lia).
pose proof (SEG_group_from_arms SM SN f IHf) as SG.
destruct (active_hd A sc) as [h|] eqn:Eh.
+ apply (SH f SG X U L A regs mem md sc n stk g HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg); [rewrite Eh; discriminate | exact HU | exact HB | exact HN].
+ apply (slice_T0 X U L A regs mem md sc n stk HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 AMH g Hg J1LIT 0 f Eh eq_refl eq_refl).
exact (SG X U L A regs mem md sc n stk g J1LIT 0 HI RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg HU HB HN).
Qed.
Theorem src0_alloc_slot_of_parts : alloc_meta_hyp B -> (forall fuel, SEG_group_at fuel -> SEG_head_at fuel) -> SEG_mm -> SEG_nest -> alloc_slot_hyp B.
Proof.
intros AMH SH SM SN. pose proof ctx_owned_ok as CO. pose proof (alloc_slot_ind AMH SH SM SN NEST_FUEL NEST_FUEL (le_n _)) as IH.
unfold alloc_slot_hyp. intros L A regs mem md sc n HW AMA BND RSV SPOK Hsc Hn Hfit MID AUXP PRE R10 R11.
destruct (st_guard _ _ (mid_statics _ _ _ _ _ MID)) as [g Hg].
assert (RX : rawX [] A) by (intros x []).
assert (Hstk : ASF <= AS_STACK <= AS_STACK) by (unfold ASF, AS_STACK, ALLOC_STACK; lia).
assert (HB : as_budget sc <= AS_STACK) by (pose proof (as_budget_range sc ltac:(lia)); unfold AS_STACK, ALLOC_STACK; lia).
assert (HN : (need sc <= NEST_FUEL)%nat) by (apply need_le_fuel; lia).
change (pc_alloc_slot (ms_pcs B)) with src0_A_alloc_slot. change (ms_segs B) with src0segs.
pose proof (IH [] U0 L A regs mem md sc n AS_STACK g HW RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg (fun k => eq_refl) HB HN) as M.
eapply mreal_mono; [| exact M]. cbv beta. intros r c' (L' & regs' & mem' & md' & Ec & MID' & AMA' & BND' & RSV' & SPOK' & LE & PRS & VM & FR & SCR & RA0 & UZ & AK & GD).
exists L', regs', mem', md'. repeat (split; [assumption|]). split; [| split; [exact SCR | split; [exact RA0 | exact UZ]]].
intros x Hx No No' Nn Ns. apply (FR x Hx); try assumption. intros Hc. apply No. exact (CO U0 L A mem md x HW MID Hc).
Qed.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
