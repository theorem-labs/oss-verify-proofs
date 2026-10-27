(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN18.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0r.
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN13.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN17.
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
Local Open Scope mm_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma pairwise_snoc {T} (Rl : T -> T -> Prop) : forall l x, pairwise Rl l -> (forall y, In y l -> Rl y x) -> pairwise Rl (l ++ [x]).
Proof.
induction l as [|y t IH]; intros x Hp Hx; cbn; [split; [intros z [] | exact I]|].
destruct Hp as [H1 H2]. split.
- intros z Hz. apply in_app_iff in Hz as [Hz|[<-|[]]]; [exact (H1 z Hz) | exact (Hx y (or_introl eq_refl))].
- apply IH; [exact H2 | intros z Hz; exact (Hx z (or_intror Hz))].
Qed.
Lemma sx32_u64 : forall x, bv_unsigned (Z_to_bv 64 (sx32 x)) = sx32 x.
Proof. intros x. apply lit64_small. apply sx32_range. Qed.
Lemma lo32_eq_mod : forall a b, a mod 2 ^ 32 = b mod 2 ^ 32 <-> lo32 a = lo32 b.
Proof. intros a b. unfold lo32. tauto. Qed.
Lemma avail0_lo32 : forall E aidx, ew E 90 = Z_to_bv 64 aidx -> 0 <= aidx <= 31 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 90 0)) (SLit (-1)))) mod 2 ^ 32 = (2 ^ (aidx + 1) - 1) mod 2 ^ 32.
Proof.
intros E aidx E90 Ha. cbn [sv_denot]. rewrite E90, (lit64_small aidx), Z.add_0_r by lia. rewrite alu64_add, sllw_rr_unsigned, !lit64_small by lia.
change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1). rewrite sllw_2 by lia. rewrite (Z.mod_small aidx 32) by lia.
unfold add64. rewrite mod64_mod32. rewrite <- Zplus_mod_idemp_l, sx32_mod32, Zplus_mod_idemp_l.
replace (2 ^ (aidx + 1) + (2 ^ 64 - 1)) with (2 ^ (aidx + 1) - 1 + 2 ^ 32 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma avail_lo32 : forall E aidx, ew E 90 = Z_to_bv 64 aidx -> 0 <= aidx <= 31 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 90 0)) (SLit (-1)))) (SLit (-1)))) mod 2 ^ 32
= (ones aidx - 1) mod 2 ^ 32.
Proof.
intros E aidx E90 Ha. pose proof (avail0_lo32 E aidx E90 Ha) as H0.
cbn [sv_denot] in H0 |- *. rewrite alu64_add, sext32_val, sx32_u64. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
unfold add64. rewrite mod64_mod32, <- Zplus_mod_idemp_l, sx32_mod32, H0, Zplus_mod_idemp_l. unfold ones.
replace (2 ^ (aidx + 1) - 1 + (2 ^ 64 - 1)) with (2 ^ (aidx + 1) - 1 - 1 + 2 ^ 32 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma freed_lo32 : forall E aidx cnt, ew E 90 = Z_to_bv 64 aidx -> ew E 82 = Z_to_bv 64 cnt -> 0 <= aidx <= cnt - 1 -> 1 <= cnt <= 32 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 82 (-1))) (SAlu ALU_XOR (SExt true 32 (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 90 0)) (SLit (-1)))) (SLit (-1))))) mod 2 ^ 32
= (ones (cnt - 1) - ones aidx) mod 2 ^ 32.
Proof.
intros E aidx cnt E90 E82 Ha Hc. pose proof (avail0_lo32 E aidx E90 ltac:(lia)) as H0.
cbn [sv_denot] in H0 |- *. rewrite alu64_add, sllw_rr_unsigned, alu64_xor, sext32_val, sx32_u64.
set (u := bv_unsigned (alu64 ALU_ADD _ _)) in *.
cbn [sv_denot]. rewrite E82, !lit64_small by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 cnt) + -1))) with (cnt - 1) by (rewrite (lit64_small cnt), lit64_small by lia; reflexivity).
rewrite sllw_2 by lia. rewrite (Z.mod_small (cnt - 1) 32) by lia. replace (cnt - 1 + 1) with cnt by lia.
pose proof (sx32_range u) as Ru.
unfold add64. rewrite mod64_mod32.
rewrite <- Zplus_mod_idemp_r. rewrite <- (mod64_mod32 (Z.lxor (sx32 u) (Z.ones 64))). rewrite (lxor_ones_mod (sx32 u) Ru).
rewrite <- Zminus_mod_idemp_r, sx32_mod32, H0, Zminus_mod_idemp_r. rewrite Zplus_mod_idemp_r. rewrite <- Zplus_mod_idemp_l, sx32_mod32, Zplus_mod_idemp_l.
unfold ones. replace (2 ^ cnt + (2 ^ 64 - 1 - (2 ^ (aidx + 1) - 1))) with (2 ^ (cnt - 1 + 1) - 1 - (2 ^ (aidx + 1) - 1) + 2 ^ 32 * 2 ^ 32) by (replace (cnt - 1 + 1) with cnt by lia; lia).
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma bits_val : forall E sc cnt len, ew E 10 = Z_to_bv 64 sc -> ew E 82 = Z_to_bv 64 cnt -> ew E 81 = Z_to_bv 64 len ->
0 <= sc < 48 -> 1 <= cnt <= 32 -> 4096 <= len <= 2 ^ 20 -> len mod 4096 = 0 ->
sv_denot E BITS = Z_to_bv 64 ((cnt - 1) + 32 + 64 * sc + 4096 * (len / 4096)).
Proof.
intros E sc cnt len E10 E82 E81 Hsc Hc Hl Hm. unfold BITS. apply (proj2 (word_eq _ _)). cbn [sv_denot].
rewrite E10, E82, E81, (lit64_small sc), (lit64_small cnt), (lit64_small len), Z.add_0_r, Z.add_0_r by lia.
rewrite alu64_add, alu64_or, alu64_or, alu64_sll, alu64_and, alu64_and, alu64_or, !lit64_small by lia.
change (bv_unsigned (Z_to_bv 64 (-4096))) with (2 ^ 64 - 2 ^ 12). change (6 mod 64) with 6.
rewrite sll64_small by (change (2 ^ 6) with 64; lia). change (2 ^ 6) with 64.
replace (Z.land (cnt + -1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; lia). rewrite (lit64_small 32) by lia.
rewrite Z.lor_0_l, land_neg_pow2_u64 by lia. replace (len - len mod 2 ^ 12) with len by (change (2 ^ 12) with 4096; rewrite Hm; lia).
replace (sc * 64) with (2 ^ 6 * sc) by (change (2 ^ 6) with 64; lia).
rewrite (lor_add_high' (cnt - 1) sc 6 ltac:(change (2 ^ 6) with 64; lia) ltac:(lia)).
pose proof (Z_div_mod_eq_full len 4096) as DM. rewrite Hm, Z.add_0_r in DM.
replace len with (2 ^ 12 * (len / 4096)) at 1 by (change (2 ^ 12) with 4096; lia).
rewrite (lor_add_high (cnt - 1 + 2 ^ 6 * sc) (len / 4096) 12 ltac:(change (2 ^ 12) with 4096; change (2 ^ 6) with 64; lia) ltac:(lia)).
rewrite add64_small by (change (2 ^ 12) with 4096; change (2 ^ 6) with 64; lia). rewrite lit64_small by (change (2 ^ 6) with 64; lia).
change (2 ^ 12) with 4096. change (2 ^ 6) with 64. lia.
Qed.
Lemma ctr_val : forall E ctr, ew E 89 = Z_to_bv 64 ctr -> 0 <= ctr < 2 ^ 32 ->
bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff 89 0)) (SLit 1))) mod 2 ^ 32 = (Z.land (ctr + 1) (2 ^ 32 - 1)) mod 2 ^ 32.
Proof.
intros E ctr E89 Hc. cbn [sv_denot]. rewrite E89, (lit64_small ctr), Z.add_0_r by lia. rewrite ctr_chunk_mod by lia.
change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aidx_byte : forall E aidx, ew E 90 = Z_to_bv 64 aidx -> 0 <= aidx <= 31 ->
bv_unsigned (sv_denot E (SAlu ALU_OR (SLit 0) (SAlu ALU_AND (SOff 90 0) (SLit 31)))) mod 2 ^ 8 = aidx mod 2 ^ 8.
Proof.
intros E aidx E90 Ha. cbn [sv_denot]. rewrite E90, (lit64_small aidx), Z.add_0_r by lia. rewrite alu64_or, alu64_and, !lit64_small by lia.
change 31 with (Z.ones 5). rewrite Z.land_ones, Z.lor_0_l, (Z.mod_small aidx (2 ^ 5)) by lia. reflexivity.
Qed.
Lemma usage_val : forall E u cnt, ew E 56 = Z_to_bv 64 u -> ew E 82 = Z_to_bv 64 cnt -> 0 <= u < 2 ^ 48 -> 1 <= cnt <= 32 ->
sv_denot E (SAlu ALU_ADD (SOff 56 0) (SOff 82 0)) = Z_to_bv 64 (u + cnt).
Proof.
intros E u cnt E56 E82 Hu Hc. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E56, E82, (lit64_small u), (lit64_small cnt), !Z.add_0_r by lia.
rewrite alu64_add, !lit64_small by lia. apply add64_small. lia.
Qed.
Lemma nth_repeat_lt {T} : forall (x d : T) n i, (i < n)%nat -> nth i (repeat x n) d = x.
Proof. intros x d n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i; [reflexivity|]. cbn. apply IH. lia. Qed.
Lemma padd_padd' : forall p d1 d2, padd (padd p d1) d2 = padd p (d1 + d2).
Proof. intros [r o] d1 d2. cbn. f_equal. lia. Qed.
Lemma areas_cells_upd_sharp : forall s q x l c, In c (areas_cells (upd_meta q x s) l) ->
In c (meta_slot_cells q (Some x)) \/
(In c (areas_cells s l) /\ exists a d, In a l /\ mc_loc c = LMem (padd a d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= PGSZ /\
(forall k, 0 <= k < METAS_PER_AREA -> slot_of a k = q -> d + Z.of_nat (mc_w c) <= AREA_HDR + META_SIZE * k \/ AREA_HDR + META_SIZE * k + META_SIZE <= d)).
Proof.
intros s q x l c H. destruct (areas_cells_cases s (upd_meta q x s) l c H) as [[Hin (a & next & Ha & Hh)] | (a & k & Ha & Hk & Hck)].
- right. split; [exact Hin|]. unfold YN2n.hdr_cells in Hh. cbn [In] in Hh.
destruct Hh as [<-|[<-|[<-|[]]]]; cbn [mc_loc mc_w].
+ exists a, 0. split; [exact Ha|]. split; [destruct a; cbn; rewrite Z.add_0_r; reflexivity|]. unfold PGSZ, AREA_HDR, META_SIZE. split; [lia|]. split; [lia|]. intros k Hk _. left. lia.
+ exists a, 8. split; [exact Ha|]. split; [reflexivity|]. unfold PGSZ, AREA_HDR, META_SIZE. split; [lia|]. split; [lia|]. intros k Hk _. left. lia.
+ exists a, 16. split; [exact Ha|]. split; [reflexivity|]. unfold PGSZ, AREA_HDR, META_SIZE. split; [lia|]. split; [lia|]. intros k Hk _. left. lia.
- destruct (sptr_eq_dec (slot_of a k) q) as [Eq|Hne].
+ left. rewrite Eq, MT_upd_same in Hck. exact Hck.
+ right. rewrite MT_upd_other in Hck by exact Hne. split.
* exact (YN2n.slot_cells_in_areas s l a k c Ha Hk Hck).
* destruct (In_meta_slot_cells _ _ _ Hck) as (d & Hl & Hd & Hw). exists a, (AREA_HDR + META_SIZE * k + d). split; [exact Ha|].
split; [rewrite Hl; unfold slot_of; rewrite padd_padd'; reflexivity|]. unfold PGSZ, AREA_HDR, META_SIZE, METAS_PER_AREA in *.
split; [lia|]. split; [lia|]. intros k2 Hk2 E2. assert (k2 <> k) by (intros ->; exact (Hne E2)). nia.
Qed.
Lemma st_ok_cond : forall E ss ms c, st_ok src0segs E ss ms -> In c (f_conds (ss_facts ss)) ->
branch_taken (ac_c c) (sv_denot E (ac_a c)) (sv_denot E (ac_b c)) = true.
Proof.
intros E ss ms c HS Hin. pose proof (st_ok_facts_ok src0segs E ss ms HS) as (_ & HC & _).
exact (proj1 (conds_ok_forall E _) HC c Hin).
Qed.
Section w.
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
Hypothesis HU : forall k, U k = 0.
Let sp : Z := bv_unsigned (getr regs 2).
Local Notation csn := (cs L A sc g j1 j2).
Local Notation E00 := (E0 regs csn).
Local Notation WSn := (WS regs).
Local Notation POSTn := (POST X L A regs mem md sc stk g).
Let agree_cs' := agree_cs L A regs sc g j1 j2.
Let agree_reg' := agree_reg L A regs sc g j1 j2.
Let cs_facts' := cs_facts X U L A regs mem md sc HI Hsc MID g j1 j2.
Let pre_facts' := pre_facts regs mem stk PRE.
Let XC : Xclean X A := fun x am Hx H => ltac:(destruct (XR x Hx) as [EXR|EXR]; rewrite EXR in H; discriminate).
Let nu : Z := cs L A sc g j1 j2 35.
Section MF.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis RX1 : rawX X s1.
Hypothesis Mm : MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None).
Hypothesis Km : In m (keys s1).
Hypothesis NXm : memb m X = false.
Hypothesis US1 : forall g' am, usedX (m :: X) s1 g' am <-> usedX X A g' am.
Hypothesis ACT1 : st_active s1 = st_active A.
Hypothesis LEN1 : (length (st_regions A) <= length (st_regions s1))%nat.
Hypothesis LE1 : layout_le A L L1.
Hypothesis AK1 : as_keep X A s1.
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis AMA1 : ama_ok s1.
Hypothesis BND1 : bounded s1.
Hypothesis VM1 : exists vm', md1 = with_vmmaps vm' md.
Hypothesis FR1 : forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L1 s1 x ->
mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis ERRW1 : forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem1 a.
Variable E6 : env.
Hypothesis AG6 : env_agree 40 E00 E6.
Hypothesis E6_40 : ew E6 40 = Z_to_bv 64 (ptr_addr L1 m).
Hypothesis E6_56 : ew E6 56 = Z_to_bv 64 (usage_of s1 sc).
Let s3 : astate := seq_st (ab_st sc s1).
Let plan : Z * Z := mmap_plan s1 sc n (initial_cnt sc (usage_of s1 sc)) (usage_of s1 sc).
Hypothesis E6_81 : ew E6 81 = Z_to_bv 64 (snd plan).
Hypothesis E6_82 : ew E6 82 = Z_to_bv 64 (fst plan).
Variables (a : word) (mem3 : word -> option byte).
Hypothesis GR : grant_ok (Z_to_bv 64 0) md1 a (snd plan) = true.
Hypothesis HM3 : midrep B L1 s3 mem3 md1.
Hypothesis HF3 : YN14.FRcB regs mem1 mem3.
Let Mh1 : m_halted md1 = None := proj1 (mid_md _ _ _ _ _ MID1).
Let Mlz1 : m_vm_lazy md1 = [] := proj1 (proj2 (mid_md _ _ _ _ _ MID1)).
Let Mmat1 : m_vm_materialized md1 = [] := proj2 (proj2 (mid_md _ _ _ _ _ MID1)).
Definition len : Z := snd plan.
Definition cnt : Z := fst plan.
Definition ua : Z := bv_unsigned a.
Definition Nr : nat := length (st_regions s3).
Definition L2 : layout := Lset L1 s3 ua.
Definition md2 : Model := mmap_model a (Z_to_bv 64 len) md1.
Definition aidx : Z := aidx_of sc cnt.
Definition am1 : ameta := am_inst m sc cnt (len / 4096) aidx Nr.
Definition s5 : astate := inst_st sc m cnt len s3.
Definition mm0 : word -> option byte := apply_zeros mem3 [(a, Z_to_bv 64 len)].
Definition ctr : Z := st_mmap_counter s3.
Let E7 : env := ewset E6 86 a.
Lemma s3_factsF : Inv (m :: X) None U s3 /\ Xclean (m :: X) s3 /\ ama_ok s3 /\ keys s3 = keys s1 /\ (forall q, MT s3 q = MT s1 q) /\ bounded s3 /\
st_regions s3 = st_regions s1 /\ st_areas s3 = st_areas s1 /\ st_active s3 = st_active s1 /\ st_usage s3 = st_usage s1.
Proof. exact (s3_factsD X U sc m s1 HI1 RX1 Mm AMA1 BND1). Qed.
Lemma grantF : page_round len = len /\ ua mod 4096 = 0 /\ 4096 <= ua /\ ua + len <= alloc_ceiling /\
region_free (vm_reserved (m_vmmaps md1) ++ vm_maps (m_vmmaps md1)) a (Z_to_bv 64 len) = true /\
(forall x, ua <= x < ua + len -> ~ in_img B x /\ 4096 <= x < alloc_ceiling) /\
1 <= cnt <= 32 /\ 4096 <= len <= 2 ^ 20 /\ len mod 4096 = 0.
Proof.
destruct (planC X U L A regs mem md sc n HI Hsc Hn MID g j1 j2 s1 BND1) as (P1 & P2 & P3). fold plan in P1, P2, P3.
assert (GR' : grant_ok (Z_to_bv 64 0) md1 a (page_round (snd plan)) = true) by (rewrite page_round_fixed by (unfold PGSZ; exact P3); exact GR).
destruct (grant_facts L A regs sc g j1 j2 s1 L1 md1 mem3 a (snd plan) HM3 ltac:(lia) P3 GR') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
unfold len, cnt, ua. repeat (split; [assumption|]). exact P3.
Qed.
Lemma plan_geom : cnt = 1 \/ class_size sc * cnt + UNIT <= len.
Proof.
unfold cnt, len. subst plan. rewrite mmap_plan_eq. unfold mp_fin.
destruct (negb _ && _); [destruct (_ || _); [left; reflexivity|]|]; right; cbn [fst snd]; apply page_round_ge.
Qed.
Lemma stride1 : (stride_of am1 = if cnt =? 1 then len - UNIT else class_size sc) /\ 16 <= stride_of am1 /\ UNIT + stride_of am1 * cnt <= len /\ am_last am1 = cnt - 1.
Proof.
pose proof grantF as (_ & _ & _ & _ & _ & _ & C1 & L1' & L2'). pose proof plan_geom as PG. pose proof (class_size_bounds sc Hsc) as CB.
unfold am1, am_inst, am_inst0, am_set_links, stride_of. cbn [am_last am_maplen am_sc].
replace (cnt - 1 =? 0) with (cnt =? 1) by (destruct (Z.eqb_spec cnt 1); destruct (Z.eqb_spec (cnt - 1) 0); lia).
assert (ML : len / 4096 =? 0 = false) by (apply Z.eqb_neq; intros E; pose proof (Z.div_str_pos len 4096 ltac:(lia)); lia).
rewrite ML. cbn [negb andb]. rewrite andb_true_r.
assert (ME : len / 4096 * 4096 = len) by (pose proof (Z_div_mod_eq_full len 4096); lia). rewrite ME.
split; [reflexivity|]. unfold UNIT in *. destruct (Z.eqb_spec cnt 1); [rewrite e in *|]; split; try lia; nia.
Qed.
Lemma aidxF : 0 <= aidx <= cnt - 1 /\ aidx <= 31 /\ aidx = (let a0 := (4096 - UNIT) / class_size sc - 1 in let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in if a1 <? 0 then 0 else a1).
Proof.
pose proof grantF as (_ & _ & _ & _ & _ & _ & C1 & _). unfold aidx, aidx_of. cbn zeta.
destruct (Z.ltb_spec (cnt - 1) ((4096 - UNIT) / class_size sc - 1)).
- destruct (Z.ltb_spec (cnt - 1) 0); [lia|]. split; [lia|]. split; [lia | reflexivity].
- destruct (Z.ltb_spec ((4096 - UNIT) / class_size sc - 1) 0); (split; [lia|]; split; [lia | reflexivity]).
Qed.
Lemma ctrF : 0 <= ctr < 2 ^ 32 /\ length (st_active s3) = 48%nat /\ length (st_usage s3) = 48%nat.
Proof. destruct s3_factsF as (I3 & _). pose proof (inv_ctx I3) as (C1 & C2 & _ & _ & _ & _ & _ & _ & C9 & _). unfold ctr. exact (conj C9 (conj C1 C2)). Qed.
Lemma E6_factsF : ew E6 10 = Z_to_bv 64 sc /\ ew E6 33 = Z_to_bv 64 (csn 33) /\ ew E6 2 = getr regs 2 /\ bv_unsigned (ew E6 40) = ptr_addr L1 m /\ ew E6 35 = Z_to_bv 64 nu /\ ew E6 34 = Z_to_bv 64 (csn 34).
Proof.
destruct (E6_factsD X U L A regs sc R10 g j1 j2 m s1 L1 mem1 md1 HI1 Km MID1 E6 AG6 E6_40) as (E10 & E33 & E2 & U40).
split; [exact E10|]. split; [exact E33|]. split; [exact E2|]. split; [exact U40|]. split; [exact (agree_cs' E6 35 AG6 ltac:(lia)) | exact (agree_cs' E6 34 AG6 ltac:(lia))].
Qed.
Lemma hd_none : forall ms, st_ok src0segs E7 ss_Kg ms -> active_hd s3 sc = None /\ csn 34 = 0.
Proof.
intros ms HS. destruct cs_facts' as (_ & _ & C34 & _ & _ & _ & HD & _). destruct s3_factsF as (_ & _ & _ & _ & _ & _ & _ & _ & Ac3 & _).
assert (HC : In (mkAC BC_EQ (SOff 34 0) (SLit 0)) (f_conds (ss_facts ss_Kg))) by (vm_compute; right; left; reflexivity).
pose proof (st_ok_cond E7 ss_Kg ms _ HS HC) as T. cbn [ac_c ac_a ac_b] in T.
assert (E34 : ew E7 34 = Z_to_bv 64 (csn 34)) by (subst E7; rewrite ew_ewset_other by lia; exact (proj2 (proj2 (proj2 (proj2 (proj2 E6_factsF)))))).
rewrite (den_off0 E7 34 (csn 34) E34), den_lit, branch_eq, !lit64_small in T by lia. apply Z.eqb_eq in T.
split; [| exact T]. unfold active_hd. rewrite Ac3, ACT1. fold (active_hd A sc). apply (proj1 HD). exact T.
Qed.
Definition SKg0 : list (option nat * Z * Z) := [(Some 2%nat, -ASF, 0); (Some 86%nat, 0, 16); (Some 40%nat, 0, 40)].
Definition WG0 (x : Z) : Prop := WSn x \/ ua <= x < ua + 16 \/ ptr_addr L1 m <= x < ptr_addr L1 m + 40.
Definition SKg1 : list (option nat * Z * Z) := (None, LOCK + 20, LOCK + 24) :: SKg0.
Definition WG1 (x : Z) : Prop := WG0 x \/ LOCK + 20 <= x < LOCK + 24.
Definition SKg2 : list (option nat * Z * Z) := (Some 33%nat, 88, 96) :: (Some 33%nat, 472, 480) :: SKg1.
Definition WG2 (x : Z) : Prop := WG1 x \/ csn 33 + 88 <= x < csn 33 + 96 \/ csn 33 + 472 <= x < csn 33 + 480.
Lemma SKg0_W : forall E b lo hi x, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew E 86 = a ->
In (b, lo, hi) SKg0 -> base_val E b + lo <= x < base_val E b + hi -> WG0 x.
Proof.
intros E b lo hi x HA E40 E86 Hin Hx. destruct E6_factsF as (_ & _ & _ & U40 & _). rewrite <- E6_40 in E40.
unfold SKg0 in Hin. cbn [In] in Hin. unfold WG0, ua.
destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-; cbn [base_val] in Hx.
- left. exact (YN13.win_stack L A regs sc g j1 j2 s1 E x HA Hx).
- right. left. rewrite E86 in Hx. lia.
- right. right. rewrite E40, U40 in Hx. lia.
Qed.
Lemma SKg1_W : forall E b lo hi x, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew E 86 = a ->
In (b, lo, hi) SKg1 -> base_val E b + lo <= x < base_val E b + hi -> WG1 x.
Proof.
intros E b lo hi x HA E40 E86 Hin Hx. unfold SKg1 in Hin. cbn [In] in Hin. unfold WG1.
destruct Hin as [H|Hin]; [injection H as <- <- <-; cbn [base_val] in Hx; right; lia |]. left. exact (SKg0_W E b lo hi x HA E40 E86 Hin Hx).
Qed.
Lemma SKg2_W : forall E b lo hi x, env_agree 40 E00 E -> ew E 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew E 86 = a ->
In (b, lo, hi) SKg2 -> base_val E b + lo <= x < base_val E b + hi -> WG2 x.
Proof.
intros E b lo hi x HA E40 E86 Hin Hx. destruct cs_facts' as (C33 & _). unfold SKg2 in Hin. cbn [In] in Hin. unfold WG2.
destruct Hin as [H|[H|Hin]]; [injection H as <- <- <-; cbn [base_val] in Hx; rewrite (agree_cs' E 33 HA), lit64_small in Hx by (lits; lia); right; left; lia
| injection H as <- <- <-; cbn [base_val] in Hx; rewrite (agree_cs' E 33 HA), lit64_small in Hx by (lits; lia); right; right; lia |].
left. exact (SKg1_W E b lo hi x HA E40 E86 Hin Hx).
Qed.
Lemma frame_keepF : forall (W : Z -> Prop) E rs sk mm mm' mm1,
frame_of E rs mm mm' -> wsub rs sk = true ->
(forall b lo hi x, In (b, lo, hi) sk -> base_val E b + lo <= x < base_val E b + hi -> W x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mm (Z_to_bv 64 x) = mm1 (Z_to_bv 64 x)) ->
forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mm' (Z_to_bv 64 x) = mm1 (Z_to_bv 64 x).
Proof.
intros W E rs sk mm mm' mm1 Hfr WSB HW HF x Hx Hw. rewrite <- (HF x Hx Hw). apply (frame_of_at E _ _ _ x Hfr Hx). intros Hin.
destruct (in_wrange_wsub regs E _ sk x WSB Hin) as (b & lo & hi & Hl & Hx'). exact (Hw (HW b lo hi x Hl Hx')).
Qed.
Lemma skelsF : wsub (ss_mem ss_Kg) SKg0 = true /\ wsub (ss_mem (add_cond ss_kg0 C_mapok)) SKg0 = true /\ wsub (ss_mem ss_G1) SKg1 = true /\
wsub (ss_mem (add_cond ss_kg2 C_aT)) SKg1 = true /\ wsub (ss_mem (add_cond ss_kg2 C_aF)) SKg1 = true /\ wsub (ss_mem ss_TL) SKg2 = true /\
ss_atoms_lt 89 ss_kg1 = true /\ ss_atoms_lt 90 ss_kg2 = true /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_kg1) = (Some 86%nat, 0, 16) :: (Some 40%nat, 0, 40) :: skel_M1 /\
ss_G1 = mkSS (ss_pc ss_kg1) (ss_regs ss_kg1) (R_ctr :: ss_mem ss_kg1) None (addfact 89 F_ctr (ss_facts ss_kg1)) /\
submemb (firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0)) (ss_mem ss_TL0) = true /\
regions_wf (firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0)) = true /\
map (fun r => (r_base r, r_lo r, r_hi r)) (firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0)) =
[(None, LOCK + 20, LOCK + 24); (Some 86%nat, 0, 16); (Some 40%nat, 0, 40); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)] /\
ss_TL = mkSS (ss_pc ss_TL0) (ss_regs ss_TL0) (R_actW :: R_useW :: firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0)) None (ss_facts ss_TL0) /\
sr_get (ss_regs ss_kg0) 10 = SOff 86 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Let E8 : env := ewset E7 89 (Z_to_bv 64 ctr).
Lemma E7_facts : env_agree 86 E6 E7 /\ env_agree 40 E00 E7 /\ ew E7 86 = a /\ ew E7 40 = Z_to_bv 64 (ptr_addr L1 m).
Proof.
assert (AG : env_agree 86 E6 E7) by (apply env_agree_ewset).
split; [exact AG|]. split; [eapply env_agree_trans; [exact AG6 | eapply env_agree_le; [| exact AG]; lia]|].
split; [subst E7; apply ew_ewset_same | rewrite <- E6_40; apply (proj1 AG); lia].
Qed.
Lemma mm0_off : forall x, 0 <= x < 2 ^ 64 -> ~ (ua <= x < ua + len) -> mm0 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x).
Proof. intros x Hx Hno. unfold mm0. apply apply_zeros1_out. pose proof grantF as (_ & _ & _ & Hc & _ & _ & _ & Hl & _). pose proof (proj1 alloc_ceiling_val). rewrite !u64_of_Z by lia. unfold ua in Hno, Hc. lia. Qed.
Lemma mm0_in : forall x, ua <= x < ua + len -> mm0 (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof. intros x Hx. unfold mm0. apply apply_zeros1_in. pose proof grantF as (_ & _ & _ & Hc & _ & _ & _ & Hl & _). pose proof (proj1 alloc_ceiling_val). pose proof (u64_range a). unfold ua in Hx, Hc. rewrite !u64_of_Z by lia. lia. Qed.
Lemma img_mm0 : forall x, in_img B x -> mm0 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x).
Proof.
intros x Hi. pose proof (src0_img_range x Hi). apply mm0_off; [lia|]. intros Hx. exact (proj1 ((proj1 (proj2 (proj2 (proj2 (proj2 (proj2 grantF)))))) x Hx) Hi).
Qed.
Lemma station_G1 : forall ms1, st_ok src0segs E7 ss_kg1 ms1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WG0 x -> ms_mem ms1 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
st_ok src0segs E8 ss_G1 ms1 /\ env_agree 89 E7 E8 /\ env_agree 40 E00 E8 /\ ew E8 89 = Z_to_bv 64 ctr /\ ew E8 86 = a /\ ew E8 40 = Z_to_bv 64 (ptr_addr L1 m).
Proof.
intros ms1 HS F1. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct E6_factsF as (E10 & E33 & E2 & U40 & _). destruct cs_facts' as (C33 & _). destruct E7_facts as (AG67 & AG7 & E7_86 & E7_40).
pose proof ctrF as (Hc & _). pose proof grantF as (_ & _ & Ha4 & Hce & _ & Pf & _).
destruct skelsF as (_ & _ & _ & _ & _ & _ & AT89 & _ & SKk1 & EG1 & _).
assert (AG78 : env_agree 89 E7 E8) by (apply env_agree_ewset).
assert (AG8 : env_agree 40 E00 E8) by (eapply env_agree_trans; [exact AG7 | eapply env_agree_le; [| exact AG78]; lia]).
assert (E8_89 : ew E8 89 = Z_to_bv 64 ctr) by (subst E8; apply ew_ewset_same).
assert (E8_86 : ew E8 86 = a) by (rewrite <- E7_86; apply (proj1 AG78); lia).
assert (E8_40 : ew E8 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite <- E7_40; apply (proj1 AG78); lia).
split; [| exact (conj AG78 (conj AG8 (conj E8_89 (conj E8_86 E8_40))))].
assert (HS0 : st_ok src0segs E8 ss_kg1 ms1) by (eapply (st_ok_agree src0segs 89 E7 E8); [exact HS | exact AG78 | exact AT89]).
rewrite EG1.
assert (CTXW : forall x, CTX <= x < CTX + CTX_SIZE -> ~ WG0 x).
{ intros x Hx [Hw|[Hw|Hw]]; [unfold WS, ASF, CTX_SIZE in *; lits; lia | | destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 x Hw) as [NI _]; apply NI; apply src0_rwseg_img; unfold CTX_SIZE in Hx; lits; lia].
destruct (Pf x ltac:(pose proof grantF as (_&_&_&_&_&_&_&Hl&_); lia)) as [NI _]. apply NI. apply src0_rwseg_img. unfold CTX_SIZE in Hx. lits. lia. }
assert (HS1 : st_ok src0segs E8 (mkSS (ss_pc ss_kg1) (ss_regs ss_kg1) (R_ctr :: ss_mem ss_kg1) None (ss_facts ss_kg1)) ms1).
{ apply (st_ok_add_region src0segs E8 _ _ R_ctr HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_ctr ms_mem]; [lits; lia | lits; lia | |].
+ intros o Ho. rewrite Z.add_0_l. apply (proj1 (so_ctx_rw B (mid_syms _ _ _ _ _ MID) (ms_mem ms1) o ltac:(change (ms_ctx B) with CTX; unfold CTX_SIZE; lits; lia))).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_cval src0segs E8 (ms_mem ms1) 0 (LOCK + 20) 4 (SOff 89 0) ctr); [apply den_off0; exact E8_89 | lia |].
intros k Hk. rewrite Z.add_0_l.
pose proof (memrep_cell B L1 s3 mem3 (MCell (LCtx CTX_mmap_counter) 4 (VZ ctr)) (mid_mem _ _ _ _ _ HM3) ltac:(unfold image; apply in_app_iff; left; unfold ctx_cells; cbn [In]; right; right; left; reflexivity)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite (mid_ctx _ _ _ _ _ HM3) in C. change (ms_ctx B) with CTX in C. change (ms_segs B) with src0segs in C.
replace (LOCK + 20) with (CTX + CTX_mmap_counter) by (unfold CTX_mmap_counter; lits; lia).
rewrite (mbyte_ext1 mm0 (ms_mem ms1)); [rewrite (mbyte_ext1 mem3 mm0); [exact (C k Hk) | apply img_mm0; apply src0_rwseg_img; unfold CTX_mmap_counter; lits; lia]|].
apply F1; [unfold CTX_mmap_counter; lits; lia | apply CTXW; unfold CTX_mmap_counter, CTX_SIZE; lia].
- apply Forall_forall. intros r Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite SKk1 in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_ctr base_val]. cbn [In] in Hr'. unfold skel_M1 in Hr'. cbn [In] in Hr'.
assert (U86 : bv_unsigned (ew E8 86) = ua) by (rewrite E8_86; reflexivity).
assert (U40' : bv_unsigned (ew E8 40) = ptr_addr L1 m) by (rewrite E8_40, <- E6_40; exact U40).
destruct Hr' as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?U86, ?U40', ?(agree_cs' E8 33 AG8), ?(agree_reg' E8 2 AG8) by lia; rewrite ?lit64_small by (lits; lia);
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); fold sp; try (lits; lia).
+ destruct (Z_le_dec (ua + 16) (LOCK + 20)); [right; lia|]. left. destruct (Z_le_dec (LOCK + 24) ua); [lia|]. exfalso.
destruct (Z_lt_le_dec ua (LOCK + 20)); [destruct (Pf (LOCK + 20) ltac:(pose proof grantF as (_&_&_&_&_&_&_&Hl&_); lia)) as [NI _] | destruct (Pf ua ltac:(pose proof grantF as (_&_&_&_&_&_&_&Hl&_); lia)) as [NI _]]; apply NI; apply src0_rwseg_img; lits; lia.
+ destruct (Z_le_dec (ptr_addr L1 m + 40) (LOCK + 20)); [right; lia|]. left. destruct (Z_le_dec (LOCK + 24) (ptr_addr L1 m)); [lia|]. exfalso.
destruct (Z_lt_le_dec (ptr_addr L1 m) (LOCK + 20)); [destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 (LOCK + 20) ltac:(lia)) as [NI _] | destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 (ptr_addr L1 m) ltac:(lia)) as [NI _]];
apply NI; apply src0_rwseg_img; lits; lia. }
apply (st_ok_add_fact src0segs E8 _ ms1 89 F_ctr) in HS1. 2:{ unfold afact_ok, F_ctr. cbn [af_lo af_hi af_al2]. rewrite E8_89, lit64_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
exact HS1.
Qed.
Definition qv : Z := (4096 - UNIT) / class_size sc.
Lemma qv_facts : 0 <= qv <= 255 /\ forall E, env_agree 40 E00 E -> sv_denot E QV = Z_to_bv 64 qv.
Proof.
destruct cs_facts' as (_ & _ & _ & C35 & _ & _ & _ & CS). pose proof (class_size_bounds sc Hsc) as CB.
assert (Hq : 0 <= qv <= 255) by (unfold qv, UNIT; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
split; [exact Hq|]. intros E HA. unfold QV. apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite divu_unsigned, alu64_sll, (agree_cs' E 35 HA) by lia.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned, !lit64_small by lia. change (4 mod 64) with 4. rewrite sll64_small by (change (2 ^ 4) with 16; lia).
change (2 ^ 4) with 16. replace (csn 35 * 16) with (class_size sc) by lia. unfold qv. rewrite divu_4080 by lia. reflexivity.
Qed.
Definition TLpost (E9 : env) (ms : machine_state) : Prop :=
st_ok src0segs E9 ss_TL0 ms /\ env_agree 90 E8 E9 /\ ew E9 90 = Z_to_bv 64 aidx.
Lemma to_TL0 : forall ss ms, tl_check ss = true -> st_ok src0segs E8 ss ms -> facts_ok E8 (ss_facts ss_kg2) ->
sv_denot E8 (sr_get (ss_regs ss) 12) = Z_to_bv 64 aidx -> sr_get (ss_regs (junk_regs [12%bv] 90 ss)) 12 = SOff 90 0 ->
exists E9, TLpost E9 ms.
Proof.
intros ss ms CK HS HFk D12 R12. pose proof aidxF as (A1 & A2 & _). pose proof grantF as (_ & _ & _ & _ & _ & _ & C1 & _).
unfold tl_check in CK. apply andb_prop in CK as [AT MG].
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) [12%bv] = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs [12%bv] 90 E8 ss ms HS AT NZ) as (E9 & [Y D9] & HS9).
assert (E90 : ew E9 90 = Z_to_bv 64 aidx).
{ pose proof (st_ok_regs_ok _ E9 _ ms HS9 12%bv) as X1. pose proof (st_ok_regs_ok _ E8 _ ms HS 12%bv) as X2. rewrite R12 in X1. rewrite D12 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
assert (HFM : facts_ok E9 facts_TL).
{ pose proof (facts_ok_agree 90 E8 E9 (ss_facts ss_kg2) (conj Y D9) ltac:(vm_compute; reflexivity) HFk) as (Y1 & Y2 & Y3).
unfold facts_TL, addfact. split; [| split; [exact Y2 | exact Y3]]. cbn [f_atoms atoms_ok]. split; [| exact Y1].
unfold afact_ok, F_aidx; cbn [af_lo af_hi af_al2]. rewrite E90, lit64_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
exists E9. split; [| split; [exact (conj Y D9) | exact E90]].
exact (st_ok_merge src0segs E9 ss_TL0 (setfacts facts_TL (junk_regs [12%bv] 90 ss)) ms (st_ok_setfacts src0segs E9 _ ms facts_TL HS9 HFM) MG).
Qed.
Lemma to_TL : forall E9 ms, TLpost E9 ms -> (forall x, 0 <= x < 2 ^ 64 -> ~ WG1 x -> ms_mem ms (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
active_hd s3 sc = None -> csn 34 = 0 ->
st_ok src0segs E9 ss_TL ms /\ env_agree 40 E00 E9 /\ ew E9 40 = Z_to_bv 64 (ptr_addr L1 m) /\ ew E9 86 = a /\ ew E9 89 = Z_to_bv 64 ctr /\ ew E9 90 = Z_to_bv 64 aidx /\
ew E9 56 = Z_to_bv 64 (usage_of s1 sc) /\ ew E9 81 = Z_to_bv 64 len /\ ew E9 82 = Z_to_bv 64 cnt /\ ew E9 10 = Z_to_bv 64 sc.
Proof.
intros E9 ms (HS & AG89 & E90) F Hhd C34. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct E6_factsF as (E10 & E33 & E2 & U40 & _). destruct cs_facts' as (C33 & _). destruct E7_facts as (AG67 & AG7 & E7_86 & E7_40).
pose proof grantF as (_ & _ & Ha4 & Hce & _ & Pf & C1 & Hl & _). destruct BND1 as (BU & _). pose proof (BU sc) as BUs.
destruct skelsF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SUB & WFS & SKS' & ETL & _).
assert (AG78 : env_agree 89 E7 E8) by (apply env_agree_ewset).
assert (AG69 : env_agree 86 E6 E9).
{ eapply env_agree_trans; [exact AG67|]. eapply env_agree_trans; [eapply env_agree_le; [| exact AG78]; lia | eapply env_agree_le; [| exact AG89]; lia]. }
assert (AG9 : env_agree 40 E00 E9) by (eapply env_agree_trans; [exact AG6 | eapply env_agree_le; [| exact AG69]; lia]).
assert (E9_40 : ew E9 40 = Z_to_bv 64 (ptr_addr L1 m)) by (rewrite <- E6_40; apply (proj1 AG69); lia).
assert (E9_86 : ew E9 86 = a) by (rewrite <- E7_86; destruct AG89 as [Y _]; rewrite (Y 86%nat) by lia; apply (proj1 AG78); lia).
assert (E9_89 : ew E9 89 = Z_to_bv 64 ctr) by (destruct AG89 as [Y _]; rewrite (Y 89%nat) by lia; subst E8; apply ew_ewset_same).
assert (E9_56 : ew E9 56 = Z_to_bv 64 (usage_of s1 sc)) by (rewrite <- E6_56; apply (proj1 AG69); lia).
assert (E9_81 : ew E9 81 = Z_to_bv 64 len) by (unfold len; rewrite <- E6_81; apply (proj1 AG69); lia).
assert (E9_82 : ew E9 82 = Z_to_bv 64 cnt) by (unfold cnt; rewrite <- E6_82; apply (proj1 AG69); lia).
assert (E9_10 : ew E9 10 = Z_to_bv 64 sc) by (rewrite <- E10; apply (proj1 AG69); lia).
split; [| exact (conj AG9 (conj E9_40 (conj E9_86 (conj E9_89 (conj E90 (conj E9_56 (conj E9_81 (conj E9_82 E9_10))))))))].
assert (E9_33 : ew E9 33 = Z_to_bv 64 (csn 33)) by exact (agree_cs' E9 33 AG9 ltac:(lia)).
assert (U33 : bv_unsigned (ew E9 33) = csn 33) by (rewrite E9_33; apply lit64_small; lits; lia).
assert (CTXW : forall x, CTX <= x < CTX + CTX_SIZE -> ~ (LOCK + 20 <= x < LOCK + 24) -> ~ WG1 x).
{ intros x Hx Hn' [[Hw|[Hw|Hw]]|Hw]; [unfold WS, ASF, CTX_SIZE in *; lits; lia | | destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 x Hw) as [NI _]; apply NI; apply src0_rwseg_img; unfold CTX_SIZE in Hx; lits; lia | exact (Hn' Hw)].
destruct (Pf x ltac:(lia)) as [NI _]. apply NI. apply src0_rwseg_img. unfold CTX_SIZE in Hx. lits. lia. }
assert (CTXK : forall x, CTX <= x < CTX + CTX_SIZE -> ~ (LOCK + 20 <= x < LOCK + 24) -> ms_mem ms (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)).
{ intros x Hx Hn'. rewrite (F x ltac:(unfold CTX_SIZE in Hx; lits; lia) (CTXW x Hx Hn')). apply img_mm0. apply src0_rwseg_img. unfold CTX_SIZE in Hx. lits. lia. }
rewrite ETL.
assert (HS0 : st_ok src0segs E9 (mkSS (ss_pc ss_TL0) (ss_regs ss_TL0) (firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0)) None (ss_facts ss_TL0)) ms).
{ apply (st_ok_submem src0segs E9 ss_TL0 ms _ HS); [apply submemb_sound; exact SUB | exact WFS]. }
assert (APART : forall lo hi r, CTX + 80 <= lo -> lo < hi -> hi <= CTX + CTX_SIZE -> In r (firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0)) ->
hi <= base_val E9 (r_base r) + r_lo r \/ base_val E9 (r_base r) + r_hi r <= lo).
{ intros lo hi r Hlo Hlh Hhi Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite SKS' in Hr. cbn [In] in Hr.
assert (U86 : bv_unsigned (ew E9 86) = ua) by (rewrite E9_86; reflexivity).
assert (U40' : bv_unsigned (ew E9 40) = ptr_addr L1 m) by (rewrite E9_40, <- E6_40; exact U40).
destruct Hr as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; apply (f_equal (fun t => match t with (b, l, h) => (b, l, h) end)) in H; cbn in H; injection H as X1 X2 X3;
rewrite <- X1, <- X2, <- X3; cbn [base_val]; rewrite ?U86, ?U40', ?(agree_reg' E9 2 AG9) by lia;
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); fold sp; try (unfold CTX_SIZE in *; lits; lia).
- destruct (Z_le_dec (ua + 16) lo); [right; lia|]. left. destruct (Z_le_dec hi ua); [lia|]. exfalso.
destruct (Z_lt_le_dec ua lo); [destruct (Pf lo ltac:(lia)) as [NI _] | destruct (Pf ua ltac:(lia)) as [NI _]]; apply NI; apply src0_rwseg_img; unfold CTX_SIZE in *; lits; lia.
- destruct (Z_le_dec (ptr_addr L1 m + 40) lo); [right; lia|]. left. destruct (Z_le_dec hi (ptr_addr L1 m)); [lia|]. exfalso.
destruct (Z_lt_le_dec (ptr_addr L1 m) lo); [destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 lo ltac:(lia)) as [NI _] | destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 (ptr_addr L1 m) ltac:(lia)) as [NI _]];
apply NI; apply src0_rwseg_img; unfold CTX_SIZE in *; lits; lia. }
assert (HS1 : st_ok src0segs E9 (mkSS (ss_pc ss_TL0) (ss_regs ss_TL0) (R_useW :: firstn 3 (ss_mem ss_TL0) ++ skipn 4 (ss_mem ss_TL0)) None (ss_facts ss_TL0)) ms).
{ apply (st_ok_add_region src0segs E9 _ _ R_useW HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_useW ms_mem]; rewrite U33; [lits; lia | lits; lia | |].
+ intros o Ho. apply (proj1 (so_ctx_rw B (mid_syms _ _ _ _ _ MID) (ms_mem ms) (csn 33 + o) ltac:(change (ms_ctx B) with CTX; cbn [cs]; unfold CTX_SIZE; lits; lia))).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E9 (ms_mem ms) (csn 33) 472 (SOff 56 0) (usage_of s1 sc)); [apply den_off0; exact E9_56|].
apply (word_mem_ext1 mem3); [intros k Hk; apply CTXK; cbn [cs]; unfold CTX_SIZE; lits; lia|].
cbn [cs]. replace (usage_of s1 sc) with (usage_of s3 sc) by (unfold usage_of; rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 s3_factsF))))))))); reflexivity).
exact (usage_word L1 s3 mem3 md1 sc HM3 Hsc).
- apply Forall_forall. intros r Hr. unfold extent_disjoint. cbn [r_base r_lo r_hi R_useW base_val]. rewrite U33. apply (APART (csn 33 + 472) (csn 33 + 480) r); cbn [cs]; unfold CTX_SIZE; try (lits; lia). exact Hr. }
apply (st_ok_add_region src0segs E9 _ _ R_actW HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_actW ms_mem]; rewrite U33; [lits; lia | lits; lia | |].
+ intros o Ho. apply (proj1 (so_ctx_rw B (mid_syms _ _ _ _ _ MID) (ms_mem ms) (csn 33 + o) ltac:(change (ms_ctx B) with CTX; cbn [cs]; unfold CTX_SIZE; lits; lia))).
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E9 (ms_mem ms) (csn 33) 88 (SOff 34 0) 0); [apply den_off0; rewrite (agree_cs' E9 34 AG9) by lia; rewrite C34; reflexivity|].
apply (word_mem_ext1 mem3); [intros k Hk; apply CTXK; cbn [cs]; unfold CTX_SIZE; lits; lia|].
cbn [cs]. replace (LOCK + 8 * sc + 88) with (CTX + (CTX_active + 8 * Z.of_nat (Z.to_nat sc))) by (unfold CTX_active; lits; lia).
change 0 with (sval_num L1 (optr None)). rewrite <- Hhd. unfold active_hd.
apply (ctx_word_gen L1 s3 mem3 md1 _ _ HM3); [| destruct (nth (Z.to_nat sc) (st_active s3) None); intros z; discriminate].
unfold ctx_cells. rewrite !in_app_iff. right. left. apply in_map_iff. exists (Z.to_nat sc). split; [reflexivity | apply in_seq; lia].
- apply Forall_cons; [unfold extent_disjoint; cbn [r_base r_lo r_hi R_actW R_useW base_val]; rewrite U33; left; lia|].
apply Forall_forall. intros r Hr. unfold extent_disjoint. cbn [r_base r_lo r_hi R_actW base_val]. rewrite U33. apply (APART (csn 33 + 88) (csn 33 + 96) r); cbn [cs]; unfold CTX_SIZE; try (lits; lia). exact Hr.
Qed.
Definition KEpost (c : config) : Prop :=
exists E9 ms, c = mkCfg ms md2 /\ st_ok src0segs E9 ss_kE ms /\ env_agree 40 E00 E9 /\
ew E9 40 = Z_to_bv 64 (ptr_addr L1 m) /\ ew E9 86 = a /\ ew E9 89 = Z_to_bv 64 ctr /\ ew E9 90 = Z_to_bv 64 aidx /\
ew E9 56 = Z_to_bv 64 (usage_of s1 sc) /\ ew E9 81 = Z_to_bv 64 len /\ ew E9 82 = Z_to_bv 64 cnt /\ ew E9 10 = Z_to_bv 64 sc /\
(forall x, 0 <= x < 2 ^ 64 -> ~ WG2 x -> ms_mem ms (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
Lemma md2_facts : m_halted md2 = None /\ m_vm_lazy md2 = [] /\ m_vm_materialized md2 = [] /\ exists vm', md2 = with_vmmaps vm' md.
Proof.
unfold md2, mmap_model. rewrite m_halted_with, m_vm_lazy_with, m_vm_materialized_with. split; [exact Mh1|]. split; [exact Mlz1|]. split; [exact Mmat1|].
destruct VM1 as [vm1 ->]. rewrite with_vmmaps_twice. eexists. reflexivity.
Qed.
Theorem reach_kE : forall ms0, st_ok src0segs E7 ss_Kg ms0 -> ms_mem ms0 = mm0 -> SR src0segs (mkCfg ms0 md2) KEpost.
Proof.
intros ms0 HS0 Hmm0. pose proof (proj1 alloc_ceiling_val) as AC. destruct md2_facts as (Mh2 & Mlz2 & Mmat2 & _).
destruct E7_facts as (AG67 & AG7 & E7_86 & E7_40). pose proof grantF as (_ & _ & Ha4 & Hce & _ & Pf & C1 & Hl & _). pose proof aidxF as (A1 & A2 & A3).
destruct skelsF as (W0 & W1 & W2 & W3 & W4 & W5 & _ & _ & _ & _ & _ & _ & _ & _ & G10).
destruct (hd_none ms0 HS0) as [Hhd C34].
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E7 ss_Kg ss_kg0); [exact Mh2 | exact Mlz2 | exact HS0 | apply run_Kg |].
intros ms1 HS1 Hfr1.
assert (F1 : forall x, 0 <= x < 2 ^ 64 -> ~ WG0 x -> ms_mem ms1 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepF WG0 E7 (ss_mem ss_Kg) SKg0 (ms_mem ms0) _ mm0 Hfr1 W0); [intros b lo hi x Hin Hx; exact (SKg0_W E7 b lo hi x AG7 E7_40 E7_86 Hin Hx) | intros; rewrite Hmm0; reflexivity]. }
apply (st_ok_add_cond src0segs E7 ss_kg0 ms1 BC_NE (ac_a C_mapok) (SLit 0)) in HS1.
2:{ cbn [ac_a C_mapok sv_denot]. rewrite E7_86, Z.add_0_r, Z_to_bv_bv_unsigned. apply mapok_taken. unfold ua in Hce. lia. }
change (add_cond ss_kg0 (mkAC BC_NE (ac_a C_mapok) (SLit 0))) with (add_cond ss_kg0 C_mapok) in HS1.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E7 (add_cond ss_kg0 C_mapok) ss_kg1); [exact Mh2 | exact Mlz2 | exact HS1 | apply run_kg0 |].
intros ms2 HS2 Hfr2.
assert (F2 : forall x, 0 <= x < 2 ^ 64 -> ~ WG0 x -> ms_mem ms2 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepF WG0 E7 (ss_mem (add_cond ss_kg0 C_mapok)) SKg0 (ms_mem ms1) _ mm0 Hfr2 W1); [intros b lo hi x Hin Hx; exact (SKg0_W E7 b lo hi x AG7 E7_40 E7_86 Hin Hx) | exact F1]. }
destruct (station_G1 ms2 HS2 F2) as (HS3 & AG78 & AG8 & E8_89 & E8_86 & E8_40).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E8 ss_G1 ss_kg2); [exact Mh2 | exact Mlz2 | exact HS3 | apply run_G1 |].
intros ms3 HS4 Hfr3.
assert (F3 : forall x, 0 <= x < 2 ^ 64 -> ~ WG1 x -> ms_mem ms3 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepF WG1 E8 (ss_mem ss_G1) SKg1 (ms_mem ms2) _ mm0 Hfr3 W2); [intros b lo hi x Hin Hx; exact (SKg1_W E8 b lo hi x AG8 E8_40 E8_86 Hin Hx) |].
intros x Hx Hw. apply F2; [exact Hx | intros Hw0; apply Hw; left; exact Hw0]. }
pose proof (st_ok_facts_ok src0segs E8 ss_kg2 ms3 HS4) as HFk.
destruct qv_facts as [Hq DQ]. pose proof aidx_regs as (RT & RF' & RTj & RFj).
assert (E8_82 : ew E8 82 = Z_to_bv 64 cnt) by (unfold cnt; rewrite <- E6_82; rewrite <- (proj1 AG67 82%nat) by lia; apply (proj1 AG78); lia).
assert (FIN : forall E9 ms4, TLpost E9 ms4 -> (forall x, 0 <= x < 2 ^ 64 -> ~ WG1 x -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) -> SR src0segs (mkCfg ms4 md2) KEpost).
{ intros E9 ms4 TP F4. destruct (to_TL E9 ms4 TP F4 Hhd C34) as (HS5 & AG9 & E9_40 & E9_86 & E9_89 & E9_90 & E9_56 & E9_81 & E9_82 & E9_10).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E9 ss_TL ss_kE); [exact Mh2 | exact Mlz2 | exact HS5 | apply run_TL |].
intros ms5 HS6 Hfr5. apply SR_ret. exists E9, ms5. split; [reflexivity|]. split; [exact HS6|]. split; [exact AG9|].
repeat (split; [assumption|]).
apply (frame_keepF WG2 E9 (ss_mem ss_TL) SKg2 (ms_mem ms4) _ mm0 Hfr5 W5); [intros b lo hi x Hin Hx; exact (SKg2_W E9 b lo hi x AG9 E9_40 E9_86 Hin Hx) |].
intros x Hx Hw. apply F4; [exact Hx | intros Hw1; apply Hw; left; exact Hw1]. }
apply (SR_sym_branch src0segs E8 ss_kg2 ms3 md2 _ BC_LTU (SOff 82 0) QV HS4).
-
intros Hb HSb. rewrite (den_off0 E8 82 cnt E8_82), (DQ E8 AG8), branch_ltu, !lit64_small in Hb by lia. apply Z.ltb_lt in Hb.
assert (EA : aidx = cnt - 1).
{ rewrite A3. cbn zeta. fold qv. replace (cnt - 1 <? qv - 1) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
change (add_cond ss_kg2 (mkAC BC_LTU (SOff 82 0) QV)) with (add_cond ss_kg2 C_aT) in HSb.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_TL E8 (add_cond ss_kg2 C_aT) ss_kT3 RS_running); [exact Mh2 | exact Mlz2 | exact HSb | apply run_aT |].
intros ms4 HS7 Hfr4.
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WG1 x -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepF WG1 E8 (ss_mem (add_cond ss_kg2 C_aT)) SKg1 (ms_mem ms3) _ mm0 Hfr4 W3); [intros b lo hi x Hin Hx; exact (SKg1_W E8 b lo hi x AG8 E8_40 E8_86 Hin Hx) | exact F3]. }
destruct (to_TL0 ss_kT3 ms4 tl_T HS7 HFk ltac:(rewrite RT; cbn [sv_denot]; rewrite E8_82, lit64_small, EA by lia; reflexivity) RTj) as (E9 & TP).
exact (FIN E9 ms4 TP F4).
-
intros Hb HSb. pose proof Hb as Hb0. rewrite (den_off0 E8 82 cnt E8_82), (DQ E8 AG8), branch_ltu, !lit64_small in Hb by lia. apply Z.ltb_ge in Hb.
change (add_cond ss_kg2 (mkAC (neg_bc BC_LTU) (SOff 82 0) QV)) with (add_cond ss_kg2 C_aF) in HSb.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_TL E8 (add_cond ss_kg2 C_aF) ss_kF3 RS_running); [exact Mh2 | exact Mlz2 | exact HSb | apply run_aF |].
intros ms4 HS7 Hfr4.
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WG1 x -> ms_mem ms4 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)).
{ apply (frame_keepF WG1 E8 (ss_mem (add_cond ss_kg2 C_aF)) SKg1 (ms_mem ms3) _ mm0 Hfr4 W4); [intros b lo hi x Hin Hx; exact (SKg1_W E8 b lo hi x AG8 E8_40 E8_86 Hin Hx) | exact F3]. }
assert (DA : sv_denot E8 AIDX_F = Z_to_bv 64 aidx).
{ unfold AIDX_F, QV0. apply (proj2 (word_eq _ _)). rewrite (lit64_small aidx) by lia. cbn [sv_denot]. rewrite !alu64_and, !alu64_add, !alu64_sltu, !alu64_add, (DQ E8 AG8), !lit64_small by lia.
change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1). rewrite (add64_small qv 0) by lia. rewrite Z.add_0_r.
pose proof (aidx_machine_ok cnt qv ltac:(lia) ltac:(lia)) as AM. unfold aidx_machine in AM. replace (cnt <? qv) with false in AM by (symmetry; apply Z.ltb_ge; lia).
cbn zeta in AM. rewrite AM, A3. cbn zeta. fold qv. reflexivity. }
destruct (to_TL0 ss_kF3 ms4 tl_F HS7 HFk ltac:(rewrite RF'; exact DA) RFj) as (E9 & TP).
exact (FIN E9 ms4 TP F4).
Qed.
Lemma am1_slots : forall i, 0 <= i < cnt -> nth_slot am1 i = slot_zero.
Proof. intros i Hi. unfold nth_slot, am1, am_inst, am_inst0, am_set_links. cbn [am_slots]. apply nth_repeat_lt. lia. Qed.
Lemma am1_fields : am_mem am1 = SP Nr 0 /\ am_last am1 = cnt - 1 /\ am_prev am1 = Some m /\ am_next am1 = Some m /\ am_sc am1 = sc /\ am_maplen am1 = len / 4096 /\ am_aidx am1 = aidx /\
am_avail am1 = ones aidx - 1 /\ am_freed am1 = ones (cnt - 1) - ones aidx /\ (am_maplen am1 =? 0) = false.
Proof.
pose proof grantF as (_ & _ & _ & _ & _ & _ & _ & Hl & _). unfold am1, am_inst, am_inst0, am_set_links. cbn. repeat split; try reflexivity.
apply Z.eqb_neq. intros E. pose proof (Z.div_str_pos len 4096 ltac:(lia)). lia.
Qed.
Lemma inst_lists :
(exists u1 u2, used_metas s3 = u1 ++ u2 /\ used_metas s5 = u1 ++ (m, am1) :: u2) /\
frames s5 = frames s3 /\ user_blocks s5 = user_blocks s3 /\
footprint s5 = footprint s3 ++ [(LMem (SP Nr 0), len)] /\
(forall c, In c (tail_cells s5) <-> In c (tail_cells s3) \/ c = MCell (LMem (padd (SP Nr 0) (group_extent am1))) 1 (VZ 0)) /\
(forall c, In c (group_cells m am1) <-> c = MCell (LMem (SP Nr 0)) 8 (VP m) \/ c = MCell (LMem (padd (SP Nr 0) 8)) 4 (VZ aidx) \/
exists i, 0 <= i < cnt /\ In c [MCell (LMem (padd (slot_start am1 i) (-4))) 1 (VZ 0); MCell (LMem (padd (slot_start am1 i) (-3))) 1 (VZ 0); MCell (LMem (padd (slot_start am1 i) (-2))) 2 (VZ 0)]) /\
(forall gm, In gm (used_metas s5) <-> gm = (m, am1) \/ In gm (used_metas s3)).
Proof.
destruct s3_factsF as (I3 & X3 & A3 & K3 & M3 & _). pose proof (inst_fields sc m cnt len s3) as (Fm & Fr & Far & _).
change (inst_st sc m cnt len s3) with s5 in Fm, Fr, Far. change (am_inst m sc cnt (len / 4096) (aidx_of sc cnt) (length (st_regions s3))) with am1 in Fm.
pose proof am1_fields as (Gmem & Glast & Gpr & Gnx & Gsc & Gml & Gai & Gav & Gfr & Gml0). pose proof grantF as (_ & _ & _ & _ & _ & _ & C1 & _).
assert (Mm3 : MT s3 m = Some MRaw \/ MT s3 m = Some (MFree None None)) by (rewrite M3; exact Mm).
assert (UM : exists u1 u2, used_metas s3 = u1 ++ u2 /\ used_metas s5 = u1 ++ (m, am1) :: u2).
{ replace (used_metas s5) with (used_metas (upd_meta m (MUsed am1) s3)) by (unfold used_metas; f_equal; unfold upd_meta; cbn [st_metas set_metas]; symmetry; exact Fm).
destruct Mm3 as [E|E]; [exact (used_metas_ins s3 m am1 MRaw E eq_refl) | exact (used_metas_ins s3 m am1 _ E eq_refl)]. }
destruct UM as (u1 & u2 & U3 & U5).
assert (FRn : forall i, In i (zseq 0 (am_last am1 + 1)) -> ss_fr (nth_slot am1 i) = None).
{ intros i Hi. apply In_zseq in Hi. rewrite Glast in Hi. rewrite am1_slots by lia. reflexivity. }
split; [exists u1, u2; exact (conj U3 U5)|]. split.
{ unfold frames. rewrite U3, U5, !flat_map_app. cbn [flat_map]. rewrite (flat_map_nil _ (zseq 0 (am_last am1 + 1))); [reflexivity|]. intros i Hi. rewrite (FRn i Hi). reflexivity. }
split.
{ unfold user_blocks. rewrite U3, U5, !flat_map_app. cbn [flat_map snd]. rewrite (flat_map_nil _ (zseq 0 (am_last am1 + 1))); [reflexivity|]. intros i Hi. rewrite (FRn i Hi). reflexivity. }
split.
{ unfold footprint. rewrite Far, Fr, length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, flat_map_app. cbn [flat_map Nat.add].
pose proof (inst_region_of sc m cnt len s3) as RO. change (inst_st sc m cnt len s3) with s5 in RO.
rewrite (RO (length (st_regions s3))), Nat.ltb_irrefl, Nat.eqb_refl. cbn [rg_kind rg_live rg_len]. rewrite app_nil_r.
cbn [app]. rewrite <- app_assoc. f_equal. f_equal. f_equal. apply YN2c.flat_map_ext_in. intros k Hk. apply in_seq in Hk.
rewrite (RO k). rewrite (proj2 (Nat.ltb_lt k _)) by lia. reflexivity. }
split.
{ intros c. unfold tail_cells. rewrite U3, U5, !flat_map_app. cbn [flat_map snd].
assert (GT : group_tail_cells am1 = [MCell (LMem (padd (SP Nr 0) (group_extent am1))) 1 (VZ 0)]).
{ unfold group_tail_cells. rewrite Gmem, (flat_map_nil (frame_tail_cells am1) (zseq 0 (am_last am1 + 1))) by (intros i Hi; unfold frame_tail_cells; rewrite (FRn i Hi); reflexivity). reflexivity. }
rewrite GT. rewrite !in_app_iff. cbn [In app]. split.
- intros [H|[[H|[]]|H]]; [left; left; exact H | right; symmetry; exact H | left; right; exact H].
- intros [[H|H]| ->]; [left; exact H | right; right; exact H | right; left; left; reflexivity]. }
split.
{ intros c. unfold group_cells. rewrite Gmem, Gml0, Gai, Glast. cbn [app]. replace (cnt - 1 + 1) with cnt by lia. split.
- intros [<-|[<-|H]]; [left; reflexivity | right; left; reflexivity | right; right].
apply in_flat_map in H as (i & Hi & Hc). apply In_zseq in Hi. exists i. split; [lia|]. unfold slot_cells in Hc. rewrite am1_slots in Hc by lia. cbn [ss_hdr ss_fr slot_zero app] in Hc. exact Hc.
- intros [->|[->|(i & Hi & Hc)]]; [left; reflexivity | right; left; reflexivity | right; right].
apply in_flat_map. exists i. split; [apply In_zseq; lia|]. unfold slot_cells. rewrite am1_slots by lia. cbn [ss_hdr ss_fr slot_zero app]. exact Hc. }
intros gm. rewrite U3, U5, !in_app_iff. cbn [In]. split; [intros [H|[H|H]]; [right; left; exact H | left; symmetry; exact H | right; right; exact H] | intros [->|[H|H]]; [right; left; reflexivity | left; exact H | right; right; exact H]].
Qed.
Lemma ctx_cells_s5 : forall c, In c (ctx_cells s5) ->
c = MCell (LCtx CTX_mmap_counter) 4 (VZ (Z.land (ctr + 1) (2 ^ 32 - 1))) \/
c = MCell (LCtx (CTX_usage + 8 * sc)) 8 (VZ (usage_of s1 sc + cnt)) \/
c = MCell (LCtx (CTX_active + 8 * sc)) 8 (VP m) \/
(In c (ctx_cells s3) /\ exists off, mc_loc c = LCtx off /\ 0 <= off /\
(off + Z.of_nat (mc_w c) <= CTX_mmap_counter \/ CTX_mmap_counter + 4 <= off) /\
(off + Z.of_nat (mc_w c) <= CTX_active + 8 * sc \/ CTX_active + 8 * sc + 8 <= off) /\
(off + Z.of_nat (mc_w c) <= CTX_usage + 8 * sc \/ CTX_usage + 8 * sc + 8 <= off)).
Proof.
intros c H. pose proof (inst_fields sc m cnt len s3) as (Fm & Fr & Far & Fb & Fac & Fu & Fmc & Fid & Ffh & Fam & Famc & Faac & Fsh & Fah & Fat & Fama & Fuq & Fbn & Fsq).
change (inst_st sc m cnt len s3) with s5 in Fm, Fr, Far, Fb, Fac, Fu, Fmc, Fid, Ffh, Fam, Famc, Faac, Fsh, Fah, Fat, Fama, Fuq, Fbn, Fsq.
pose proof ctrF as (_ & LA & LU). destruct s3_factsF as (_ & _ & _ & _ & _ & _ & _ & _ & Ac3 & U3).
assert (EU : usage_of s3 sc = usage_of s1 sc) by (unfold usage_of; rewrite U3; reflexivity).
unfold ctx_cells in H. rewrite Fid, Fmc, Ffh, Far, Fam, Famc, Faac, Fsh, Fah, Fat, Fama, Fsq, Fb, Fac, Fu, Fuq, Fbn in H. rewrite !in_app_iff in H.
unfold CTX_free_meta_head, CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count, CTX_meta_alloc_shift,
CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk, CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
destruct H as [H|[H|[H|[H|H]]]].
- cbn [In] in H. fold ctr in H. destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
try (left; reflexivity); right; right; right; (split; [unfold ctx_cells; apply in_app_iff; left; inlist | eexists; split; [reflexivity|]; cbn [mc_w]; lia]).
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. rewrite nth_lupd, LA.
destruct (Nat.eqb_spec k (Z.to_nat sc)).
+ subst k. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb optr]. right. right. left. rewrite Z2Nat.id by lia. reflexivity.
+ cbn [andb]. right. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. assert (Z.of_nat k <> sc) by lia. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. unfold zset. rewrite nth_zupd, LU.
destruct (Nat.eqb_spec k (Z.to_nat sc)).
+ subst k. replace (Nat.ltb (Z.to_nat sc) 48) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb]. right. left. rewrite Z2Nat.id, EU by lia. reflexivity.
+ cbn [andb]. right. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. assert (Z.of_nat k <> sc) by lia. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. lia.
- apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. right. right. right. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; right; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
eexists; split; [reflexivity|]. cbn [mc_w]. unfold CTX_bounces. lia.
Qed.
Definition Wall (x : Z) : Prop := WG2 x \/ ua <= x < ua + len.
Lemma Wall_cases : forall x, Wall x ->
WSn x \/ (ua <= x < ua + len) \/ (ptr_addr L1 m <= x < ptr_addr L1 m + 40) \/
(CTX <= x < CTX + CTX_SIZE /\ (CTX + CTX_mmap_counter <= x < CTX + CTX_mmap_counter + 4 \/ CTX + CTX_active + 8 * sc <= x < CTX + CTX_active + 8 * sc + 8 \/ CTX + CTX_usage + 8 * sc <= x < CTX + CTX_usage + 8 * sc + 8)).
Proof.
intros x [[[[Hw|[Hw|Hw]]|Hw]|[Hw|Hw]]|Hw]; pose proof grantF as (_ & _ & _ & _ & _ & _ & _ & Hl & _).
- left. exact Hw. - right. left. lia. - right. right. left. exact Hw.
- right. right. right. unfold CTX_mmap_counter, CTX_active, CTX_usage, CTX_SIZE. lits. lia.
- right. right. right. cbn [cs] in Hw. unfold CTX_mmap_counter, CTX_active, CTX_usage, CTX_SIZE. lits. lia.
- right. right. right. cbn [cs] in Hw. unfold CTX_mmap_counter, CTX_active, CTX_usage, CTX_SIZE. lits. lia.
- right. left. exact Hw.
Qed.
Lemma old_region_off : forall k rg x, region_of s3 k = Some rg -> rg_live rg = true ->
ly_reg L1 k + reg_lo rg <= x < ly_reg L1 k + rg_len rg -> ~ (ptr_addr L1 m <= x < ptr_addr L1 m + 40) -> ~ Wall x.
Proof.
intros k rg x Hk Hl Hx Hm HW. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & _).
pose proof grantF as (_ & _ & Ha4 & Hce & RF & Pf & C1 & Hl' & _). pose proof (reg_lo_le rg) as RL.
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM3) k rg Hk Hl) as (_ & Plo & Phi & Pimg).
pose proof (mid_syms _ _ _ _ _ HM3) as SO.
destruct (Wall_cases x HW) as [Hw|[Hw|[Hw|[Hc _]]]].
- unfold WS, ASF in *. lia.
- exact (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM3) a len ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF k rg x Hk Hl Hx ltac:(unfold ua in Hw; exact Hw)).
- exact (Hm Hw).
- apply (Pimg x ltac:(lia)). apply (so_ctx_img _ SO). exact Hc.
Qed.
Lemma mem5_old : forall mm5, (forall x, 0 <= x < 2 ^ 64 -> ~ WG2 x -> mm5 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
forall x, 0 <= x < 2 ^ 64 -> ~ Wall x -> mm5 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x).
Proof. intros mm5 F5 x Hx HW. rewrite (F5 x Hx) by (intros H; apply HW; left; exact H). apply mm0_off; [exact Hx|]. intros H; apply HW; right; exact H. Qed.
Lemma L2_old : forall p, (prid p < Nr)%nat -> ptr_addr L2 p = ptr_addr L1 p.
Proof. intros [r o] Hr. unfold ptr_addr, L2. cbn [loc_addr]. rewrite (Lset_lt L1 s3 ua r Hr). reflexivity. Qed.
Lemma L2_new : forall o, ptr_addr L2 (SP Nr o) = ua + o.
Proof. intros o. unfold ptr_addr, L2, Nr. cbn [loc_addr]. rewrite (Lset_new L1 s3 ua). reflexivity. Qed.
Lemma L2_ctx : ly_ctx L2 = CTX /\ ly_sec L2 = ly_sec L1 /\ ly_brk0 L2 = ly_brk0 L1.
Proof. unfold L2, Lset. cbn. split; [exact (mid_ctx _ _ _ _ _ HM3) | split; reflexivity]. Qed.
Lemma key_prid : forall q, In q (keys s3) -> (prid q < Nr)%nat /\ exists ar k, In ar (st_areas s3) /\ 0 <= k < METAS_PER_AREA /\ q = slot_of ar k /\
exists r o rg, ar = SP r o /\ PGSZ <= o /\ region_of s3 r = Some rg /\ rg_live rg = true /\ o + PGSZ <= rg_len rg.
Proof.
intros q Hq. destruct s3_factsF as (I3 & X3 & A3 & K3 & M3 & _).
destruct (key_facts (m :: X) U L1 s3 mem3 md1 q I3 HM3 Hq) as (_ & _ & _ & ar & k & Har & Hk & Eq).
pose proof (inv_areas I3) as (_ & Hareas & _). destruct (Hareas ar Har) as (r & o & rg & Ear & Ho & Hlo & Hr & Hl & Hlen & _).
split; [rewrite Eq, Ear; unfold slot_of; cbn; exact (region_of_lt _ _ _ Hr)|].
exists ar, k. split; [exact Har|]. split; [exact Hk|]. split; [exact Eq|]. exists r, o, rg. repeat (split; [assumption|]). exact Hlen.
Qed.
Lemma kE_regions :
nth_error (ss_mem ss_kE) 0 = Some (YP09.mkRegion (Some 33%nat) 88 96 88 96 [mkChunk 88 (CVal 8 (SOff 40 0))]) /\
nth_error (ss_mem ss_kE) 1 = Some (YP09.mkRegion (Some 33%nat) 472 480 472 480 [mkChunk 472 (CVal 8 (SAlu ALU_ADD (SOff 56 0) (SOff 82 0)))]) /\
nth_error (ss_mem ss_kE) 2 = Some (YP09.mkRegion None (LOCK + 20) (LOCK + 24) (LOCK + 20) (LOCK + 24) [mkChunk (LOCK + 20) (CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff 89 0)) (SLit 1)))]) /\
nth_error (ss_mem ss_kE) 3 = Some (YP09.mkRegion (Some 86%nat) 0 16 0 16 [mkChunk 8 (CVal 1 (SAlu ALU_OR (SLit 0) (SAlu ALU_AND (SOff 90 0) (SLit 31)))); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 9 (CZero 7)]) /\
nth_error (ss_mem ss_kE) 4 = Some (YP09.mkRegion (Some 40%nat) 0 40 0 40
[mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0));
mkChunk 24 (CVal 4 (SAlu ALU_ADD (SExt true 32 AVAIL0) (SLit (-1))));
mkChunk 32 (CVal 8 BITS); mkChunk 16 (CVal 8 (SOff 86 0));
mkChunk 28 (CVal 4 (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 82 (-1))) (SAlu ALU_XOR (SExt true 32 AVAIL0) (SLit (-1)))))]) /\
(exists rstk, nth_error (ss_mem ss_kE) 5 = Some rstk /\ r_base rstk = Some 2%nat /\ r_wlo rstk = - ASF /\ r_whi rstk = 0) /\
finalS_check ss_kE (SLit 0) = true /\ nth_error (ss_mem ss_kE) 7 = Some R_guard.
Proof. vm_compute. repeat (split; [reflexivity|]). split; [eexists; repeat split; reflexivity | split; reflexivity]. Qed.
Lemma midrep_s5 : forall E9 ms5,
st_ok src0segs E9 ss_kE ms5 -> env_agree 40 E00 E9 ->
ew E9 40 = Z_to_bv 64 (ptr_addr L1 m) -> ew E9 86 = a -> ew E9 89 = Z_to_bv 64 ctr -> ew E9 90 = Z_to_bv 64 aidx ->
ew E9 56 = Z_to_bv 64 (usage_of s1 sc) -> ew E9 81 = Z_to_bv 64 len -> ew E9 82 = Z_to_bv 64 cnt -> ew E9 10 = Z_to_bv 64 sc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WG2 x -> ms_mem ms5 (Z_to_bv 64 x) = mm0 (Z_to_bv 64 x)) ->
midrep B L2 s5 (ms_mem ms5) md2.
Proof.
intros E9 ms5 HS AG9 E9_40 E9_86 E9_89 E9_90 E9_56 E9_81 E9_82 E9_10 F5.
pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct s3_factsF as (I3 & X3 & A3 & K3 & M3 & B3 & R3 & Ar3 & Ac3 & U3).
pose proof grantF as (PR & Hal & Ha4 & Hce & RF & Pf & C1 & Hl & Hlm). pose proof aidxF as (A1 & A2 & _). pose proof ctrF as (Hctr & LA & LU).
pose proof stride1 as (ST1 & ST2 & ST3 & ST4). destruct E6_factsF as (_ & E33 & _ & U40 & _). destruct cs_facts' as (C33 & _).
pose proof am1_fields as (Gmem & Glast & Gpr & Gnx & Gsc & Gml & Gai & Gav & Gfr & Gml0).
pose proof inst_lists as ((u1 & u2 & U35 & U5) & FR5 & UB5 & FP5 & TC5 & GC5 & UM5).
pose proof (inst_fields sc m cnt len s3) as (Fm & Fr & Far & Fb & _). change (inst_st sc m cnt len s3) with s5 in Fm, Fr, Far, Fb.
pose proof (mid_syms _ _ _ _ _ HM3) as SO. pose proof (mid_mem _ _ _ _ _ HM3) as MR3. destruct L2_ctx as (LC & LS & LB).
pose proof (Inv_ptrs_below (m :: X) None U s3 I3 X3 A3) as PB. destruct BND1 as (BU & _). pose proof (BU sc) as BUs.
assert (Km3 : In m (keys s3)) by (rewrite K3; exact Km).
destruct (key_prid m Km3) as (PRm & arm & km & Harm & Hkm & Eqm & _).
set (mem5 := ms_mem ms5) in *.
assert (U33 : bv_unsigned (ew E9 33) = csn 33) by (rewrite (agree_cs' E9 33 AG9), lit64_small by (lits; lia); reflexivity).
assert (U40' : bv_unsigned (ew E9 40) = ptr_addr L1 m) by (rewrite E9_40, <- E6_40; exact U40).
assert (U86 : bv_unsigned (ew E9 86) = ua) by (rewrite E9_86; reflexivity).
destruct kE_regions as (R0 & R1 & R2 & R3' & R4 & _ & _).
assert (OLD : forall x, 0 <= x < 2 ^ 64 -> ~ Wall x -> mem5 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)) by (exact (mem5_old mem5 F5)).
assert (MFR : forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> ~ (ua <= x < ua + len)).
{ intros x Hx. exact (mslot_fresh X U L A regs sc g j1 j2 m s1 L1 md1 HI1 RX1 Mm Km AMA1 BND1 mem3 a len HM3 ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF x Hx). }
assert (ZMAP : forall x, ua + 16 <= x < ua + len -> mem5 (Z_to_bv 64 x) = Some (Z_to_bv 8 0)).
{ intros x Hx. rewrite (F5 x ltac:(lia)); [apply mm0_in; lia|]. destruct (Pf x ltac:(lia)) as [NI Rx].
intros [[[Hw|[Hw|Hw]]|Hw]|[Hw|Hw]]; [unfold WS, ASF in *; lia | lia | exact (MFR x Hw ltac:(lia)) | apply NI; apply src0_rwseg_img; lits; lia | cbn [cs] in Hw; apply NI; apply src0_rwseg_img; lits; lia | cbn [cs] in Hw; apply NI; apply src0_rwseg_img; lits; lia]. }
assert (ZMAPb : forall x, ua + 16 <= x < ua + len -> mbyte src0segs mem5 x = Some (Z_to_bv 8 0)).
{ intros x Hx. unfold mbyte. rewrite (ZMAP x Hx). reflexivity. }
assert (GZ : forall x, ua + 9 <= x < ua + 16 -> mbyte src0segs mem5 x = Some (Z_to_bv 8 0)).
{ intros x Hx. replace x with (bv_unsigned (ew E9 86) + 9 + (x - ua - 9)) by lia. apply (zeros_of_chunk_at E9 ss_kE ms5 3 _ 86 9 7 HS R3' eq_refl ltac:(right; right; left; reflexivity)). lia. }
assert (M_act : word_mem src0segs mem5 (csn 33 + 88) (ptr_addr L1 m)).
{ rewrite <- U33. apply (word_of_chunk_at E9 ss_kE ms5 0 _ 33 88 (SOff 40 0) _ HS R0 eq_refl ltac:(left; reflexivity)). exact (den_off0 E9 40 _ E9_40). }
assert (M_use : word_mem src0segs mem5 (csn 33 + 472) (usage_of s1 sc + cnt)).
{ rewrite <- U33. apply (word_of_chunk_at E9 ss_kE ms5 1 _ 33 472 _ _ HS R1 eq_refl ltac:(left; reflexivity)). exact (usage_val E9 _ _ E9_56 E9_82 BUs C1). }
assert (M_ctr : forall k, (k < 4)%nat -> mbyte src0segs mem5 (LOCK + 20 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (Z.land (ctr + 1) (2 ^ 32 - 1)) 4 k))).
{ intros k Hk. replace (LOCK + 20) with (0 + (LOCK + 20)) by lia.
apply (chunk_bytes_cval src0segs E9 mem5 0 (LOCK + 20) 4 _ _ (st_ok_chunk src0segs E9 ss_kE ms5 2 _ _ HS R2 ltac:(left; reflexivity))); [| exact Hk].
exact (ctr_val E9 ctr E9_89 Hctr). }
assert (M_ghdr : word_mem src0segs mem5 ua (ptr_addr L1 m)).
{ replace ua with (bv_unsigned (ew E9 86) + 0) by lia. apply (word_of_chunk_at E9 ss_kE ms5 3 _ 86 0 (SOff 40 0) _ HS R3' eq_refl ltac:(right; left; reflexivity)). exact (den_off0 E9 40 _ E9_40). }
assert (M_gaidx : forall k, (k < 4)%nat -> mbyte src0segs mem5 (ua + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte aidx 4 k))).
{ intros k Hk. destruct k as [|k].
- rewrite <- U86. pose proof (chunk_bytes_cval src0segs E9 mem5 (bv_unsigned (ew E9 86)) 8 1 _ aidx (st_ok_chunk src0segs E9 ss_kE ms5 3 _ _ HS R3' ltac:(left; reflexivity)) (aidx_byte E9 aidx E9_90 ltac:(lia)) 0 ltac:(lia)) as T.
cbn [Z.of_nat] in T |- *. rewrite T. f_equal. f_equal. unfold le_byte.
change (8 * Z.of_nat (N.to_nat 1)) with 8. change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 0) with 0. rewrite !Z.shiftr_0_r.
change (2 ^ 8) with 256. change (2 ^ 32) with 4294967296. rewrite (Z.mod_small aidx 4294967296), !(Z.mod_small aidx 256) by lia. reflexivity.
- rewrite GZ by lia. f_equal. f_equal. unfold le_byte. change (8 * Z.of_nat 4) with 32. change (2 ^ 32) with 4294967296. rewrite (Z.mod_small aidx 4294967296) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity|].
split; [lia|]. apply (Z.lt_le_trans _ (2 ^ 8)); [change (2 ^ 8) with 256; lia|]. apply Z.pow_le_mono_r; lia. }
assert (M_m : forall off sv v, In (mkChunk off (CVal 8 sv)) (r_chunks (YP09.mkRegion (Some 40%nat) 0 40 0 40
[mkChunk 8 (CVal 8 (SOff 40 0)); mkChunk 0 (CVal 8 (SOff 40 0)); mkChunk 24 (CVal 4 (SAlu ALU_ADD (SExt true 32 AVAIL0) (SLit (-1)))); mkChunk 32 (CVal 8 BITS); mkChunk 16 (CVal 8 (SOff 86 0));
mkChunk 28 (CVal 4 (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff 82 (-1))) (SAlu ALU_XOR (SExt true 32 AVAIL0) (SLit (-1)))))])) ->
sv_denot E9 sv = Z_to_bv 64 v -> word_mem src0segs mem5 (ptr_addr L1 m + off) v).
{ intros off sv v Hin Hv. rewrite <- U40'. exact (word_of_chunk_at E9 ss_kE ms5 4 _ 40 off sv v HS R4 eq_refl Hin Hv). }
assert (M_m0 : word_mem src0segs mem5 (ptr_addr L1 m + 0) (ptr_addr L1 m)) by (apply (M_m 0 (SOff 40 0)); [inlist | exact (den_off0 E9 40 _ E9_40)]).
assert (M_m8 : word_mem src0segs mem5 (ptr_addr L1 m + 8) (ptr_addr L1 m)) by (apply (M_m 8 (SOff 40 0)); [inlist | exact (den_off0 E9 40 _ E9_40)]).
assert (M_m16 : word_mem src0segs mem5 (ptr_addr L1 m + 16) ua) by (apply (M_m 16 (SOff 86 0)); [inlist | apply den_off0; rewrite E9_86; symmetry; apply Z_to_bv_bv_unsigned]).
assert (M_m32 : word_mem src0segs mem5 (ptr_addr L1 m + 32) (meta_bits am1)).
{ apply (M_m 32 BITS); [inlist|]. rewrite (bits_val E9 sc cnt len E9_10 E9_82 E9_81 Hsc C1 Hl Hlm). unfold meta_bits. rewrite Glast, Gsc, Gml. f_equal. }
assert (M_m24 : forall k, (k < 4)%nat -> mbyte src0segs mem5 (ptr_addr L1 m + 24 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ones aidx - 1) 4 k))).
{ intros k Hk. rewrite <- U40'. apply (chunk_bytes_cval src0segs E9 mem5 _ 24 4 _ _ (st_ok_chunk src0segs E9 ss_kE ms5 4 _ _ HS R4 ltac:(right; right; left; reflexivity))); [| exact Hk].
exact (avail_lo32 E9 aidx E9_90 ltac:(lia)). }
assert (M_m28 : forall k, (k < 4)%nat -> mbyte src0segs mem5 (ptr_addr L1 m + 28 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ones (cnt - 1) - ones aidx) 4 k))).
{ intros k Hk. rewrite <- U40'. apply (chunk_bytes_cval src0segs E9 mem5 _ 28 4 _ _ (st_ok_chunk src0segs E9 ss_kE ms5 4 _ _ HS R4 ltac:(right; right; right; right; right; left; reflexivity))); [| exact Hk].
exact (freed_lo32 E9 aidx cnt E9_90 E9_82 ltac:(lia) C1). }
assert (AREA_OFF : forall ar x, In ar (st_areas s3) -> ptr_addr L1 ar <= x < ptr_addr L1 ar + PGSZ -> ~ (ptr_addr L1 m <= x < ptr_addr L1 m + 40) -> ~ Wall x).
{ intros ar x Har Hx Hm. pose proof (inv_areas I3) as (_ & Hareas & _). destruct (Hareas ar Har) as (r & o & rg & Ear & Ho & Hlo & Hr & Hlv & Hlen & _).
apply (old_region_off r rg x Hr Hlv); [| exact Hm]. rewrite Ear in Hx. unfold ptr_addr in Hx. cbn [loc_addr] in Hx. pose proof (reg_lo_le rg). lia. }
assert (MSLOT_NONMAP : forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> in_nonmap_region L1 s3 x).
{ intros x Hx. assert (Hpg : ptr_addr L1 arm <= x < ptr_addr L1 arm + PGSZ) by (rewrite Eqm in Hx; unfold slot_of in Hx; rewrite ptr_addr_padd in Hx; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia).
apply (area_nonmap B (m :: X) None U L1 s3 mem3 md1 I3 HM3 s3 L1 arm x Harm Hpg); [intros k rg Hk Hlv Hkd; exists rg; repeat split; try assumption; lia | intros k rg Hk _ _; exact Hk | intros; reflexivity]. }
assert (MAP_OFF : forall k rg x, region_of s3 k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> ly_reg L1 k <= x < ly_reg L1 k + rg_len rg -> ~ Wall x).
{ intros k rg x Hk Hkd Hlv Hx. apply (old_region_off k rg x Hk Hlv); [unfold reg_lo; rewrite Hkd; lia|].
intros Hm. destruct (MSLOT_NONMAP x Hm) as [_ NM]. apply NM. exists k, rg. auto. }
assert (CTX_OFF : forall x, CTX <= x < CTX + CTX_SIZE -> ~ (CTX + CTX_mmap_counter <= x < CTX + CTX_mmap_counter + 4) -> ~ (CTX + CTX_active + 8 * sc <= x < CTX + CTX_active + 8 * sc + 8) ->
~ (CTX + CTX_usage + 8 * sc <= x < CTX + CTX_usage + 8 * sc + 8) -> ~ Wall x).
{ intros x Hx N1 N2 N3 HW. destruct (Wall_cases x HW) as [Hw|[Hw|[Hw|[_ Hw]]]].
- pose proof (so_ctx_hi _ SO). change (ms_ctx B) with CTX in H. unfold WS, ASF in *. lia.
- destruct (Pf x Hw) as [NI _]. apply NI. apply (so_ctx_img _ SO). exact Hx.
- destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 x Hw) as [NI _]. apply NI. apply (so_ctx_img _ SO). exact Hx.
- destruct Hw as [Hw|[Hw|Hw]]; [exact (N1 Hw) | exact (N2 Hw) | exact (N3 Hw)]. }
assert (XFER : forall c, In c (image s3) \/ In c (tail_cells s3) -> (forall j, (j < mc_w c)%nat -> ~ Wall (loc_addr L1 (mc_loc c) + Z.of_nat j) /\ 0 <= loc_addr L1 (mc_loc c) + Z.of_nat j < 2 ^ 64) ->
cell_mem B L2 mem5 c).
{ intros c Hc Hoff. apply (cell_mem_L' B L1 L2 s3 ltac:(rewrite LC; symmetry; exact (mid_ctx _ _ _ _ _ HM3)) LS (fun r Hr => Lset_lt L1 s3 ua r Hr) mem5 c (PB c Hc)).
apply (YN2d.cell_mem_ext B L1 mem3 mem5 c).
- intros j Hj. destruct (Hoff j Hj) as [HW Hx]. exact (OLD _ Hx HW).
- destruct Hc as [Hc|Hc]; [exact (memrep_cell B L1 s3 mem3 c MR3 Hc) | exact (memrep_tail B L1 s3 mem3 c MR3 Hc)]. }
assert (MT5 : forall q, MT s5 q = MT (upd_meta m (MUsed am1) s3) q).
{ intros q. unfold s5. rewrite (inst_MT sc m cnt len s3 q), MT_upd. fold aidx. change (length (st_regions s3)) with Nr. fold am1. reflexivity. }
assert (IMG : forall c, In c (image s5) -> cell_mem B L2 mem5 c).
{ intros c Hc. unfold image in Hc. rewrite !in_app_iff in Hc. destruct Hc as [Hc|[Hc|Hc]].
-
destruct (ctx_cells_s5 c Hc) as [-> | [-> | [-> | (Hold & off & Hloc & Hoff & A1' & A2' & A3')]]].
+ unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num loc_addr]. rewrite LC. change (ms_segs B) with src0segs. intros k Hk.
replace (CTX + CTX_mmap_counter) with (LOCK + 20) by (unfold CTX_mmap_counter; lits; lia). exact (M_ctr k Hk).
+ unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num loc_addr]. rewrite LC. change (ms_segs B) with src0segs.
replace (CTX + (CTX_usage + 8 * sc)) with (csn 33 + 472) by (cbn [cs]; unfold CTX_usage; lits; lia). exact M_use.
+ unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. change (loc_addr L2 (LMem m)) with (ptr_addr L2 m). cbn [loc_addr]. rewrite LC. change (ms_segs B) with src0segs. rewrite (L2_old m PRm).
replace (CTX + (CTX_active + 8 * sc)) with (csn 33 + 88) by (cbn [cs]; unfold CTX_active; lits; lia). exact M_act.
+ apply XFER; [left; unfold image; rewrite !in_app_iff; left; exact Hold|]. intros j Hj. rewrite Hloc. cbn [loc_addr]. rewrite (mid_ctx _ _ _ _ _ HM3). change (ms_ctx B) with CTX.
destruct (In_ctx_cells s3 c Hold) as (off' & Hloc' & _ & Hsz). rewrite Hloc in Hloc'. injection Hloc' as <-. pose proof (so_ctx_hi _ SO) as CH. change (ms_ctx B) with CTX in CH.
split; [| unfold CTX_SIZE in *; lits; lia]. apply CTX_OFF; unfold CTX_SIZE in *; lia.
-
rewrite Far in Hc. rewrite (areas_cells_MT_ext (upd_meta m (MUsed am1) s3) s5 (st_areas s3) MT5) in Hc.
destruct (areas_cells_upd_sharp s3 m (MUsed am1) (st_areas s3) c Hc) as [Hnew | (Hold & ar & d & Har & Hloc & Hd & Hdw & Hapart)].
+ cbn [meta_slot_cells optr] in Hnew. rewrite Gpr, Gnx, Gmem in Hnew. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hnew.
assert (LOCm : forall off, loc_addr L2 (LMem (padd m off)) = ptr_addr L1 m + off) by (intros off; change (loc_addr L2 (LMem (padd m off))) with (ptr_addr L2 (padd m off)); rewrite ptr_addr_padd, (L2_old m PRm); reflexivity).
destruct Hnew as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num optr]; rewrite LOCm; change (ms_segs B) with src0segs.
* change (loc_addr L2 (LMem m)) with (ptr_addr L2 m). rewrite (L2_old m PRm). exact M_m0.
* change (loc_addr L2 (LMem m)) with (ptr_addr L2 m). rewrite (L2_old m PRm). exact M_m8.
* change (loc_addr L2 (LMem (SP Nr 0))) with (ptr_addr L2 (SP Nr 0)). rewrite L2_new, Z.add_0_r. exact M_m16.
* exact M_m24.
* exact M_m28.
* exact M_m32.
+ apply XFER; [left; unfold image; rewrite !in_app_iff; right; left; rewrite Ar3 in Hold |- *; exact Hold|].
intros j Hj. rewrite Hloc. change (loc_addr L1 (LMem (padd ar d))) with (ptr_addr L1 (padd ar d)). rewrite ptr_addr_padd.
destruct (areas_off_img B (m :: X) None U L1 s3 mem3 md1 I3 HM3 ar (ptr_addr L1 ar + d + Z.of_nat j) Har ltac:(lia)) as [NI Rx].
split; [| lia]. apply (AREA_OFF ar); [exact Har | lia |].
intros Hm. destruct (sptr_eq_dec ar arm) as [->|Hne].
* destruct (Hapart km Hkm ltac:(symmetry; exact Eqm)); rewrite Eqm in Hm; unfold slot_of in Hm; rewrite ptr_addr_padd in Hm; unfold AREA_HDR, META_SIZE in *; lia.
* destruct (areas_pages_disjoint B L1 s3 mem3 md1 HM3 ar arm Har Harm Hne);
rewrite Eqm in Hm; unfold slot_of in Hm; rewrite ptr_addr_padd in Hm; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia.
-
apply in_flat_map in Hc as ([g' am'] & Hgm & Hc). cbn [fst snd] in Hc. apply UM5 in Hgm as [Hgm | Hgm].
+ injection Hgm as -> ->. apply GC5 in Hc as [-> | [-> | (i & Hi & Hc)]].
* unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. change (loc_addr L2 (LMem (SP Nr 0))) with (ptr_addr L2 (SP Nr 0)). change (loc_addr L2 (LMem m)) with (ptr_addr L2 m). rewrite L2_new, (L2_old m PRm), Z.add_0_r. change (ms_segs B) with src0segs. exact M_ghdr.
* unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. change (loc_addr L2 (LMem (padd (SP Nr 0) 8))) with (ptr_addr L2 (padd (SP Nr 0) 8)). rewrite ptr_addr_padd, L2_new, Z.add_0_r. change (ms_segs B) with src0segs. exact M_gaidx.
* assert (ST : forall d, loc_addr L2 (LMem (padd (slot_start am1 i) d)) = ua + UNIT + stride_of am1 * i + d).
{ intros d. unfold slot_start. rewrite Gmem, !padd_padd'. cbn [padd loc_addr]. unfold L2, Nr. rewrite (Lset_new L1 s3 ua). lia. }
assert (ZB : forall x, ua + 12 <= x < ua + len -> mbyte src0segs mem5 x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct (Z_lt_le_dec x (ua + 16)); [apply GZ; lia | apply ZMAPb; lia]).
assert (Hsi : 0 <= stride_of am1 * i <= stride_of am1 * (cnt - 1)) by nia.
cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num]; rewrite ST; change (ms_segs B) with src0segs; intros k Hk;
rewrite YN03.le_byte_0; apply ZB; unfold UNIT in *; nia.
+ pose proof (proj1 (used_metas_usedX' (m :: X) None U s3 I3 X3 g' am') Hgm) as HU'.
destruct (used_group_region (m :: X) None U s3 g' am' I3 HU') as (rg & Hrg & Hkd & Hlv & Hpo & Hext & _).
destruct (In_group_cells (m :: X) None U s3 g' am' c I3 HU' Hc) as (d & Hloc & Hd & Hdw).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM3) _ rg Hrg Hlv) as (_ & Plo & Phi & _).
apply XFER; [left; unfold image; rewrite !in_app_iff; right; right; apply in_flat_map; exists (g', am'); split; [exact Hgm | exact Hc]|].
intros j Hj. rewrite Hloc. destruct (am_mem am') as [k o] eqn:Emem. cbn [loc_addr prid poff padd] in *.
split; [| lia]. apply (MAP_OFF k rg); [exact Hrg | exact Hkd | exact Hlv | lia]. }
assert (TAIL : forall c, In c (tail_cells s5) -> cell_mem B L2 mem5 c).
{ intros c Hc. apply TC5 in Hc as [Hc | ->].
- destruct (tail_cell_region (m :: X) None U s3 I3 X3 c Hc) as (p & rg & Hloc & Hrg & Hkd & Hlv & Hpo & Hpw).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM3) _ rg Hrg Hlv) as (_ & Plo & Phi & _).
apply XFER; [right; exact Hc|]. intros j Hj. rewrite Hloc. destruct p as [k o]. cbn [loc_addr prid poff padd] in *.
split; [| lia]. apply (MAP_OFF k rg); [exact Hrg | exact Hkd | exact Hlv | lia].
- unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. change (loc_addr L2 (LMem (padd (SP Nr 0) (group_extent am1)))) with (ptr_addr L2 (padd (SP Nr 0) (group_extent am1))).
rewrite ptr_addr_padd, L2_new. change (ms_segs B) with src0segs. intros k Hk. rewrite YN03.le_byte_0. apply ZMAPb. unfold group_extent. rewrite Glast. unfold UNIT, IB in *. nia. }
assert (PRES5 : forall x, 0 <= x < 2 ^ 64 -> ~ in_img B x -> x < alloc_ceiling -> ~ (ua <= x < ua + len) -> present mem3 x -> present mem5 x).
{ intros x Hx NI Rx Nua Hp. destruct (Z_lt_le_dec x (ptr_addr L1 m)) as [H1|H1]; [| destruct (Z_lt_le_dec x (ptr_addr L1 m + 40)) as [H2|H2]].
2:{ apply (writable_off_img_present mem5 x Hx ltac:(intros Hi; exact (NI (in_img1_img x Hi)))). apply (writable_of_region regs E9 ss_kE ms5 4 _ x HS R4). cbn [r_base r_wlo r_whi base_val]. rewrite U40'. lia. }
all: destruct Hp as [b Hb]; exists b; rewrite <- Hb; apply OLD; [exact Hx|]; intros HW; destruct (Wall_cases x HW) as [Hw|[Hw|[Hw|[Hcx _]]]];
[unfold WS, ASF in *; lia | exact (Nua Hw) | lia | apply NI; apply (so_ctx_img _ SO); exact Hcx]. }
assert (FOOT : Forall (foot_ok L2 mem5) (footprint s5)).
{ rewrite FP5. apply Forall_app. split.
- apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 MR3)) e He) as FO.
destruct (In_footprint_inv s3 e He) as [-> | [(ar & Har & ->) | (k & rg & Hrg & Hkd & Hlv & ->)]]; cbn [foot_ok fst snd] in FO |- *; [exact I | |].
+ change (loc_addr L2 (LMem ar)) with (ptr_addr L2 ar). change (loc_addr L1 (LMem ar)) with (ptr_addr L1 ar) in FO.
pose proof (inv_areas I3) as (_ & Hareas & _). destruct (Hareas ar Har) as (r & o & rg & Ear & Ho & Hlo & Hr & Hlv & Hlen & _).
rewrite (L2_old ar ltac:(rewrite Ear; cbn; exact (region_of_lt _ _ _ Hr))). intros x Hx.
destruct (areas_off_img B (m :: X) None U L1 s3 mem3 md1 I3 HM3 ar x Har Hx) as [NI Rx].
apply PRES5; [lia | exact NI | lia | | exact (FO x Hx)].
apply (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM3) a len ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF r rg x Hr Hlv).
rewrite Ear in Hx. unfold ptr_addr in Hx. cbn [loc_addr] in Hx. pose proof (reg_lo_le rg). lia.
+ cbn [loc_addr] in FO |- *. unfold L2. rewrite (Lset_lt L1 s3 ua k (region_of_lt _ _ _ Hrg)). intros x Hx.
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ HM3) _ rg Hrg Hlv) as (_ & Plo & Phi & Pimg).
apply PRES5; [lia | apply Pimg; lia | lia | | exact (FO x Hx)].
apply (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM3) a len ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF k rg x Hrg Hlv). unfold reg_lo. rewrite Hkd. lia.
- apply Forall_cons; [| apply Forall_nil]. cbn [foot_ok fst snd]. change (loc_addr L2 (LMem (SP Nr 0))) with (ptr_addr L2 (SP Nr 0)). rewrite L2_new, Z.add_0_r.
intros x Hx. destruct (Z_lt_le_dec x (ua + 16)).
+ destruct (Pf x Hx) as [NI Rx]. apply (writable_off_img_present mem5 x ltac:(lia) ltac:(intros Hi; exact (NI (in_img1_img x Hi)))).
apply (writable_of_region regs E9 ss_kE ms5 3 _ x HS R3'). cbn [r_base r_wlo r_whi base_val]. rewrite U86. lia.
+ exists (Z_to_bv 8 0). apply ZMAP. lia. }
assert (NN : forall k rg, region_of s3 k = Some rg -> 0 <= rg_len rg) by (exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas I3)))))))))).
destruct (ledger_new_map L1 s3 md1 (mid_ledger _ _ _ _ _ HM3) (mid_ledgerx _ _ _ _ _ HM3) NN (mid_md _ _ _ _ _ HM3) s5 a len ltac:(lia) ltac:(unfold PGSZ; exact Hlm) GR Fr Fb) as [LG5 LX5].
{ intros r p Hb. pose proof (inv_areas I3) as (_ & _ & _ & _ & _ & _ & HBk & _). rewrite Hb in HBk. destruct HBk as (_ & rg & Hrg & _). exact (region_of_lt _ _ _ Hrg). }
change (Lset L1 s3 (bv_unsigned a)) with L2 in LG5, LX5. change (mmap_model a (Z_to_bv 64 len) md1) with md2 in LG5, LX5.
split.
- exact SO.
- split; [apply Forall_forall; exact IMG | split; [apply Forall_forall; exact TAIL | exact FOOT]].
-
apply Forall_forall. intros c Hc k Hk.
assert (UBm : forall x, in_user_block L2 s5 x -> in_user_block L1 s3 x /\ ~ (ua <= x < ua + len)).
{ intros x ([bp bn] & Hb & Hbx). rewrite UB5 in Hb. cbn [fst snd] in Hbx.
destruct (user_block_in_map (m :: X) U s3 L2 bp bn x I3 X3 Hb Hbx) as (kk & rg & Hrg & Hkd & Hlv & Hkx).
pose proof (region_of_lt _ _ _ Hrg) as Hlt. unfold L2 in Hkx. rewrite (Lset_lt L1 s3 ua kk Hlt) in Hkx.
split.
- exists (bp, bn). split; [exact Hb|]. cbn [fst snd]. change (loc_addr L2 (LMem bp)) with (ptr_addr L2 bp) in Hbx. change (loc_addr L1 (LMem bp)) with (ptr_addr L1 bp).
rewrite <- (L2_old bp); [exact Hbx|]. unfold user_blocks in Hb. apply in_flat_map in Hb as ([g' am'] & Hgm & Hb). cbn [snd] in Hb. apply in_flat_map in Hb as (i & Hi & Hb).
destruct (ss_fr (nth_slot am' i)) as [fr|]; [| destruct Hb]. destruct (fr_kind fr); [| destruct Hb]. destruct Hb as [Hb|[]]. injection Hb as E1 E2. rewrite <- E1.
unfold slot_start. rewrite !padd_padd'. destruct (am_mem am') as [k' o'] eqn:Em'. cbn [padd prid].
pose proof (used_group_prid_lt (m :: X) None U s3 g' am' I3 (proj1 (used_metas_usedX' (m :: X) None U s3 I3 X3 g' am') Hgm)) as PL. rewrite Em' in PL. exact PL.
- apply (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM3) a len ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF kk rg x Hrg Hlv). unfold reg_lo. rewrite Hkd. lia. }
apply TC5 in Hc as [Hc | ->].
+ pose proof (proj1 (Forall_forall _ _) (mid_tailg _ _ _ _ _ HM3) c Hc k Hk) as [[e [He Hex]] NUB].
assert (EL : loc_addr L2 (mc_loc c) = loc_addr L1 (mc_loc c)).
{ destruct (PB c (or_intror Hc)) as [Hpl _]. destruct (mc_loc c) as [o|p]; [cbn [loc_addr]; rewrite LC, (mid_ctx _ _ _ _ _ HM3); reflexivity|].
change (ptr_addr L2 p = ptr_addr L1 p). apply L2_old. exact Hpl. }
rewrite EL. split.
* exists e. split; [rewrite FP5; apply in_app_iff; left; exact He|].
destruct (In_footprint_inv s3 e He) as [-> | [(ar & Har & ->) | (kk & rg & Hrg & Hkd & Hlv & ->)]]; cbn [fst snd] in Hex |- *.
-- cbn [loc_addr] in Hex |- *. rewrite LC. rewrite (mid_ctx _ _ _ _ _ HM3) in Hex. exact Hex.
-- change (loc_addr L2 (LMem ar)) with (ptr_addr L2 ar). pose proof (inv_areas I3) as (_ & Hareas & _). destruct (Hareas ar Har) as (r & o & rg & Ear & _ & _ & Hr & _).
rewrite (L2_old ar ltac:(rewrite Ear; cbn; exact (region_of_lt _ _ _ Hr))). exact Hex.
-- cbn [loc_addr] in Hex |- *. unfold L2. rewrite (Lset_lt L1 s3 ua kk (region_of_lt _ _ _ Hrg)). exact Hex.
* intros HU5. exact (NUB (proj1 (UBm _ HU5))).
+ cbn [mc_loc mc_w] in Hk |- *. change (loc_addr L2 (LMem (padd (SP Nr 0) (group_extent am1)))) with (ptr_addr L2 (padd (SP Nr 0) (group_extent am1))). rewrite ptr_addr_padd, L2_new.
assert (Hge : 16 <= group_extent am1 < len) by (unfold group_extent; rewrite Glast; unfold UNIT, IB in *; nia).
split.
* exists (LMem (SP Nr 0), len). split; [rewrite FP5; apply in_app_iff; right; left; reflexivity|]. cbn [fst snd]. change (loc_addr L2 (LMem (SP Nr 0))) with (ptr_addr L2 (SP Nr 0)). rewrite L2_new. lia.
* intros HU5. destruct (UBm _ HU5) as [_ Nua]. apply Nua. lia.
-
apply (YN2d.statics_ok_ext B s3 0 mem3); [| exact (mid_statics _ _ _ _ _ HM3)]. intros x Hx.
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)) as Hhi. apply OLD; [lia|]. intros HW.
destruct (Wall_cases x HW) as [Hw|[Hw|[Hw|[Hcx _]]]]; [unfold WS, ASF in *; lia | destruct (Pf x Hw) as [NI _]; exact (NI (so_statics_img _ SO x Hx)) | destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 x Hw) as [NI _]; exact (NI (so_statics_img _ SO x Hx)) | exact (src0_SNC x Hx Hcx)].
- exact LG5.
- exact LX5.
-
destruct (mid_layout _ _ _ _ _ HM3) as (Y1 & Y2 & Y3 & Y4).
assert (CR : forall e, In e (footprint s3) -> crange L2 e = crange L1 e /\ (forall x, fst (crange L1 e) <= x < fst (crange L1 e) + snd (crange L1 e) -> ~ (ua <= x < ua + len))).
{ intros e He. unfold crange. destruct (In_footprint_inv s3 e He) as [-> | [(ar & Har & ->) | (kk & rg & Hrg & Hkd & Hlv & ->)]]; cbn [fst snd].
- cbn [loc_addr]. rewrite LC, (mid_ctx _ _ _ _ _ HM3). change (ms_ctx B) with CTX. split; [reflexivity|]. intros x Hx Hua. destruct (Pf x Hua) as [NI _]. apply NI. apply (so_ctx_img _ SO). exact Hx.
- change (loc_addr L2 (LMem ar)) with (ptr_addr L2 ar). change (loc_addr L1 (LMem ar)) with (ptr_addr L1 ar).
pose proof (inv_areas I3) as (_ & Hareas & _). destruct (Hareas ar Har) as (r & o & rg & Ear & Ho & Hlo & Hr & Hlv & Hlen & _).
rewrite (L2_old ar ltac:(rewrite Ear; cbn; exact (region_of_lt _ _ _ Hr))). split; [reflexivity|]. intros x Hx.
apply (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM3) a len ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF r rg x Hr Hlv).
rewrite Ear in Hx. unfold ptr_addr in Hx. cbn [loc_addr] in Hx. pose proof (reg_lo_le rg). lia.
- cbn [loc_addr]. unfold L2 at 1. rewrite (Lset_lt L1 s3 ua kk (region_of_lt _ _ _ Hrg)). split; [reflexivity|]. intros x Hx.
apply (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM3) a len ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF kk rg x Hrg Hlv). unfold reg_lo. rewrite Hkd. lia. }
assert (MC : map (crange L2) (footprint s3) = map (crange L1) (footprint s3)) by (apply map_ext_in; intros e He; exact (proj1 (CR e He))).
split; [rewrite LC; rewrite (mid_ctx _ _ _ _ _ HM3) in Y1; exact Y1|]. split.
{ intros k rg Hk Hlv. unfold s5 in Hk. rewrite (inst_region_of sc m cnt len s3 k) in Hk. unfold L2. destruct (Nat.ltb_spec k (length (st_regions s3))).
- rewrite (Lset_lt L1 s3 ua k H). exact (Y2 k rg Hk Hlv).
- destruct (Nat.eqb_spec k (length (st_regions s3))); [| discriminate]. subst k. rewrite (Lset_new L1 s3 ua). unfold PGSZ. exact Hal. }
split.
{ rewrite FP5, map_app, MC. cbn [map]. apply pairwise_snoc; [exact Y3|]. intros y Hy. apply in_map_iff in Hy as (e & <- & He). destruct (CR e He) as [_ Hfr].
unfold ranges_disjoint, crange. cbn [fst snd]. change (loc_addr L2 (LMem (SP Nr 0))) with (ptr_addr L2 (SP Nr 0)). rewrite L2_new, Z.add_0_r.
unfold crange in Hfr. cbn [fst snd] in Hfr.
destruct (Z_le_dec (loc_addr L1 (fst e) + snd e) ua) as [|N1]; [left; lia|]. right. destruct (Z_le_dec (ua + len) (loc_addr L1 (fst e))) as [|N2]; [lia|]. exfalso.
destruct (Z_lt_le_dec (loc_addr L1 (fst e)) ua); [apply (Hfr ua); lia | apply (Hfr (loc_addr L1 (fst e))); [| lia]].
pose proof (proj1 (Y4 e He)). unfold crange in H. cbn [fst snd] in H.
assert (0 < snd e); [| lia]. destruct (In_footprint_inv s3 e He) as [-> | [(ar & Har & ->) | (kk & rg & Hrg & Hkd & Hlv & ->)]]; cbn [snd]; [unfold CTX_SIZE; lia | unfold PGSZ; lia |].
pose proof (lg_maps _ _ _ _ (mid_ledger _ _ _ _ _ HM3) kk rg Hrg Hlv ltac:(rewrite Hkd; discriminate)) as Hin2.
destruct (lx_maps _ _ _ (mid_ledgerx _ _ _ _ _ HM3) _ Hin2) as [Pl _]. unfold iv_len in Pl. cbn [snd] in Pl. unfold w64 in Pl.
destruct (Z_lt_le_dec 0 (rg_len rg)); [lia|]. pose proof (NN kk rg Hrg). assert (E0 : rg_len rg = 0) by lia. rewrite E0 in Pl. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Pl. lia. }
intros e He. rewrite FP5 in He. apply in_app_iff in He as [He | [<- | []]].
{ rewrite (proj1 (CR e He)). exact (Y4 e He). }
unfold crange. cbn [fst snd]. change (loc_addr L2 (LMem (SP Nr 0))) with (ptr_addr L2 (SP Nr 0)). rewrite L2_new. lia.
- exact LC.
- rewrite LS. exact (mid_sec _ _ _ _ _ HM3).
- destruct md2_facts as (Mh2 & Mlz2 & Mmat2 & _). exact (conj Mh2 (conj Mlz2 Mmat2)).
Qed.
Theorem leaf_inst : forall ms0, st_ok src0segs E7 ss_Kg ms0 -> ms_mem ms0 = mm0 ->
mreal src0segs (mkCfg ms0 md2) (ibind (mm_granted sc m cnt len s3) KS) POSTn.
Proof.
intros ms0 HS0 Hmm0. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
assert (Esp : sp = bv_unsigned (getr regs 2)) by reflexivity. assert (EASF : ASF = 384) by reflexivity.
destruct s3_factsF as (I3 & X3 & A3 & K3 & M3 & B3 & R3 & Ar3 & Ac3 & U3).
pose proof grantF as (PR & Hal & Ha4 & Hce & RF & Pf & C1 & Hl & Hlm). pose proof ctrF as (Hctr & LA & LU). pose proof stride1 as (ST1 & ST2 & ST3 & ST4).
pose proof am1_fields as (Gmem & Glast & Gpr & Gnx & Gsc & Gml & Gai & Gav & Gfr & Gml0).
pose proof inst_lists as ((u1 & u2 & U35 & U5) & FR5 & UB5 & FP5 & TC5 & GC5 & UM5).
pose proof (inst_fields sc m cnt len s3) as (Fm & Fr & Far & Fb & Fac & Fu & Fmc & Fid & Ffh & Fam & Famc & Faac & Fsh & Fah & Fat & Fama & Fuq & Fbn & Fsq).
change (inst_st sc m cnt len s3) with s5 in Fm, Fr, Far, Fb, Fac, Fu, Fmc, Fid, Ffh, Fam, Famc, Faac, Fsh, Fah, Fat, Fama, Fuq, Fbn, Fsq.
destruct (hd_none ms0 HS0) as [Hhd C34]. destruct md2_facts as (Mh2 & Mlz2 & Mmat2 & VM2). destruct E6_factsF as (_ & _ & _ & U40 & _).
assert (Km3 : In m (keys s3)) by (rewrite K3; exact Km). destruct (key_prid m Km3) as (PRm & arm & km & Harm & Hkm & Eqm & _).
rewrite (mm_granted_eq sc m cnt len s3 Hhd ltac:(exact Hlm)). cbn [ibind KS fst snd mreal]. change (inst_st sc m cnt len s3) with s5.
eapply SR_bind; [exact (reach_kE ms0 HS0 Hmm0)|].
intros c (E9 & ms5 & -> & HS & AG9 & E9_40 & E9_86 & E9_89 & E9_90 & E9_56 & E9_81 & E9_82 & E9_10 & F5).
pose proof (midrep_s5 E9 ms5 HS AG9 E9_40 E9_86 E9_89 E9_90 E9_56 E9_81 E9_82 E9_10 F5) as MID5.
destruct kE_regions as (R0 & R1 & R2 & R3' & R4 & (rstk & R5 & Hb5 & Hlo5 & Hhi5) & CK & RG7).
destruct (finalS L A regs mem sc stk PRE g j1 j2 E9 ss_kE ms5 (SLit 0) CK HS AG9) as (PRS & E1 & Hra & Hpc & Hrv & RA0).
apply (SR_final_retS E9 ss_kE ms5 md2 _ HS Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh2 | exact Mlz2 |].
assert (OLD : forall x, 0 <= x < 2 ^ 64 -> ~ Wall x -> ms_mem ms5 (Z_to_bv 64 x) = mem3 (Z_to_bv 64 x)) by (exact (mem5_old (ms_mem ms5) F5)).
assert (NEW_OWNED : forall x, ua <= x < ua + len -> owned B L2 s5 x).
{ intros x Hx. left. split.
- exists (LMem (SP Nr 0), len). split; [rewrite FP5; apply in_app_iff; right; left; reflexivity|]. cbn [fst snd]. change (loc_addr L2 (LMem (SP Nr 0))) with (ptr_addr L2 (SP Nr 0)). rewrite L2_new. lia.
- intros ([bp bn] & Hb & Hbx). rewrite UB5 in Hb. cbn [fst snd] in Hbx.
destruct (user_block_in_map (m :: X) U s3 L2 bp bn x I3 X3 Hb Hbx) as (kk & rg & Hrg & Hkd & Hlv & Hkx).
unfold L2 in Hkx. rewrite (Lset_lt L1 s3 ua kk (region_of_lt _ _ _ Hrg)) in Hkx.
apply (fresh_region L1 s3 md1 (mid_ledgerx _ _ _ _ _ HM3) a len ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF kk rg x Hrg Hlv); [unfold reg_lo; rewrite Hkd; lia | unfold ua in Hx; exact Hx]. }
assert (MSLOT_NONMAP5 : forall x, ptr_addr L1 m <= x < ptr_addr L1 m + 40 -> in_nonmap_region L2 s5 x).
{ intros x Hx. assert (Hpg : ptr_addr L1 arm <= x < ptr_addr L1 arm + PGSZ) by (rewrite Eqm in Hx; unfold slot_of in Hx; rewrite ptr_addr_padd in Hx; unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *; lia).
destruct (area_nonmap B (m :: X) None U L1 s3 mem3 md1 I3 HM3 s3 L1 arm x Harm Hpg ltac:(intros k rg Hk Hlv Hkd; exists rg; repeat split; try assumption; lia) ltac:(intros k rg Hk _ _; exact Hk) ltac:(intros; reflexivity))
as [(r & rg & Hr & Hlv & Hkd & Hrx) NM].
pose proof (region_of_lt _ _ _ Hr) as Hlt. split.
- exists r, rg. unfold s5. rewrite (inst_region_of sc m cnt len s3 r), (proj2 (Nat.ltb_lt _ _) Hlt). unfold L2. rewrite (Lset_lt L1 s3 ua r Hlt).
split; [exact Hr|]. split; [exact Hlv|]. split; [exact Hkd | exact Hrx].
- intros (k & rg' & Hk & Hlv' & Hkd' & Hkx). unfold s5 in Hk. rewrite (inst_region_of sc m cnt len s3 k) in Hk. unfold L2 in Hkx.
destruct (Nat.ltb_spec k (length (st_regions s3))).
+ rewrite (Lset_lt L1 s3 ua k H) in Hkx. apply NM. exists k, rg'. split; [exact Hk|]. split; [exact Hlv'|]. split; [exact Hkd' | exact Hkx].
+ destruct (Nat.eqb_spec k (length (st_regions s3))); [| discriminate]. subst k. rewrite (Lset_new L1 s3 ua) in Hkx. injection Hk as <-. cbn [rg_len] in Hkx.
exact (mslot_fresh X U L A regs sc g j1 j2 m s1 L1 md1 HI1 RX1 Mm Km AMA1 BND1 mem3 a len HM3 ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF x Hx ltac:(unfold ua in Hkx; exact Hkx)). }
exists L2, (ms_regs ms5), (ms_mem ms5), md2. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split; [exact MID5|]. split.
{   unfold ama_ok. rewrite Far, Fama, Fr, length_app. cbn [length]. intros Hne. pose proof (A3 Hne). lia. }
split.
{   pose proof B3 as (Bu & Bs & Ba). split; [| rewrite Fsh, Far; exact (conj Bs Ba)].
pose proof (usage_small (m :: X) None U s3 sc I3 B3 HU Hsc) as US. pose proof (Bu sc) as Bsc.
intros k. replace (usage_of s5 k) with (znth k (zset sc (usage_of s3 sc + cnt) (st_usage s3))) by (unfold usage_of; rewrite Fu; reflexivity).
destruct (Z_lt_le_dec k 0) as [Hk|Hk].
- unfold znth at 1 2. unfold zset. replace (Z.to_nat k) with 0%nat by lia. rewrite nth_zupd. destruct (_ && _)%bool; [lia | pose proof (Bu 0) as B0; unfold usage_of, znth in B0; exact B0].
- rewrite znth_zset by lia. destruct (_ && _); [lia | exact (Bu k)]. }
split.
{   intros g' am' i fr Hin Hk. rewrite FR5 in Hin.
exact (rsv_ok_xfer X U A regs HI XR RSV (m :: X) s3 I3 X3 ltac:(intros q am Hu; apply (proj1 (US1 q am)); unfold usedX, MTX in Hu |- *; rewrite <- M3; exact Hu) g' am' i fr Hin Hk). }
split.
{   intros g' am' Hm' Hlt. unfold s5 in Hm'. rewrite (inst_MT sc m cnt len s3 g') in Hm'.
destruct (sptr_eqb g' m) eqn:Eg.
- injection Hm' as <-. change (am_sc am1 <> 0). rewrite Gsc. apply (class_size_big_not0 sc Hsc).
pose proof (class_size_bounds sc Hsc) as [S16 _].
apply (mapped_aidx_class (class_size sc) cnt ltac:(lia) ltac:(lia)). cbv zeta. fold (aidx_of sc cnt). fold aidx. rewrite <- Gai, <- Glast. exact Hlt.
- exact (span_ok_xfer X A SPOK (m :: X) s3 X3 ltac:(intros q am Hu; apply (proj1 (US1 q am)); unfold usedX, MTX in Hu |- *; rewrite <- M3; exact Hu) g' am' Hm' Hlt). }
split.
{   destruct LE1 as (Y1 & Y2 & Y3 & Y4). unfold layout_le, L2, Lset. cbn [ly_ctx ly_sec ly_brk0 ly_reg].
split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. intros r Hr. destruct (Nat.eqb_spec r (length (st_regions s3))) as [Er|Nr']; [exfalso; rewrite R3 in Er; lia | exact (Y4 r Hr)]. }
split; [exact PRS|]. split; [exact VM2|]. split.
{   intros x Hx Nc No No' Nn Ns. unfold call_scratch, spZ in Ns. change (errno_addr B) with ERRNO in Ns. fold sp in Ns. change (ms_ctx B) with CTX in Nc.
assert (Nua : ~ (ua <= x < ua + len)) by (intros H; exact (No' (NEW_OWNED x H))).
assert (Nm : ~ (ptr_addr L1 m <= x < ptr_addr L1 m + 40)) by (intros H; exact (Nn (MSLOT_NONMAP5 x H))).
rewrite (OLD x Hx).
2:{ intros HW. destruct (Wall_cases x HW) as [Hw|[Hw|[Hw|[Hcx _]]]]; [apply Ns; left; unfold WS in Hw; lia | exact (Nua Hw) | exact (Nm Hw) | exact (Nc Hcx)]. }
rewrite (HF3 x Hx) by (first [intros Hw; apply Ns; left; unfold WS in Hw; lia | exact Nc]).
apply (FR1 x Hx); [intros Hw; apply Ns; left; unfold WS in Hw; lia | lia | exact Nc |].
assert (RO3 : forall k, region_of s3 k = region_of s1 k) by (intros k; unfold region_of; rewrite R3; reflexivity).
intros [(r & rg & Hr & Hlv & Hkd & Hrx) NM]. apply Nn. split.
- exists r, rg. unfold s5. rewrite (inst_region_of sc m cnt len s3 r), RO3. pose proof (region_of_lt _ _ _ Hr) as Hlt. rewrite <- R3 in Hlt.
rewrite (proj2 (Nat.ltb_lt _ _) Hlt). unfold L2. rewrite (Lset_lt L1 s3 ua r Hlt). split; [exact Hr|]. split; [exact Hlv|]. split; [exact Hkd | exact Hrx].
- intros (k & rg' & Hk & Hlv' & Hkd' & Hkx). unfold s5 in Hk. rewrite (inst_region_of sc m cnt len s3 k), RO3 in Hk. unfold L2 in Hkx.
destruct (Nat.ltb_spec k (length (st_regions s3))).
+ rewrite (Lset_lt L1 s3 ua k H) in Hkx. apply NM. exists k, rg'. split; [exact Hk|]. split; [exact Hlv'|]. split; [exact Hkd' | exact Hkx].
+ destruct (Nat.eqb_spec k (length (st_regions s3))); [| discriminate]. subst k. rewrite (Lset_new L1 s3 ua) in Hkx. injection Hk as <-. cbn [rg_len] in Hkx. exact (Nua Hkx). }
split.
{   intros x Hsx. unfold call_scratch, spZ in Hsx. change (errno_addr B) with ERRNO in Hsx. fold sp in Hsx. destruct Hsx as [Hsx|Hsx].
- destruct (Z_lt_le_dec x (sp - ASF)) as [Hlo|Hhi].
+ apply (writable_ext1 mem); [| apply P5; lia]. rewrite (OLD x ltac:(lia)).
2:{ intros HW. destruct (Wall_cases x HW) as [Hw|[Hw|[Hw|[Hcx _]]]]; [unfold WS in Hw; lia | lia | destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 x Hw); lia | unfold CTX_SIZE in Hcx; lits; lia]. }
rewrite (HF3 x ltac:(lia)) by (first [unfold WS; lia | unfold CTX_SIZE; lits; lia]).
apply FR1; [lia | unfold WS; lia | lits; lia | unfold CTX_SIZE; lits; lia | intros Hnm; destruct (nonmap_low regs L1 s1 mem1 md1 x MID1 Hnm); lia].
+ apply (writable_of_region regs E9 ss_kE ms5 5 rstk x HS R5). rewrite Hb5, Hlo5, Hhi5. cbn [base_val]. rewrite (agree_reg' E9 2 AG9 ltac:(lia)).
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp. lia.
- apply (writable_ext1 mem1); [| apply ERRW1; exact Hsx]. rewrite (OLD x ltac:(lits; lia)).
2:{ intros HW. destruct (Wall_cases x HW) as [Hw|[Hw|[Hw|[Hcx _]]]]; [unfold WS, ASF in *; lits; lia | destruct (Pf x Hw) as [NI _]; apply NI; apply src0_rwseg_img; lits; lia | destruct (m_range X U m s1 L1 mem1 md1 HI1 Km MID1 x Hw) as [NI _]; apply NI; apply src0_rwseg_img; lits; lia | unfold CTX_SIZE in Hcx; lits; lia]. }
apply (HF3 x ltac:(lits; lia)); [unfold WS, ASF in *; lits; lia | unfold CTX_SIZE; lits; lia]. }
split; [rewrite RA0; reflexivity|].
split.
2:{   split; [| exact (guard_of_state L A regs sc g j1 j2 E9 ss_kE ms5 7 HS AG9 RG7)].
eapply as_keep_trans; [exact AK1|].
assert (K13 : as_keep X s1 s3) by (apply as_keep_same; [intros x _ Hr; unfold rawm; rewrite M3; exact Hr | exact Ar3 | exact R3]).
eapply as_keep_trans; [exact K13|]. split; [| split].
- intros x Hx Hr. unfold rawm, s5. rewrite (inst_MT sc m cnt len s3 x).
destruct (sptr_eqb x m) eqn:Exm; [apply sptr_eqb_eq in Exm; subst x; apply (proj2 (memb_In m X)) in Hx; rewrite NXm in Hx; discriminate | exact Hr].
- intros ar Har. rewrite Far. exact Har.
- intros k rg Hrk Hrl. exists rg. unfold s5. rewrite (inst_region_of sc m cnt len s3 k). pose proof (region_of_lt _ _ _ Hrk) as Hrlt.
rewrite (proj2 (Nat.ltb_lt _ _) Hrlt). split; [exact Hrk|]. split; [exact Hrl|]. split; [tauto | lia]. }
intros _ gg am' Hgg Hmt Hstr i Hi.
assert (Egg : gg = m).
{ unfold active_hd in Hgg. rewrite Fac, nth_lupd, LA in Hgg. rewrite Nat.eqb_refl in Hgg. replace (Nat.ltb (Z.to_nat sc) 48) with true in Hgg by (symmetry; apply Nat.ltb_lt; lia). cbn in Hgg. injection Hgg as <-. reflexivity. }
subst gg. unfold s5 in Hmt. rewrite (inst_MT sc m cnt len s3 m), sptr_eqb_refl in Hmt. injection Hmt as <-. fold aidx in Hstr, Hi |- *. change (length (st_regions s3)) with Nr in Hstr, Hi |- *. fold am1 in Hstr, Hi |- *.
unfold slot_start. rewrite Gmem, Z.mul_0_r, Z.add_0_r. rewrite ptr_addr_padd, L2_new, Z.add_0_r.
unfold mbyte. rewrite (F5 (ua + UNIT + i)); [rewrite mm0_in; [reflexivity | unfold UNIT, IB in *; lia] | unfold UNIT, IB in *; lia |].
destruct (Pf (ua + UNIT + i) ltac:(unfold UNIT, IB in *; lia)) as [NI Rx].
intros [[[Hw|[Hw|Hw]]|Hw]|[Hw|Hw]]; [unfold WS, ASF, UNIT in *; lia | unfold UNIT in *; lia | | apply NI; apply src0_rwseg_img; lits; lia | cbn [cs] in Hw; apply NI; apply src0_rwseg_img; lits; lia | cbn [cs] in Hw; apply NI; apply src0_rwseg_img; lits; lia].
exact (mslot_fresh X U L A regs sc g j1 j2 m s1 L1 md1 HI1 RX1 Mm Km AMA1 BND1 mem3 a len HM3 ltac:(lia) ltac:(pose proof (u64_range a); unfold ua in Ha4; lia) ltac:(unfold ua in Hce; lia) RF _ Hw ltac:(unfold ua, UNIT, IB in *; lia)).
Qed.
End MF.
End w.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
