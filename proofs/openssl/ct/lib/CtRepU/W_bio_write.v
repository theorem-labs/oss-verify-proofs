(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push F_strlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac al8chk A := zstep; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].
Local Ltac litchk := zstep; let K := fresh "K" in first [if_false | if_cases K; zify_cond K; [exfalso; revert K; vm_compute; congruence | clear K]].
Local Ltac wrchk A := zstep; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso;
   repeat match type of K with context [Z.land ?e 7] =>
     replace (Z.land e 7) with 0 in K by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; rewrite ?unsigned_lit by lia; change (2^3) with 8; clear - A; Z.div_mod_to_equations; lia) end;
   rewrite ?unsigned_lit in K by lia;
   repeat match type of K with context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; cbn in K;
   first [discriminate K | lia | (vm_compute in K; congruence) | (match type of K with ?T => fail 100 "wrchk" T end)] | clear K].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BIO_WRITE : Z := 0x10c8e4.
Definition BIO_WRITE_INTERN : Z := 0x10c920.
Definition BIO_WRITE_EX : Z := 0x10cae8.
Definition BWRITE_CONV : Z := 0x10d5e8.
Definition NULL_WRITE : Z := 0x194348.
Definition BIO_PUTS : Z := 0x10cc54.
Definition NULL_PUTS : Z := 0x194390.
(* [comment removed for export] *)
Definition BIO_WRITE_NULL_STACK : Z := 144.
(* [comment removed for export] *)
Definition BIO_PUTS_NULL_STACK : Z := 64.

(* [comment removed for export] *)
Definition null_meth_cells (m : mem) : Prop :=
  ro_cells ctusegs m (NULL_METHOD + 16) [C8 (wz BWRITE_CONV); C8 (wz NULL_WRITE)]
  /\ ro_cells ctusegs m (NULL_METHOD + 48) [C8 (wz NULL_PUTS)].

(* [comment removed for export] *)
Lemma land_pow2_small : forall d n, 0 <= d < 2^n -> 0 <= n -> Z.land d (2^n) = 0.
Proof.
  intros d n Hd Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
  destruct (Z.eqb_spec n i); [|apply andb_false_r]. subst i.
  destruct (Z.eq_dec d 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
  rewrite (Z.bits_above_log2 d n); [reflexivity| lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma slt_mask_pos : forall d, 0 < d < 2^63 ->
  Z.land (Z.land (0 + - Z.b2z (9223372036854775808 <? Z.lxor d 9223372036854775808)) 18446744073709551615) d = d.
Proof.
  intros d Hd. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor by (apply land_pow2_small; lia).
  replace (2 ^ 63 <? d + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  change (Z.land (0 + - Z.b2z true) 18446744073709551615) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma shiftr_small_0 : forall z k, 0 <= z < 2^32 -> 32 <= k -> Z.shiftr z k = 0.
Proof.
  intros z k Hz Hk. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small.
  split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hz)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma le8_split_small : forall z, 0 <= z < 2^32 -> le8 (Z_to_bv 64 z) = le4 (Z_to_bv 64 z) ++ le4 (Z_to_bv 64 0).
Proof.
  intros z Hz. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
  rewrite (shiftr_small_0 z (8+8+8+8)), (shiftr_small_0 z (8+8+8+8+8)), (shiftr_small_0 z (8+8+8+8+8+8)), (shiftr_small_0 z (8+8+8+8+8+8+8)) by lia.
  rewrite !Z.shiftr_0_l. reflexivity.
Qed.
Lemma c8_small_as_c4 : forall m A pre z post,
  rw_cells ctusegs m A (pre ++ C8 (Z_to_bv 64 z) :: post) -> 0 <= z < 2^32 ->
  rw_cells ctusegs m A (pre ++ C4 (Z_to_bv 64 z) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros m A pre z post H Hz. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. cbn in W2. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite (le8_split_small z Hz). rewrite <- !app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BIO_write_zero_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv ctusegs m -> a2 = Z_to_bv 64 0 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch []%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_WRITE) fc None m (seg_rom ctusegs)).
Proof.
  intros until m. intros MI ->. unfold BIO_WRITE in *.
  pose proof (munch_refl []%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  zstep. if_true. zstep. zstep. finish.
Qed.

(* [comment removed for export] *)
Lemma BIO_write_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (out pv nw dlen lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_WRITE_NULL_STACK)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> obj_range out BIO_SIZE lo -> (out mod 8 = 0)%Z -> (0 <= nw < 2^64)%Z ->
  null_meth_cells m ->
  a0 = Z_to_bv 64 out -> a2 = Z_to_bv 64 dlen -> (0 < dlen < 2^31 - 1)%Z ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 dlen) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (out, out + 128)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv (nw + dlen)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_WRITE) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO SP16 HO HOLO HOAL NW (HM1 & HM2) -> -> DL.
  pose proof HOLO as HOLO'. unfold obj_range in HOLO'.
  unfold BIO_WRITE_NULL_STACK, BIO_WRITE, GLOBALS_TOP, BIO_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (out, out + 128)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPO : out + 128 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= out) by lia.
  unfold NULL_METHOD in HM1, HM2. change (2978032 + 16) with 2978048 in HM1. change (2978032 + 48) with 2978080 in HM2.
  unfold BWRITE_CONV, NULL_WRITE, NULL_PUTS, MallocRep.wz in HM1, HM2.
  assert (SEPM : 2978032 + 72 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= 2978032) by lia.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HO.
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K;
    [exfalso; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; discriminate| try clear K].
  carve_frame 32%nat ST. do 4 zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 64%nat ST. do 8 zstep. do 4 zstep.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K SPR LO GLO; lia|]. clear K. zstep. al8chk SP16.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HOAL.
  zstep. zstep. if_false. zstep. litchk. (* [comment removed for export] *)
  zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. if_false. zstep. litchk. zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 5 zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HOAL. zstep. zstep. if_false. zstep. litchk. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. zstep. do 3 zstep. release_frame FR2 ST (bv_unsigned sp + -128). zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K;
    [exfalso; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; discriminate| try clear K].
  wrchk SP16. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  do 3 zstep. zstep. release_frame FR1 ST (bv_unsigned sp + -96). zstep.
  (* [comment removed for export] *)
  zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K SPR LO GLO; lia|]. clear K. zstep. al8chk SP16.
  zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  do 6 zstep. zstep. release_frame FR0 ST (bv_unsigned sp + -32). zstep.
  (* [comment removed for export] *)
  zstep. if_false.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: C8 (Z_to_bv 64 dlen) :: ?rest) =>
    apply (c8_small_as_c4 _ _ [c0] dlen rest) in FR; [| lia] end. cbn [app] in FR.
  zstep. rewrite (sx32_small dlen) by lia. (* [comment removed for export] *)
  do 2 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma BIO_write_ex_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (out pv nw dlen WR lo : Z) (wj : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_WRITE_NULL_STACK)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> obj_range out BIO_SIZE lo -> (out mod 8 = 0)%Z -> (0 <= nw < 2^64)%Z ->
  null_meth_cells m ->
  rw_cells ctusegs m WR [CB 8%nat wj] -> (bv_unsigned sp <= WR /\ WR + 8 <= 2^64)%Z -> (WR mod 8 = 0)%Z ->
  a0 = Z_to_bv 64 out -> a2 = Z_to_bv 64 dlen -> a3 = Z_to_bv 64 WR -> (0 < dlen < 2^31 - 1)%Z ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (WR, WR + 8); (out, out + 128)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv (nw + dlen))
      /\ rw_cells ctusegs m' WR [C8 (Z_to_bv 64 dlen)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_WRITE_EX) fc None m (seg_rom ctusegs)).
Proof.
  intros until wj. intros ST MI GLO LO SP16 HO HOLO HOAL NW (HM1 & HM2) HW WRR HWAL -> -> -> DL.
  pose proof HOLO as HOLO'. unfold obj_range in HOLO'.
  unfold BIO_WRITE_NULL_STACK, BIO_WRITE_EX, GLOBALS_TOP, BIO_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (WR, WR + 8); (out, out + 128)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPO : out + 128 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= out) by lia.
  assert (SEPW : WR + 8 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= WR) by lia.
  unfold NULL_METHOD in HM1, HM2. change (2978032 + 16) with 2978048 in HM1. change (2978032 + 48) with 2978080 in HM2.
  unfold BWRITE_CONV, NULL_WRITE, NULL_PUTS, MallocRep.wz in HM1, HM2.
  assert (SEPM : 2978032 + 72 <= bv_unsigned sp - 144 \/ bv_unsigned sp <= 2978032) by lia.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HO.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 6 zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  carve_frame 64%nat ST. do 8 zstep. do 4 zstep.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K SPR LO GLO WRR; lia|]. clear K. zstep. al8chk HWAL.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HOAL.
  zstep. zstep. if_false. zstep. litchk. (* [comment removed for export] *)
  zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. if_false. zstep. litchk. zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 5 zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HOAL. zstep. zstep. if_false. zstep. litchk. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. zstep. do 3 zstep. release_frame FR2 ST (bv_unsigned sp + -128). zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K;
    [exfalso; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; discriminate| try clear K].
  wrchk SP16. zstep. zstep. zstep. zstep.
  do 3 zstep. zstep. release_frame FR1 ST (bv_unsigned sp + -96). zstep.
  (* [comment removed for export] *)
  zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; clear - K SPR LO GLO WRR; lia|]. clear K. zstep. al8chk HWAL.
  zstep. zstep. zstep. (* [comment removed for export] *)
  zstep.
  do 6 zstep. zstep. release_frame FR0 ST (bv_unsigned sp + -32). zstep.
  (* [comment removed for export] *)
  do 5 zstep. (* [comment removed for export] *)
  setreg 10%Z (Z_to_bv 64 1) ltac:(f_equal; replace (dlen <? 1) with false by (symmetry; apply Z.ltb_ge; lia); destruct (0 <? out); reflexivity).
  do 4 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma BIO_puts_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (out pv nw S lo : Z) (str slack : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_PUTS_NULL_STACK)%Z ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> obj_range out BIO_SIZE lo -> (out mod 8 = 0)%Z -> (0 <= nw < 2^64)%Z ->
  null_meth_cells m ->
  bytes_at ctusegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (65536 <= S /\ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= GLOBALS_TOP)%Z -> (0 < Z.of_nat (length str) < 2^31 - 1)%Z ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 S ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (out, out + 128)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv (nw + Z.of_nat (length str)))
      /\ bytes_at ctusegs m' S (str ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_PUTS) fc None m (seg_rom ctusegs)).
Proof.
  intros until slack. intros ST MI GLO LO HO HOLO HOAL NW (HM1 & HM2) HS NONUL PAD SR LEN -> ->.
  pose proof HOLO as HOLO'. unfold obj_range in HOLO'.
  unfold BIO_PUTS_NULL_STACK, BIO_PUTS, GLOBALS_TOP, BIO_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (out, out + 128)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPO : out + 128 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= out) by lia.
  pose proof (bytes_at_bound _ _ _ _ HS) as SB. rewrite length_app in SB. cbn [length] in SB.
  assert (SEPS : S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= S) by (rewrite length_app; cbn [length]; lia).
  assert (SEPS2 : S + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= out \/ out + 128 <= S) by (rewrite length_app; cbn [length]; lia).
  unfold NULL_METHOD in HM1, HM2. change (2978032 + 16) with 2978048 in HM1. change (2978032 + 48) with 2978080 in HM2.
  unfold BWRITE_CONV, NULL_WRITE, NULL_PUTS, MallocRep.wz in HM1, HM2.
  assert (SEPM : 2978032 + 72 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= 2978032) by lia.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HO.
  set (len := Z.of_nat (length str)) in *.
  (* [comment removed for export] *)
  carve_frame 48%nat ST. do 6 zstep. zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. al8chk HOAL. zstep. zstep. if_false. zstep. zstep. litchk. zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  zstep. if_false. zstep. zstep. if_true. (* [comment removed for export] *)
  zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. if_false. zstep. litchk. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  carve_frame 16%nat ST. do 4 zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  name_mem m1. eapply evt_cut.
  { eapply strlen_spec with (str := str) (slack := slack); [rewrite unsigned_lit by lia; exact HS| exact NONUL| rewrite unsigned_lit by lia; exact PAD| eassumption]. }
  clear HS. post_call ctusegs m1.
  match goal with H : bytes_at ctusegs _ _ _ |- _ => rename H into HS end. rewrite unsigned_lit in HS by lia.
  fold len.
  do 4 zstep. (* [comment removed for export] *)
  setreg 10%Z (Z_to_bv 64 len)
    ltac:(f_equal; rewrite (Z.shiftr_div_pow2 len 31), Z.div_small by lia; change (Z.land (Z.b2z (0 <? 1) + -1) 18446744073709551615) with 0; rewrite Z.lor_0_l; reflexivity).
  do 3 zstep. release_frame FR0 ST (bv_unsigned sp + -48). zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. rewrite (bk_swrap32_small (len + 0)) by lia. rewrite Z.add_0_r. zstep. if_cases K; zify_cond K;
    [exfalso; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; rewrite (proj2 (Z.ltb_lt _ _)) in K by lia; discriminate| try clear K].
  zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite (Z.shiftr_div_pow2 len 31), Z.div_small in K by lia; apply K; reflexivity]. try clear K.
  zstep. rewrite (bk_swrap32_small (len + 0)) by lia. rewrite Z.add_0_r. (* [comment removed for export] *)
  do 4 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.
End WithCeiling0.
