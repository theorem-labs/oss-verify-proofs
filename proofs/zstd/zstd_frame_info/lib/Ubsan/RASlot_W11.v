(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W11.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RASlot_W2.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition rsmall_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes usegs RSMALL_CNT 27 with Some bs => bs | None => [] end).
Definition rmed_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes usegs RMED_CNT 4 with Some bs => bs | None => [] end).

#[using="Type"] Lemma rsmall_cnt_ro : forall m, mem_inv usegs m -> ro_cells usegs m RSMALL_CNT [CB 27 rsmall_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RSMALL_CNT; lia | unfold RSMALL_CNT; cbn; lia]. Qed.
#[using="Type"] Lemma rmed_cnt_ro : forall m, mem_inv usegs m -> ro_cells usegs m RMED_CNT [CB 4 rmed_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RMED_CNT; lia | unfold RMED_CNT; cbn; lia]. Qed.

#[using="Type"] Lemma rsmall_cnt_read : forall m sc i, mem_inv usegs m -> 0 <= sc < 9 -> 0 <= i < 3 ->
  ov_read_bytes usegs m (wa (RSMALL_CNT + 3 * sc + i)) 1 = Some [b8 (small_cnt sc i)].
Proof.
  intros m sc i MI Hsc Hi.
  destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  Local Ltac2 Set LiaHints.tbl := fun () => "0080>11954610599.8 12561014716.8 13368604394.8 17278245107.9 36800083845.1036800083845.9 42192479848.1051227166468.8 00000500=00E00L00W00^00e00fS3HscS3Hsc2HiS3Hsc2HiS2Hi2HnS3Hsc2Hn2HkS2Hi2HkS2Hn2HkS".
replace (RSMALL_CNT + 3 * sc + i) with (RSMALL_CNT + (3 * sc + i)) by lia.
  rewrite (bytes_at_read usegs m RSMALL_CNT rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
  replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
  unfold small_cnt. rewrite !Nat2Z.id.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rmed_cnt_read : forall m i, mem_inv usegs m -> 0 <= i < 4 ->
  ov_read_bytes usegs m (wa (RMED_CNT + i)) 1 = Some [b8 (med_cnt i)].
Proof.
  intros m i MI Hi.
  destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030=10357982403.615686399655.6796775439.6  00000400800<S2HiS2HiS2Hi".
rewrite (bytes_at_read usegs m RMED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
#[using="SZ"] Lemma rhalve_big_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  0 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a2' a3',
      ms' = MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 (wz (halve_big F cnt size)) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x15478) fc None m (seg_rom usegs))
    (MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x15464) fc None m (seg_rom usegs)).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
  - cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
    step. step. Local Ltac2 Set LiaHints.tbl := fun () => "00A0>19338236499.4320191501379.432043847691.41 41351692016.4241352163945.3942661698494.4347816451760.4247822661935.4348268228076.4352592503743.395331805151.43 59314923118.4063850975006.4365106303156.4265106351149.396758062595.43 9600236033.40 00000100=00>00F00J00S00W00[00^00e00m01001501901=01>01BSS2SZ2CR2PR1KSS2CR3C32S2CRS2SZ2CR1KS2PRS2PRS1KS2SZ2CRS2CR3C32S1KS3C32S2SZS2SZSS2CR".
rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
    step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
    apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
  - cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
    assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
    step. rewrite (unsigned_lit (size * cnt)) by lia.
    step. rewrite (wz_unsigned cnt) by lia.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    + (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      rewrite (F_malloc_entry.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
      apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| exact MI].
      rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      apply evt_done. do 2 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End HALVE.
#[using="Type"] Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof.
  intros H.
  assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 1) as [->|NE].
    - change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
    - Local Ltac2 Set LiaHints.tbl := fun () => "0030=15042952629.41718820729.6 6755884809.6 000001005006SS2NES".
replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
      rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
  rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
#[using="UR"] Lemma rhalve_even_loop : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  2 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> Z.even cnt = true -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a3' a4',
      ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x15464) fc None m (seg_rom usegs))
    (MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x1543c) fc None m (seg_rom usegs)).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
  - change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>2043847691.42 24946289669.4425853701207.4327811077419.4431767182813.4432173087313.4941349968239.4441354132621.4341415987435.4541418133777.4341656453216.4948335439357.495045218403.44 5331805151.44 53817072791.4553817093936.4759308533096.406758062595.44 8471139760.47 00000100400<00@00C00G00O00W00X00Y00g01501=01E01I01M01Q01R01SSS1KS2CR3C32S2URS1KS2C2S2CR3C32S2CR3C32SSS2CR3EVm2HS2C2S2CR3C323EVm1nS2CR3C32S2CR3C32S2CRS2CRS2CRSS".
lia.
  - cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
    assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
    + (* [comment removed for export] *)
      replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
      step. apply evt_done. do 2 eexists. reflexivity.
    + replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned cnt) by lia. rewrite (F_malloc_entry.srliw_small cnt 1) by lia.
      step. rewrite (wz_unsigned cnt) by lia. step.
      assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * (* [comment removed for export] *)
        assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
        assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
        { rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]. }
        change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
        apply IH; [rewrite HS in C2 |- *; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia| lia| exact EV2| exact MI].
      * (* [comment removed for export] *)
        step.
        assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
        replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
        apply evt_done. do 2 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="UR"] Lemma rhalve_even_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  1 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists a3' a4',
      ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x15464) fc None m (seg_rom usegs))
    (MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x15434) fc None m (seg_rom usegs)).
Proof.
  intros until m; intros CR C32 MI; unfold rcnt_regs.
  (* [comment removed for export] *)
  step. Local Ltac2 Set LiaHints.tbl := fun () => "0040>39049578461.4341352163945.4052520436111.4158940969005.4300000500=00>00FS3C32S2CR3C32SS2CR3NE1".
rewrite (wz_unsigned cnt) by lia.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
  - (* [comment removed for export] *)
    assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
    replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
    step. step. apply evt_done. do 2 eexists. reflexivity.
  - assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
    destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
    apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End HALVE2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

#[using="SC"] Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof.
  unfold cnt0. destruct (Z.ltb_spec sc 9).
  - unfold small_cnt_pick. pose proof (small_cnt_range sc). Local Ltac2 Set LiaHints.tbl := fun () => "00G0>13227725593.1330363033283.155208631479.13 5208631604.12 52352673314.1452352673443.1352930602171.1252930602296.1358139561083.125818568920.13 5818569051.12 59654440132.1259654440263.1361222816495.1261222816620.1361703251183.1366053841170.1466053841299.1367212774306.148197809883.12 8197810008.13 8433447544.12 8433447931.13 00000400>00B00C00G00H00I00J00N00O00P00Q00U00[00a00j00n00o01301401501601:S2MCS2MC2H12H2S2H1FS2H2FSSS2H0SSFS2H1S2SC1HS2SC1HS2SC1H2H1S2H2FS2H1SSFS2H1".
destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
      first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
  - pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
    pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc MR SC UR"] Lemma rcount_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 x1 gmw rqw : word) Fr fc,
  mem_inv usegs m ->
  evt usegs (fun ms' => exists a2' a3' a4',
      ms' = MS (rcnt_regs u size x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a2' a3' a4' a5 a6 a7 rqw (wz cnt0) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x15478) fc None m (seg_rom usegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a0 a1 a2 a3 a4 a5 a6 a7 rqw (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
             (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x153d8) fc None m (seg_rom usegs)).
Proof.
  intros until fc. intros MI.
  pose proof (size_class_range sc SC) as SZR.
  pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
  pose proof rcnt0_range as C0R.
  unfold rcnt_regs, RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES, RPAGE_SIZE, RSMALL_CNT, RMED_CNT in *.
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read st m sc (wa (320304 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
  Local Ltac2 Set LiaHints.tbl := fun () => "00`0>10312311201.4311408186381.4713224913845.4518397739387.461847287747.46 20050800344.4721117097293.4221121176574.4225519559788.462688827061.47 2688827190.46 32886413064.4535759278399.4135779217169.4635907686401.4735907686786.4636455219922.4736598523691.4137609598733.4340823334348.4041046672482.4641415828300.4541415942734.4642466869077.4749182423289.475002755470.46 52928847408.4252930962873.4553132564148.4853810874150.4156096478626.4658137392857.4358139496190.425818585435.46 5818995035.43 58829209207.4660015582180.4061220909156.4261222865647.4661222865772.4761222980335.4361222980460.4461222980589.4561803412289.457443261284.43 8197793624.47 8198170456.44 8243212024.43 00000500900>00B00K00O00R00U00Z00^00b00f00g00h00l01001101501:01;01?01@01A01B01F01J01K01L01M01P01T01X01\01]01^01g01l02202802>02D02J02P02T02X02Y02Z02_S3MCRS2K1S3MCRS2R1S3MCR3HERS2R2S1KS1KS3SZRS2URS2URS2R0SSS2R1S2R0SS2SCS3MCRSS2K0SSSS2K1S2K0SSSS1KS2R1S2L3S2L3SSS3MCR3HERS3SZRS2SC1KS2SC1KS2SC1KS2SC1KS2SC1KS2SC1KS2R0S2SCSSS3MCR".
step. clear RDU.
  (* [comment removed for export] *)
  step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
  - (* [comment removed for export] *)
    apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold RMED_CNT in RDM.
    step. clear RDM. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a3' & a4' & ->). unfold rcnt_regs.
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
    eapply evt_mono.
    { eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a2'' & a3'' & ->). unfold rcnt_regs. do 3 eexists. reflexivity.
  - (* [comment removed for export] *)
    assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
    unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
    pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold RSMALL_CNT in RD0.
    replace (wa (66732 + 3 * sc + 0)) with (Z_to_bv 64 (66732 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
    step. clear RD0. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
    { replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold RSMALL_CNT in RD1.
    replace (wa (66732 + 3 * sc + 1)) with (Z_to_bv 64 (66732 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
    step. clear RD1. rewrite zxb_b8 by lia.
    step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
    { replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold RSMALL_CNT in RD2.
    replace (wa (66732 + 3 * sc + 2)) with (Z_to_bv 64 (66732 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
    step. clear RD2. rewrite zxb_b8 by lia. step.
    apply evt_done. do 3 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End COUNT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

#[using="SZ C0"] Lemma rcnt2_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 (if big then 0x154a0 else 0x154e4)) fc None m (seg_rom usegs))
    (MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x15478) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros MI. unfold rcnt_regs.
  assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
  pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
  assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.
  (* [comment removed for export] *)
  step. Local Ltac2 Set LiaHints.tbl := fun () => "00E0>13721704148.4415095956317.4515524707335.4515524707335.4616637396593.4416639408463.4334019513447.4442275237624.4652520452874.4553512866218.4555813860202.4658286658260.4459301978119.4559577143601.4459579457969.4262357396789.4463463648957.4565102387343.4565104205973.4265106487317.44799247169.44  00000100500900>00B00F00I00M00N00O00S00T00Y00Z00[00^00b00f00j00n012SS2K3S2PRS3PR1S2C0S2C0S1HS2K3SSS2K3SS3C1RSSS1HS2K3S2SZS2SZS2SZS2SZ".
rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite ?unsigned_lit by lia. step. step.
    assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
    { unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
      destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
    assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
    { rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
      destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
    rewrite EV. clear EV.
    assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CNT2.
End CANSEC1.
