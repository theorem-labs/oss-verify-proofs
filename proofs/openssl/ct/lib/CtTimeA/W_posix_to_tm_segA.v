(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnP Require Import MagicDiv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeKit TimeMagic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition A_M86400_A : Z := 0x10548.     (* [comment removed for export] *)

Lemma M86400_cellsA : forall m, mem_inv ctasegs m -> ro_cells ctasegs m A_M86400_A [C8 (Z_to_bv 64 M86400)].
Proof.
  intros m MI. split; [cbn; tauto|]. apply ro_bytes_at; [exact MI| unfold A_M86400_A; lia| cbn; unfold A_M86400_A; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2tm_segA_A : forall (x1 sp2 gp tp x5 x6 x7 s0' x10 x11 x12 x13 x14 x15 x16 x17 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (t D : Z),
  mem_inv ctasegs m -> MIN_POSIX_TIME <= t <= MAX_POSIX_TIME ->
  evt ctasegs (fun ms' => ms' =
      MS (mkR x1 sp2 gp tp x5 x6 x7 s0' (Z_to_bv 64 D) (Z_to_bv 64 (RT t)) (Z_to_bv 64 (DAYS t)) (Z_to_bv 64 (ERA_ARG t)) (Z_to_bv 64 86400)
              (Z_to_bv 64 (DS t)) (Z_to_bv 64 (SG t)) (Z_to_bv 64 (-719468)) x17 (Z_to_bv 64 t) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (Z_to_bv 64 0x2704e0) fc None m (seg_rom ctasegs))
    (MS (mkR x1 sp2 gp tp x5 x6 x7 s0' (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 t) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x270488) fc None m (seg_rom ctasegs)).
Proof.
  intros until D. intros MI RNG.
  pose proof (QR_facts t RNG) as (QR & HR & HRp & HRn & HQ & HDS).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  unfold MIN_POSIX_TIME, MAX_POSIX_TIME in RNG.
  pose proof (M86400_cellsA m MI) as ROM. unfold A_M86400_A in ROM.
  (* [comment removed for export] *)
  do 7 zstep. zstep.
  set (q0 := (t * M86400) / 2^64).
  assert (Hq0 : - 2^62 <= q0 <= 2^62) by (subst q0; unfold M86400; split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
  setreg 10%Z (Z_to_bv 64 q0) ltac:(f_equal; rewrite !signed_lit by (unfold M86400; lia); rewrite shiftr_div by lia; reflexivity).
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  setreg 11%Z (Z_to_bv 64 (QT t))
    ltac:(f_equal; rewrite signed_lit by lia; rewrite sign_bit63 by lia; rewrite shiftr_div by lia; subst q0; rewrite div_ltb0 by lia;
          rewrite Z.div_div by lia; change (2^64 * 2^13) with (2^77);
          replace (t * M86400 <? 0) with (t <? 0) by (unfold M86400; destruct (Z.ltb_spec t 0); [symmetry; apply Z.ltb_lt; lia| symmetry; apply Z.ltb_ge; lia]);
          unfold QT; symmetry; apply div86400_magic; lia).
  (* [comment removed for export] *)
  zstep. zstep. setreg 10%Z (Z_to_bv 64 (RT t)) ltac:(wmod).
  zstep. setreg 15%Z (Z_to_bv 64 (SG t)) ltac:(unfold SG; f_equal; symmetry; rewrite signed_lit by lia; rewrite shiftr_div by lia; apply sra63; lia).
  zstep. setreg 11%Z (Z_to_bv 64 (DAYS t)) ltac:(unfold DAYS; wmod).
  zstep. setreg 14%Z (Z_to_bv 64 (DS t)) ltac:(unfold DS; wmod).
  zstep. zstep.
  (* [comment removed for export] *)
  zstep. if_cases K1; zify_cond K1; rewrite ?signed_lit in K1 by (unfold DAYS, SG in *; destruct (RT t <? 0); lia).
  - apply evt_done. unfold ERA_ARG. replace (0 <? DS t) with true by (symmetry; apply Z.ltb_lt; unfold DS, DAYS, SG in *; destruct (RT t <? 0); lia). reflexivity.
  - zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (ERA_ARG t))
      ltac:(unfold ERA_ARG; replace (0 <? DS t) with false by (symmetry; apply Z.ltb_ge; unfold DS, DAYS, SG in *; destruct (RT t <? 0); lia); unfold DS; wmod).
    apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2tm_segB_A : forall (x1 sp2 gp tp x5 x6 x7 s0' x17 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (t D : Z),
  MIN_POSIX_TIME <= t <= MAX_POSIX_TIME -> 0 <= DOY t <= 365 -> 0 <= YN t <= DOE t ->
  evt ctasegs (fun ms' => exists x5' x6' x7' x17', ms' =
      MS (mkR x1 sp2 gp tp x5' x6' x7' s0' (Z_to_bv 64 D) (Z_to_bv 64 (RT t)) (Z_to_bv 64 (ERA t)) (Z_to_bv 64 (YOE t)) (Z_to_bv 64 86400)
              (Z_to_bv 64 (M3 t)) (Z_to_bv 64 (SG t)) (Z_to_bv 64 (DOY t)) x17' (Z_to_bv 64 t) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (Z_to_bv 64 0x2705f4) fc None m (seg_rom ctasegs))
    (MS (mkR x1 sp2 gp tp x5 x6 x7 s0' (Z_to_bv 64 D) (Z_to_bv 64 (RT t)) (Z_to_bv 64 (DAYS t)) (Z_to_bv 64 (ERA_ARG t)) (Z_to_bv 64 86400)
              (Z_to_bv 64 (DS t)) (Z_to_bv 64 (SG t)) (Z_to_bv 64 (-719468)) x17 (Z_to_bv 64 t) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x2704e0) fc None m (seg_rom ctasegs)).
Proof.
  intros until D. intros RNG HDOY HYN.
  pose proof (QR_facts t RNG) as (QR & HR & HRp & HRn & HQ & HDS). pose proof (ERA_facts t RNG) as (HERA & HDOE & HEA).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (E31 : 2^31 = 2147483648) by reflexivity. assert (E32 : 2^32 = 4294967296) by reflexivity.
  unfold MIN_POSIX_TIME, MAX_POSIX_TIME in RNG.
  zstep. setreg 12%Z (Z_to_bv 64 (ERA_ARG t)) ltac:(w32k HEA).
  (* [comment removed for export] *)
  zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  zstep. setreg 11%Z (Z_to_bv 64 (ERA_ARG t * 963315389)) ltac:(wmodk RNG).
  zstep.
  zstep.
  zstep. setreg 11%Z (Z_to_bv 64 (ERA t))
    ltac:(f_equal; rewrite signed_lit by lia; rewrite sign_bit63 by lia; rewrite shiftr_div by lia;
          replace (ERA_ARG t * 963315389 <? 0) with (ERA_ARG t <? 0) by (destruct (Z.ltb_spec (ERA_ARG t) 0); [symmetry; apply Z.ltb_lt; lia| symmetry; apply Z.ltb_ge; lia]);
          unfold ERA; symmetry; apply div146097_magic; lia).
  (* [comment removed for export] *)
  zstep. setreg 16%Z (Z_to_bv 64 (ERA t * -146097)) ltac:(wmodk RNG).
  zstep. setreg 12%Z (Z_to_bv 64 (DOE t)) ltac:(unfold DOE; wmodk RNG).
  zstep. setreg 14%Z (Z_to_bv 64 (DOE t)) ltac:(unfold DOE in *; w32k HDOE).
  (* [comment removed for export] *)
  zstep.
  zstep.
  zstep.
  zstep. setreg 16%Z (Z_to_bv 64 (DOE t * 1282606671 / 2^32)) ltac:(f_equal; rewrite ?land64, shiftr_div, ?mod64_small by lia; reflexivity).
  zstep.
  zstep. setreg 14%Z (Z_to_bv 64 (DOE t * 441679365 / 2^32)) ltac:(f_equal; rewrite ?land64, shiftr_div, ?mod64_small by lia; reflexivity).
  (* [comment removed for export] *)
  zstep. setreg 16%Z (Z_to_bv 64 (DOE t * 1282606671 / 2^32 - DOE t)) ltac:(w32).
  zstep.
  zstep. setreg 14%Z (Z_to_bv 64 (DOE t * 441679365 / 2^32 - DOE t)) ltac:(w32).
  set (V1 := DOE t * 1282606671 / 2^32 - DOE t) in *. set (V3 := DOE t * 441679365 / 2^32 - DOE t) in *.
  assert (HV1 : - 2^31 <= V1 <= 0 /\ (V1 <? 0) = (0 <? DOE t)) by (subst V1; clear - HDOE; split; [mlia| destruct (Z.ltb_spec 0 (DOE t)); [apply Z.ltb_lt; mlia| apply Z.ltb_ge; mlia]]).
  assert (HV3 : - 2^31 <= V3 <= 0 /\ (V3 <? 0) = (0 <? DOE t)) by (subst V3; clear - HDOE; split; [mlia| destruct (Z.ltb_spec 0 (DOE t)); [apply Z.ltb_lt; mlia| apply Z.ltb_ge; mlia]]).
  (* [comment removed for export] *)
  zstep. setreg 6%Z (Z_to_bv 64 (if V1 <? 0 then 1 else 0)) ltac:(f_equal; symmetry; rewrite ?land64; apply (bit31_gen _ V1); [lia| mliak HV1]).
  zstep. setreg 16%Z (Z_to_bv 64 (V1 / 2^10)) ltac:(f_equal; symmetry; rewrite ?land64; apply (sraiw_gen _ V1); [lia| lia| mliak HV1]).
  zstep. setreg 16%Z (Z_to_bv 64 (- (DOE t / 1460)))
    ltac:(rewrite (proj2 HV1); pose proof (ndiv1460_magic (DOE t) ltac:(lia)) as MG; destruct (0 <? DOE t); subst V1; wmodk MG HDOE).
  (* [comment removed for export] *)
  set (W2 := DOE t * 3853287931 / 2^32). assert (HW2 : 0 <= W2 < 2^31) by (subst W2; mliak HDOE).
  assert (CG2 : ((Z.land (Z.shiftr (Z.land (DOE t * 18446744073267872251) 18446744073709551615) 32 + DOE t) 18446744073709551615) - W2) mod 2^32 = 0).
  { rewrite !land64, shiftr_div by lia. subst W2. apply (hi32_negc_congr _ 441679365); [reflexivity| reflexivity| lia| lia]. }
  zstep. setreg 6%Z (Z_to_bv 64 0)
    ltac:(f_equal; symmetry; transitivity (if W2 <? 0 then 1 else 0);
          [apply (bit31_gen _ W2); [lia| exact CG2] | rewrite (proj2 (Z.ltb_ge W2 0)) by lia; reflexivity]).
  zstep. setreg 5%Z (Z_to_bv 64 (W2 / 2^15)) ltac:(f_equal; symmetry; apply (sraiw_gen _ W2); [lia| lia| exact CG2]).
  zstep. setreg 5%Z (Z_to_bv 64 (DOE t / 36524)) ltac:(pose proof (div36524_magic (DOE t) ltac:(lia)) as MG; subst W2; wmodk MG HDOE).
  zstep. setreg 6%Z (Z_to_bv 64 (if V3 <? 0 then 1 else 0)) ltac:(f_equal; symmetry; rewrite ?land64; apply (bit31_gen _ V3); [lia| mliak HV3]).
  zstep. setreg 14%Z (Z_to_bv 64 (V3 / 2^17)) ltac:(f_equal; symmetry; rewrite ?land64; apply (sraiw_gen _ V3); [lia| lia| mliak HV3]).
  zstep. setreg 14%Z (Z_to_bv 64 (- (DOE t / 146096)))
    ltac:(rewrite (proj2 HV3); pose proof (ndiv146096_magic (DOE t) ltac:(lia)) as MG; destruct (0 <? DOE t); subst V3; wmodk MG HDOE).
  (* [comment removed for export] *)
  zstep.
  zstep. setreg 14%Z (Z_to_bv 64 (DOE t / 36524 - DOE t / 146096)) ltac:(wmodk RNG).
  zstep.
  zstep. setreg 16%Z (Z_to_bv 64 (DOE t - DOE t / 1460)) ltac:(wmodk RNG).
  zstep. setreg 14%Z (Z_to_bv 64 (YN t)) ltac:(unfold YN in *; w32k HYN HDOE).
  (* [comment removed for export] *)
  zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  zstep. set (W5 := YN t * 3012360625 / 2^32). assert (HW5 : 0 <= W5 < 2^31) by (subst W5; mliak HYN HDOE).
  assert (CG5 : ((Z.land (Z.shiftr (Z.land (YN t * 18446744072426944945) 18446744073709551615) 32 + YN t) 18446744073709551615) - W5) mod 2^32 = 0).
  { rewrite !land64, shiftr_div by lia. subst W5. apply (hi32_negc_congr _ 1282606671); [reflexivity| reflexivity| lia| lia]. }
  set (V4 := YN t * 1282606671 / 2^32 - YN t) in *.
  assert (HV4 : - 2^31 <= V4 <= 0 /\ (V4 <? 0) = (0 <? YN t)) by (subst V4; clear - HYN HDOE; split; [mlia| destruct (Z.ltb_spec 0 (YN t)); [apply Z.ltb_lt; mlia| apply Z.ltb_ge; mlia]]).
  (* [comment removed for export] *)
  zstep.
  zstep. setreg 17%Z (Z_to_bv 64 (YN t * 1282606671 / 2^32)) ltac:(f_equal; rewrite ?land64, shiftr_div, ?mod64_small by lia; reflexivity).
  zstep.
  zstep. setreg 14%Z (Z_to_bv 64 V4) ltac:(subst V4; w32k HYN HDOE).
  (* [comment removed for export] *)
  zstep. setreg 17%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; rewrite ?land64; rewrite ?mod64_small by lia; rewrite shiftr_div by lia; apply Z.div_small; lia).
  zstep. setreg 16%Z (Z_to_bv 64 (YN t * 120494425 / 2^42)) ltac:(f_equal; rewrite signed_lit by lia; rewrite shiftr_div by lia; reflexivity).
  zstep. setreg 16%Z (Z_to_bv 64 (YN t / 36500)) ltac:(pose proof (div36500_magic (YN t) ltac:(lia)) as MG; wmodk MG HYN HDOE).
  (* [comment removed for export] *)
  zstep. setreg 17%Z (Z_to_bv 64 0)
    ltac:(f_equal; symmetry; transitivity (if W5 <? 0 then 1 else 0);
          [apply (bit31_gen _ W5); [lia| exact CG5] | rewrite (proj2 (Z.ltb_ge W5 0)) by lia; reflexivity]).
  zstep. setreg 6%Z (Z_to_bv 64 (W5 / 2^8)) ltac:(f_equal; symmetry; apply (sraiw_gen _ W5); [lia| lia| exact CG5]).
  (* [comment removed for export] *)
  zstep. setreg 16%Z (Z_to_bv 64 (DOE t + YN t / 36500)) ltac:(wmodk RNG).
  zstep. setreg 7%Z (Z_to_bv 64 (if V4 <? 0 then 1 else 0)) ltac:(f_equal; symmetry; rewrite ?land64; apply (bit31_gen _ V4); [lia| mliak HV4]).
  zstep. setreg 14%Z (Z_to_bv 64 (V4 / 2^10)) ltac:(f_equal; symmetry; rewrite ?land64; apply (sraiw_gen _ V4); [lia| lia| mliak HV4]).
  (* [comment removed for export] *)
  zstep. setreg 12%Z (Z_to_bv 64 (YOE t)) ltac:(unfold YOE in *; pose proof (div365_magic (YN t) ltac:(lia)) as MG; subst W5; wmodk MG HYN HDOE).
  (* [comment removed for export] *)
  zstep. setreg 14%Z (Z_to_bv 64 (- (YN t / 1460)))
    ltac:(rewrite (proj2 HV4); pose proof (ndiv1460_magic (YN t) ltac:(lia)) as MG; destruct (0 <? YN t); subst V4; wmodk MG HYN HDOE).
  assert (HYOE : 0 <= YOE t <= YN t) by (unfold YOE; mliak HYN HDOE).
  (* [comment removed for export] *)
  zstep. setreg 17%Z (Z_to_bv 64 (YOE t * -365)) ltac:(wmodk RNG).
  zstep. setreg 14%Z (Z_to_bv 64 (DOE t + YN t / 36500 - YN t / 1460)) ltac:(wmodk RNG).
  zstep. setreg 16%Z (Z_to_bv 64 (DOY t)) ltac:(unfold DOY; wmodk RNG).
  (* [comment removed for export] *)
  zstep.
  zstep. if_cases K2; zify_cond K2; rewrite ?signed_lit in K2 by lia.
  - zstep. unfold M3. replace (DOY t <? 306) with true by (symmetry; apply Z.ltb_lt; lia). apply evt_done. do 4 eexists. reflexivity.
  - zstep. zstep. unfold M3. replace (DOY t <? 306) with false by (symmetry; apply Z.ltb_ge; lia). apply evt_done. do 4 eexists. reflexivity.
Qed.
