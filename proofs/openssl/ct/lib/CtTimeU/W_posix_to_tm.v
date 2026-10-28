(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit F_memset.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import MagicDiv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeMagic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition tm_cells (t : tm6) : list cell :=
  [C4 (Z_to_bv 64 (t_sec t)); C4 (Z_to_bv 64 (t_min t)); C4 (Z_to_bv 64 (t_hour t)); C4 (Z_to_bv 64 (t_mday t));
   C4 (Z_to_bv 64 (t_mon t - 1)); C4 (Z_to_bv 64 (t_year t - 1900)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Definition zero56 : list cell := [CB 56%nat (repeat (Z_to_bv 8 0) 56%nat)].
Definition p2tm_cells (t : Z) : list cell := match utc_from_posix t with Some tm => tm_cells tm | None => zero56 end.
Definition p2tm_ret (t : Z) : Z := match utc_from_posix t with Some _ => 1 | None => 0 end.

Definition A_M86400 : Z := 0x3a8a8.     (* [comment removed for export] *)

Section WithCeiling. Context {CE__ : Ceiling}.

Lemma M86400_cells : forall m, mem_inv ctusegs m -> ro_cells ctusegs m A_M86400 [C8 (Z_to_bv 64 M86400)].
Proof.
  intros m MI. split; [cbn; tauto|]. apply ro_bytes_at; [exact MI| unfold A_M86400; lia| cbn; unfold A_M86400; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2tm_segA : forall (sp2 gp tp x5 x6 x7 s0' x10 x11 x12 x13 x14 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (t D : Z),
  mem_inv ctusegs m -> MIN_POSIX_TIME <= t <= MAX_POSIX_TIME ->
  evt ctusegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x12d01c) sp2 gp tp x5 x6 x7 s0' (Z_to_bv 64 D) (Z_to_bv 64 (RT t)) (Z_to_bv 64 (DS t)) (Z_to_bv 64 (ADJ t))
              (Z_to_bv 64 (DAYS t)) (Z_to_bv 64 (ERA_ARG t)) (Z_to_bv 64 86400) (Z_to_bv 64 (SG t)) (Z_to_bv 64 (-719468)) (Z_to_bv 64 t) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (Z_to_bv 64 0x12d0a0) fc None m (seg_rom ctusegs))
    (MS (mkR (Z_to_bv 64 0x12d01c) sp2 gp tp x5 x6 x7 s0' (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 t) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12d044) fc None m (seg_rom ctusegs)).
Proof.
  intros until D. intros MI RNG.
  pose proof (QR_facts t RNG) as (QR & HR & HRp & HRn & HQ & HDS).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  unfold MIN_POSIX_TIME, MAX_POSIX_TIME in RNG.
  pose proof (M86400_cells m MI) as ROM. unfold A_M86400 in ROM.
  (* [comment removed for export] *)
  do 8 zstep.
  set (q0 := (t * M86400) / 2^64).
  assert (Hq0 : - 2^62 <= q0 <= 2^62) by (subst q0; unfold M86400; split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
  setreg 10%Z (Z_to_bv 64 q0) ltac:(f_equal; rewrite !signed_lit by (unfold M86400; lia); rewrite shiftr_div by lia; reflexivity).
  zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (QT t))
    ltac:(f_equal; rewrite signed_lit by lia; rewrite sign_bit63 by lia; rewrite shiftr_div by lia; subst q0; rewrite div_ltb0 by lia;
          rewrite Z.div_div by lia; change (2^64 * 2^13) with (2^77);
          replace (t * M86400 <? 0) with (t <? 0) by (unfold M86400; destruct (Z.ltb_spec t 0); [symmetry; apply Z.ltb_lt; lia| symmetry; apply Z.ltb_ge; lia]);
          unfold QT; symmetry; apply div86400_magic; lia).
  (* [comment removed for export] *)
  zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (RT t)) ltac:(wmod).
  zstep.
  setreg 16%Z (Z_to_bv 64 (SG t)) ltac:(unfold SG; f_equal; symmetry; rewrite signed_lit by lia; rewrite shiftr_div by lia; apply sra63; lia).
  zstep.
  setreg 13%Z (Z_to_bv 64 (DAYS t)) ltac:(unfold DAYS; wmod).
  zstep.
  setreg 11%Z (Z_to_bv 64 (DS t)) ltac:(unfold DS; wmod).
  zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (ADJ t)) ltac:(unfold ADJ, SG; f_equal; destruct (RT t <? 0); reflexivity).
  zstep.
  (* [comment removed for export] *)
  zstep. if_cases K1; zify_cond K1; rewrite ?signed_lit in K1 by (unfold DAYS, SG in *; destruct (RT t <? 0); lia).
  - apply evt_done. unfold ERA_ARG. replace (0 <? DS t) with true by (symmetry; apply Z.ltb_lt; unfold DS, DAYS, SG in *; destruct (RT t <? 0); lia). reflexivity.
  - zstep. zstep. zstep. setreg 14%Z (Z_to_bv 64 (ERA_ARG t))
      ltac:(unfold ERA_ARG; replace (0 <? DS t) with false by (symmetry; apply Z.ltb_ge; unfold DS, DAYS, SG in *; destruct (RT t <? 0); lia); unfold DS; wmod).
    apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p2tm_segB : forall (sp2 gp tp x5 x6 x7 s0' s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (t D : Z),
  MIN_POSIX_TIME <= t <= MAX_POSIX_TIME -> 0 <= DOY t <= 365 -> 0 <= YN t <= DOE t ->
  evt ctusegs (fun ms' => exists x17',  ms' =
      MS (mkR (Z_to_bv 64 0x12d01c) sp2 gp tp (Z_to_bv 64 (-365)) x6 x7 s0' (Z_to_bv 64 D) (Z_to_bv 64 (SECS t)) (Z_to_bv 64 (DOY t)) (Z_to_bv 64 (M3 t))
              (Z_to_bv 64 (ERA t * 400 + YOE t)) (Z_to_bv 64 (MOY t)) (Z_to_bv 64 306) (Z_to_bv 64 (-701792041)) x17' (Z_to_bv 64 t) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (Z_to_bv 64 0x12d1f0) fc None m (seg_rom ctusegs))
    (MS (mkR (Z_to_bv 64 0x12d01c) sp2 gp tp x5 x6 x7 s0' (Z_to_bv 64 D) (Z_to_bv 64 (RT t)) (Z_to_bv 64 (DS t)) (Z_to_bv 64 (ADJ t))
              (Z_to_bv 64 (DAYS t)) (Z_to_bv 64 (ERA_ARG t)) (Z_to_bv 64 86400) (Z_to_bv 64 (SG t)) (Z_to_bv 64 (-719468)) (Z_to_bv 64 t) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12d0a0) fc None m (seg_rom ctusegs)).
Proof.
  intros until D. intros RNG HDOY HYN.
  pose proof (QR_facts t RNG) as (QR & HR & HRp & HRn & HQ & HDS). pose proof (ERA_facts t RNG) as (HERA & HDOE & HEA).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (E31 : 2^31 = 2147483648) by reflexivity. assert (E32 : 2^32 = 4294967296) by reflexivity.
  unfold MIN_POSIX_TIME, MAX_POSIX_TIME in RNG.
  (* [comment removed for export] *)
  zstep.
  setreg 10%Z (Z_to_bv 64 (SECS t)) ltac:(unfold SECS; wmodk RNG).
  zstep.
  setreg 14%Z (Z_to_bv 64 (ERA_ARG t)) ltac:(w32k HEA).
  (* [comment removed for export] *)
  do 7 zstep.
  setreg 12%Z (Z_to_bv 64 (ERA_ARG t * 963315389)) ltac:(wmodk RNG).
  zstep. zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (ERA t))
    ltac:(f_equal; rewrite signed_lit by lia; rewrite sign_bit63 by lia; rewrite shiftr_div by lia;
          replace (ERA_ARG t * 963315389 <? 0) with (ERA_ARG t <? 0) by (destruct (Z.ltb_spec (ERA_ARG t) 0); [symmetry; apply Z.ltb_lt; lia| symmetry; apply Z.ltb_ge; lia]);
          unfold ERA; symmetry; apply div146097_magic; lia).
  (* [comment removed for export] *)
  do 6 zstep.
  setreg 13%Z (Z_to_bv 64 (ERA t * -146097)) ltac:(wmodk RNG).
  zstep.
  setreg 12%Z (Z_to_bv 64 (ERA t * 400)) ltac:(wmodk RNG).
  zstep.
  setreg 14%Z (Z_to_bv 64 (DOE t)) ltac:(unfold DOE; wmodk RNG).
  zstep.
  setreg 11%Z (Z_to_bv 64 (DOE t)) ltac:(unfold DOE in *; w32k HDOE).
  (* [comment removed for export] *)
  do 5 zstep.
  setreg 15%Z (Z_to_bv 64 (DOE t * 1282606671 / 2^32)) ltac:(f_equal; rewrite ?land64, shiftr_div, ?mod64_small by lia; reflexivity).
  setreg 13%Z (Z_to_bv 64 (DOE t * 441679365 / 2^32)) ltac:(f_equal; rewrite ?land64, shiftr_div, ?mod64_small by lia; reflexivity).
  zstep. zstep. zstep.
  setreg 15%Z (Z_to_bv 64 (DOE t * 1282606671 / 2^32 - DOE t)) ltac:(w32).
  setreg 13%Z (Z_to_bv 64 (DOE t * 441679365 / 2^32 - DOE t)) ltac:(w32).
  set (V1 := DOE t * 1282606671 / 2^32 - DOE t) in *.
  set (V3 := DOE t * 441679365 / 2^32 - DOE t) in *.
  assert (HV1 : - 2^31 <= V1 <= 0 /\ (V1 <? 0) = (0 <? DOE t)) by (subst V1; clear - HDOE; split; [mlia| destruct (Z.ltb_spec 0 (DOE t)); [apply Z.ltb_lt; mlia| apply Z.ltb_ge; mlia]]).
  assert (HV3 : - 2^31 <= V3 <= 0 /\ (V3 <? 0) = (0 <? DOE t)) by (subst V3; clear - HDOE; split; [mlia| destruct (Z.ltb_spec 0 (DOE t)); [apply Z.ltb_lt; mlia| apply Z.ltb_ge; mlia]]).
  (* [comment removed for export] *)
  zstep. zstep.
  setreg 17%Z (Z_to_bv 64 (if V3 <? 0 then 1 else 0)) ltac:(f_equal; symmetry; rewrite ?land64; apply (bit31_gen _ V3); [lia| mliak HV3]).
  zstep.
  setreg 13%Z (Z_to_bv 64 (V3 / 2^17)) ltac:(f_equal; symmetry; rewrite ?land64; apply (sraiw_gen _ V3); [lia| lia| mliak HV3]).
  zstep. zstep.
  setreg 17%Z (Z_to_bv 64 (if V1 <? 0 then 1 else 0)) ltac:(f_equal; symmetry; rewrite ?land64; apply (bit31_gen _ V1); [lia| mliak HV1]).
  zstep.
  setreg 15%Z (Z_to_bv 64 (V1 / 2^10)) ltac:(f_equal; symmetry; rewrite ?land64; apply (sraiw_gen _ V1); [lia| lia| mliak HV1]).
  zstep.
  setreg 15%Z (Z_to_bv 64 (- (DOE t / 1460)))
    ltac:(rewrite (proj2 HV1); pose proof (ndiv1460_magic (DOE t) ltac:(lia)) as MG; destruct (0 <? DOE t); subst V1; wmodk MG HDOE).
  (* [comment removed for export] *)
  set (W2 := DOE t * 3853287931 / 2^32).
  assert (HW2 : 0 <= W2 < 2^31) by (subst W2; mliak HDOE).
  assert (CG2 : ((Z.land (Z.shiftr (Z.land (DOE t * 18446744073267872251) 18446744073709551615) 32 + DOE t) 18446744073709551615) - W2) mod 2^32 = 0).
  { rewrite !land64, shiftr_div by lia. subst W2. apply (hi32_negc_congr _ 441679365); [reflexivity| reflexivity| lia| lia]. }
  zstep.
  setreg 17%Z (Z_to_bv 64 0)
    ltac:(f_equal; symmetry; transitivity (if W2 <? 0 then 1 else 0);
          [apply (bit31_gen _ W2); [lia| exact CG2] | rewrite (proj2 (Z.ltb_ge W2 0)) by lia; reflexivity]).
  zstep.
  setreg 11%Z (Z_to_bv 64 (W2 / 2^15)) ltac:(f_equal; symmetry; apply (sraiw_gen _ W2); [lia| lia| exact CG2]).
  zstep.
  setreg 11%Z (Z_to_bv 64 (DOE t / 36524)) ltac:(pose proof (div36524_magic (DOE t) ltac:(lia)) as MG; subst W2; wmodk MG HDOE).
  (* [comment removed for export] *)
  setreg 13%Z (Z_to_bv 64 (- (DOE t / 146096)))
    ltac:(rewrite (proj2 HV3); pose proof (ndiv146096_magic (DOE t) ltac:(lia)) as MG; destruct (0 <? DOE t); subst V3; wmodk MG HDOE).
  (* [comment removed for export] *)
  zstep. zstep.
  setreg 11%Z (Z_to_bv 64 (DOE t / 36524 - DOE t / 146096)) ltac:(wmodk RNG).
  zstep. zstep.
  setreg 15%Z (Z_to_bv 64 (DOE t - DOE t / 1460)) ltac:(wmodk RNG).
  zstep.
  setreg 11%Z (Z_to_bv 64 (YN t)) ltac:(unfold YN in *; w32k HYN HDOE).
  (* [comment removed for export] *)
  do 6 zstep.
  set (W5 := YN t * 3012360625 / 2^32).
  assert (HW5 : 0 <= W5 < 2^31) by (subst W5; mliak HYN HDOE).
  assert (CG5 : ((Z.land (Z.shiftr (Z.land (YN t * 18446744072426944945) 18446744073709551615) 32 + YN t) 18446744073709551615) - W5) mod 2^32 = 0).
  { rewrite !land64, shiftr_div by lia. subst W5. apply (hi32_negc_congr _ 1282606671); [reflexivity| reflexivity| lia| lia]. }
  set (V4 := YN t * 1282606671 / 2^32 - YN t) in *.
  assert (HV4 : - 2^31 <= V4 <= 0 /\ (V4 <? 0) = (0 <? YN t)) by (subst V4; clear - HYN HDOE; split; [mlia| destruct (Z.ltb_spec 0 (YN t)); [apply Z.ltb_lt; mlia| apply Z.ltb_ge; mlia]]).
  zstep. zstep.
  setreg 16%Z (Z_to_bv 64 (YN t * 1282606671 / 2^32)) ltac:(f_equal; rewrite ?land64, shiftr_div, ?mod64_small by lia; reflexivity).
  zstep. zstep.
  setreg 11%Z (Z_to_bv 64 V4) ltac:(subst V4; w32k HYN HDOE).
  zstep.
  setreg 16%Z (Z_to_bv 64 0) ltac:(f_equal; symmetry; rewrite ?land64; rewrite ?mod64_small by lia; rewrite shiftr_div by lia; apply Z.div_small; lia).
  zstep.
  setreg 13%Z (Z_to_bv 64 (YN t * 120494425 / 2^42)) ltac:(f_equal; rewrite signed_lit by lia; rewrite shiftr_div by lia; reflexivity).
  zstep.
  setreg 13%Z (Z_to_bv 64 (YN t / 36500)) ltac:(pose proof (div36500_magic (YN t) ltac:(lia)) as MG; wmodk MG HYN HDOE).
  zstep. zstep. zstep.
  setreg 14%Z (Z_to_bv 64 (DOE t + YN t / 36500)) ltac:(wmodk RNG).
  zstep.
  setreg 13%Z (Z_to_bv 64 0)
    ltac:(f_equal; symmetry; transitivity (if W5 <? 0 then 1 else 0);
          [apply (bit31_gen _ W5); [lia| exact CG5] | rewrite (proj2 (Z.ltb_ge W5 0)) by lia; reflexivity]).
  zstep.
  setreg 15%Z (Z_to_bv 64 (W5 / 2^8)) ltac:(f_equal; symmetry; apply (sraiw_gen _ W5); [lia| lia| exact CG5]).
  zstep.
  setreg 15%Z (Z_to_bv 64 (YOE t)) ltac:(unfold YOE in *; pose proof (div365_magic (YN t) ltac:(lia)) as MG; subst W5; w32k MG HYN HDOE).
  zstep.
  setreg 13%Z (Z_to_bv 64 (if V4 <? 0 then 1 else 0)) ltac:(f_equal; symmetry; rewrite ?land64; apply (bit31_gen _ V4); [lia| mliak HV4]).
  zstep.
  setreg 11%Z (Z_to_bv 64 (V4 / 2^10)) ltac:(f_equal; symmetry; rewrite ?land64; apply (sraiw_gen _ V4); [lia| lia| mliak HV4]).
  zstep.
  setreg 11%Z (Z_to_bv 64 (- (YN t / 1460)))
    ltac:(rewrite (proj2 HV4); pose proof (ndiv1460_magic (YN t) ltac:(lia)) as MG; destruct (0 <? YN t); subst V4; wmodk MG HYN HDOE).
  (* [comment removed for export] *)
  assert (HYOE : 0 <= YOE t <= YN t) by (unfold YOE; mliak HYN HDOE).
  zstep.
  setreg 13%Z (Z_to_bv 64 (ERA t * 400 + YOE t)) ltac:(wmodk RNG).
  zstep.
  setreg 12%Z (Z_to_bv 64 (YOE t * -365)) ltac:(wmodk RNG).
  zstep.
  setreg 11%Z (Z_to_bv 64 (DOE t + YN t / 36500 - YN t / 1460)) ltac:(wmodk RNG).
  zstep.
  setreg 11%Z (Z_to_bv 64 (DOY t)) ltac:(unfold DOY; wmodk RNG).
  (* [comment removed for export] *)
  zstep. zstep.
  setreg 12%Z (Z_to_bv 64 (5 * DOY t)) ltac:(wmodk RNG).
  zstep.
  setreg 12%Z (Z_to_bv 64 (5 * DOY t + 2)) ltac:(w32k HDOY).
  set (W6 := (5 * DOY t + 2) * 3593175255 / 2^32).
  assert (HW6 : 0 <= W6 < 2^31) by (subst W6; mliak HDOY).
  assert (CG6 : ((Z.land (Z.shiftr (Z.land ((5 * DOY t + 2) * 18446744073007759575) 18446744073709551615) 32 + (5 * DOY t + 2)) 18446744073709551615) - W6) mod 2^32 = 0).
  { rewrite !land64, shiftr_div by lia. subst W6. apply (hi32_negc_congr _ 701792041); [reflexivity| reflexivity| lia| lia]. }
  do 4 zstep.
  setreg 14%Z (Z_to_bv 64 0)
    ltac:(f_equal; symmetry; transitivity (if W6 <? 0 then 1 else 0);
          [apply (bit31_gen _ W6); [lia| exact CG6] | rewrite (proj2 (Z.ltb_ge W6 0)) by lia; reflexivity]).
  zstep.
  setreg 12%Z (Z_to_bv 64 (W6 / 2^7)) ltac:(f_equal; symmetry; apply (sraiw_gen _ W6); [lia| lia| exact CG6]).
  zstep. zstep.
  setreg 14%Z (Z_to_bv 64 (MOY t)) ltac:(unfold MOY; pose proof (div153_magic (5 * DOY t + 2) ltac:(lia)) as MG; subst W6; wmodk MG HDOY).
  (* [comment removed for export] *)
  zstep. if_cases K2; zify_cond K2; rewrite ?signed_lit in K2 by lia.
  - zstep. unfold M3. replace (DOY t <? 306) with true by (symmetry; apply Z.ltb_lt; lia). apply evt_done. eexists. reflexivity.
  - zstep. zstep. unfold M3. replace (DOY t <? 306) with false by (symmetry; apply Z.ltb_ge; lia). apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zero56_tm_slots : forall m A,
  rw_cells ctusegs m A zero56 ->
  rw_cells ctusegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                        C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; tauto| bytes_lit_eq| reflexivity]. Qed.

Definition p2tm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) (t D : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p2tm_ret t)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (D, D + 56)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' D (p2tm_cells t).

Lemma OPENSSL_posix_to_tm_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo t D : Z) (junk : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned sp <= D)%Z -> (D + 56 <= 2^64)%Z ->
  rw_cells ctusegs m D [CB 56%nat junk] ->
  (- 2^63 <= t < 2^63)%Z -> a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 D ->
  evt ctusegs (p2tm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m t D)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_POSIX_TO_TM) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk. intros ST MI GLO LO HD HD2 OUT Ht -> ->. unfold GLOBALS_TOP in GLO. unfold OPENSSL_POSIX_TO_TM in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (D, D + 56)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (E31 : 2^31 = 2147483648) by reflexivity. assert (E32 : 2^32 = 4294967296) by reflexivity.
  assert (SEPD : D + 56 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= D) by lia.
  carve_frame 32%nat ST. do 6 zstep.
  (* [comment removed for export] *)
  do 7 zstep.
  name_mem m1. eapply evt_cut; [eapply memset_callZ; [exact OUT| exact MI| lia| lia| lia| lia]|]. post_call ctusegs m1.
  name_mem m2. rename MI0 into MI. rename POST into OUT. change (0 mod 256) with 0 in OUT. change (Z.to_nat 56) with 56%nat in OUT.
  (* [comment removed for export] *)
  do 10 zstep. if_cases K0; zify_cond K0; rewrite ?land64, ?E64 in K0.
  { (* [comment removed for export] *)
    assert (RNG : t < MIN_POSIX_TIME \/ MAX_POSIX_TIME < t).
    { unfold MIN_POSIX_TIME, MAX_POSIX_TIME. destruct (Z_lt_le_dec t 253402300800) as [A|A]; [| lia].
      rewrite Z.mod_small in K0 by lia. lia. }
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold p2tm_post, p2tm_ret, p2tm_cells.
    replace (utc_from_posix t) with (@None tm6)
      by (symmetry; unfold utc_from_posix; replace ((t <? MIN_POSIX_TIME) || (MAX_POSIX_TIME <? t)) with true; [reflexivity|];
          symmetry; apply orb_true_intro; destruct RNG; [left| right]; apply Z.ltb_lt; lia).
    do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. }
  (* [comment removed for export] *)
  assert (RNG : MIN_POSIX_TIME <= t <= MAX_POSIX_TIME).
  { unfold MIN_POSIX_TIME, MAX_POSIX_TIME. destruct (Z_lt_le_dec t 253402300800) as [A|A].
    - rewrite Z.mod_small in K0 by lia. lia.
    - exfalso. rewrite <- (Z.mod_add _ (-1)) in K0 by lia. rewrite Z.mod_small in K0 by lia. lia. }
  clear K0.
  pose proof (QR_facts t RNG) as (QR & HR & HRp & HRn & HQ & HDS). pose proof (ERA_facts t RNG) as (HERA & HDOE & HEA).
  pose proof (DOE_facts t RNG) as (HYN & HDOY & HMOY & HMON & HMDAY & HYOE). pose proof (SECS_facts t RNG) as (HSECS & HHH & HS2 & HMI & HSS).
  (* [comment removed for export] *)
  eapply evt_cut; [apply p2tm_segA; [exact MI| exact RNG]|]. intros ms' ->.
  eapply evt_cut; [apply p2tm_segB; [exact RNG| lia| lia]|]. intros ms' [x17' ->].
  apply zero56_tm_slots in OUT.
  unfold MIN_POSIX_TIME, MAX_POSIX_TIME in RNG.
  (* [comment removed for export] *)
  zstep.
  setreg 12%Z (Z_to_bv 64 (MON t)) ltac:(f_equal; symmetry; rewrite ?land64; apply swrap32_eqm; [clear - HMON; lia| unfold MON; mliak RNG]).
  zstep. zstep. zstep.
  setreg 17%Z (Z_to_bv 64 (SECS t * 2^32)) ltac:(wmodk RNG).
  zstep.
  zstep.
  setreg 14%Z (Z_to_bv 64 (MOY t * 153)) ltac:(wmodk RNG).
  zstep.
  setreg 15%Z (Z_to_bv 64 (if MON t <? 3 then 1 else 0))
    ltac:(f_equal; rewrite zb_b2z_if; rewrite ?unsigned_lit, ?land64, ?mod64_small by lia; rewrite slti_lit by lia;
          destruct (Z.ltb_spec (MON t) 3); [rewrite (proj2 (Z.ltb_lt _ _)) by lia| rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity).
  zstep.
  setreg 13%Z (Z_to_bv 64 (YR t)) ltac:(unfold YR; destruct (MON t <? 3); wmodk RNG).
  zstep. zstep. zstep.
  setreg 14%Z (Z_to_bv 64 (153 * MOY t + 2)) ltac:(w32k HMOY).
  zstep. zstep.
  (* [comment removed for export] *)
  do 6 zstep.
  setreg 12%Z (Z_to_bv 64 (MON t - 1)) ltac:(wmodk RNG).
  setreg 14%Z (Z_to_bv 64 ((153 * MOY t + 2) * - 1717986919)) ltac:(wmodk RNG).
  zstep. zstep.
  setreg 17%Z (Z_to_bv 64 (SECS t * 2443359173)) ltac:(f_equal; symmetry; apply mulhu_3600; lia).
  zstep.
  setreg 13%Z (Z_to_bv 64 (YR t - 1900)) ltac:(wmodk RNG).
  zstep.
  setreg 5%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; rewrite sign_bit63 by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
  zstep.
  setreg 14%Z (Z_to_bv 64 ((153 * MOY t + 2) * - 1717986919 / 2^33)) ltac:(f_equal; rewrite signed_lit by lia; rewrite shiftr_div by lia; reflexivity).
  zstep.
  setreg 17%Z (Z_to_bv 64 (HH t))
    ltac:(unfold HH; pose proof (div3600_magic (SECS t) ltac:(lia)) as MG; f_equal; rewrite ?land64, ?mod64_small by lia; rewrite shiftr_div by lia; symmetry; exact MG).
  (* [comment removed for export] *)
  do 5 zstep.
  setreg 14%Z (Z_to_bv 64 (- ((153 * MOY t + 2) / 5)))
    ltac:(pose proof (ndiv5_magic (153 * MOY t + 2) ltac:(lia)) as MG; replace (0 <? 153 * MOY t + 2) with true in MG by (symmetry; apply Z.ltb_lt; lia);
          change (if true then 1 else 0) with 1 in MG; wmodk MG HMOY).
  zstep.
  setreg 12%Z (Z_to_bv 64 (HH t * 3600)) ltac:(wmodk RNG).
  zstep.
  setreg 11%Z (Z_to_bv 64 (DOY t + - ((153 * MOY t + 2) / 5))) ltac:(wmodk RNG).
  zstep.
  setreg 10%Z (Z_to_bv 64 (S2 t)) ltac:(unfold S2; wmodk RNG).
  zstep.
  setreg 11%Z (Z_to_bv 64 (MDAY t)) ltac:(unfold MDAY; wmodk RNG).
  zstep.
  setreg 12%Z (Z_to_bv 64 (S2 t * 34953)) ltac:(wmodk RNG).
  zstep.
  setreg 13%Z (Z_to_bv 64 (TimeMagic.MI t))
    ltac:(unfold TimeMagic.MI; pose proof (div60_magic (S2 t) ltac:(lia)) as MG; rewrite <- MG; f_equal; symmetry; apply (srliw_gen _ (S2 t * 34953));
          [lia| lia| mliak HS2]).
  zstep.
  setreg 12%Z (Z_to_bv 64 (TimeMagic.MI t))
    ltac:(unfold TimeMagic.MI; pose proof (div60_magic (S2 t) ltac:(lia)) as MG; f_equal; rewrite ?land64, ?mod64_small by nia; rewrite shiftr_div by lia; symmetry; exact MG).
  zstep.
  setreg 12%Z (Z_to_bv 64 (TimeMagic.MI t * 64)) ltac:(wmodk RNG).
  zstep.
  setreg 14%Z (Z_to_bv 64 (TimeMagic.MI t * 4)) ltac:(wmodk RNG).
  zstep.
  setreg 14%Z (Z_to_bv 64 (TimeMagic.MI t * -60)) ltac:(w32k HMI).
  zstep.
  setreg 10%Z (Z_to_bv 64 (SS t)) ltac:(unfold SS; wmodk RNG).
  zstep. zstep.
  setreg 10%Z (Z_to_bv 64 (SS t)) ltac:(clear - HSS E64; wmod).
  (* [comment removed for export] *)
  do 5 zstep.
  (* [comment removed for export] *)
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold p2tm_post, p2tm_ret, p2tm_cells. rewrite (p2tm_agree t RNG). unfold tm_cells. cbn [t_sec t_min t_hour t_mday t_mon t_year].
  do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

End WithCeiling.
