(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit F_memcpy F_vsnprintf.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs TimeToTmFeb W_time_leaves W_time_to_tm_A W_time_to_tm_it W_time_to_tm_B W_time_to_tm_C.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
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


(* [comment removed for export] *)
Ltac isdig_call cv :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evt_cut;
    [ eapply ossl_ascii_isdigit_spec with (c := cv);
      [ rewrite ?unsigned_lit by lia; eassumption | eassumption | unfold GLOBALS_TOP; lia | rewrite ?unsigned_lit by lia; lia | lia | reflexivity ]
    | intros ms' PO; unfold leaf16_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO; post_call ctpsegs mx ]
  end.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition t2t_fin_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (DA GS tm : Z) (t : tm6) (wd yd : Z) (sv : list cell) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
                  (Z_to_bv 64 tm) (Z_to_bv 64 1) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x11d810) fc None m' (seg_rom ctpsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m' /\ stk ctpsegs m' lo (bv_unsigned sp + -272)
    /\ rw_cells ctpsegs m' (bv_unsigned sp + -272)
         (T2T_CONSTS 19 19 GS tm ++ TM_CELLS (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd ++ sv).

Lemma t2t_segD : forall (x1 sp gp tp x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms wd yd : Z) (t : tm6) (sv : list cell),
  stk ctpsegs m lo (bv_unsigned sp + -272) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctpsegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctpsegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> GS + 19 <= 2^63 ->
  rw_cells ctpsegs m (bv_unsigned sp + -272) (T2T_CONSTS 19 19 GS tm ++ TM_CELLS 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd ++ sv) -> cells_size sv = 104%nat ->
  tm_valid t -> 0 <= ms < 1000 -> 0 <= tm < 2^64 ->
  evt ctpsegs (t2t_fin_post sp gp tp F fc lo m DA GS tm t wd yd sv)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp (Z_to_bv 64 10) x10 (Z_to_bv 64 4) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) x19 x20 (Z_to_bv 64 7) x22 (Z_to_bv 64 (t_year t - 1900)) (Z_to_bv 64 8) (Z_to_bv 64 (t_mon t - 1)) (Z_to_bv 64 12) (Z_to_bv 64 (GS + 9)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x11d480) fc None m (seg_rom ctpsegs)).
Proof.
  intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR SVS TV MSR TMR.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  unfold gcells, zb8 in HS. unfold CH_Z, CH_DOT in HS. unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47 in FR. cbn [app] in FR.
  (* [comment removed for export] *)
  iter_call 4 (TM_CELLS 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd). name_mem m1.
  change (fld 4 t) with (t_hour t) in *.
  step. step. zstep. zstep. zstep. step. if_cases K0; zify_cond K0; [| exfalso; first [apply K0; reflexivity| lia]]. try clear K0.
  (* [comment removed for export] *)
  iter_call 5 (TM_CELLS 0 0 (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd). name_mem m2.
  change (fld 5 t) with (t_min t) in *.
  step. step. zstep. zstep. zstep. step. if_cases K0; zify_cond K0; [| exfalso; first [apply K0; reflexivity| lia]]. try clear K0.
  (* [comment removed for export] *)
  iter_call 6 (TM_CELLS 0 (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd). name_mem m3.
  change (fld 6 t) with (t_sec t) in *.
  step. step. zstep. zstep. zstep. step. if_cases K0; zify_cond K0; [exfalso; first [apply K0; reflexivity| lia]|]. try clear K0.
  (* [comment removed for export] *)
  step. step. step. step. step. if_cases K1; zify_cond K1; [exfalso; first [apply K1; reflexivity| lia]|]. try clear K1.
  zstep. step. rewrite (zxb_lit 46) by lia. step.
  step. if_cases K2; zify_cond K2; [exfalso; first [apply K2; reflexivity| lia]|]. try clear K2.
  zstep. step. brF ltsz. step. zstep. step. zstep. zstep.
  pose proof (digit_range (ms / 100) ltac:(split; [apply Z.div_pos; lia| enough (ms / 100 < 10) by lia; apply Z.div_lt_upper_bound; lia])) as DG1.
  pose proof (digit_range ((ms / 10) mod 10) ltac:(pose proof (Z.mod_pos_bound (ms / 10) 10 ltac:(lia)); lia)) as DG2.
  pose proof (digit_range (ms mod 10) ltac:(pose proof (Z.mod_pos_bound ms 10 ltac:(lia)); lia)) as DG3.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit (digit (ms / 100))) by lia. step. isdig_call (digit (ms / 100)). rewrite (isdigit_range (digit (ms / 100))) by lia.
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  zstep. zstep. zstep. zstep. step. if_cases K4; zify_cond K4; [| exfalso; first [apply K4; reflexivity| lia]]. try clear K4.
  step. rewrite (zxb_lit (digit ((ms / 10) mod 10))) by lia. step. isdig_call (digit ((ms / 10) mod 10)). rewrite (isdigit_range (digit ((ms / 10) mod 10))) by lia.
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  zstep. zstep. zstep. zstep. step. if_cases K4; zify_cond K4; [| exfalso; first [apply K4; reflexivity| lia]]. try clear K4.
  step. rewrite (zxb_lit (digit (ms mod 10))) by lia. step. isdig_call (digit (ms mod 10)). rewrite (isdigit_range (digit (ms mod 10))) by lia.
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  zstep. zstep. zstep. zstep. step. if_cases K4; zify_cond K4; [| exfalso; first [apply K4; reflexivity| lia]]. try clear K4.
  (* [comment removed for export] *)
  step. rewrite (zxb_lit 90) by lia. step. isdig_call 90. rewrite (isdigit_false 90) by lia.
  step. if_cases K3; zify_cond K3; [| exfalso; first [apply K3; reflexivity| lia]]. try clear K3.
  (* [comment removed for export] *)
  step. step. if_cases K5; zify_cond K5; [exfalso; revert K5; clear; intros K5; rewrite ?land64 in K5; Z.to_euclidean_division_equations; lia|]. try clear K5.
  step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  step.
  (* [comment removed for export] *)
  zstep. step. rewrite (zxb_lit 90) by lia.
  step. step. if_cases K7; zify_cond K7; [exfalso; rewrite ?unsigned_lit in K7 by lia; lia|]. try clear K7.
  step. step. if_cases K7; zify_cond K7; [exfalso; rewrite ?unsigned_lit in K7 by lia; lia|]. try clear K7.
  step. step. if_cases K7; zify_cond K7; [exfalso; first [apply K7; reflexivity| lia]|]. try clear K7.
  zstep. step. step. if_cases K8; zify_cond K8; [exfalso; first [apply K8; reflexivity| lia]|]. try clear K8.
  step.
  name_mem m9. apply evt_done. unfold t2t_fin_post. do 25 eexists. exists m9. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47. cbn [app]. assumption.
Qed.

(* [comment removed for export] *)
Lemma t2t_end0 : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo GS : Z) (tmc : list cell),
  stk ctpsegs m lo (bv_unsigned sp + -272) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  rw_cells ctpsegs m (bv_unsigned sp + -272) (T2T_CONSTS 19 19 GS 0 ++ tmc ++ T2T_SAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> cells_size tmc = 56%nat ->
  evt ctpsegs (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctpsegs)
      /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m' /\ stk ctpsegs m' lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 0) (Z_to_bv 64 1) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x11d810) fc None m (seg_rom ctpsegs)).
Proof.
  intros until tmc. intros ST MI GLO LO SP63 FR TMS.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  (* [comment removed for export] *)
  pose proof (proj1 (rw_cells_app m _ _ _) FR) as [FRC FRR]. pose proof (proj1 (rw_cells_app m _ _ _) FRR) as [FRT FRS]. clear FR FRR.
  destruct (rw_cells_forget _ _ _ _ FRT) as [junk FRT']. clear FRT. rewrite TMS in FRT', FRS.
  change (Z.of_nat 56) with (Z.of_nat (cells_size [CB 56%nat junk])) in FRS.
  pose proof (proj2 (rw_cells_app m _ _ _) (conj FRT' FRS)) as FRR. pose proof (proj2 (rw_cells_app m _ _ _) (conj FRC FRR)) as FR. clear FRC FRT' FRS FRR.
  unfold T2T_CONSTS, T2T_SAVED, A_MINTAB, MASK47 in FR. cbn [app cells_size csize Nat.add] in FR.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. try clear K0.
  step. do 13 step. step. release_frame FR ST (bv_unsigned sp). step.
  name_mem m2. apply evt_done. do 14 eexists. exists m2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

(* [comment removed for export] *)
Lemma t2t_end1 : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo GS tm : Z) (tmc : list cell) (junk : list byte),
  stk ctpsegs m lo (bv_unsigned sp + -272) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  rw_cells ctpsegs m (bv_unsigned sp + -272) (T2T_CONSTS 19 19 GS tm ++ tmc ++ T2T_SAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> cells_size tmc = 56%nat -> cells_wf tmc ->
  0 < tm -> bv_unsigned sp <= tm -> tm + 56 <= 2^63 -> rw_cells ctpsegs m tm [CB 56%nat junk] ->
  evt ctpsegs (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctpsegs)
      /\ munch [(lo, bv_unsigned sp); (tm, tm + 56)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m' /\ stk ctpsegs m' lo (bv_unsigned sp)
      /\ rw_cells ctpsegs m' tm [CB 56%nat (cells_bytes tmc)])
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 tm) (Z_to_bv 64 1) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x11d810) fc None m (seg_rom ctpsegs)).
Proof.
  intros until junk. intros ST MI GLO LO SP63 FR TMS TMW TM0 TMLO TMHI HT.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (tm, tm + 56)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (proj1 (rw_cells_app m _ _ _) FR) as [FRC FRR]. pose proof (proj1 (rw_cells_app m _ _ _) FRR) as [FRT FRS]. clear FR FRR.
  destruct (rw_cells_forget _ _ _ _ FRT) as [jt FRT']. rewrite TMS in FRT', FRS.
  assert (Ejt : jt = cells_bytes tmc).
  { destruct FRT as [[W1 B1] _]. destruct FRT' as [[W2 B2] _]. cbn [cells_bytes cbytes app] in B2. rewrite app_nil_r in B2.
    symmetry. eapply bytes_at_same; [exact B1| exact B2| rewrite (cells_bytes_length tmc W1), TMS; destruct W2 as [W2 _]; cbn in W2; lia]. }
  subst jt. clear FRT.
  change (Z.of_nat 56) with (Z.of_nat (cells_size [CB 56%nat (cells_bytes tmc)])) in FRS.
  pose proof (proj2 (rw_cells_app m _ _ _) (conj FRT' FRS)) as FRR. pose proof (proj2 (rw_cells_app m _ _ _) (conj FRC FRR)) as FR. clear FRC FRS FRR.
  unfold T2T_CONSTS, T2T_SAVED, A_MINTAB, MASK47 in FR. cbn [app cells_size csize Nat.add] in FR.
  unfold T2T_CONSTS, A_MINTAB, MASK47 in FRT'. cbn [app cells_size csize Nat.add] in FRT'.
  replace (bv_unsigned sp + -272 + Z.of_nat 112) with (bv_unsigned sp + -160) in FRT' by lia.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. try clear K0.
  step. step. step. step. step.
  pose proof (proj2 (proj1 FRT')) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
  name_mem m1. eapply evt_cut.
  { eapply memcpy_spec with (src := cells_bytes tmc) (junk := junk); rewrite ?unsigned_lit by lia;
      [ exact SRCB | rewrite (cells_bytes_length _ TMW), TMS; reflexivity | exact HT | lia | assumption ]. }
  intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO. post_call ctpsegs m1.
  match goal with H : rw_cells ctpsegs _ tm [CB _ (cells_bytes tmc)] |- _ => rename H into HT2 end.
  (* [comment removed for export] *)
  step. step. do 13 step. step.
  match goal with H : stk ctpsegs _ lo (bv_unsigned sp + -272) |- _ => release_frame FR H (bv_unsigned sp) end. step.
  name_mem m2. apply evt_done. do 14 eexists. exists m2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  change (Z.to_nat 56) with 56%nat in HT2. exact HT2.
Qed.

End WithCeiling.
