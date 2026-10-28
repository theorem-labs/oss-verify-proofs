(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit F_memcpy F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs TimeToTmFeb W_time_leaves W_time_to_tm_A W_time_to_tm_it W_time_to_tm_B W_time_to_tm_C.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac step := ual; ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ual; ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.

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
    | intros ms' PO; unfold leaf16_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO; post_call ctusegs mx ]
  end.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition t2t_fin_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte)
    (DA GS tm : Z) (t : tm6) (wd yd : Z) (sv : list cell) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
                  x18 (Z_to_bv 64 1) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x12c770) fc None m' (seg_rom ctusegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -256)
    /\ rw_cells ctusegs m' (bv_unsigned sp + -256)
         (T2T_CONSTS 19 (t_mon t - 1) (t_year t - 1900) tm ++ TM_CELLS (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd ++ sv).

Lemma t2t_segD : forall (x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms wd yd : Z) (t : tm6) (sv : list cell),
  stk ctusegs m lo (bv_unsigned sp + -256) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctusegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctusegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> 0 < GS -> GS + 19 <= 2^63 ->
  rw_cells ctusegs m (bv_unsigned sp + -256) (T2T_CONSTS 19 (t_mon t - 1) (t_year t - 1900) tm ++ TM_CELLS 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd ++ sv) -> cells_size sv = 104%nat ->
  tm_valid t -> 0 <= ms < 1000 -> 0 <= tm < 2^64 ->
  evt ctusegs (t2t_fin_post sp gp tp F fc lo m DA GS tm t wd yd sv)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 4) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) (Z_to_bv 64 24) (Z_to_bv 64 19) x21 x22 (Z_to_bv 64 1) (Z_to_bv 64 8) (Z_to_bv 64 GS) (Z_to_bv 64 12) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12c298) fc None m (seg_rom ctusegs)).
Proof.
  intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS G0 SHI FR SVS TV MSR TMR.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  unfold gcells, zb8 in HS. unfold CH_Z, CH_DOT in HS. unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47 in FR. cbn [app] in FR.
  (* [comment removed for export] *)
  iter_call 4 (TM_CELLS 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd) (t_mon t - 1) (t_year t - 1900). name_mem m1.
  change (fld 4 t) with (t_hour t) in *.
  zstep. zstep. zstep. zstep. zstep. btaken.
  (* [comment removed for export] *)
  iter_call 5 (TM_CELLS 0 0 (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd) (t_mon t - 1) (t_year t - 1900). name_mem m2.
  change (fld 5 t) with (t_min t) in *.
  zstep. zstep. zstep. zstep. zstep. btaken.
  (* [comment removed for export] *)
  iter_call 6 (TM_CELLS 0 (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd) (t_mon t - 1) (t_year t - 1900). name_mem m3.
  change (fld 6 t) with (t_sec t) in *.
  zstep. zstep. zstep. zstep. zstep. bnot.
  (* [comment removed for export] *)
  zstep. zstep. zstep. bnot. zstep. zstep. zstep. zstep. bnot. zstep. bnot.
  zstep. zstep. zstep. zstep. zstep. zstep.
  pose proof (digit_range (ms / 100) ltac:(split; [apply Z.div_pos; lia| enough (ms / 100 < 10) by lia; apply Z.div_lt_upper_bound; lia])) as DG1.
  pose proof (digit_range ((ms / 10) mod 10) ltac:(pose proof (Z.mod_pos_bound (ms / 10) 10 ltac:(lia)); lia)) as DG2.
  pose proof (digit_range (ms mod 10) ltac:(pose proof (Z.mod_pos_bound ms 10 ltac:(lia)); lia)) as DG3.
  (* [comment removed for export] *)
  change (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (digit (ms / 100))))) with (zxb (Z_to_bv 8 (digit (ms / 100)))).
  rewrite (zxb_lit (digit (ms / 100))) by lia. isdig_call (digit (ms / 100)). rewrite (isdigit_range (digit (ms / 100))) by lia.
  zstep. bnot. zstep. zstep. zstep. zstep. bnot.
  zstep. zstep. zstep. zstep.
  change (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (digit ((ms / 10) mod 10))))) with (zxb (Z_to_bv 8 (digit ((ms / 10) mod 10)))).
  rewrite (zxb_lit (digit ((ms / 10) mod 10))) by lia. isdig_call (digit ((ms / 10) mod 10)). rewrite (isdigit_range (digit ((ms / 10) mod 10))) by lia.
  zstep. bnot. zstep. zstep. zstep. zstep. bnot.
  zstep. zstep. zstep. zstep.
  change (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (digit (ms mod 10))))) with (zxb (Z_to_bv 8 (digit (ms mod 10)))).
  rewrite (zxb_lit (digit (ms mod 10))) by lia. isdig_call (digit (ms mod 10)). rewrite (isdigit_range (digit (ms mod 10))) by lia.
  zstep. bnot. zstep. zstep. zstep. zstep. bnot.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. isdig_call 90. rewrite (isdigit_false 90) by lia.
  zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. bnot. zstep. zstep. zstep. bnot.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. bnot. zstep. zstep. bnot. zstep. zstep. bnot. zstep. zstep. bnot. zstep.
  name_mem m9. apply evt_done. unfold t2t_fin_post. do 26 eexists. exists m9. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47. cbn [app]. assumption.
Qed.

(* [comment removed for export] *)
Lemma t2t_end0 : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo mo yr : Z) (tmc : list cell),
  stk ctusegs m lo (bv_unsigned sp + -256) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  rw_cells ctusegs m (bv_unsigned sp + -256) (T2T_CONSTS 19 mo yr 0 ++ tmc ++ T2T_SAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> cells_size tmc = 56%nat ->
  evt ctusegs (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 1) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12c770) fc None m (seg_rom ctusegs)).
Proof.
  intros until tmc. intros ST MI GLO LO SP63 FR TMS.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  pose proof (proj1 (rw_cells_app m _ _ _) FR) as [FRC FRR]. pose proof (proj1 (rw_cells_app m _ _ _) FRR) as [FRT FRS]. clear FR FRR.
  destruct (rw_cells_forget _ _ _ _ FRT) as [junk FRT']. clear FRT. rewrite TMS in FRT', FRS.
  change (Z.of_nat 56) with (Z.of_nat (cells_size [CB 56%nat junk])) in FRS.
  pose proof (proj2 (rw_cells_app m _ _ _) (conj FRT' FRS)) as FRR. pose proof (proj2 (rw_cells_app m _ _ _) (conj FRC FRR)) as FR. clear FRC FRT' FRS FRR.
  unfold T2T_CONSTS, T2T_SAVED, A_MINTAB, MASK47 in FR. cbn [app cells_size csize Nat.add] in FR.
  (* [comment removed for export] *)
  step. step. btaken.
  step. do 13 step. step. release_frame FR ST (bv_unsigned sp). step.
  name_mem m2. apply evt_done. do 14 eexists. exists m2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

(* [comment removed for export] *)
Lemma t2t_end1 : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo mo yr tm : Z) (tmc : list cell) (junk : list byte),
  stk ctusegs m lo (bv_unsigned sp + -256) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  rw_cells ctusegs m (bv_unsigned sp + -256) (T2T_CONSTS 19 mo yr tm ++ tmc ++ T2T_SAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> cells_size tmc = 56%nat -> cells_wf tmc ->
  0 < tm -> bv_unsigned sp <= tm -> tm + 56 <= 2^63 -> rw_cells ctusegs m tm [CB 56%nat junk] ->
  evt ctusegs (fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(lo, bv_unsigned sp); (tm, tm + 56)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' tm [CB 56%nat (cells_bytes tmc)])
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 1) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12c770) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk. intros ST MI GLO LO SP63 FR TMS TMW TM0 TMLO TMHI HT.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (tm, tm + 56)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
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
  replace (bv_unsigned sp + -256 + Z.of_nat 96) with (bv_unsigned sp + -160) in FRT' by lia.
  (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. try clear K0.
  step. step. step. step.
  pose proof (proj2 (proj1 FRT')) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
  name_mem m1. eapply evt_cut.
  { eapply memcpy_spec with (src := cells_bytes tmc) (junk := junk); rewrite ?unsigned_lit by lia;
      [ exact SRCB | rewrite (cells_bytes_length _ TMW), TMS; reflexivity | exact HT | lia | assumption ]. }
  intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO. post_call ctusegs m1.
  match goal with H : rw_cells ctusegs _ tm [CB _ (cells_bytes tmc)] |- _ => rename H into HT2 end.
  (* [comment removed for export] *)
  step. step. do 13 step. step.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -256) |- _ => release_frame FR H (bv_unsigned sp) end. step.
  name_mem m2. apply evt_done. do 14 eexists. exists m2. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  change (Z.to_nat 56) with 56%nat in HT2. exact HT2.
Qed.

End WithCeiling.
