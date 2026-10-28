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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 TimeKit3 TimeFmtPure TimeToTmDefs TimeToTmFeb W_time_leaves W_time_to_tm_A W_time_to_tm_it W_time_to_tm_B.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac step := ual; ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ual; ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac rzstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac notake := let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; repeat (rewrite Z.shiftl_mul_pow2 in K by lia); rewrite ?land64 in K; rewrite ?unsigned_lit in K by lia; first [lia | apply K; reflexivity] |]; try clear K.
Local Ltac take := let K := fresh "K" in if_cases K; zify_cond K;
  [| exfalso; repeat (rewrite Z.shiftl_mul_pow2 in K by lia); rewrite ?land64 in K; rewrite ?unsigned_lit in K by lia; first [lia | apply K; reflexivity]]; try clear K.

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
Ltac forget_reg r := let v := reg_val r in let w := fresh "jk" in generalize v; intros w.
Ltac fstep r := step; forget_reg r.

(* [comment removed for export] *)
Ltac zeller_tail :=
  do 45 rzstep;
  (* [comment removed for export] *)
  rzstep.

(* [comment removed for export] *)
Ltac seg_finish :=
  let K := fresh "K" in
  if_cases K; zify_cond K; [| exfalso; first [apply K; reflexivity | lia]]; clear K;
  repeat match goal with H : rw_cells _ _ (bv_unsigned _ + -256) ?cs |- _ =>
    match cs with context [C4 ?v] => tryif is_var v then fail else
      lazymatch v with Z_to_bv 64 _ => fail | _ => let w := fresh "wv" in remember v as w eqn:EW; clear EW end end end;
  repeat match goal with H : rw_cells _ _ (bv_unsigned _ + -256) ?cs |- _ =>
    match cs with context [C4 ?v] => is_var v; rewrite <- (Z_to_bv_bv_unsigned v) in H end end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mz _) =>
    apply evt_done; eexists; eexists; unfold t2t_head_post; do 19 eexists; exists mz; split; [reflexivity|];
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
    unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47; cbn [app];
    match goal with H : rw_cells _ _ (bv_unsigned _ + -256) _ |- _ => exact H end
  end.

Definition feb_md2B (y : Z) : Z :=
  bv_swrap 32 (Z.land (Z.b2z (42949672 <? feb_rot y 2)) (Z.b2z (Z.land (y - 1900 + 1900) 3 <? 1)) + 28).
Definition feb_mdB (y : Z) : Z := if feb_rot y 4 <? 10737419 then 29 else feb_md2B y.
Definition feb_mdB_checkf (y : Z) : bool := feb_mdB y =? days_in_month y 2.
Lemma feb_mdB_check_all : check_from feb_mdB_checkf (Z.to_nat 10000) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma feb_mdB_ok : forall y, 0 <= y <= 9999 -> feb_mdB y = days_in_month y 2.
Proof.
  intros y Hy. apply Z.eqb_eq. apply (check_from_ok feb_mdB_checkf (Z.to_nat 10000) 0); [exact feb_mdB_check_all| rewrite Z2Nat.id by lia; lia].
Qed.
Lemma feb_casesB : forall y, 0 <= y <= 9999 ->
  (feb_rot y 4 < 10737419 /\ days_in_month y 2 = 29) \/ (10737419 <= feb_rot y 4 /\ feb_md2B y = days_in_month y 2).
Proof.
  intros y Hy. pose proof (feb_mdB_ok y Hy) as E. unfold feb_mdB in E.
  destruct (Z.ltb_spec (feb_rot y 4) 10737419); [left| right]; split; lia.
Qed.

Section WithCeiling. Context {CE__ : Ceiling}.

Lemma t2t_segC : forall (x1 sp gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms : Z) (t : tm6) (sv : list cell),
  stk ctusegs m lo (bv_unsigned sp + -256) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctusegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctusegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> 0 < GS -> GS + 19 <= 2^63 ->
  rw_cells ctusegs m (bv_unsigned sp + -256) (T2T_CONSTS 19 (t_mon t - 1) (t_year t - 1900) tm ++ TM_CELLS 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0 ++ sv) -> cells_size sv = 104%nat ->
  tm_valid t -> 0 <= ms < 1000 ->
  evt ctusegs (fun ms' => exists wd yd, t2t_head_post sp gp tp F fc lo m DA GS tm t ms 4 (t_mon t - 1) (t_year t - 1900)
                 (TM_CELLS 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd) sv ms')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 3) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) (Z_to_bv 64 24) (Z_to_bv 64 19) x21 x22 (Z_to_bv 64 1) (Z_to_bv 64 6) (Z_to_bv 64 GS) (Z_to_bv 64 12) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12c298) fc None m (seg_rom ctusegs)).
Proof.
  intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS G0 SHI FR SVS TV MSR.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  unfold gcells, zb8 in HS. unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47 in FR. cbn [app] in FR.
  (* [comment removed for export] *)
  iter_call 3 (TM_CELLS 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0) (t_mon t - 1) (t_year t - 1900). name_mem m1.
  pose proof (fld_range 3 t TV ltac:(lia)) as [F30 F31]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F30.
  change (fld 3 t) with (t_mday t) in *.
  match goal with H : rw_cells ctusegs _ (bv_unsigned sp + -256) _ |- _ => rename H into FR1 end. yr_split 9%nat FR1. step. rewrite (sx32_signed (t_year t - 1900)) by lia. yr_join 9%nat FR1.
  zstep. zstep.
  lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcx _ ?mx ?ro) =>
    apply (evt_cut ctusegs (fun ms0 => exists a b c d : word,
              ms0 = MS (bvmap_set 17 d (bvmap_set 16 c (bvmap_set 15 b (bvmap_set 13 a R)))) FF (Z_to_bv 64 0x12c500) fcx None mx ro)) end.
  { zstep. if_cases KF; zify_cond KF.
  - assert (MN2 : t_mon t - 1 <> 1) by (intros E; apply KF; rewrite E; reflexivity).
    pose proof (mdays_cell m1 (t_mon t - 1) ltac:(assumption) ltac:(lia)) as MD. unfold A_MDAYS in MD.
    pose proof (mdaystab_ge (t_year t) (t_mon t - 1) ltac:(lia) MN2) as MDG. replace (t_mon t - 1 + 1) with (t_mon t) in MDG by lia.
    assert (MDR : 28 <= mdaystab (t_mon t - 1) <= 31).
    { unfold mdaystab. assert (H : t_mon t - 1 = 0 \/ t_mon t - 1 = 2 \/ t_mon t - 1 = 3 \/ t_mon t - 1 = 4 \/ t_mon t - 1 = 5 \/ t_mon t - 1 = 6
                        \/ t_mon t - 1 = 7 \/ t_mon t - 1 = 8 \/ t_mon t - 1 = 9 \/ t_mon t - 1 = 10 \/ t_mon t - 1 = 11 \/ t_mon t - 1 = 0) by lia.
      destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]; rewrite E; cbv; split; congruence. }
    do 5 zstep. setreg 13%Z (Z_to_bv 64 (4 * (t_mon t - 1) + 268624)) ltac:(f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
    rzstep. rewrite (sx32_small (mdaystab (t_mon t - 1))) by lia. rzstep. brF ltsz.
    rzstep. apply evt_done. do 4 eexists. reflexivity.
  - assert (M2 : t_mon t = 2) by (revert KF; clear - VMO; intros KF; rewrite ?land64 in KF; Z.to_euclidean_division_equations; lia).
    pose proof VMD as VMD2. rewrite M2 in VMD2.
    rzstep. rzstep. rzstep. uchk. rzstep. rzstep. setreg 13%Z (Z_to_bv 64 (t_year t - 1900 + 1900)) ltac:(w32k VY).
    uchk. do 8 rzstep.
    setreg 16%Z (Z_to_bv 64 (feb_rot (t_year t) 4)) ltac:(reflexivity).
    destruct (feb_casesB (t_year t) ltac:(lia)) as [[R4 D29]|[R4 FE]].
    + rzstep. if_cases KL; zify_cond KL; rewrite ?feb_rot_land in KL; [| exfalso; clear - KL R4; lia]. clear KL.
      rzstep. rzstep. brF ltsz.
      apply evt_done. do 4 eexists. reflexivity.
    + rzstep. if_cases KL; zify_cond KL; rewrite ?feb_rot_land in KL; [exfalso; clear - KL R4; lia|]. clear KL.
      do 9 rzstep. setreg 13%Z (Z_to_bv 64 (days_in_month (t_year t) 2)) ltac:(rewrite <- FE; reflexivity).
      assert (DIM : 28 <= days_in_month (t_year t) 2 <= 29) by (unfold days_in_month; cbv [Z.eqb orb Pos.eqb]; destruct (leap_year _); lia).
      rzstep. brF ltsz.
      rzstep. apply evt_done. do 4 eexists. reflexivity. }
  intros ms' (ja & jb & jc & jd & ->).
  rzstep. rzstep. setreg 13%Z (Z_to_bv 64 (t_year t - 1900 + 1900)) ltac:(w32k VY). rzstep. uchk.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (ydays_cell mx (t_mon t - 1) ltac:(assumption) ltac:(lia)) as YD end. unfold A_YDAYS in YD.
  rzstep. rzstep. rzstep. rzstep. rzstep. uchk. rzstep.
  setreg 14%Z (Z_to_bv 64 (4 * (t_mon t - 1) + 268720)) ltac:(f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
  assert (YDR : 0 <= ydaystab (t_mon t - 1) <= 334).
  { unfold ydaystab. assert (H : t_mon t - 1 = 0 \/ t_mon t - 1 = 1 \/ t_mon t - 1 = 2 \/ t_mon t - 1 = 3 \/ t_mon t - 1 = 4 \/ t_mon t - 1 = 5 \/ t_mon t - 1 = 6
                      \/ t_mon t - 1 = 7 \/ t_mon t - 1 = 8 \/ t_mon t - 1 = 9 \/ t_mon t - 1 = 10 \/ t_mon t - 1 = 11) by lia.
    destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]; rewrite E; cbv; split; congruence. }
  rzstep. rewrite (sx32_small (ydaystab (t_mon t - 1))) by lia.
  rzstep.
  rzstep. setreg 12%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t)) ltac:(w32k YDR VMD DM).
  uchk.
  rzstep. setreg 12%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t - 1)) ltac:(w32k YDR VMD DM).
  rzstep. setreg 14%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t)) ltac:(w32k YDR VMD DM).
  rzstep. uchk.
  rzstep. rzstep. rzstep.
  destruct (Z_lt_ge_dec (t_mon t - 1) 2) as [MJ|MM].
  - take.
    rzstep. uchk. rzstep. rzstep. rzstep.
    zeller_tail. seg_finish.
  - notake.
    do 8 rzstep.
    lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcx _ ?mx ?ro) =>
      apply (evt_cut ctusegs (fun ms0 => exists (lb : Z) (b c : word), 0 <= lb <= 1 /\
                ms0 = MS (bvmap_set 16 c (bvmap_set 15 b (bvmap_set 14 (Z_to_bv 64 lb) R))) FF (Z_to_bv 64 0x12c5b8) fcx None mx ro)) end.
    { rzstep. if_cases KX; clear KX.
      + rzstep. apply evt_done. exists 1. do 2 eexists. split; [lia| reflexivity].
      + do 9 rzstep. apply evt_done. do 3 eexists. split; [| reflexivity].
        repeat match goal with |- context [Z.b2z ?c] => lazymatch c with true => fail | false => fail | _ => destruct c end end; cbv; split; intro HH; discriminate HH. }
    intros ms' (lb & kb & kc & LB & ->).
    rzstep. rzstep. setreg 12%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t - 1 + lb)) ltac:(w32k YDR VMD DM LB).
    uchk. rzstep. rzstep. rzstep.
    zeller_tail. seg_finish.
Qed.

End WithCeiling.
