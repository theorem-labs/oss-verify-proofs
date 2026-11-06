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
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs TimeToTmFeb W_time_leaves W_time_to_tm_A W_time_to_tm_it W_time_to_tm_B.
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
Ltac forget_reg r := let v := reg_val r in let w := fresh "jk" in generalize v; intros w.
Ltac fstep r := step; forget_reg r.

(* [comment removed for export] *)
Ltac zeller_tail :=
  fstep 16%Z; fstep 14%Z; fstep 15%Z; fstep 13%Z; fstep 15%Z; fstep 16%Z; fstep 14%Z; step; fstep 13%Z; fstep 17%Z;
  fstep 15%Z; fstep 14%Z; fstep 16%Z; fstep 13%Z; fstep 15%Z; fstep 17%Z; fstep 17%Z; fstep 13%Z; fstep 16%Z; fstep 12%Z;
  fstep 14%Z; fstep 10%Z; fstep 13%Z; fstep 15%Z; fstep 13%Z; fstep 10%Z; fstep 13%Z; fstep 10%Z; fstep 12%Z; fstep 12%Z;
  fstep 12%Z; fstep 10%Z; fstep 10%Z; step; fstep 12%Z; fstep 12%Z; fstep 12%Z; fstep 13%Z; fstep 12%Z; fstep 12%Z;
  fstep 13%Z; fstep 10%Z; fstep 10%Z;
  (* [comment removed for export] *)
  step; zstep; zstep; zstep; step.

(* [comment removed for export] *)
Ltac seg_finish :=
  let K := fresh "K" in
  if_cases K; zify_cond K; [| exfalso; first [apply K; reflexivity | lia]]; clear K;
  repeat match goal with H : rw_cells _ _ (bv_unsigned _ + -272) ?cs |- _ =>
    match cs with context [C4 ?v] => is_var v; rewrite <- (Z_to_bv_bv_unsigned v) in H end end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mz _) =>
    apply evt_done; eexists; eexists; unfold t2t_head_post; do 18 eexists; exists mz; split; [reflexivity|];
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
    unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47; cbn [app];
    match goal with H : rw_cells _ _ (bv_unsigned _ + -272) _ |- _ => exact H end
  end.

Section WithCeiling. Context {CE__ : Ceiling}.

Lemma t2t_segC : forall (x1 sp gp tp x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo DA GS tm ms : Z) (t : tm6) (sv : list cell),
  stk ctpsegs m lo (bv_unsigned sp + -272) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - TIME_TO_TM_STACK -> bv_unsigned sp < 2^63 ->
  ro_cells ctpsegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> (DA + 24 <= lo \/ bv_unsigned sp <= DA) -> DA + 24 <= 2^64 ->
  ro_cells ctpsegs m GS (gcells t ms) -> (GS + 19 <= lo \/ bv_unsigned sp <= GS) -> GS + 19 <= 2^63 ->
  rw_cells ctpsegs m (bv_unsigned sp + -272) (T2T_CONSTS 19 19 GS tm ++ TM_CELLS 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0 ++ sv) -> cells_size sv = 104%nat ->
  tm_valid t -> 0 <= ms < 1000 ->
  evt ctpsegs (fun ms' => exists wd yd, t2t_head_post sp gp tp F fc lo m DA GS tm t ms 4 (Z_to_bv 64 (t_year t - 1900)) (Z_to_bv 64 (t_mon t - 1))
                 (TM_CELLS 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd) sv ms')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -272)) gp tp x5 x6 x7 sp (Z_to_bv 64 12) x10 (Z_to_bv 64 3) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 DA) x19 x20 (Z_to_bv 64 7) x22 (Z_to_bv 64 (t_year t - 1900)) (Z_to_bv 64 6) (Z_to_bv 64 (t_mon t - 1)) (Z_to_bv 64 12) (Z_to_bv 64 (GS + 7)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x11d480) fc None m (seg_rom ctpsegs)).
Proof.
  intros until sv. intros ST MI GLO LO SP63 HD SEPD DHI HS SEPS SHI FR SVS TV MSR.
  pose proof LO as LO'. unfold TIME_TO_TM_STACK, GLOBALS_TOP in LO', GLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  unfold gcells, zb8 in HS. unfold T2T_CONSTS, TM_CELLS, A_MINTAB, MASK47 in FR. cbn [app] in FR.
  (* [comment removed for export] *)
  iter_call 3 (TM_CELLS 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0). name_mem m1.
  pose proof (fld_range 3 t TV ltac:(lia)) as [F30 F31]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F30.
  change (fld 3 t) with (t_mday t) in *.
  (* [comment removed for export] *)
  step.
  lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcx _ ?mx ?ro) =>
    apply (evt_cut ctpsegs (fun ms0 => exists a b c : word,
              ms0 = MS (bvmap_set 15 c (bvmap_set 14 b (bvmap_set 13 a R))) FF (Z_to_bv 64 1168932) fcx None mx ro)) end.
  { step. if_cases KF; zify_cond KF.
    - assert (MN2 : t_mon t - 1 <> 1) by (intros E; apply KF; rewrite E; reflexivity).
      pose proof (mdays_cell m1 (t_mon t - 1) ltac:(assumption) ltac:(lia)) as MD. unfold A_MDAYS in MD.
      pose proof (mdaystab_ge (t_year t) (t_mon t - 1) ltac:(lia) MN2) as MDG. replace (t_mon t - 1 + 1) with (t_mon t) in MDG by lia.
      assert (MDR : 28 <= mdaystab (t_mon t - 1) <= 31).
      { unfold mdaystab. assert (H : t_mon t - 1 = 0 \/ t_mon t - 1 = 2 \/ t_mon t - 1 = 3 \/ t_mon t - 1 = 4 \/ t_mon t - 1 = 5 \/ t_mon t - 1 = 6
                          \/ t_mon t - 1 = 7 \/ t_mon t - 1 = 8 \/ t_mon t - 1 = 9 \/ t_mon t - 1 = 10 \/ t_mon t - 1 = 11 \/ t_mon t - 1 = 0) by lia.
        destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]; rewrite E; cbv; split; congruence. }
      zstep. zstep. zstep. zstep. setreg 13%Z (Z_to_bv 64 (4 * (t_mon t - 1) + 268656)) ltac:(f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
     
      step. rewrite (sx32_small (mdaystab (t_mon t - 1))) by lia.
      step. brF ltsz. step.
      apply evt_done. do 3 eexists. reflexivity.
    - assert (M2 : t_mon t = 2) by (revert KF; clear - VMO; intros KF; rewrite ?land64 in KF; Z.to_euclidean_division_equations; lia).
      pose proof VMD as VMD2. rewrite M2 in VMD2.
      zstep. step. zstep. step. zstep. zstep. zstep. zstep. step.
      setreg 14%Z (Z_to_bv 64 (feb_rot (t_year t) 4)) ltac:(reflexivity).
      destruct (feb_cases (t_year t) ltac:(lia)) as [[R4 D29]|[R4 FE]].
      + step. if_cases KL; zify_cond KL; rewrite ?feb_rot_land in KL; [| exfalso; clear - KL R4; lia]. clear KL.
        step. step. brF ltsz. apply evt_done. do 3 eexists. reflexivity.
      + step. if_cases KL; zify_cond KL; rewrite ?feb_rot_land in KL; [exfalso; clear - KL R4; lia|]. clear KL.
        zstep. zstep. zstep. zstep. step. zstep. zstep. zstep. zstep.
        setreg 13%Z (Z_to_bv 64 (days_in_month (t_year t) 2)) ltac:(rewrite <- FE; reflexivity).
        assert (DIM : 28 <= days_in_month (t_year t) 2 <= 29) by (unfold days_in_month; cbv [Z.eqb orb Pos.eqb]; destruct (leap_year _); lia).
        step. brF ltsz. step. apply evt_done. do 3 eexists. reflexivity. }
 
  intros ms' (ja & jb & jc & ->).
  (* [comment removed for export] *)
  pose proof (ydays_cell m1 (t_mon t - 1) ltac:(assumption) ltac:(lia)) as YD. unfold A_YDAYS in YD.
  zstep. zstep. zstep. zstep. setreg 13%Z (Z_to_bv 64 (4 * (t_mon t - 1) + 268752)) ltac:(f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
  fstep 13%Z. fstep 13%Z. fstep 13%Z. step. step. step.
  destruct (Z_lt_ge_dec (t_mon t - 1) 2) as [MJ|MM].
  - (* [comment removed for export] *)
    step. brT ltsz. fstep 13%Z. fstep 12%Z. step.
    zeller_tail. seg_finish.
  - (* [comment removed for export] *)
    step. brF ltsz.
    fstep 12%Z. step. fstep 14%Z. step. fstep 14%Z. fstep 15%Z. fstep 16%Z. fstep 15%Z. step.
    lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcx _ ?mx ?ro) =>
      apply (evt_cut ctpsegs (fun ms0 => exists a b c : word,
                ms0 = MS (bvmap_set 16 c (bvmap_set 15 b (bvmap_set 14 a R))) FF (Z_to_bv 64 0x11d6ac) fcx None mx ro)) end.
    { step. if_cases KX; clear KX.
      + step. apply evt_done. do 3 eexists. reflexivity.
      + fstep 15%Z. fstep 14%Z. fstep 14%Z. fstep 15%Z. step. fstep 14%Z. fstep 15%Z. fstep 14%Z. step.
        apply evt_done. do 3 eexists. reflexivity. }
    intros ms' (ka & kb & kc & ->).
    (* [comment removed for export] *)
    fstep 13%Z. step. fstep 13%Z.
    zeller_tail. seg_finish.
Qed.

End WithCeiling.
