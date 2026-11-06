(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem. 
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.ct.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import RT_iface2 LibKitA ARun BnHeapA.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApUTacB.
From OSSVerify.Proofs.openssl.ct.lib.CtRepB Require Import ApATac ApBImg ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeKit TimeKit2 TimeKit3 TimeFmtPure TimeToTmDefs TimeToTmFeb W_time_to_tm_it.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeB Require Import TimeDefsA TimeKitA W_time_leavesA TimeToTmDefsA W_time_to_tm_itA W_time_to_tm_BA.
From OSSVerify.Proofs.openssl.ct.lib.CtKitB Require Import CtUbTabB CtUTacB.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtTimeB Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OSSVerify.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac rzstep := OSSVerify.Proofs.openssl.ct.lib.Lib.Step.zstep.    (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

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
Local Ltac notake := let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; repeat (rewrite Z.shiftl_mul_pow2 in K by lia); rewrite ?land64 in K; rewrite ?unsigned_lit in K by lia; first [lia | apply K; reflexivity] |]; try clear K.
Local Ltac take := let K := fresh "K" in if_cases K; zify_cond K;
  [| exfalso; repeat (rewrite Z.shiftl_mul_pow2 in K by lia); rewrite ?land64 in K; rewrite ?unsigned_lit in K by lia; first [lia | apply K; reflexivity]]; try clear K.

(* [comment removed for export] *)
Local Ltac forget_reg r := let v := reg_val r in let w := fresh "jk" in generalize v; intros w.

(* [comment removed for export] *)
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

Section WithRT.
Context {AR : ARun}.
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac fstep r := rstep; forget_reg r.

(* [comment removed for export] *)
Local Ltac iter_callA i m0 MU OFF ACCD ACCS ACCMIN ACCMAX :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let IT := fresh "IT" in
    pose proof (t2t_iterA i ltac:(lia)) as IT; unfold t2t_iterA_stmt in IT;
    eapply evt_cut;
    [ eapply IT; clear IT; try eassumption;
      first [ unfold t2t_lowA, MASK47, gcells, zb8; match goal with H : rw_cells _ mx _ _ |- _ => exact H end
            | eapply (acc_munch ctbsegs _ m0 mx); [ first [exact ACCD | exact ACCS | exact ACCMIN | exact ACCMAX] | exact MU | exact OFF | unfold A_MINTAB_A, A_MAXTAB_A; alia | unfold A_MINTAB_A, A_MAXTAB_A; alia ]
            | alia ]
    | clear IT; intros ms' PO; unfold t2t_iterA_post in PO; revert ms' PO; post_call ctbsegs mx;
      match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => let v := eval vm_compute in p in change p with v end ]
  end.

(* [comment removed for export] *)
Local Ltac zeller_tailB :=
  rstep; fstep 14%Z; fstep 16%Z; fstep 10%Z; fstep 16%Z; fstep 17%Z; fstep 14%Z; fstep 10%Z; fstep 5%Z; fstep 16%Z; fstep 14%Z;
  fstep 17%Z; fstep 10%Z; fstep 16%Z; fstep 17%Z; fstep 17%Z; fstep 10%Z; fstep 5%Z; fstep 15%Z; fstep 14%Z; fstep 17%Z; fstep 16%Z;
  fstep 10%Z; fstep 14%Z; fstep 13%Z; fstep 14%Z; fstep 10%Z; fstep 14%Z; fstep 14%Z; fstep 14%Z; fstep 10%Z; fstep 10%Z;
  rstep; fstep 13%Z; fstep 13%Z; fstep 13%Z; fstep 14%Z; fstep 13%Z; fstep 13%Z; fstep 14%Z; fstep 10%Z; fstep 10%Z; step;
  zstep; step; step.

(* [comment removed for export] *)
Local Ltac seg_finishB f :=
  brc;
  repeat match goal with H : rw_cells _ _ (f + 32) ?cs |- _ =>
    match cs with context [C4 ?v] => is_var v; rewrite <- (Z_to_bv_bv_unsigned v) in H end end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mz _) =>
    apply evt_done; eexists; eexists; unfold t2t_headA_post; do 19 eexists; exists mz; split; [reflexivity|];
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
    split; [unfold t2t_lowA, MASK47; eassumption| unfold TM_CELLS_A; eassumption]
  end.

Lemma t2t_segCA : forall (x1 sp gp x5 x6 x10 x11 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo spa f DA GS tm ms : Z) (t : tm6)
         (j0 j160 j168 junk : list byte) (g : nat),
  stk ctbsegs m lo spa -> mem_inv ctbsegs m -> ACEIL <= lo -> lo + 16 <= spa -> spa + 304 <= USTACK_TOP -> spa mod 16 = 0 ->
  SEGTOP_A <= ACEIL -> SHHI <= ACEIL -> ACEIL + STACK_WIN <= USTACK_TOP ->
  rw_cells ctbsegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] -> acc ctbsegs m DA 16 -> DA mod 8 = 0 ->
  0 < DA -> DA + 16 <= ACEIL ->
  rw_cells ctbsegs m GS (gcells t ms) -> acc ctbsegs m GS 19 -> GS mod 8 = 0 -> 0 < GS -> GS + 19 <= ACEIL ->
  rw_cells ctbsegs m spa (t2t_lowA j0 j160 j168 19 tm f DA GS (t_mon t - 1) (t_year t - 1900) g junk) ->
  acc ctbsegs m A_MINTAB_A 36 -> acc ctbsegs m A_MAXTAB_A 36 -> acc ctbsegs m A_MDAYS_A 48 -> acc ctbsegs m A_YDAYS_A 48 ->
  tm_valid t -> 0 <= ms < 1000 -> 0 <= f -> f + 128 <= ACEIL -> f mod 8 = 0 -> (f + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= f) ->
  (DA + 16 <= f + 32 \/ f + 32 + 56 <= DA) -> (GS + 19 <= f + 32 \/ f + 32 + 56 <= GS) ->
  rw_cells ctbsegs m (f + 32) (TM_CELLS_A 0 0 0 0 (t_mon t - 1) (t_year t - 1900) 0 0) ->
  evt ctbsegs (fun ms' => exists wd yd, t2t_headA_post sp spa gp F fc lo m f DA GS tm 4 (t_mon t - 1) (t_year t - 1900)
                 (TM_CELLS_A 0 0 0 (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd) j0 j160 j168 junk g ms')
    (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 (Z_to_bv 64 GS) sp (Z_to_bv 64 spa) x10 x11 (Z_to_bv 64 3) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 6) (Z_to_bv 64 (f + 32)) x22 x23 x24 (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 1) x28 x29 x30 x31)
        F (Z_to_bv 64 T2T_HEAD_A) fc None m (seg_rom ctbsegs)).
Proof.
  intros until g. intros ST MI CEIL LO TOP AL16 C1 C2 C3 HD ACCD ALD D0 DHI HS ACCS ALS S0 SHI LOW ACCMIN ACCMAX ACCMD ACCYD TV MSR F0 FHI F8 FG5 SEPD SEPS TMP.
  unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3, TOP. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu, C1, C2, C3, DHI, SHI, FHI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  pose proof (munch_refl [(lo, spa + 200); (f + 32, f + 32 + 56)]%Z m) as MU. pose proof (wmono_refl ctbsegs m) as WM.
  assert (OFF : offshW [(lo, spa + 200); (f + 32, f + 32 + 56)]%Z) by (cbn [offshW]; alia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO LO0 TOP; lia).
  assert (SEPT : f + 32 + 56 <= spa - 16 \/ spa + 304 <= f + 32) by (clear - FHI CEILu LO; lia).
  unfold TM_CELLS_A in TMP. unfold t2t_lowA, MASK47 in LOW. unfold gcells, zb8 in HS. unfold A_MDAYS_A in ACCMD. unfold A_YDAYS_A in ACCYD.
  (* [comment removed for export] *)
  iter_callA 3 m MU OFF ACCD ACCS ACCMIN ACCMAX. name_mem m1.
  pose proof (fld_range 3 t TV ltac:(lia)) as [F30 F31]. cbv [mintab maxtab Z.eqb orb Pos.eqb] in F30.
  change (fld 3 t) with (t_mday t) in *.
  match goal with H : rw_cells ctbsegs _ spa _ |- _ => rename H into FR1 end.
  (* [comment removed for export] *)
  yr_split 10%nat FR1. step. rewrite (sx32_signed (t_year t - 1900)) by lia. yr_join 10%nat FR1.
  step. step.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcx _ ?mx ?ro) =>
    apply (evt_cut ctbsegs (fun ms0 => exists a b c d : word,
              ms0 = MS (bvmap_set 17 d (bvmap_set 15 c (bvmap_set 10 b (bvmap_set 5 a R)))) FF (Z_to_bv 64 0x27448c) fcx None mx ro)) end.
  { step. if_cases KF; zify_cond KF.
    - (* [comment removed for export] *)
      assert (MN2 : t_mon t - 1 <> 1) by (intros E; apply KF; rewrite E; reflexivity).
      pose proof (mdaysA_cell m1 (t_mon t - 1) ltac:(assumption) ltac:(lia)) as MD. unfold A_MDAYS_A in MD.
      pose proof (mdaystab_ge (t_year t) (t_mon t - 1) ltac:(lia) MN2) as MDG. replace (t_mon t - 1 + 1) with (t_mon t) in MDG by lia.
      assert (MDR : 28 <= mdaystab (t_mon t - 1) <= 31).
      { unfold mdaystab. assert (H : t_mon t - 1 = 0 \/ t_mon t - 1 = 2 \/ t_mon t - 1 = 3 \/ t_mon t - 1 = 4 \/ t_mon t - 1 = 5 \/ t_mon t - 1 = 6
                          \/ t_mon t - 1 = 7 \/ t_mon t - 1 = 8 \/ t_mon t - 1 = 9 \/ t_mon t - 1 = 10 \/ t_mon t - 1 = 11 \/ t_mon t - 1 = 0) by lia.
        destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]; rewrite E; cbv; split; congruence. }
      rstep. rstep. notake.
      rstep. rzstep. rzstep. rzstep. rzstep. rstep. notake.
      rzstep. setreg 10%Z (Z_to_bv 64 (4 * (t_mon t - 1) + 482432)) ltac:(f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
      (* [comment removed for export] *)
      abX.
      rstep. rewrite (sx32_small (mdaystab (t_mon t - 1))) by lia.
      rstep. brF ltsz. step.
      apply evt_done. do 4 eexists. reflexivity.
    - (* [comment removed for export] *)
      assert (M2 : t_mon t = 2) by (revert KF; clear - VMO; intros KF; rewrite ?land64 in KF; Z.to_euclidean_division_equations; lia).
      pose proof VMD as VMD2. rewrite M2 in VMD2.
      rzstep. rzstep. rstep.
      rstep. notake. rstep. rzstep. setreg 10%Z (Z_to_bv 64 (t_year t - 1900 + 1900)) ltac:(w32k VY). rstep. brF ltsz.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      step. zstep. step. zstep. zstep. zstep. zstep. step.
      setreg 17%Z (Z_to_bv 64 (feb_rot (t_year t) 4)) ltac:(reflexivity).
      destruct (feb_casesB (t_year t) ltac:(lia)) as [[R4 D29]|[R4 FE]].
      + step. if_cases KL; zify_cond KL; rewrite ?feb_rot_land in KL; [| exfalso; clear - KL R4; lia]. clear KL.
        (* [comment removed for export] *)
        step. step. brF ltsz. apply evt_done. do 4 eexists. reflexivity.
      + step. if_cases KL; zify_cond KL; rewrite ?feb_rot_land in KL; [exfalso; clear - KL R4; lia|]. clear KL.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. step. zstep. zstep. zstep. zstep.
        setreg 10%Z (Z_to_bv 64 (days_in_month (t_year t) 2)) ltac:(rewrite <- FE; reflexivity).
        assert (DIM : 28 <= days_in_month (t_year t) 2 <= 29) by (unfold days_in_month; cbv [Z.eqb orb Pos.eqb]; destruct (leap_year _); lia).
        step. brF ltsz. step. apply evt_done. do 4 eexists. reflexivity. }
  intros ms' (ja & jb & jc & jd & ->).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. rzstep. setreg 15%Z (Z_to_bv 64 (t_year t - 1900 + 1900)) ltac:(w32k VY).
  step. name_mem m2.
  pose proof (ydaysA_cell m2 (t_mon t - 1) ltac:(assumption) ltac:(lia)) as YD. unfold A_YDAYS_A in YD.
  assert (YDR : 0 <= ydaystab (t_mon t - 1) <= 334).
  { unfold ydaystab. assert (H : t_mon t - 1 = 0 \/ t_mon t - 1 = 1 \/ t_mon t - 1 = 2 \/ t_mon t - 1 = 3 \/ t_mon t - 1 = 4 \/ t_mon t - 1 = 5 \/ t_mon t - 1 = 6
                      \/ t_mon t - 1 = 7 \/ t_mon t - 1 = 8 \/ t_mon t - 1 = 9 \/ t_mon t - 1 = 10 \/ t_mon t - 1 = 11) by lia.
    destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]; rewrite E; cbv; split; congruence. }
  rstep. brF ltsz.
  rstep. rzstep. rzstep. rzstep. rzstep. rstep. notake.
  rzstep. setreg 10%Z (Z_to_bv 64 (4 * (t_mon t - 1) + 483136)) ltac:(f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
  (* [comment removed for export] *)
  abX.
  rstep. rewrite (sx32_small (ydaystab (t_mon t - 1))) by lia.
  rzstep. setreg 16%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t)) ltac:(wmod).
  rzstep. setreg 10%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t)) ltac:(w32k YDR VMD DM).
  rstep. notake.
  rzstep. setreg 10%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t - 1)) ltac:(w32k YDR VMD DM).
  rzstep. setreg 16%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t)) ltac:(w32k YDR VMD DM).
  rstep. brF ltsz.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. step.
  destruct (Z_lt_ge_dec (t_mon t - 1) 2) as [MJ|MM].
  - (* [comment removed for export] *)
    step. take.
    rzstep. setreg 14%Z (Z_to_bv 64 (t_year t - 1900 + 1900 - 1)) ltac:(w32k VY). rstep. brF ltsz.
    rstep. fstep 10%Z. fstep 15%Z. step.
    zeller_tailB. seg_finishB f.
  - (* [comment removed for export] *)
    step. notake.
    rstep. fstep 14%Z. rstep. fstep 14%Z. fstep 16%Z. fstep 17%Z. fstep 16%Z. rstep.
    lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcx _ ?mx ?ro) =>
      apply (evt_cut ctbsegs (fun ms0 => exists (lb : Z) (b c : word), 0 <= lb <= 1 /\
                ms0 = MS (bvmap_set 17 c (bvmap_set 16 b (bvmap_set 14 (Z_to_bv 64 lb) R))) FF (Z_to_bv 64 0x274558) fcx None mx ro)) end.
    { rstep. if_cases KX; clear KX.
      + (* [comment removed for export] *)
        rstep. apply evt_done. exists 1. do 2 eexists. split; [lia| reflexivity].
      + (* [comment removed for export] *)
        fstep 16%Z. fstep 14%Z. fstep 14%Z. rzstep. rstep. rzstep. rzstep. rzstep. rstep.
        let v := reg_val 14%Z in apply evt_done; lazymatch v with Z_to_bv 64 ?lb => exists lb end.
        do 2 eexists. split; [| reflexivity].
        repeat match goal with |- context [Z.b2z (?x <? ?y)] => destruct (x <? y) end; cbv; split; congruence. }
    intros ms'' (lb & kb & kc & LB & ->).
    (* [comment removed for export] *)
    rzstep. setreg 16%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t - 1 + lb)) ltac:(wmod).
    rzstep. setreg 10%Z (Z_to_bv 64 (ydaystab (t_mon t - 1) + t_mday t - 1 + lb)) ltac:(w32k YDR VMD DM LB).
    rstep. notake.
    step. rstep. fstep 10%Z.
    zeller_tailB. seg_finishB f.
Qed.

End WithRT.
