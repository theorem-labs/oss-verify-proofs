(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_fsD B0_cmp_fsE B0_cmp_fsF B0_cmp_fsW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Lemma med_idx_eq : forall ec fm r3 lo hi,
  (if r3 =? 0 then rd32 ec (rd32 fm lo) else if r3 =? 1 then rd32 ec (rd32 fm (Z.shiftr (lo + hi) 1)) else rd32 ec (rd32 fm hi))%Z
  = rd32 ec (rd32 fm (med_idx r3 lo hi)).
Proof.
  intros. unfold med_idx. destruct (r3 =? 0)%Z; [reflexivity|]. destruct (r3 =? 1)%Z; [|reflexivity].
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma fqs_iter_unfold : forall ec fm sp slo shi rr,
  fqs_iter ec (FQS fm sp slo shi rr) =
  (let lo := zget slo (sp - 1) in let hi := zget shi (sp - 1) in
   if (hi - lo <? 10)%Z then FQS (fallbackSimpleSort fm ec lo hi) (sp - 1) slo shi rr
   else let r' := (((rr * 7621) + 1) mod 32768)%Z in
        let med := rd32 ec (rd32 fm (med_idx (r' mod 3) lo hi)) in
        let sz := Z.to_nat (hi - lo + 1) in
        qtail sp lo hi r' slo shi (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi))).
Proof.
  intros. unfold fqs_iter, qtail. cbn [fq_fm fq_sp fq_slo fq_shi fq_r]. rewrite <- med_idx_eq. reflexivity.
Qed.

Section B0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop. Variables Hh l1 r1 nnd : Z.
  Variables (ec : zarr) (Jlo Jhi : list byte).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation SLO := (ae_SLO Y). Notation SHI := (ae_SHI Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NA2 := (18446744073709551615 - fe_A2 X)%Z.
  Hypothesis ECR : ec_range ec nb. Hypothesis ECOK' : zbok ec.
  Hypothesis LJlo : Z.of_nat (length Jlo) = 400%Z. Hypothesis LJhi : Z.of_nat (length Jhi) = 400%Z.
  (* [comment removed for export] *)
  Notation QS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 1) (Z_to_bv 64 A2) (Z_to_bv 64 r1) (Z_to_bv 64 A1) cSB (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) (Z_to_bv 64 l1) (Z_to_bv 64 NA2) t3 t4 t5 t6).
  Notation WQ := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (ae_P Y + 112, ae_P Y + 216); (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400)]%Z.
  (* [comment removed for export] *)

  Lemma B0_qloop : forall (f : nat) (q qfin : fqs) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 v128 v136 v152 v160 v208 : word),
    (0 < fq_sp q)%Z -> (0 <= fq_r q < 32768)%Z -> fm_range (fq_fm q) nb -> zbok (fq_fm q) -> stk_def (fq_slo q) (fq_shi q) (fq_sp q) ->
    (forall v, qfacts nb (fqs_loop v ec q)) -> fqs_loop f ec q = qfin -> (fq_sp qfin <= 0)%Z ->
    u8arr b0segs m A1 (zb8 (fq_fm q) ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) ->
    rw_cells b0segs m (P + 72) (SCb X Y nnd Hh (Z_to_bv 64 (fq_r q)) v128 v136 v152 v160 v208) ->
    u32arr b0segs m SHI (ovw (fq_shi q) Jhi 100) -> u32arr b0segs m SLO (ovw (fq_slo q) Jlo 100) -> mem_inv b0segs m ->
    munch WQ me m -> wmono b0segs me m ->
    shzW b0segs WQ me A1 (A1 + ARR1_SIZE) -> shzW b0segs WQ me A2 (A2 + ARR2_SIZE) ->
    shzW b0segs WQ me SLO (SLO + 400) -> shzW b0segs WQ me SHI (SHI + 400) ->
    (forall m' (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 u128 u136 u152 u160 u208 : word),
      u8arr b0segs m' A1 (zb8 (fq_fm qfin) ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) ->
      rw_cells b0segs m' (P + 72) (SCb X Y nnd Hh (Z_to_bv 64 (fq_r qfin)) u128 u136 u152 u160 u208) ->
      u32arr b0segs m' SHI (ovw (fq_shi qfin) Jhi 100) -> u32arr b0segs m' SLO (ovw (fq_slo qfin) Jlo 100) -> mem_inv b0segs m' ->
      munch WQ me m' -> wmono b0segs me m' -> fm_range (fq_fm qfin) nb -> zbok (fq_fm qfin) -> (0 <= fq_r qfin < 32768)%Z ->
      evt b0segs Q (MS (QS x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (Z_to_bv 64 0xa6a0c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (fq_sp q)) a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa5a18) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros q qfin me m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 v128 v136 v152 v160 v208 Hsp Hr FMR FMOK' SD QFx RES FIN AR1 AR2 SC SHIc SLOc MI MU WMo SH1 SH2 SHl SHh K.
    { cbn [fqs_loop] in RES. subst qfin. lia. }
    rewrite fqs_loop_S in RES. replace (0 <? fq_sp q)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia).
    cps_pose (QFx 0%nat ltac:(cbn; lia)) as (Hsp98 & Glo0 & Glh & Ghi). cbn [fqs_loop] in Hsp98, Glo0, Glh, Ghi.
    assert (QF' : forall v, qfacts nb (fqs_loop v ec (fqs_iter ec q))).
    { intros v. specialize (QFx (S v)). rewrite fqs_loop_S in QFx. replace (0 <? fq_sp q)%Z with true in QFx by (symmetry; apply Z.ltb_lt; lia). exact QFx. }
    clear QFx. destruct q as [fm sp slo shi rr]. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in *.
    set (lo := zget slo (sp - 1)) in *. set (hi := zget shi (sp - 1)) in *.
    fsenv_open XOK. afenv_open YOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & AP1F & AP2F).
    pose proof YSEP as SPY. unfold afenv_sep, apartv in SPY. cps_destruct SPY as (AP1B & AP2B & _).
    bz_params. unfold SCb in SC.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length shi Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length slo Jlo 100 ltac:(lia)) as LL.
    destruct (SD (sp - 1)%Z ltac:(lia)) as [Dlo Dhi].
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    (* [comment removed for export] *)
    brun_to 0xa5a58%Z.
    lazymatch goal with |- context [Z_to_bv 64 (ae_SLO Y + ?x)] => replace (ae_SLO Y + x)%Z with (SLO + 4 * (sp - 1))%Z by lia end.
    (* [comment removed for export] *)
    brun_to 0xa5a60%Z.
    pose proof (saddr_intro (SLO + 4 * (sp - 1))) as ASlo. set (SHlo := ((SLO + 4 * (sp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHlo.
    wstep.
    (* [comment removed for export] *)
    brun_to 0xa5a80%Z.
    lazymatch goal with |- context [Z_to_bv 64 (ae_SHI Y + ?x)] => replace (ae_SHI Y + x)%Z with (SHI + 4 * (sp - 1))%Z by lia end.
    (* [comment removed for export] *)
    brun_to 0xa5a88%Z.
    pose proof (saddr_intro (SHI + 4 * (sp - 1))) as AShi. set (SHhi := ((SHI + 4 * (sp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHhi.
    wstep.
    (* [comment removed for export] *)
    brun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read b0segs mm SLO slo Jlo 100 (sp - 1) _ SLOc ltac:(lia) Dlo ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. fold lo. try rewrite (sx32_of_Z_signed lo) by lia. try rewrite (sx32_of_Z lo) by lia.
    (* [comment removed for export] *)
    brun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovw_read b0segs mm SHI shi Jhi 100 (sp - 1) _ SHIc ltac:(lia) Dhi ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. fold hi. try rewrite (sx32_of_Z_signed hi) by lia. try rewrite (sx32_of_Z hi) by lia.
    (* [comment removed for export] *)
    brun_to 0xa5ab4%Z. demod. try rewrite (sx32_of_Z_signed (hi - lo)) by lia.
    rewrite fqs_iter_unfold in RES, QF'. cbv zeta in RES, QF'. fold lo hi in RES, QF'.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* [comment removed for export] *)
    wstep; if_cases Kd; zify_cond_z Kd.
    - (* [comment removed for export] *)
      replace (hi - lo <? 10)%Z with false in RES, QF' by (symmetry; apply Z.ltb_ge; lia).
      enter_with (B0_qmed X Y Q Hh sp l1 r1 nnd SHlo SHhi XOK XSEP YOK hi lo rr fm ec m1 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| unfold SCb; exact SC| exact MI| apply munch_refl| apply wmono_refl| | |].
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
      intros m2 y12 y13 y17. cbv zeta. intros AR1_1 AR2_1 SC1 MI1 MU1 WM1 Hmed.
      clear AR1 AR2 SC MI. transport_after_call b0segs m1 m2 MU1 WM1.
      set (r' := ((rr * 7621 + 1) mod 32768)%Z) in *. set (med := rd32 ec (rd32 fm (med_idx (r' mod 3) lo hi))) in *.
      set (sz := Z.to_nat (hi - lo + 1)) in *.
      assert (Hr' : (0 <= r' < 32768)%Z) by (subst r'; apply Z.mod_pos_bound; lia).
      enter_with (B0_ploop X Y Q l1 r1 nnd Hh (Z_to_bv 64 r') (Z_to_bv 64 SHhi) (Z_to_bv 64 SHlo) (Z_to_bv 64 sp) (Z_to_bv 64 (SLO + 4 * (sp - 1))) (Z_to_bv 64 (SHI + 4 * (sp - 1)))
                    (Z_to_bv 64 (sp - 1)) XOK XSEP YOK (S sz) (FP fm lo hi lo hi) med hi lo ec m2 m2 _ _ _ _ _ _ _ _ sz (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi)));
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi];
        [st_eq| lia| lia| unfold fp_ok; cbn; lia| lia| lia| reflexivity| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1_1| exact AR2_1| exact SC1| exact MI1| apply munch_refl| apply wmono_refl| | |].
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
      (* [comment removed for export] *)
      unfold KBbrk. intros m3 z1 z5 z6 z12 z13 z17 z28 z31 AR1_2 AR2_2 SC2 MI2 MU2 WM2 FMR2 FMOK2 OK2 BR2. bz_params.
      clear AR1_1 AR2_1 SC1 MI1 MU1 WM1. transport_after_call b0segs m2 m3 MU2 WM2.
      enter_with (B0_qpush X Y Q Hh sp l1 r1 nnd SHlo SHhi XOK YOK YSEP ASlo AShi _ med hi lo r' slo shi Jlo Jhi m3 m3 _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| exact OK2| exact BR2| exact FMR2| exact FMOK2| exact SD| reflexivity| reflexivity| exact LJlo| exact LJhi| exact AR1_2| exact SC2| exact SHIc| exact SLOc| exact MI2| apply munch_refl| apply wmono_refl| | | |].
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SHl| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SHh| exact MU| sub_fp_solve| lia| lia]. }
      intros m4 y1 y5 y6 y7 y10 y11 y12' y13' y14 y15 y17' y28 y29 y30 y31. cbv zeta. intros AR1_3 SC3 SHI3 SLO3 MI3 MU3 WM3 FMR3 FMOK3 SD3 Hsp3 Hr3. bz_params.
      clear AR1_2 MI2 SC2 SHIc SLOc MU2 WM2. transport_after_call b0segs m3 m4 MU3 WM3.
      set (q' := qtail sp lo hi r' slo shi (fpart_loop (S sz) sz ec med (FP fm lo hi lo hi))) in *.
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (fq_sp q')) by lia. wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        enter_with (IH q' qfin me m4); [st_eq| lia| rewrite Hr3; lia| exact FMR3| exact FMOK3| exact SD3| exact QF'| exact RES| exact FIN| exact AR1_3| exact AR2_2| rewrite Hr3; exact SC3| exact SHI3| exact SLO3| exact MI3| exact MU| exact WMo| exact SH1| exact SH2| exact SHl| exact SHh| exact K].
      + (* [comment removed for export] *)
        apply Bool.andb_false_iff in Kc. destruct Kc as [Kc|Kc]; apply Z.ltb_ge in Kc; [| exfalso; lia].
        wstep.
        assert (E : qfin = q').
        { clearbody q'. clear -RES Kc. destruct f; [cbn [fqs_loop] in RES; symmetry; exact RES|]. rewrite fqs_loop_S in RES.
          replace (0 <? fq_sp q')%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). symmetry; exact RES. }
        clear RES. subst qfin.
        enter_with (K m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1_3| exact AR2_2| rewrite Hr3; exact SC3| exact SHI3| exact SLO3| exact MI3| exact MU| exact WMo| exact FMR3| exact FMOK3| rewrite Hr3; lia].
    - (* [comment removed for export] *)
      replace (hi - lo <? 10)%Z with true in RES, QF' by (symmetry; apply Z.ltb_lt; lia).
      wstep.
      enter_with (B0_fss X Y Q l1 r1 XOK XSEP YOK hi lo fm ec m1 m1 _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact MI| apply munch_refl| apply wmono_refl| | |].
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
      intros m' x5 x6 x7 x10 x11 x12 x13 x17. cbv zeta. intros AR1' AR2' MI' MU' WM' FMR' FMOK''. bz_params.
      clear AR1 AR2 MI. transport_after_call b0segs m1 m' MU' WM'.
      (* [comment removed for export] *)
      wstep; if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        enter_with (IH (FQS (fallbackSimpleSort fm ec lo hi) (sp - 1) slo shi rr) qfin me m'); cbn [fq_fm fq_sp fq_slo fq_shi fq_r];
          [st_eq| lia| lia| exact FMR'| exact FMOK''| | exact QF'| exact RES| exact FIN| exact AR1'| exact AR2'| unfold SCb; exact SC| exact SHIc| exact SLOc| exact MI'| exact MU| exact WMo| exact SH1| exact SH2| exact SHl| exact SHh| exact K].
        intros i Hi. apply SD. lia.
      + (* [comment removed for export] *)
        wstep.
        assert (E : qfin = FQS (fallbackSimpleSort fm ec lo hi) (sp - 1) slo shi rr).
        { destruct f; cbn [fqs_loop] in RES; [symmetry; exact RES|]. cbn [fq_sp] in RES. replace (0 <? sp - 1)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). symmetry; exact RES. }
        clear RES. subst qfin. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
        enter_with (K m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1'| exact AR2'| unfold SCb; exact SC| exact SHIc| exact SLOc| exact MI'| exact MU| exact WMo| exact FMR'| exact FMOK''| lia].
  Qed.
End B0FS.
End ACeilS1.
