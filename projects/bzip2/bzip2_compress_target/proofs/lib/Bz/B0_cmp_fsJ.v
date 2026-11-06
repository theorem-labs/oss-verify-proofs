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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsFs2 B0_cmp_fsV B0_cmp_fsB B0_cmp_fsS B0_cmp_fsI B0_cmp_fsW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Section B0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop.
  Variables (Jlo Jhi : list byte).
  (* [comment removed for export] *)
  Variables (fm0 ec0 bh0 : zarr).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y.
  Hypothesis YOFF : afenv_offsh X Y. Hypothesis AX : sanchor (ae_FB Y) (ae_SHF Y).
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation SLO := (ae_SLO Y). Notation SHI := (ae_SHI Y). Notation SHF := (ae_SHF Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NA2 := (18446744073709551615 - fe_A2 X)%Z.
  Hypothesis LJlo : Z.of_nat (length Jlo) = 400%Z. Hypothesis LJhi : Z.of_nat (length Jhi) = 400%Z.
  Hypothesis FEC : fsf_ec fm0 ec0 bh0 nb. Hypothesis FBK : fsf_bucket fm0 ec0 bh0 nb.
  (* [comment removed for export] *)
  Notation HH Hh ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 (Z_to_bv 64 Hh) t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 1) (Z_to_bv 64 A2) s4 (Z_to_bv 64 A1) cSB (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) s10 (Z_to_bv 64 NA2) t3 (Z_to_bv 64 nb) t5 t6).
  Notation Wh := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_A2 X, fe_A2 X + ARR2_SIZE); (fe_FT X, fe_FT X + 262148); (ae_P Y + 88, ae_P Y + 216);
                  (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400); (ae_SHF Y + 4, ae_SHF Y + 112)]%Z.
  Definition hmem (fm ec bh slo shi : zarr) (m : word -> option byte) : Prop :=
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) /\ u8arr b0segs m A2 (zb8 ec ARR2_SIZE) /\ u32arr b0segs m FT (zw32 bh 65537) /\
    (exists (nd hd : Z) (v112 v128 v136 v152 v160 v208 : word), rw_cells b0segs m (P + 72) (SCb X Y nd hd v112 v128 v136 v152 v160 v208)) /\
    u32arr b0segs m SHI (ovw shi Jhi 100) /\ u32arr b0segs m SLO (ovw slo Jlo 100) /\ id (rw_cells b0segs m (SHF + 4) (shc f8b)) /\ mem_inv b0segs m.
  Definition hsh (me : word -> option byte) : Prop :=
    shzW b0segs Wh me A1 (A1 + ARR1_SIZE) /\ shzW b0segs Wh me A2 (A2 + ARR2_SIZE) /\ shzW b0segs Wh me FT (FT + 262144).
  Definition hinv (fm ec bh : zarr) (Hh : Z) : Prop := fm_range fm nb /\ zbok fm /\ zbok ec /\ bh_w32 bh /\ (1 <= Hh <= nb)%Z.

  (* [comment removed for export] *)
  Ltac open XOK XSEP :=
    fsenv_open XOK; afenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & ?AP1F & ?AP2F);
    let SPX := fresh "SPX" in pose proof (afenv_sepx_of X Y XOK YOK YSEP YOFF) as SPX; unfold afenv_sepx, apartv, SH_HI in SPX;
    cps_destruct SPX as (?AP1L & ?AP1H & ?AP2L & ?AP2H & ?APFL & ?APFH & ?AS1 & ?AS2 & ?ASF & ?ASL & ?ASH & ?HLP & ?HHP & ?HSP & ?HPH);
    box_ors.
  Ltac shc_move H MU WM H' := pose proof (shc_transport _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; CmpSepV.slia_v)) as H'.

  Lemma B0_hloop : forall (f t : nat) (hfin : fhs) (me m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t5 t6 : word),
    let h := fp_hs fm0 ec0 bh0 nb t in
    fh_done h = false -> fs_H_loop f nb h = hfin -> fh_done hfin = true ->
    hinv (fh_fm h) (fh_ec h) (fh_bh h) (fh_H h) -> hmem (fh_fm h) (fh_ec h) (fh_bh h) (fh_slo h) (fh_shi h) m ->
    munch Wh me m -> wmono b0segs me m -> hsh me ->
    (forall m' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x30 x31 : word),
      hmem (fh_fm hfin) (fh_ec hfin) (fh_bh hfin) (fh_slo hfin) (fh_shi hfin) m' -> munch Wh me m' -> wmono b0segs me m' ->
      fm_range (fh_fm hfin) nb -> zbok (fh_fm hfin) -> zbok (fh_ec hfin) -> bh_w32 (fh_bh hfin) ->
      evt b0segs Q (MS (HH (fh_H hfin) x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x30 x31) F (Z_to_bv 64 0xa6d44) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (HH (fh_H h) ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t5 t6) F (Z_to_bv 64 0xa5424) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros t hfin me m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t5 t6 h Hd RES FIN HI HM MU WMo HSH K.
    { cbn [fs_H_loop] in RES. subst hfin. rewrite Hd in FIN. discriminate. }
    rewrite fs_H_loop_S, Hd in RES.
    cps_destruct HI as (FMR & FMOK' & ECOK' & BW & HHh). cps_destruct HM as (AR1 & AR2 & FTB & SCx & SHIc & SLOc & SHC & MI).
    destruct SCx as (nd & hd & v112 & v128 & v136 & v152 & v160 & v208 & SC). pose proof HSH as HSH0. cps_destruct HSH as (SH1 & SH2 & SHFt).
    open XOK XSEP. bz_params. pose proof SC as SC0. unfold SCb in SC.
    pose proof (zb8_length (fh_fm h) ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length (fh_ec h) ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zw32_length (fh_bh h) 65537 ltac:(lia)) as LB.
    pose proof (ovw_length (fh_shi h) Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length (fh_slo h) Jlo 100 ltac:(lia)) as LL.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases K4; zify_cond_z K4; [exfalso; lia|]. wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    enter_with (B0_fs_eclass X Y Q XOK XSEP YOK (Z.to_nat nb) 0 0 (fh_H h) (fh_fm h) (fh_ec h) (fh_bh h) m m _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| lia| exact HHh| exact FMOK'| exact ECOK'| exact BW| exact (proj2 FMR)| exact AR1| exact AR2| exact FTB| exact MI| apply munch_refl| apply wmono_refl| | | | |].
    { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
    { eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    { eapply (frdW_cell_at b0segs _ _ (P + 72)%Z _ 144%nat); [apply frdW_intro; [exact SC| cbn [disjoint_from cells_size csize Nat.add]; lia]| reflexivity| lia]. }
    intros m1 x5 x10 x11 x12 x13 x14 x15 x16 x17. cbv zeta. intros AR1_1 AR2_1 FTB1 MI1 MU1 WM1 ECOK1.
    bz_params. clear AR1 AR2 FTB MI. shc_move SHC MU1 WM1 SHC1. clear SHC. transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
    set (ec' := fs_eclass (Z.to_nat nb) (fh_ec h) (fh_fm h) (fh_bh h) (fh_H h) nb 0 0) in *.
    assert (Eec : ec' = fp_ecT fm0 ec0 bh0 nb t) by reflexivity.
    assert (ECR1 : ec_range ec' nb). { rewrite Eec. exact (FEC t Hd). }
    (* [comment removed for export] *)
    wstep. wstep.
    set (s0 := FBS (fh_fm h) ec' (fh_bh h) (fh_slo h) (fh_shi h) (-1) 0 false).
    set (sfin := fs_bucket_loop (Z.to_nat (nb + 2)) nb s0).
    assert (BF : forall v, fb_done (fs_bucket_loop v nb s0) = false -> bucket_ok nb (fs_bucket_loop v nb s0)).
    { intros v Hv. exact (FBK t v Hd Hv). }
    enter_with (B0_bloop X Y Q (fh_H h) ec' Jlo Jhi XOK XSEP YOK YSEP YOFF AX ECR1 ECOK1 LJlo LJhi (Z.to_nat (nb + 2)) s0 sfin m1 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| reflexivity| reflexivity| exact BF| reflexivity| | | | apply munch_refl| apply wmono_refl| |].
    { apply fs_bucket_loop_term; [lia| reflexivity| reflexivity| exact BF]. }
    { split; [exact FMR| split; [exact FMOK'| split; [exact BW| cbn; lia]]]. }
    { split; [exact AR1_1| split; [exact AR2_1| split; [exact FTB1| split; [| split; [exact SHIc| split; [exact SLOc| split; [exact SHC1| exact MI1]]]]]]].
      do 8 eexists. unfold SCb. exact SC. }
    { unfold bsh. split; [| split].
      - eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia].
      - eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia].
      - eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
    intros m3 y1 y5 y7 y10 y11 y12 y13 y14 y15 y16 y20 y26 y28 y30 y31 Hec2 BI2 BM2 MU2 WM2.
    cps_destruct BI2 as (FMR2 & FMOK2 & BW2 & Hnnd2). cps_destruct BM2 as (AR1_2 & AR2_2 & FTB2 & SCx2 & SHI2 & SLO2 & SHC3 & MI2). bz_params.
    destruct SCx2 as (nd2 & hd2 & u112 & u128 & u136 & u152 & u160 & u208 & SC2).
    clear AR1_1 AR2_1 FTB1 SC SC0 SHIc SLOc MI1 SHC1. transport_after_call b0segs m1 m3 MU2 WM2. clear MU2 WM2.
    pose proof AR2_2 as AR2_3. rewrite <- Hec2 in AR2_3.
    assert (HM2 : hmem (fb_fm sfin) (fb_ec sfin) (fb_bh sfin) (fb_slo sfin) (fb_shi sfin) m3).
    { split; [exact AR1_2| split; [exact AR2_3| split; [exact FTB2| split; [| split; [exact SHI2| split; [exact SLO2| split; [exact SHC3| exact MI2]]]]]]].
      exists nd2, hd2, u112, u128, u136, u152, u160, u208. exact SC2. }
    unfold SCb in SC2.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z (fb_nnd sfin)) by lia. wstep. wstep. wstep; if_cases K4'; zify_cond_z K4'; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. wstep. try rewrite (sx32_of_Z (fh_H h + 1073741824)) by lia. (wstep; notrap). wstep. try rewrite (sx32_of_Z (fh_H h * 2)) by lia.
    assert (NXT : fs_H_iter nb h = FHS (fb_fm sfin) (fb_ec sfin) (fb_bh sfin) (fb_slo sfin) (fb_shi sfin) (fh_H h * 2) ((nb <? fh_H h * 2) || (fb_nnd sfin =? 0))%Z) by reflexivity.
    (* [comment removed for export] *)
    wstep; if_cases KH; zify_cond_z KH.
    - (* [comment removed for export] *)
      rewrite NXT in RES. cbn [fh_done] in RES. replace (nb <? fh_H h * 2)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in RES.
      rewrite fs_H_loop_done in RES by reflexivity. subst hfin.
      enter_with (K m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fh_fm fh_ec fh_bh fh_slo fh_shi fh_H];
        [st_eq| exact HM2| exact MU| exact WMo| exact FMR2| exact FMOK2| rewrite Hec2; exact ECOK1| exact BW2].
    - replace (nb <? fh_H h * 2)%Z with false in NXT by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in NXT.
      (* [comment removed for export] *)
      wstep; if_cases KN; zify_cond_z KN.
      + (* [comment removed for export] *)
        replace (fb_nnd sfin =? 0)%Z with true in NXT by (symmetry; apply Z.eqb_eq; lia).
        rewrite NXT in RES. rewrite fs_H_loop_done in RES by reflexivity. subst hfin.
        enter_with (K m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fh_fm fh_ec fh_bh fh_slo fh_shi fh_H];
          [st_eq| exact HM2| exact MU| exact WMo| exact FMR2| exact FMOK2| rewrite Hec2; exact ECOK1| exact BW2].
      + (* [comment removed for export] *)
        replace (fb_nnd sfin =? 0)%Z with false in NXT by (symmetry; apply Z.eqb_neq; lia).
        pose proof (fp_hs_S fm0 ec0 bh0 nb t Hd) as HS. fold h in HS. rewrite NXT in HS.
        wstep.
        specialize (IH (S t) hfin me m3). rewrite HS in IH. cbn [fh_fm fh_ec fh_bh fh_slo fh_shi fh_H fh_done] in IH.
        rewrite NXT in RES.
        enter_with IH; [st_eq| reflexivity| exact RES| exact FIN| | exact HM2| exact MU| exact WMo| exact HSH0| exact K].
        split; [exact FMR2| split; [exact FMOK2| split; [rewrite Hec2; exact ECOK1| split; [exact BW2| lia]]]].
  Qed.
End B0FS.
End ACeilS1.
