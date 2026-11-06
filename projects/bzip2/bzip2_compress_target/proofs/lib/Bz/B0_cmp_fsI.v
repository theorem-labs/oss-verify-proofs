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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsFs2 B0_cmp_fsV B0_cmp_fsC B0_cmp_fsF B0_cmp_fsG B0_cmp_fsH B0_cmp_fsS B0_cmp_fsW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Lemma landv_range : forall bh k, (0 <= landv bh k < 18446744073709551616)%Z.
Proof.
  intros bh k. unfold landv.
  set (a := (bv_swrap 32 (Z.shiftl 1 (k mod 32)) mod 18446744073709551616)%Z).
  set (b := bv_unsigned (sx32 (Z_to_bv 64 (zget bh (k / 32))))).
  assert (Ha : (0 <= a < 18446744073709551616)%Z) by (subst a; apply Z.mod_pos_bound; lia).
  assert (Hb : (0 <= b)%Z) by (subst b; apply bv_unsigned_in_range).
  pose proof (OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.land_lt_pow2 a b 64 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia) Hb) as H.
  change (2^64)%Z with 18446744073709551616%Z in H. exact H.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma landv'_range : forall bh k, (0 <= landv' bh k < 18446744073709551616)%Z.
Proof. intros bh k. unfold landv'. rewrite Z.land_comm. apply landv_range. Qed.
Lemma landv'_zero_isset : forall bh k, bh_w32 bh -> (0 <= k)%Z -> landv' bh k = 0%Z -> isset_bh bh k = false.
Proof. intros bh k BW Hk E. pose proof (landv'_isset bh k BW Hk) as V. rewrite E in V. cbn in V. destruct (isset_bh bh k); [discriminate| reflexivity]. Qed.
Lemma landv'_nz_isset : forall bh k, bh_w32 bh -> (0 <= k)%Z -> landv' bh k <> 0%Z -> isset_bh bh k = true.
Proof. intros bh k BW Hk E. pose proof (landv'_isset bh k BW Hk) as V. destruct (isset_bh bh k); [reflexivity|]. cbn in V. apply Z.eqb_eq in V. lia. Qed.

Section B0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop. Variable Hh : Z.
  Variables (ec : zarr) (Jlo Jhi : list byte).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y.
  Hypothesis YOFF : afenv_offsh X Y. Hypothesis AX : sanchor (ae_FB Y) (ae_SHF Y).
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation SLO := (ae_SLO Y). Notation SHI := (ae_SHI Y). Notation SHF := (ae_SHF Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NA2 := (18446744073709551615 - fe_A2 X)%Z.
  Hypothesis ECR : ec_range ec nb. Hypothesis ECOK' : zbok ec.
  Hypothesis LJlo : Z.of_nat (length Jlo) = 400%Z. Hypothesis LJhi : Z.of_nat (length Jhi) = 400%Z.
  (* [comment removed for export] *)
  Notation HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 (Z_to_bv 64 Hh) t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 1) (Z_to_bv 64 A2) s4 (Z_to_bv 64 A1) cSB (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) s10 (Z_to_bv 64 NA2) t3 (Z_to_bv 64 nb) t5 t6).
  (* [comment removed for export] *)
  Notation Wb := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_FT X, fe_FT X + 262148); (ae_P Y + 88, ae_P Y + 216);
                  (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400); (ae_SHF Y + 4, ae_SHF Y + 112)]%Z.
  (* [comment removed for export] *)
  Definition bmem (fm bh slo shi : zarr) (m : word -> option byte) : Prop :=
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) /\ u8arr b0segs m A2 (zb8 ec ARR2_SIZE) /\ u32arr b0segs m FT (zw32 bh 65537) /\
    (exists (nd hd : Z) (v112 v128 v136 v152 v160 v208 : word), rw_cells b0segs m (P + 72) (SCb X Y nd hd v112 v128 v136 v152 v160 v208)) /\
    u32arr b0segs m SHI (ovw shi Jhi 100) /\ u32arr b0segs m SLO (ovw slo Jlo 100) /\ id (rw_cells b0segs m (SHF + 4) (shc f8b)) /\ mem_inv b0segs m.
  (* [comment removed for export] *)
  Definition bsh (me : word -> option byte) : Prop :=
    shzW b0segs Wb me A1 (A1 + ARR1_SIZE) /\ shzW b0segs Wb me A2 (A2 + ARR2_SIZE) /\ shzW b0segs Wb me FT (FT + 262144).
  (* [comment removed for export] *)
  Definition binv (fm bh : zarr) (r nnd : Z) : Prop := fm_range fm nb /\ zbok fm /\ bh_w32 bh /\ (0 <= nnd <= r + 1 /\ nnd <= nb)%Z.

  (* [comment removed for export] *)
  Ltac bmem_i AR1 AR2 FTB SC SHI SLO SHC MI :=
    split; [exact AR1| split; [exact AR2| split; [exact FTB| split; [do 8 eexists; exact SC| split; [exact SHI| split; [exact SLO| split; [exact SHC| exact MI]]]]]]].
  Ltac store_addr E' :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?ad ?bs) _) =>
      replace (write_to_mem m0 ad bs) with (write_to_mem m0 (wa E') bs) by (f_equal; unfold wa; f_equal; lia) end.
  Ltac open XOK XSEP :=
    fsenv_open XOK; afenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & ?AP1F & ?AP2F);
    let SPX := fresh "SPX" in pose proof (afenv_sepx_of X Y XOK YOK YSEP YOFF) as SPX; unfold afenv_sepx, apartv, SH_HI in SPX;
    cps_destruct SPX as (?AP1L & ?AP1H & ?AP2L & ?AP2H & ?APFL & ?APFH & ?AS1 & ?AS2 & ?ASF & ?ASL & ?ASH & ?HLP & ?HHP & ?HSP & ?HPH);
    box_ors.
  Ltac wbound k := let Hw := fresh "Hw" in assert (Hw : (0 <= k / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  (* [comment removed for export] *)
  Notation Wt := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (ae_P Y + 88, ae_P Y + 216); (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400)]%Z.
  Ltac shc_move H MU WM H' := pose proof (shc_transport _ _ _ _ _ H MU WM ltac:(cbn [disjoint_from]; CmpSepV.slia_v)) as H'.

  (* [comment removed for export] *)
  Definition KCont (s : fbs) (me : word -> option byte) : Prop :=
    forall m' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x26 x28 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = false -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') m' ->
      munch Wb me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) (Z_to_bv 64 (fb_r s')) x26 x28 x30 x31) F (Z_to_bv 64 0xa55bc) fc None m' (seg_rom b0segs)).
  Definition KBrk (s : fbs) (me : word -> option byte) : Prop :=
    forall m' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x20 x26 x28 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = true -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') m' ->
      munch Wb me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) x20 x26 x28 x30 x31) F (Z_to_bv 64 0xa6ce4) fc None m' (seg_rom b0segs)).

  (* [comment removed for export] *)
  Lemma B0_bk2 : forall (fm bh slo shi : zarr) (r0 nnd k1 k2 : Z) (me m : word -> option byte)
      (ra t0 t2 a0 a2 a3 a4 a5 a6 s4 t3 t5 t6 : word),
    let s := FBS fm ec bh slo shi r0 nnd false in
    k1 = bk1 nb bh (r0 + 1) -> k2 = bk2 nb bh k1 -> (nb <=? k1 - 1)%Z = false ->
    (0 <= r0 + 1)%Z -> (r0 + 2 <= k1 <= k2)%Z -> (k2 <= nb + 65)%Z ->
    bucket_ok nb s -> binv fm bh r0 nnd -> bmem fm bh slo shi m -> munch Wb me m -> wmono b0segs me m -> bsh me ->
    KCont s me -> KBrk s me ->
    evt b0segs Q (MS (HR ra t0 t2 a0 (Z_to_bv 64 k2) a2 a3 a4 a5 a6 (Z_to_bv 64 nnd) s4 (Z_to_bv 64 (k1 - 1)) t3 t5 t6) F (Z_to_bv 64 0xa5818) fc None m (seg_rom b0segs)).
  Proof.
    intros fm bh slo shi r0 nnd k1 k2 me m ra t0 t2 a0 a2 a3 a4 a5 a6 s4 t3 t5 t6 s Hk1 Hk2 C1 Hr0 Hk12 Hk2n BOK BI BM MU WMo BSH KC KB.
    unfold KCont, KBrk in KC, KB. cbv zeta in KC, KB. subst s. rewrite fs_bucket_iter_unfold in KC, KB. cbv zeta in KC, KB. rewrite <- Hk1, <- Hk2, C1 in KC, KB.
    cps_destruct BI as (FMR & FMOK' & BW & Hnnd). cps_destruct BM as (AR1 & AR2 & FTB & SCx & SHIc & SLOc & SHC & MI).
    destruct SCx as (nd & hd & v112 & v128 & v136 & v152 & v160 & v208 & SC). cps_destruct BSH as (SH1 & SH2 & SHFt).
    open XOK XSEP. bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    pose proof (ovw_length shi Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length slo Jlo 100 ltac:(lia)) as LL.
    (* [comment removed for export] *)
    brun_to 0xa5824%Z. try rewrite (sx32_of_Z (k2 - 1)) by lia. try rewrite (sx32_of_Z (k2 + -1)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kr; zify_cond_z Kr.
    2:{ (* [comment removed for export] *)
      replace (nb <=? k2 - 1)%Z with true in KB by (symmetry; apply Z.leb_le; lia).
      wstep.
      enter_with (KB m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
        [st_eq| reflexivity| reflexivity| split; [exact FMR| split; [exact FMOK'| split; [exact BW| lia]]]| bmem_i AR1 AR2 FTB SC SHIc SLOc SHC MI| exact MU| exact WMo]. }
    replace (nb <=? k2 - 1)%Z with false in KC by (symmetry; apply Z.leb_gt; lia). clear KB.
    (* [comment removed for export] *)
    wstep; if_cases Klr; zify_cond_z Klr.
    - (* [comment removed for export] *)
      replace (k1 - 1 <? k2 - 1)%Z with false in KC by (symmetry; apply Z.ltb_ge; lia).
      enter_with (KC m _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
        [st_eq| reflexivity| reflexivity| split; [exact FMR| split; [exact FMOK'| split; [exact BW| lia]]]| bmem_i AR1 AR2 FTB SC SHIc SLOc SHC MI| exact MU| exact WMo].
    - (* [comment removed for export] *)
      replace (k1 - 1 <? k2 - 1)%Z with true in KC by (symmetry; apply Z.ltb_lt; lia).
      destruct BOK as [_ QOK]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd] in QOK. rewrite <- Hk1, <- Hk2 in QOK.
      specialize (QOK ltac:(lia) ltac:(lia) ltac:(lia)). destruct QOK as [QFx QFIN].
      unfold SCb in SC.
      pose proof (munch_refl Wt m) as MUp. pose proof (wmono_refl b0segs m) as WMp.
      (* [comment removed for export] *)
      brun_to 0xa5864%Z.
      (* [comment removed for export] *)
      wstep. wstep. wstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.
      (* [comment removed for export] *)
      wstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      shc_move SHC MUp WMp SHC1. clear SHC MUp WMp.
      enter_with (B0_scope_begin X Y Q XOK YOK m1 m1 f8b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact SHC1| exact MI| apply munch_refl| apply wmono_refl|].
      intros m2 SHC2 MI2 MU2 WM2. clear SHC1 MI. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      pose proof (app_fp_WtB X Y XOK YOK YOFF) as AFt.
      destruct (afs_stack_readers X Y Wt m2 XOK YOK AX AFt SHC2) as [SHl2 SHh2].
      change (rw_cells b0segs m2 (SHF + 4) (shc z8)) with (id (rw_cells b0segs m2 (SHF + 4) (shc z8))) in SHC2.
      pose proof (munch_refl Wt m2) as MUp. pose proof (wmono_refl b0segs m2) as WMp.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok b0segs mm SLO _ 0 _ SLOc ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
      wstep. store_addr (SLO + 4 * 0)%Z. ovw_store SLOc 0%Z (k1 - 1)%Z wval_lit. try clear SO.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok b0segs mm SHI _ 0 _ SHIc ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
      wstep. store_addr (SHI + 4 * 0)%Z. ovw_store SHIc 0%Z (k2 - 1)%Z wval_lit. try clear SO.
      (* [comment removed for export] *)
      wstep.
      set (nnd' := (nnd + (k2 - 1 - (k1 - 1) + 1))%Z) in *.
      set (q0 := FQS fm 1 (zset slo 0 (k1 - 1)) (zset shi 0 (k2 - 1)) 0) in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
      enter_with (B0_qloop X Y Q Hh (k1 - 1) (k2 - 1) nnd' ec Jlo Jhi XOK XSEP YOK YSEP ECR ECOK' LJlo LJhi
                    (fqs_fuel (k1 - 1) (k2 - 1)) q0 (fqs_loop (fqs_fuel (k1 - 1) (k2 - 1)) ec q0) m3 m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| cbn; lia| cbn; lia| exact FMR| exact FMOK'| | exact QFx| reflexivity| exact QFIN| exact AR1| exact AR2| | exact SHIc| exact SLOc| exact MI2| apply munch_refl| apply wmono_refl| | | | |].
      { clear KC. subst q0. intros i Hi. cbn [fq_slo fq_shi fq_sp] in Hi |- *. rewrite !zdef_zset. replace i with 0%Z by lia. cbn. split; reflexivity. }
      { unfold SCb. cbn [fq_r q0]. subst nnd'.
        lazymatch goal with |- rw_cells _ _ _ ?cs => lazymatch type of SC with rw_cells _ _ _ ?cs' => replace cs with cs'; [exact SC| repeat (f_equal; try (f_equal; lia))] end end. }
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SHl2| exact MUp| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SHh2| exact MUp| sub_fp_solve| lia| lia]. }
      intros m4 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 u128 u136 u152 u160 u208 AR1_1 AR2_1 SC1 SHI1 SLO1 MI1 MU1 WM1 FMR1 FMOK1 Hr1.
      bz_params. clear AR1 AR2 SC SHIc SLOc MI2. transport_after_call b0segs m3 m4 MU1 WM1. clear MU1 WM1.
      set (qf := fqs_loop (fqs_fuel (k1 - 1) (k2 - 1)) ec q0) in *.
      unfold SCb in SC1.
      (* [comment removed for export] *)
      wstep. wstep.
      (* [comment removed for export] *)
      shc_move SHC2 MUp WMp SHC3. clear SHC2 MUp WMp SHl2 SHh2.
      enter_with (B0_scope_end X Y Q XOK YOK m4 m4 z8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact SHC3| exact MI1| apply munch_refl| apply wmono_refl|].
      intros m5 SHC5 MI5 MU5 WM5. clear SHC3 MI1. transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
      change (rw_cells b0segs m5 (SHF + 4) (shc f8b)) with (id (rw_cells b0segs m5 (SHF + 4) (shc f8b))) in SHC5.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      wstep; if_cases Kx; zify_cond_z Kx; [| exfalso; lia].
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep.
      enter_with (B0_headers X Y Q Hh (k2 - 1) XOK XSEP YOK (Z.to_nat (k2 - 1 - (k1 - 1) + 1)) (k1 - 1) (-1) (fq_fm qf) ec bh m5 m5 _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact ECR| exact FMOK1| exact ECOK'| exact BW| exact AR1_1| exact AR2_1| exact FTB| exact MI5| apply munch_refl| apply wmono_refl| | | | |].
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SH2| exact MU| sub_fp_solve| lia| lia]. }
      { eapply shzW_sub; [exact SHFt| exact MU| sub_fp_solve| lia| lia]. }
      { eapply (frdW_cell_at b0segs _ _ (P + 72)%Z _ 144%nat); [apply frdW_intro; [exact SC1| cbn [disjoint_from cells_size csize Nat.add]; lia]| reflexivity| lia]. }
      intros m6 y11 y14 y15 y16. cbv zeta. intros AR1_2 AR2_2 FTB2 MI6 MU6 WM6 BW2. bz_params.
      clear AR1_1 AR2_1 FTB MI5. shc_move SHC5 MU6 WM6 SHC6. clear SHC5. transport_after_call b0segs m5 m6 MU6 WM6.
      unfold fallbackQSort3, fpush in KC. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in KC. replace (0 + 1)%Z with 1%Z in KC by reflexivity. fold q0 in KC. fold qf in KC.
      enter_with (KC m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
        [st_eq| reflexivity| reflexivity| split; [exact FMR1| split; [exact FMOK1| split; [exact BW2| subst nnd'; lia]]]| | exact MU| exact WMo].
      split; [exact AR1_2| split; [exact AR2_2| split; [exact FTB2| split; [| split; [exact SHI1| split; [exact SLO1| split; [exact SHC6| exact MI6]]]]]]].
      exists nnd', Hh, (Z_to_bv 64 (fq_r qf)), u128, u136, u152, u160, u208. unfold SCb. exact SC1.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bk1 : forall (fm bh slo shi : zarr) (r0 nnd k1 : Z) (me m : word -> option byte)
      (ra t0 t2 a0 a2 a3 a4 a5 a6 s4 s10 t3 t5 t6 : word),
    let s := FBS fm ec bh slo shi r0 nnd false in
    k1 = bk1 nb bh (r0 + 1) -> (0 <= r0 + 1)%Z -> (r0 + 2 <= k1 <= nb + 64)%Z ->
    bucket_ok nb s -> binv fm bh r0 nnd -> bmem fm bh slo shi m -> munch Wb me m -> wmono b0segs me m -> bsh me ->
    KCont s me -> KBrk s me ->
    evt b0segs Q (MS (HR ra t0 t2 a0 (Z_to_bv 64 k1) a2 a3 a4 a5 a6 (Z_to_bv 64 nnd) s4 s10 t3 t5 t6) F (Z_to_bv 64 0xa5754) fc None m (seg_rom b0segs)).
  Proof.
    intros fm bh slo shi r0 nnd k1 me m ra t0 t2 a0 a2 a3 a4 a5 a6 s4 s10 t3 t5 t6 s Hk1 Hr0 Hk1r BOK BI BM MU WMo BSH KC KB. subst s.
    pose proof BOK as BOK0. destruct BOK as [SOK _]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd] in SOK.
    unfold scan_ok in SOK. cbv zeta in SOK. rewrite <- Hk1 in SOK. cps_destruct SOK as (_ & _ & _ & _ & _ & SD).
    pose proof BI as BI0. cps_destruct BI as (FMR & FMOK' & BW & Hnnd). pose proof BM as BM0. cps_destruct BM as (AR1 & AR2 & FTB & SCx & SHIc & SLOc & SHC & MI).
    pose proof BSH as BSH0. cps_destruct BSH as (SH1 & SH2 & SHFt).
    open XOK XSEP. bz_params.
    (* [comment removed for export] *)
    brun_to 0xa5760%Z. try rewrite (sx32_of_Z (k1 - 1)) by lia. try rewrite (sx32_of_Z (k1 + -1)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kl; zify_cond_z Kl.
    2:{ (* [comment removed for export] *)
      pose proof KB as KB'. unfold KBrk in KB'. cbv zeta in KB'. rewrite fs_bucket_iter_unfold in KB'. cbv zeta in KB'. rewrite <- Hk1 in KB'.
      replace (nb <=? k1 - 1)%Z with true in KB' by (symmetry; apply Z.leb_le; lia).
      wstep.
      enter_with (KB' m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
        [st_eq| reflexivity| reflexivity| exact BI0| exact BM0| exact MU| exact WMo]. }
    assert (C1 : (nb <=? k1 - 1)%Z = false) by (apply Z.leb_gt; lia).
    specialize (SD ltac:(lia)). cps_destruct SD as (STOPD & HD & SEF).
    set (kD := fs_scan_clr_unal (FSC nb) bh k1) in *.
    pose proof (fs_scan_clr_unal_ge (FSC nb) bh k1) as GD. fold kD in GD.
    (* [comment removed for export] *)
    wbound k1. brun_to 0xa5794%Z.
    enter_with (B0_scanD X Y Q XOK YOK (FSC nb) k1 bh _ me m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HD| exact STOPD| exact BW| exact FTB| exact MI| exact MU| exact SHFt|].
    intros x13. cbv zeta. fold kD. pose proof (landv'_range bh kD) as LV.
    (* [comment removed for export] *)
    wstep; if_cases Ki; zify_cond_z Ki.
    - (* [comment removed for export] *)
      apply landv'_nz_isset in Ki; [| exact BW| lia].
      enter_with (B0_bk2 fm bh slo shi r0 nnd k1 kD me m); [st_eq| exact Hk1| | exact C1| lia| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WMo| exact BSH0| exact KC| exact KB].
      unfold bk2. cbv zeta. fold kD. rewrite Ki. cbn [negb]. reflexivity.
    - (* [comment removed for export] *)
      apply landv'_zero_isset in Ki; [| exact BW| lia]. specialize (SEF Ki). cps_destruct SEF as (STOPE & HE & STOPF & HF).
      set (kE := fs_scan_word_00 (FSC nb) bh kD) in *. set (kF := fs_scan_clr (FSC nb) bh kE) in *.
      pose proof (fs_scan_word_00_ge (FSC nb) bh kD) as GE. fold kE in GE. pose proof (fs_scan_clr_ge (FSC nb) bh kE) as GF. fold kF in GF.
      wbound kD. brun_to 0xa6910%Z.
      enter_with (B0_scanE X Y Q XOK YOK (FSC nb) kD bh _ me m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HE| exact STOPE| exact BW| exact FTB| exact MI| exact MU| exact SHFt|].
      intros y10 y12 y13. cbv zeta. fold kE.
      wbound kE. brun_to 0xa6998%Z.
      enter_with (B0_scanF X Y Q XOK YOK (FSC nb) kE bh _ me m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HF| exact STOPF| exact BW| exact FTB| exact MI| exact MU| exact SHFt|].
      intros z12 z13. cbv zeta. fold kF.
      enter_with (B0_bk2 fm bh slo shi r0 nnd k1 kF me m); [st_eq| exact Hk1| | exact C1| lia| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WMo| exact BSH0| exact KC| exact KB].
      unfold bk2. cbv zeta. fold kD. rewrite Ki. cbn [negb]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_biter : forall (fm bh slo shi : zarr) (r0 nnd : Z) (me m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t5 t6 : word),
    let s := FBS fm ec bh slo shi r0 nnd false in
    bucket_ok nb s -> binv fm bh r0 nnd -> bmem fm bh slo shi m -> munch Wb me m -> wmono b0segs me m -> bsh me ->
    KCont s me -> KBrk s me ->
    evt b0segs Q (MS (HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nnd) (Z_to_bv 64 r0) s10 t3 t5 t6) F (Z_to_bv 64 0xa55bc) fc None m (seg_rom b0segs)).
  Proof.
    intros fm bh slo shi r0 nnd me m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t5 t6 s BOK BI BM MU WMo BSH KC KB. subst s.
    pose proof BOK as BOK0. destruct BOK as [SOK _]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd] in SOK.
    unfold scan_ok in SOK. cbv zeta in SOK. cps_destruct SOK as (Hk0 & H01 & STOPA & HA & SBC & _).
    pose proof BI as BI0. cps_destruct BI as (FMR & FMOK' & BW & Hnnd). pose proof BM as BM0. cps_destruct BM as (AR1 & AR2 & FTB & SCx & SHIc & SLOc & SHC & MI).
    pose proof BSH as BSH0. cps_destruct BSH as (SH1 & SH2 & SHFt).
    open XOK XSEP. bz_params.
    set (k0 := (r0 + 1)%Z) in *.
    set (kA := fs_scan_set_unal (FSC nb) bh k0) in *.
    pose proof (fs_scan_set_unal_ge (FSC nb) bh k0) as GA. fold kA in GA.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z_signed (r0 + 1)) by lia. try rewrite (sx32_of_Z (r0 + 1)) by lia. fold k0.
    enter_with (B0_scanA X Y Q XOK YOK (FSC nb) k0 bh _ me m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HA| exact STOPA| exact BW| exact FTB| exact MI| exact MU| exact SHFt|].
    intros x14. cbv zeta. fold kA. pose proof (landv'_range bh kA) as LV.
    (* [comment removed for export] *)
    wstep; if_cases Ki; zify_cond_z Ki.
    - (* [comment removed for export] *)
      apply landv'_zero_isset in Ki; [| exact BW| lia].
      assert (Hk1 : kA = bk1 nb bh k0). { unfold bk1. cbv zeta. fold kA. rewrite Ki. reflexivity. }
      rewrite <- Hk1 in H01.
      enter_with (B0_bk1 fm bh slo shi r0 nnd kA me m); [st_eq| exact Hk1| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WMo| exact BSH0| exact KC| exact KB].
    - (* [comment removed for export] *)
      apply landv'_nz_isset in Ki; [| exact BW| lia]. specialize (SBC Ki). cps_destruct SBC as (STOPB & HB & STOPC & HC).
      set (kB := fs_scan_word_ff (FSC nb) bh kA) in *. set (kC := fs_scan_set (FSC nb) bh kB) in *.
      pose proof (fs_scan_word_ff_ge (FSC nb) bh kA) as GB. fold kB in GB. pose proof (fs_scan_set_ge (FSC nb) bh kB) as GC. fold kC in GC.
      assert (Hk1 : kC = bk1 nb bh k0). { unfold bk1. cbv zeta. fold kA. rewrite Ki. fold kB. reflexivity. }
      rewrite <- Hk1 in H01.
      enter_with (B0_scanB X Y Q XOK YOK (FSC nb) kA bh _ me m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HB| exact STOPB| exact BW| exact FTB| exact MI| exact MU| exact SHFt|].
      intros y10 y12 y13. cbv zeta. fold kB.
      wbound kB. brun_to 0xa56dc%Z.
      enter_with (B0_scanC X Y Q XOK YOK (FSC nb) kB bh _ me m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HC| exact STOPC| exact BW| exact FTB| exact MI| exact MU| exact SHFt|].
      intros z12 z13. cbv zeta. fold kC.
      enter_with (B0_bk1 fm bh slo shi r0 nnd kC me m); [st_eq| exact Hk1| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WMo| exact BSH0| exact KC| exact KB].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bloop : forall (u : nat) (s sfin : fbs) (me m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t5 t6 : word),
    fb_done s = false -> fb_ec s = ec ->
    (forall v, fb_done (fs_bucket_loop v nb s) = false -> bucket_ok nb (fs_bucket_loop v nb s)) ->
    fs_bucket_loop u nb s = sfin -> fb_done sfin = true ->
    binv (fb_fm s) (fb_bh s) (fb_r s) (fb_nnd s) -> bmem (fb_fm s) (fb_bh s) (fb_slo s) (fb_shi s) m -> munch Wb me m -> wmono b0segs me m -> bsh me ->
    (forall m' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x20 x26 x28 x30 x31 : word),
      fb_ec sfin = ec -> binv (fb_fm sfin) (fb_bh sfin) (fb_r sfin) (fb_nnd sfin) -> bmem (fb_fm sfin) (fb_bh sfin) (fb_slo sfin) (fb_shi sfin) m' ->
      munch Wb me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd sfin)) x20 x26 x28 x30 x31) F (Z_to_bv 64 0xa6ce4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (fb_nnd s)) (Z_to_bv 64 (fb_r s)) s10 t3 t5 t6) F (Z_to_bv 64 0xa55bc) fc None m (seg_rom b0segs)).
  Proof.
    induction u as [|u IH]; intros s sfin me m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t5 t6 Hd Hec BF RES FIN BI BM MU WMo BSH K.
    { cbn [fs_bucket_loop] in RES. subst sfin. rewrite Hd in FIN. discriminate. }
    rewrite fs_bucket_loop_S, Hd in RES.
    pose proof (BF 0%nat Hd) as BOK. cbn [fs_bucket_loop] in BOK.
    destruct s as [fm ec0 bh slo shi r0 nnd dn]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done] in *. subst ec0 dn.
    eapply (B0_biter fm bh slo shi r0 nnd me m); [exact BOK| exact BI| exact BM| exact MU| exact WMo| exact BSH| |].
    - unfold KCont. intros m' x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x26 x28 x30 x31. cbv zeta. intros Hd' Hec' BI' BM' MU' WM'.
      eapply (IH (fs_bucket_iter nb (FBS fm ec bh slo shi r0 nnd false)) sfin me m');
        [exact Hd'| exact Hec'| | exact RES| exact FIN| exact BI'| exact BM'| exact MU'| exact WM'| exact BSH| exact K].
      intros v Hv. specialize (BF (S v)). rewrite fs_bucket_loop_S in BF. cbn [fb_done] in BF. exact (BF Hv).
    - unfold KBrk. intros m' x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x20 x26 x28 x30 x31. cbv zeta. intros Hd' Hec' BI' BM' MU' WM'.
      rewrite (fs_bucket_loop_done u) in RES by exact Hd'. subst sfin.
      eapply K; [exact Hec'| exact BI'| exact BM'| exact MU'| exact WM'].
  Qed.
End B0FS.
End ACeilS1.
