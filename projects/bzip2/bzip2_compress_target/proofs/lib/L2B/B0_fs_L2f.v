(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCSortF BzArrD CmpMem BzCLemmasFs BzCFactsFs BzCFactsFs2 CmpFsKit0 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_fsW B0_cmp_fsS B0_cmp_fsP B0_cmp_fsQ B0_cmp_fsZ.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).
Strategy 1000 [fs_ftab_zero fs_count fs_copy fs_accum fs_distrib fs_bh_zero fs_bh_init fs_sentinel fs_eclass fs_H_loop fs_H_iter
               fs_bucket_loop fs_bucket_iter fs_headers fs_skip0 fs_rebuild fqs_loop fallbackQSort3 fallbackSort].

(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (CmpHmKit.rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

Lemma In_f8 : In 248 set_shadow_vals. Proof. unfold set_shadow_vals. do 12 right. left. reflexivity. Qed.
Lemma In_00 : In 0 set_shadow_vals. Proof. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma n_rw_CB_of_bytes : forall (m : mem) d (bs : list byte), bytes_at b0segs m d bs -> wr_at bsegs m d (Z.of_nat (length bs)) -> rw_cells b0segs m d [CB (length bs) bs].
Proof.
  intros m d bs HB HW. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xFs (X : fsenv) (F' : bvmap 5 word) (fc' : bv 32) : fsenv :=
  FE (fe_ra X) (fe_sp X) (fe_gp X) (fe_tp X) (fe_s0 X) (fe_s1 X) (fe_s2 X) (fe_s3 X) (fe_s4 X) (fe_s5 X) (fe_s6 X) (fe_s7 X) (fe_s8 X) (fe_s9 X) (fe_s10 X) (fe_s11 X)
     F' fc' (fe_A1 X) (fe_A2 X) (fe_FT X) (fe_nb X) (fe_lo X) (fe_q1 X) (fe_q2 X) (fe_qF X) (fe_qsp X) (fe_fm X) (fe_ec X) (fe_bh X) (fe_sv X) (fe_m0 X).

Section FSG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis SFREE : stack_free_contract RT 6.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.

Variable X : fsenv.
Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
Notation usp := (bv_unsigned (fe_sp X)).
Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation lo := (fe_lo X).
Notation ec0 := (fe_ec X). Notation fm0 := (fe_fm X). Notation bh0 := (fe_bh X).
Notation Wfs := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)].
Notation cSB := (Z_to_bv 64 2147450880).
Notation HF := (fp_hsF fm0 ec0 bh0 nb).
Notation RBF := (fs_rebuild (Z.to_nat nb) (fh_ec HF) (fp_fc0 ec0 nb) (fh_fm HF) 0 0).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fs_aconsts_of_art : forall Σ (m : mem), ART RT Σ m -> aconsts B0C m /\ aconsts_uar B0C m.
Proof.
  intros Σ m H. destruct (af_client_consts RT AF Σ m H) as (G1 & G2 & G3 & G4).
  split; split.
  - exact (ro_C8_KN m _ _ G1).
  - exact (ro_C8_KN m _ _ G2).
  - exact (ro_C8_KN m _ _ G3).
  - exact (ro_C4_KN m _ _ G4).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act.
Variables (Σ1 : rts RT) (PMc : Model -> Prop) (Y : afenv) (fr : list (Z * nat)) (live0 : list (Z * Z)) (sp0 : Z).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y. Hypothesis YOFF : afenv_offsh X Y. Hypothesis AX : sanchor (ae_FB Y) (ae_SHF Y).
Notation P := (ae_P Y). Notation FB := (ae_FB Y). Notation SHF := (ae_SHF Y).
Notation SLO := (ae_SLO Y). Notation SHI := (ae_SHI Y). Notation FCP := (ae_FCP Y).
Hypothesis G : act_geom RT lo P usp sp0 true 6 FB SHF 4096 512 fr live0 Wfs.
Hypothesis SOK : sig_ok RT sp0 true 6 FB fr live0 Σ1.
Hypothesis LIV1 : In (A1, ARR1_SIZE) live0. Hypothesis LIV2 : In (A2, ARR2_SIZE) live0. Hypothesis LIVF : In (FT, 262148) live0.
Hypothesis IMG1 : 0x62b000 <= A1. Hypothesis IMG2 : 0x62b000 <= A2. Hypothesis IMGF : 0x62b000 <= FT.
(* [comment removed for export] *)
Hypothesis GLS1 : A1 + ARR1_SIZE <= SHF \/ SHF + 512 <= A1.
Hypothesis GLS2 : A2 + ARR2_SIZE <= SHF \/ SHF + 512 <= A2.
Hypothesis GLSF : FT + 262148 <= SHF \/ SHF + 512 <= FT.
Hypothesis GSELF : FB + 4096 <= SHF \/ SHF + 512 <= FB.
Variable mi : mem.   (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wfs mi).

Lemma LIVS1 : In (A1, ARR1_SIZE) (rt_live RT Σ1). Proof. exact (proj2 (proj2 SOK) _ LIV1). Qed.
Lemma LIVS2 : In (A2, ARR2_SIZE) (rt_live RT Σ1). Proof. exact (proj2 (proj2 SOK) _ LIV2). Qed.
Lemma LIVSF : In (FT, 262148) (rt_live RT Σ1). Proof. exact (proj2 (proj2 SOK) _ LIVF). Qed.

(* [comment removed for export] *)
Definition fs_shsep : Prop :=
  (A1 + ARR1_SIZE <= A2 \/ A2 + ARR2_SIZE <= A1) /\ (A1 + ARR1_SIZE <= FT \/ FT + 262148 <= A1) /\ (A2 + ARR2_SIZE <= FT \/ FT + 262148 <= A2) /\
  (A1 + ARR1_SIZE <= FB \/ FB + 2112 <= A1) /\ (A2 + ARR2_SIZE <= FB \/ FB + 2112 <= A2) /\ (FT + 262148 <= FB \/ FB + 2112 <= FT) /\
  (A1 + ARR1_SIZE <= SLO \/ SLO + 400 <= A1) /\ (A2 + ARR2_SIZE <= SLO \/ SLO + 400 <= A2) /\ (FT + 262148 <= SLO \/ SLO + 400 <= FT) /\
  (A1 + ARR1_SIZE <= SHI \/ SHI + 400 <= A1) /\ (A2 + ARR2_SIZE <= SHI \/ SHI + 400 <= A2) /\ (FT + 262148 <= SHI \/ SHI + 400 <= FT) /\
  (A1 + ARR1_SIZE <= FCP \/ FCP + 1024 <= A1) /\ (A2 + ARR2_SIZE <= FCP \/ FCP + 1024 <= A2) /\ (FT + 262148 <= FCP \/ FCP + 1024 <= FT) /\
  (A1 + ARR1_SIZE <= SHF \/ SHF + 512 <= A1) /\ (A2 + ARR2_SIZE <= SHF \/ SHF + 512 <= A2) /\ (FT + 262148 <= SHF \/ SHF + 512 <= FT) /\
  (FB + 2112 <= SHF \/ SHF + 512 <= FB) /\ (SLO + 400 <= SHF \/ SHF + 512 <= SLO) /\ (SHI + 400 <= SHF \/ SHF + 512 <= SHI) /\ (FCP + 1024 <= SHF \/ SHF + 512 <= FCP) /\
  A1 + ARR1_SIZE <= P /\ A2 + ARR2_SIZE <= P /\ FT + 262148 <= P /\ FB + 4096 <= P /\ SHF + 512 <= P /\ SLO + 400 <= P /\ SHI + 400 <= P /\ FCP + 1024 <= P /\
  FB + 24 <= SLO /\ SLO + 400 <= SHI /\ SHI + 400 <= FCP /\ FCP + 1024 <= FB + 2112 /\ 17594333495296 <= P.
Lemma fs_shsep_ok : fs_shsep.
Proof.
  fsenv_open XOK. afenv_open YOK. pose proof G as [_ _ _ _ GLOW GLOR _ _ _ GFR GSH GSP0 _ _]. unfold RT_STACK, STACK_WIN, SEGTOP_A, USTACK_TOP in *.
  pose proof XSEP as (S12 & S1F & S2F). pose proof YSEP as (Y1 & Y2 & YF). unfold apartv in *.
  pose proof alloc_ceiling_range as ACR.
  unfold fs_shsep.
  split; [exact S12|]. split; [exact S1F|]. split; [exact S2F|]. split; [exact Y1|]. split; [exact Y2|]. split; [exact YF|].
  split; [clear - Y1 YSLO; lia|]. split; [clear - Y2 YSLO; lia|]. split; [clear - YF YSLO; lia|].
  split; [clear - Y1 YSHI; lia|]. split; [clear - Y2 YSHI; lia|]. split; [clear - YF YSHI; lia|].
  split; [clear - Y1 YFCP; lia|]. split; [clear - Y2 YFCP; lia|]. split; [clear - YF YFCP; lia|].
  split; [exact GLS1|]. split; [exact GLS2|]. split; [exact GLSF|].
  split; [clear - GSELF; lia|]. split; [clear - GSELF YSLO; lia|]. split; [clear - GSELF YSHI; lia|]. split; [clear - GSELF YFCP; lia|].
  clear S12 S1F S2F Y1 Y2 YF. repeat split; lia.
Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof fs_shsep_ok as H; unfold fs_shsep in H;
  destruct H as (?XS1 & ?XS2 & ?XS3 & ?XS4 & ?XS5 & ?XS6 & ?XS7 & ?XS8 & ?XS9 & ?XS10 & ?XS11 & ?XS12 & ?XS13 & ?XS14 & ?XS15 & ?XS16 & ?XS17 & ?XS18 & ?XS19 & ?XS20
                 & ?XS21 & ?XS22 & ?XL1 & ?XL2 & ?XL3 & ?XL4 & ?XL5 & ?XL6 & ?XL7 & ?XL8 & ?XL9 & ?XL10 & ?XL11 & ?XL12 & ?XL13);
  box_ors.
(* [comment removed for export] *)
Ltac fs_keys :=
  pose proof (ck_intro P CStack) as KP; pose proof (ck_intro usp CStack) as KU; pose proof (ck_intro FB CFrame) as KFB; pose proof (ck_intro SLO CFrame) as KSLO;
  pose proof (ck_intro SHI CFrame) as KSHI; pose proof (ck_intro FCP CFrame) as KFCP; pose proof (ck_intro SHF CShadow) as KSH;
  pose proof (ck_intro A1 (CLive A1 ARR1_SIZE)) as KA1; pose proof (ck_intro A2 (CLive A2 ARR2_SIZE)) as KA2; pose proof (ck_intro FT (CLive FT 262148)) as KFT.
Ltac fp_ours := per_interval; cbn [outside]; lia.

(* [comment removed for export] *)
Notation WZ := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_A2 X, fe_A2 X + ARR2_SIZE); (fe_FT X, fe_FT X + 262148); (ae_P Y + 32, ae_P Y + 224); (ae_P Y + 244, ae_P Y + 1272);
                (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400); (ae_SHF Y + 4, ae_SHF Y + 112); (ae_FCP Y, ae_FCP Y + 1024)].
Lemma fs_readersZ : forall (m : mem), ART RT Σ1 m -> bytes_at b0segs m (SHF + 120) (repeat z8 128) ->
  shzW b0segs WZ m A1 (A1 + ARR1_SIZE) /\ shzW b0segs WZ m A2 (A2 + ARR2_SIZE) /\ shzW b0segs WZ m FT (FT + 262144) /\ shzW b0segs WZ m FCP (FCP + 1024).
Proof.
  intros m ART0 SHZ. fsenv_open XOK. afenv_open YOK. pose proof alloc_ceiling_range as ACR. pose proof AX as [AX1 AX2].
  pose proof fs_shsep_ok as SHS. unfold fs_shsep in SHS.
  destruct SHS as (_ & _ & _ & D1 & D2 & DF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & L3 & L4 & PHI).
  destruct YOFF as (O1 & O2 & O3 & O4).
  assert (OP : P + 224 <= SH_LO \/ SH_HI <= P + 32) by (right; unfold SH_HI; clear - PHI; lia).
  assert (OQ : P + 1272 <= SH_LO \/ SH_HI <= P + 244) by (right; unfold SH_HI; clear - PHI; lia).
  unfold SH_LO, SH_HI in O4.
  assert (OL : SLO + 400 <= SH_LO \/ SH_HI <= SLO) by (unfold SH_LO, SH_HI; clear - O4 YSLO; lia).
  assert (OH : SHI + 400 <= SH_LO \/ SH_HI <= SHI) by (unfold SH_LO, SH_HI; clear - O4 YSHI; lia).
  assert (OC : FCP + 1024 <= SH_LO \/ SH_HI <= FCP) by (unfold SH_LO, SH_HI; clear - O4 YFCP; lia).
  assert (GEN : forall lo hi, 0 <= lo -> hi <= 2^47 -> (hi <= FB + 32 \/ FB + 896 <= lo) ->
            forall x, lo <= x < hi -> disjoint_from WZ (x / 8 + 2147450880) 1).
  { intros lo' hi' H0 H47 DJ x Hx. cbn [disjoint_from].
    assert (X47 : 0 <= x < 2^47) by (clear - H0 H47 Hx; lia).
    split; [apply shd_app; [exact X47| exact O1]|]. split; [apply shd_app; [exact X47| exact O2]|]. split; [apply shd_app; [exact X47| exact O3]|].
    split; [apply shd_app; [exact X47| exact OP]|]. split; [apply shd_app; [exact X47| exact OQ]|].
    split; [apply shd_app; [exact X47| exact OL]|]. split; [apply shd_app; [exact X47| exact OH]|].
    split; [apply (shd_anchor FB SHF 4 112 x AX); clear - DJ Hx; lia|]. split; [apply shd_app; [exact X47| exact OC]| exact I]. }
  destruct (af_acc_live RT AF Σ1 m A1 ARR1_SIZE ART0 LIVS1) as [_ ACC1]. destruct (af_acc_live RT AF Σ1 m A2 ARR2_SIZE ART0 LIVS2) as [_ ACC2].
  destruct (af_acc_live RT AF Σ1 m FT 262148 ART0 LIVSF) as [_ ACCF].
  pose proof (acc_of_zero_shadow b0segs m FB SHF 120 128 AX1 AX2 ltac:(clear - YFl; lia) ltac:(clear; lia) SHZ) as ACCC.
  replace (FB + 8 * 120) with FCP in ACCC by (clear - YFCP; lia). change (8 * Z.of_nat 128) with 1024 in ACCC.
  split; [| split; [| split]].
  - apply (shzW_of_acc_gen b0segs WZ m A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1); [clear - XA1l; lia| clear; lia| clear - AL1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XA1l; lia| clear - XA1h ACR; lia| clear - D1; lia].
  - apply (shzW_of_acc_gen b0segs WZ m A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2); [clear - XA2l; lia| clear; lia| clear - AL2; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XA2l; lia| clear - XA2h ACR; lia| clear - D2; lia].
  - apply (shzW_of_acc_gen b0segs WZ m FT 262148 FT (FT + 262144) ACCF); [clear - XFl; lia| clear; lia| clear - ALF; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XFl; lia| clear - XFh ACR; lia| clear - DF; lia].
  - apply (shzW_of_acc_gen b0segs WZ m FCP 1024 FCP (FCP + 1024) ACCC); [clear - YFl YFCP; lia| clear; lia| clear - YFCP AX1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - YFl YFCP; lia| clear - YFh YFCP ACR; lia| clear - YFCP; lia].
Qed.

Lemma fs_act : forall (v0 v8 v16 v24 v32 v40 v48 v56 v64 : word) (v72 v88 v96 v104 v112 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word)
    (v224 v232 : word) (j4 jft : list byte) (u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F1 fc1 T c1,
  fs_facts fm0 ec0 bh0 nb ->
  rw_cells b0segs mi P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64] ->
  rw_cells b0segs mi (P + 72) [C8 v72; C8 (Z_to_bv 64 nb); C8 v88; C8 v96; C8 v104; C8 v112; C8 (Z_to_bv 64 0); C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                               C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
  rw_cells b0segs mi (P + 224) [C8 v224; C8 v232; CB 4 j4] -> rw_cells b0segs mi (P + 244) [CB 1028 jft] ->
  stk b0segs mi (P + 1272) (usp + -104) -> rw_cells b0segs mi (usp + -104) (FSAVED X) ->
  u8arr b0segs mi A1 (zb8 fm0 ARR1_SIZE) -> u8arr b0segs mi A2 (zb8 ec0 ARR2_SIZE) -> u32arr b0segs mi FT (zw32 bh0 65537) ->
  ART RT Σ1 mi -> KMem.mem_inv bsegs mi -> stk bsegs mi lo P -> wr_at bsegs mi FB 4088 -> wr_at bsegs mi SHF 512 ->
  ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0xa4cac) (Z_to_bv 64 P) gp tp u0 u1 u2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 FB) e1 e2 e3 e4 e5 e6 e7
                              (fe_s2 X) (Z_to_bv 64 A2) (fe_s4 X) (Z_to_bv 64 A1) cSB (fe_s7 X) (Z_to_bv 64 FT) (fe_s9 X) (fe_s10 X) (fe_s11 X) u3 u4 u5 u6)
                         F1 (Z_to_bv 64 0xa4cac) fc1 None mi (seg_rom b0segs))) c1 ->
  (forall c' (Σ2 : rts RT) (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR (fe_ra X) (fe_sp X) gp tp t0 t1 t2 (fe_s0 X) (fe_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                                 (fe_s2 X) (fe_s3 X) (fe_s4 X) (fe_s5 X) (fe_s6 X) (fe_s7 X) (fe_s8 X) (fe_s9 X) (fe_s10 X) (fe_s11 X) t3 t4 t5 t6)
                            F' (ret_pc (fe_ra X)) fc' None m' (seg_rom b0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
     ART RT Σ2 m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo usp ->
     u8arr b0segs m' A1 (zb8 (fh_fm HF) ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 (fst (fst RBF)) ARR2_SIZE) -> u32arr b0segs m' FT (zw32 (fh_bh HF) 65537) ->
     PRESI m' -> realizes bsegs c' T) ->
  realizes bsegs c1 T.
Proof.
  intros v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v88 v96 v104 v112 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 j4 jft
    u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 T c1 FACTS SLa SLb SLc FTJ GAP SAV AR1 AR2 FTB ART1 MI1 ST1 WRF WRS Hc1 Hk.
  fsenv_open XOK. afenv_open YOK. shsep_open. fs_keys.
  pose proof alloc_ceiling_range as ACR.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0.
  pose proof SOK as (FRM & SP0E & _). pose proof LIVS1 as LV1. pose proof LIVS2 as LV2. pose proof LIVSF as LVF.
  pose proof AX as [AX1 AX2].
  destruct FACTS as (FD & FF4 & FFM & FEC & FBK & FRB).
  assert (PR1 : PRESI mi) by (intros a _; reflexivity).
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB mi FB 24 (wr_at_sub bsegs mi FB 4088 FB 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & HDj).
  change (Z.to_nat 24) with 24%nat in HDj.
  apply (rw_cells_split_CB b0segs _ _ [] 24 _ [] [8;8;8]%nat) in HDj; [| reflexivity]. cbn [mk_CB_cells app] in HDj. cb8_all HDj.
  destruct (n_wr_at_rw_CB mi SHF 120 (wr_at_sub bsegs mi SHF 512 SHF 120 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (j120 & RZ).
  change (Z.to_nat 120) with 120%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (B0_fs_S1 (xFs X F1 fc1) Y _ XOK YOK YOFF AX mi); [exact SLc| exact HDj| exact RZ| exact (kmem_inv_N _ _ MI1)|]. clear SLc HDj RZ.
  intros m2 y12_2 y13_2 y14_2 SLc HD SHC NMI2 MU2 WM2 . apply evt_done. intros c2 Hc2.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLc, HD, SHC, NMI2, MU2, WM2.
  lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W mi m2 SOK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & _) end.
  xfer_l1 mi m2 MU2 WM2. clear NMI2 MU2 WM2.

  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 120 128 m2); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART2| exact MI2| exact ST2| exact WRS| exact Hc2|].
  clear Hc2. intros c3 m3 w0_3 w1_3 w2_3 r0_3 d1_3 d2_3 d3_3 d4_3 d5_3 d6_3 d7_3 w3_3 w4_3 w5_3 w6_3 F3 fc3 Hc3 ART3 MI3 ST3 WM3 BY3 STEP3.
  pose proof (pres_step_ours G Σ1 _ _ m2 m3 SOK PR2 STEP3 ltac:(right; right; lia)) as PR3.
  xfer_rt G SOK STEP3 WM3 m2 m3.
  clear STEP3 WM3 BY3.
  rewrite (KMState.ret_pc_even 0xa4f0c ltac:(lia) eq_refl) in Hc3.

  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m3 (SHF + 248) 16 (wr_at_sub bsegs m3 SHF 512 (SHF + 248) 16 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz3 & RZ).
  change (Z.to_nat 16) with 16%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c3 MST Hc3).
  eapply (B0_fs_S2 (xFs X F3 fc3) Y _ XOK YOK YOFF m3); [exact SLa| exact SLb| exact RZ| exact (kmem_inv_N _ _ MI3)|]. clear SLa SLb RZ.
  intros m4 SLa SLb NMI4 MU4 WM4 . apply evt_done. intros c4 Hc4.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLa, SLb, NMI4, MU4, WM4.
  lazymatch type of MU4 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m3 m4 SOK ART3 MI3 ST3 PR3 NMI4 MU4 WM4 ltac:(fp_ours)) as (ART4 & MI4 & ST4 & PR4 & _) end.
  xfer_l1 m3 m4 MU4 WM4. clear NMI4 MU4 WM4.

  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 0 120 128 m4); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART4| exact MI4| exact ST4| exact WRS| exact Hc4|].
  clear Hc4. intros c5 m5 w0_5 w1_5 w2_5 r0_5 d1_5 d2_5 d3_5 d4_5 d5_5 d6_5 d7_5 w3_5 w4_5 w5_5 w6_5 F5 fc5 Hc5 ART5 MI5 ST5 WM5 BY5 STEP5.
  pose proof (pres_step_ours G Σ1 _ _ m4 m5 SOK PR4 STEP5 ltac:(right; right; lia)) as PR5.
  xfer_rt G SOK STEP5 WM5 m4 m5.
  change (bytes_at b0segs m5 (SHF + 120) (repeat z8 128)) in BY5. rename BY5 into SHZ.
  clear STEP5 WM5.
  rewrite (KMState.ret_pc_even 0xa4f64 ltac:(lia) eq_refl) in Hc5.

  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m5 FCP 1024 (wr_at_sub bsegs m5 FB 4088 FCP 1024 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jfc & FCJ).
  change (Z.to_nat 1024) with 1024%nat in FCJ.
  destruct (n_wr_at_rw_CB m5 SLO 400 (wr_at_sub bsegs m5 FB 4088 SLO 400 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (Jlo & SJ).
  destruct (n_wr_at_rw_CB m5 SHI 400 (wr_at_sub bsegs m5 FB 4088 SHI 400 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (Jhi & HJ).
  assert (LJlo : Z.of_nat (length Jlo) = 400) by (pose proof (proj1 (proj1 (proj1 SJ))) as W; cbn in W; lia).
  assert (LJhi : Z.of_nat (length Jhi) = 400) by (pose proof (proj1 (proj1 (proj1 HJ))) as W; cbn in W; lia).
  change (Z.to_nat 400) with (Z.to_nat (4 * 100)) in SJ, HJ.
  pose proof (ovw_init b0segs m5 SLO 100 Jlo SJ ltac:(lia)) as SLOc. pose proof (ovw_init b0segs m5 SHI 100 Jhi HJ ltac:(lia)) as SHIc. clear SJ HJ.
  destruct (fs_readersZ m5 ART5 SHZ) as (SH1 & SH2 & SHFt & SHCp).
  destruct (AF_DRV Σ1 m5 ART5) as ((GS & _) & _). pose proof (ro_C8_KN m5 _ _ GS) as GOTS. clear GS.
  assert (GOTV : frdW b0segs WZ m5 0xcda98 [C8 (Z_to_bv 64 0xccd30)]).
  { apply frdW_intro_ro; [exact GOTS|]. cbn [disjoint_from cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
    clear - IMG1 IMG2 IMGF YFl YSLO YSHI YFCP XL13 YSl. unfold SH_LO in YSl. repeat split; lia. }
  clear GOTS.
  eapply (l1_realizes RT AF Σ1 PMc _ T c5 MST Hc5).
  eapply (B0_fs_body (xFs X F5 fc5) Y _ XOK XSEP YOK YSEP YOFF AX Jlo Jhi LJlo LJhi m5);
    [exact FD| exact FF4| exact FFM| exact FEC| exact FBK| exact FRB| exact SLa| exact SLb| exact FTJ| exact FCJ| exact AR1| exact AR2| exact FTB| exact SHIc| exact SLOc| exact SHC| exact GOTV
    | exact (kmem_inv_N _ _ MI5)| exact SH1| exact SH2| exact SHFt| exact SHCp|].
  clear SLa SLb FTJ FCJ AR1 AR2 FTB SHIc SLOc SHC GOTV SH1 SH2 SHFt SHCp.
  intros m6 w48 w56 w64 nd hd u112 u128 u136 u152 u160 u208 y5_6 y6_6 y7_6 y12_6 y13_6 y14_6 y15_6 y16_6 y17_6 y18_6 y20_6 y23_6 y25_6 y26_6 y27_6 y28_6 y29_6 y30_6 y31_6
    SLa SLb AR1 AR2 FTB FTL FCB SHIc SLOc SHC NMI6 MU6 WM6. apply evt_done. intros c6 Hc6.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLa, SLb, AR1, AR2, FTB, FTL, FCB, SHIc, SLOc, SHC, NMI6, MU6, WM6.
  change (SCb (xFs X F5 fc5) Y nd hd u112 u128 u136 u152 u160 u208) with (SCb X Y nd hd u112 u128 u136 u152 u160 u208) in SLb.
  lazymatch type of MU6 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m5 m6 SOK ART5 MI5 ST5 PR5 NMI6 MU6 WM6 ltac:(fp_ours)) as (ART6 & MI6 & ST6 & PR6 & _) end.
  xfer_l1 m5 m6 MU6 WM6. clear NMI6 MU6 WM6.

  clear SHZ.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 120 128 m6); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART6| exact MI6| exact ST6| exact WRS| exact Hc6|].
  clear Hc6. intros c7 m7 w0_7 w1_7 w2_7 r0_7 d1_7 d2_7 d3_7 d4_7 d5_7 d6_7 d7_7 w3_7 w4_7 w5_7 w6_7 F7 fc7 Hc7 ART7 MI7 ST7 WM7 BY7 STEP7.
  pose proof (pres_step_ours G Σ1 _ _ m6 m7 SOK PR6 STEP7 ltac:(right; right; lia)) as PR7.
  xfer_rt G SOK STEP7 WM7 m6 m7.
  clear STEP7 WM7 BY7.
  rewrite (KMState.ret_pc_even 0xa6ee0 ltac:(lia) eq_refl) in Hc7.

  (* [comment removed for export] *)
  destruct (rw_cells_cutZ b0segs _ FB _ 1%nat HD) as [HD0 HDr]. cbn [firstn skipn cells_size csize Nat.add] in HD0, HDr. clear HD.
  eapply (l1_realizes RT AF Σ1 PMc _ T c7 MST Hc7).
  eapply (B0_fs_S7 (xFs X F7 fc7) Y _ XOK XSEP YOK YSEP YOFF m7); [exact SLa| exact HD0| exact (kmem_inv_N _ _ MI7)|]. clear SLa HD0.
  intros m8 SLa HD0 NMI8 MU8 WM8 . apply evt_done. intros c8 Hc8.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLa, HD0, NMI8, MU8, WM8.
  lazymatch type of MU8 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m7 m8 SOK ART7 MI7 ST7 PR7 NMI8 MU8 WM8 ltac:(fp_ours)) as (ART8 & MI8 & ST8 & PR8 & _) end.
  xfer_l1 m7 m8 MU8 WM8. clear NMI8 MU8 WM8.
  (* [comment removed for export] *)
  eapply (sfree_call G PMc FDO MST Σ1 2112 m8); [exact SFREE| left; reflexivity| exact SOK| reflexivity| exact ART8| exact MI8| exact ST8| exact PR8| exact Hc8|].
  clear Hc8. intros c9 Σ2 m9 q0 q1 q2 vr g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 F9 fc9 Hc9 FRS2 LVE2 SP2 CR2 ART9 MI9 ST9 WM9 PR9 STEP9.
  rewrite (KMState.ret_pc_even 0xa6f04 ltac:(lia) eq_refl) in Hc9.
  assert (LIVa : In (A1, ARR1_SIZE) (rt_live RT Σ2)) by (rewrite LVE2; exact LV1).
  assert (LIVb : In (A2, ARR2_SIZE) (rt_live RT Σ2)) by (rewrite LVE2; exact LV2).
  assert (LIVc : In (FT, 262148) (rt_live RT Σ2)) by (rewrite LVE2; exact LVF).
  clear HD0 HDr FCB SHIc SLOc SHC WRF WRS.
  xfer_rt G I STEP9 WM9 m8 m9.
  (* [comment removed for export] *)
  unfold SCb in SLb.
  eapply (l1_realizes RT AF Σ2 PMc _ T c9 MST Hc9).
  eapply (B0_fs_S8 (xFs X F9 fc9) Y _ XOK YOK m9); [exact SLa| exact SLb| exact SLc| exact FTL| exact GAP| exact SAV| exact ST9|].
  intros STu. apply evt_done. intros c10 Hc10.
  eapply (Hk c10 Σ2 m9); [exact Hc10| exact FRS2| exact LVE2| exact SP2| exact CR2| exact ART9| exact MI9| exact STu| exact AR1| exact AR2| exact FTB| exact PR9].

Qed.
End Act.
End FSG.
