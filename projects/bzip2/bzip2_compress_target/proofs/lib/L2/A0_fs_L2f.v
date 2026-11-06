(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCSortF BzArrD CmpMem BzCLemmasFs BzCFactsFs BzCFactsFs2 CmpFsKit0 AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_fsP A0_cmp_fsQ A0_cmp_fsZ.
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
Lemma n_rw_CB_of_bytes : forall (m : mem) d (bs : list byte), bytes_at a0segs m d bs -> wr_at asegs m d (Z.of_nat (length bs)) -> rw_cells a0segs m d [CB (length bs) bs].
Proof.
  intros m d bs HB HW. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma repeat_zero_nth : forall n k (b : byte), nth_error (repeat (Z_to_bv 8 0) n) k = Some b -> b = Z_to_bv 8 0.
Proof. intros n k b H. apply nth_error_In in H. apply repeat_spec in H. subst; reflexivity. Qed.

(* [comment removed for export] *)
Definition xFs (X : fsenv) (F' : bvmap 5 word) (fc' : bv 32) : fsenv :=
  FE (fe_ra X) (fe_sp X) (fe_gp X) (fe_tp X) (fe_s0 X) (fe_s1 X) (fe_s2 X) (fe_s3 X) (fe_s4 X) (fe_s5 X) (fe_s6 X) (fe_s7 X) (fe_s8 X) (fe_s9 X) (fe_s10 X) (fe_s11 X)
     F' fc' (fe_A1 X) (fe_A2 X) (fe_FT X) (fe_nb X) (fe_lo X) (fe_q1 X) (fe_q2 X) (fe_qF X) (fe_qsp X) (fe_fm X) (fe_ec X) (fe_bh X) (fe_sv X) (fe_m0 X).

Section FSG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis MCPY : memcpy_icontract RT e_asan_memcpy.
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
Lemma fs_aconsts_of_art : forall Σ (m : mem), ART RT Σ m -> aconsts A0C m /\ aconsts_uar A0C m.
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
Hypothesis IMGF : 0x61e000 <= FT.
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
Notation W6 := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_A2 X, fe_A2 X + ARR2_SIZE); (fe_FT X, fe_FT X + 262148); (ae_P Y + 24, ae_P Y + 224);
                (ae_SLO Y, ae_SLO Y + 400); (ae_SHI Y, ae_SHI Y + 400); (ae_SHF Y + 4, ae_SHF Y + 112); (ae_FCP Y, ae_FCP Y + 1024)].
Lemma fs_readers6 : forall (m : mem), ART RT Σ1 m -> bytes_at a0segs m (SHF + 120) (repeat z8 128) ->
  shzW a0segs W6 m A1 (A1 + ARR1_SIZE) /\ shzW a0segs W6 m A2 (A2 + ARR2_SIZE) /\ shzW a0segs W6 m FT (FT + 262144) /\ shzW a0segs W6 m FCP (FCP + 1024).
Proof.
  intros m ART0 SHZ. fsenv_open XOK. afenv_open YOK. pose proof alloc_ceiling_range as ACR. pose proof AX as [AX1 AX2].
  pose proof fs_shsep_ok as SHS. unfold fs_shsep in SHS.
  destruct SHS as (_ & _ & _ & D1 & D2 & DF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2 & L3 & L4 & PHI).
  destruct YOFF as (O1 & O2 & O3 & O4).
  assert (OP : P + 224 <= SH_LO \/ SH_HI <= P + 24) by (right; unfold SH_HI; clear - PHI; lia).
  unfold SH_LO, SH_HI in O4.
  assert (OL : SLO + 400 <= SH_LO \/ SH_HI <= SLO) by (unfold SH_LO, SH_HI; clear - O4 YSLO; lia).
  assert (OH : SHI + 400 <= SH_LO \/ SH_HI <= SHI) by (unfold SH_LO, SH_HI; clear - O4 YSHI; lia).
  assert (OC : FCP + 1024 <= SH_LO \/ SH_HI <= FCP) by (unfold SH_LO, SH_HI; clear - O4 YFCP; lia).
  assert (GEN : forall lo hi, 0 <= lo -> hi <= 2^47 -> (hi <= FB + 32 \/ FB + 896 <= lo) ->
            forall x, lo <= x < hi -> disjoint_from W6 (x / 8 + 2147450880) 1).
  { intros lo' hi' H0 H47 DJ x Hx. cbn [disjoint_from].
    assert (X47 : 0 <= x < 2^47) by (clear - H0 H47 Hx; lia).
    split; [apply shd_app; [exact X47| exact O1]|]. split; [apply shd_app; [exact X47| exact O2]|]. split; [apply shd_app; [exact X47| exact O3]|].
    split; [apply shd_app; [exact X47| exact OP]|]. split; [apply shd_app; [exact X47| exact OL]|]. split; [apply shd_app; [exact X47| exact OH]|].
    split; [apply (shd_anchor FB SHF 4 112 x AX); clear - DJ Hx; lia|]. split; [apply shd_app; [exact X47| exact OC]| exact I]. }
  destruct (af_acc_live RT AF Σ1 m A1 ARR1_SIZE ART0 LIVS1) as [_ ACC1]. destruct (af_acc_live RT AF Σ1 m A2 ARR2_SIZE ART0 LIVS2) as [_ ACC2].
  destruct (af_acc_live RT AF Σ1 m FT 262148 ART0 LIVSF) as [_ ACCF].
  pose proof (acc_of_zero_shadow a0segs m FB SHF 120 128 AX1 AX2 ltac:(clear - YFl; lia) ltac:(clear; lia) SHZ) as ACCC.
  replace (FB + 8 * 120) with FCP in ACCC by (clear - YFCP; lia). change (8 * Z.of_nat 128) with 1024 in ACCC.
  split; [| split; [| split]].
  - apply (shzW_of_acc_gen a0segs W6 m A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1); [clear - XA1l; lia| clear; lia| clear - AL1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XA1l; lia| clear - XA1h ACR; lia| clear - D1; lia].
  - apply (shzW_of_acc_gen a0segs W6 m A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2); [clear - XA2l; lia| clear; lia| clear - AL2; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XA2l; lia| clear - XA2h ACR; lia| clear - D2; lia].
  - apply (shzW_of_acc_gen a0segs W6 m FT 262148 FT (FT + 262144) ACCF); [clear - XFl; lia| clear; lia| clear - ALF; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - XFl; lia| clear - XFh ACR; lia| clear - DF; lia].
  - apply (shzW_of_acc_gen a0segs W6 m FCP 1024 FCP (FCP + 1024) ACCC); [clear - YFl YFCP; lia| clear; lia| clear - YFCP AX1; Z.div_mod_to_equations; lia|].
    apply GEN; [clear - YFl YFCP; lia| clear - YFh YFCP ACR; lia| clear - YFCP; lia].
Qed.

Lemma fs_act : forall (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 : word) (v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word)
    (v224 v232 : word) (j4 jft : list byte) (u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F1 fc1 T c1,
  fs_facts fm0 ec0 bh0 nb ->
  rw_cells a0segs mi P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72] ->
  rw_cells a0segs mi (P + 80) [C8 v80; C8 v88; C8 (Z_to_bv 64 nb); C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                               C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
  rw_cells a0segs mi (P + 224) [C8 v224; C8 v232; CB 4 j4] -> rw_cells a0segs mi (P + 244) [CB 1028 jft] ->
  stk a0segs mi (P + 1272) (usp + -104) -> rw_cells a0segs mi (usp + -104) (FSAVED X) ->
  u8arr a0segs mi A1 (zb8 fm0 ARR1_SIZE) -> u8arr a0segs mi A2 (zb8 ec0 ARR2_SIZE) -> u32arr a0segs mi FT (zw32 bh0 65537) ->
  ART RT Σ1 mi -> KMem.mem_inv asegs mi -> stk asegs mi lo P -> wr_at asegs mi FB 4088 -> wr_at asegs mi SHF 512 ->
  ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x9aab4) (Z_to_bv 64 P) gp tp u0 u1 u2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 FB) e1 e2 e3 e4 e5 e6 e7
                              (fe_s2 X) (fe_s3 X) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB (Z_to_bv 64 0) (Z_to_bv 64 FT) (fe_s9 X) (fe_s10 X) (fe_s11 X) u3 u4 u5 u6)
                         F1 (Z_to_bv 64 0x9aab4) fc1 None mi (seg_rom a0segs))) c1 ->
  (forall c' (Σ2 : rts RT) (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR (fe_ra X) (fe_sp X) gp tp t0 t1 t2 (fe_s0 X) (fe_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                                 (fe_s2 X) (fe_s3 X) (fe_s4 X) (fe_s5 X) (fe_s6 X) (fe_s7 X) (fe_s8 X) (fe_s9 X) (fe_s10 X) (fe_s11 X) t3 t4 t5 t6)
                            F' (ret_pc (fe_ra X)) fc' None m' (seg_rom a0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo usp ->
     u8arr a0segs m' A1 (zb8 (fh_fm HF) ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 (fst (fst RBF)) ARR2_SIZE) -> u32arr a0segs m' FT (zw32 (fh_bh HF) 65537) ->
     PRESI m' -> realizes asegs c' T) ->
  realizes asegs c1 T.
Proof.
  intros v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 v224 v232 j4 jft
    u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 T c1 FACTS SLa SLb SLc FTJ GAP SAV AR1 AR2 FTB ART1 MI1 ST1 WRF WRS Hc1 Hk.
  fsenv_open XOK. afenv_open YOK. shsep_open. fs_keys.
  pose proof alloc_ceiling_range as ACR.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _]. unfold USTACK_TOP, RT_STACK, STACK_WIN, SEGTOP_A in GLOW, GLOR, GSPT, GFR, GSH, GSP0.
  pose proof SOK as (FRM & SP0E & _). pose proof LIVS1 as LV1. pose proof LIVS2 as LV2. pose proof LIVSF as LVF.
  pose proof AX as [AX1 AX2].
  destruct FACTS as (FD & FF4 & FFM & FEC & FBK & FRB).
  assert (PR1 : PRESI mi) by (intros a _; reflexivity).
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB mi FB 24 (wr_at_sub asegs mi FB 4088 FB 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & HDj).
  change (Z.to_nat 24) with 24%nat in HDj.
  apply (rw_cells_split_CB a0segs _ _ [] 24 _ [] [8;8;8]%nat) in HDj; [| reflexivity]. cbn [mk_CB_cells app] in HDj. cb8_all HDj.
  destruct (n_wr_at_rw_CB mi SHF 120 (wr_at_sub asegs mi SHF 512 SHF 120 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (j120 & RZ).
  change (Z.to_nat 120) with 120%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (A0_fs_S1 (xFs X F1 fc1) Y _ XOK YOK YOFF AX mi); [exact SLa| exact SLc| exact HDj| exact RZ| exact (kmem_inv_N _ _ MI1)|]. clear SLa SLc HDj RZ.
  intros m2 y12_2 y13_2 y14_2 SLa SLc HD SHC NMI2 MU2 WM2 . apply evt_done. intros c2 Hc2.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLa, SLc, HD, SHC, NMI2, MU2, WM2.
  lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W mi m2 SOK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & _) end.
  xfer_l1 mi m2 MU2 WM2. clear NMI2 MU2 WM2.

  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 120 128 m2); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART2| exact MI2| exact ST2| exact WRS| exact Hc2|].
  clear Hc2. intros c3 m3 w0_3 w1_3 w2_3 r0_3 d1_3 d2_3 d3_3 d4_3 d5_3 d6_3 d7_3 w3_3 w4_3 w5_3 w6_3 F3 fc3 Hc3 ART3 MI3 ST3 WM3 BY3 STEP3.
  pose proof (pres_step_ours G Σ1 _ _ m2 m3 SOK PR2 STEP3 ltac:(right; right; lia)) as PR3.
  xfer_rt G SOK STEP3 WM3 m2 m3.
  clear STEP3 WM3 BY3.
  rewrite (KMState.ret_pc_even 0x9ad14 ltac:(lia) eq_refl) in Hc3.

  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m3 (SHF + 248) 16 (wr_at_sub asegs m3 SHF 512 (SHF + 248) 16 WRS ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz3 & RZ).
  change (Z.to_nat 16) with 16%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c3 MST Hc3).
  eapply (A0_fs_S2 (xFs X F3 fc3) Y _ XOK YOK YOFF m3); [exact SLa| exact SLb| exact RZ| exact (kmem_inv_N _ _ MI3)|]. clear SLa SLb RZ.
  intros m4 SLa SLb NMI4 MU4 WM4 . apply evt_done. intros c4 Hc4.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLa, SLb, NMI4, MU4, WM4.
  lazymatch type of MU4 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m3 m4 SOK ART3 MI3 ST3 PR3 NMI4 MU4 WM4 ltac:(fp_ours)) as (ART4 & MI4 & ST4 & PR4 & _) end.
  xfer_l1 m3 m4 MU4 WM4. clear NMI4 MU4 WM4.

  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 0 120 128 m4); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART4| exact MI4| exact ST4| exact WRS| exact Hc4|].
  clear Hc4. intros c5 m5 w0_5 w1_5 w2_5 r0_5 d1_5 d2_5 d3_5 d4_5 d5_5 d6_5 d7_5 w3_5 w4_5 w5_5 w6_5 F5 fc5 Hc5 ART5 MI5 ST5 WM5 BY5 STEP5.
  pose proof (pres_step_ours G Σ1 _ _ m4 m5 SOK PR4 STEP5 ltac:(right; right; lia)) as PR5.
  xfer_rt G SOK STEP5 WM5 m4 m5.
  change (bytes_at a0segs m5 (SHF + 120) (repeat z8 128)) in BY5. rename BY5 into SHZ.
  clear STEP5 WM5.
  rewrite (KMState.ret_pc_even 0x9ad6c ltac:(lia) eq_refl) in Hc5.

  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c5 MST Hc5). eapply (A0_fs_S3 (xFs X F5 fc5) Y _ m5). clear Hc5. apply evt_done. intros c5z Hc5.
  pose proof (proj2 FTJ) as WRT. cbn [cells_size csize Nat.add] in WRT. change (Z.of_nat 1028) with 1028 in WRT. clear FTJ.
  eapply (memset_call G PMc FDO MST Σ1 (P + 244) 1028 z8 m5); [exact MSET| exact SOK| lia| lia| | exact ART5| exact MI5| exact ST5| exact Hc5|].
  { apply (cdst_stack AF G Σ1 m5 (P + 244) 1028 SOK ART5 WRT); unfold USTACK_TOP; lia. }
  clear Hc5. intros c6 m6 w0_6 w1_6 w2_6 d1_6 d2_6 d3_6 d4_6 d5_6 d6_6 d7_6 w3_6 w4_6 w5_6 w6_6 F6 fc6 Hc6 ART6 MI6 ST6 WM6 BY6 STEP6.
  pose proof (pres_step_ours G Σ1 _ _ m5 m6 SOK PR5 STEP6 ltac:(left; lia)) as PR6.
  xfer_rt G SOK STEP6 WM6 m5 m6. clear STEP6 WM6.
  rewrite (KMState.ret_pc_even 0x9ad8c ltac:(lia) eq_refl) in Hc6.
  assert (FTL : u32arr a0segs m6 (P + 244) (zw32 fp_ft1 257)).
  { pose proof (n_rw_CB_of_bytes m6 (P + 244) (repeat z8 (Z.to_nat 1028)) BY6 ltac:(rewrite repeat_length; exact WRT)) as FTZ.
    rewrite repeat_length in FTZ. change (Z.to_nat 1028) with (Z.to_nat (4 * 257)) in FTZ.
    rewrite (zw32_ext fp_ft1 znew 257). 2:{ intros i Hi. unfold fp_ft1. rewrite fs_ftab_zero_get, zget_znew. destruct (_ && _); reflexivity. }
    eapply (zw32_init a0segs _ _ 257 _ FTZ); [lia| apply repeat_zero_nth]. }
  clear BY6 WRT.

  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ1 m6 A2 ARR2_SIZE ART6 LV2) as [_ ACC2].
  assert (AFW4 : app_fp [(P + 184, P + 200); (P + 244, P + 1272)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [right; lia| split; [right; lia| exact I]]).
  assert (SH2 : shzW a0segs [(P + 184, P + 200); (P + 244, P + 1272)] m6 A2 (A2 + ARR2_SIZE)).
  { apply (shzW_of_acc a0segs _ m6 A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2 AFW4); [lia| lia| lia|]. clear - AL2. Z.div_mod_to_equations. lia. }
  clear ACC2 AFW4.
  eapply (l1_realizes RT AF Σ1 PMc _ T c6 MST Hc6).
  eapply (A0_fs_S4 (xFs X F6 fc6) Y _ XOK XSEP YOK YSEP YOFF m6); [exact SLb| exact AR2| exact FTL| exact (kmem_inv_N _ _ MI6)| exact SH2|]. clear SLb AR2 FTL SH2.
  intros m7 y13_7 y14_7 SLb AR2 FTL NMI7 MU7 WM7 FT2B. apply evt_done. intros c7 Hc7.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLb, AR2, FTL, FT2B, NMI7, MU7, WM7.
  lazymatch type of MU7 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m6 m7 SOK ART6 MI6 ST6 PR6 NMI7 MU7 WM7 ltac:(fp_ours)) as (ART7 & MI7 & ST7 & PR7 & _) end.
  xfer_l1 m6 m7 MU7 WM7. clear NMI7 MU7 WM7.

  (* [comment removed for export] *)
  set (ft2 := fp_ft2 ec0 nb) in *.
  assert (SRC : bytes_at a0segs m7 (P + 244) (u32s (zw32 ft2 256))).
  { pose proof (proj1 FTL) as B. rewrite (zw32_split_at ft2 256 257) in B by lia. rewrite u32s_app in B.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [B _]. exact B. }
  assert (LBS : Z.of_nat (length (u32s (zw32 ft2 256))) = 1024) by (rewrite u32s_length, zw32_length_nat; reflexivity).
  pose proof (acc_of_zero_shadow a0segs m7 FB SHF 120 128 AX1 AX2 ltac:(lia) ltac:(lia) SHZ) as ACCC.
  replace (FB + 8 * 120) with FCP in ACCC by lia. change (8 * Z.of_nat 128) with 1024 in ACCC.
  assert (WRC : wr_at asegs m7 FCP 1024) by exact (wr_at_sub asegs m7 FB 4088 FCP 1024 WRF ltac:(lia) ltac:(lia) ltac:(lia)).   (* [comment removed for export] *)
  rewrite <- LBS in Hc7.
  eapply (memcpy_call G PMc FDO MST Σ1 FCP (P + 244) (u32s (zw32 ft2 256)) m7);
    [exact MCPY| exact SOK| lia| lia| rewrite LBS; lia| exact SRC| | | rewrite LBS; lia| exact ART7| exact MI7| exact ST7| exact Hc7|].
  { rewrite LBS. apply (csrc_stack AF G Σ1 m7 (P + 244) 1024 SOK ART7); unfold USTACK_TOP; lia. }
  { rewrite LBS. apply (cdst_frame G Σ1 m7 FCP 1024 SOK ACCC WRC); lia. }
  clear Hc7 SRC ACCC. intros c8 m8 w0_8 w1_8 w2_8 d1_8 d2_8 d3_8 d4_8 d5_8 d6_8 d7_8 w3_8 w4_8 w5_8 w6_8 F8 fc8 Hc8 ART8 MI8 ST8 WM8 BY8 STEP8.
  rewrite LBS in STEP8.
  pose proof (pres_step_ours G Σ1 _ _ m7 m8 SOK PR7 STEP8 ltac:(right; left; lia)) as PR8.
  xfer_rt G SOK STEP8 WM8 m7 m8. clear STEP8 WM8.
  rewrite (KMState.ret_pc_even 0x9ae08 ltac:(lia) eq_refl) in Hc8.
  assert (FCB : u32arr a0segs m8 FCP (zw32 (fp_fc0 ec0 nb) 256)).
  { rewrite (zw32_ext (fp_fc0 ec0 nb) ft2 256).
    2:{ intros i Hi. subst ft2. unfold fp_fc0. rewrite fs_copy_get, zget_znew.
        replace ((0 <=? i) && (i <? 0 + Z.of_nat 256))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    split; [exact BY8|]. rewrite zw32_length_nat. exact WRC. }
  clear BY8 WRC LBS.

  (* [comment removed for export] *)
  destruct (af_acc_live RT AF Σ1 m8 A1 ARR1_SIZE ART8 LV1) as [_ ACC1]. destruct (af_acc_live RT AF Σ1 m8 A2 ARR2_SIZE ART8 LV2) as [_ ACC2].
  pose proof (af_live_offshadow RT AF Σ1 m8 A1 ARR1_SIZE ART8 LV1) as OF1.
  assert (AFW5 : app_fp [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - OF1; lia| split; [right; lia| exact I]]).
  assert (SH1 : shzW a0segs [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)] m8 A1 (A1 + ARR1_SIZE)).
  { apply (shzW_of_acc a0segs _ m8 A1 ARR1_SIZE A1 (A1 + ARR1_SIZE) ACC1 AFW5); [lia| lia| lia|]. clear - AL1. Z.div_mod_to_equations. lia. }
  assert (SH2 : shzW a0segs [(A1, A1 + ARR1_SIZE); (P + 244, P + 1272)] m8 A2 (A2 + ARR2_SIZE)).
  { apply (shzW_of_acc a0segs _ m8 A2 ARR2_SIZE A2 (A2 + ARR2_SIZE) ACC2 AFW5); [lia| lia| lia|]. clear - AL2. Z.div_mod_to_equations. lia. }
  clear ACC1 ACC2 AFW5 OF1.
  eapply (l1_realizes RT AF Σ1 PMc _ T c8 MST Hc8).
  eapply (A0_fs_S5 (xFs X F8 fc8) Y _ XOK XSEP YOK YSEP YOFF m8); [exact SLb| exact AR1| exact AR2| exact FTL| exact (kmem_inv_N _ _ MI8)| exact SH1| exact SH2| exact FT2B| exact FD|]. clear SLb AR1 AR2 FTL SH1 SH2.
  intros m9 y3_9 y4_9 y5_9 y6_9 y7_9 SLb AR1 AR2 FTL NMI9 MU9 WM9 . apply evt_done. intros c9 Hc9.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLb, AR1, AR2, FTL, NMI9, MU9, WM9.
  lazymatch type of MU9 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m8 m9 SOK ART8 MI8 ST8 PR8 NMI9 MU9 WM9 ltac:(fp_ours)) as (ART9 & MI9 & ST9 & PR9 & _) end.
  xfer_l1 m8 m9 MU9 WM9. clear NMI9 MU9 WM9.

  (* [comment removed for export] *)
  set (nB := fp_nB nb) in *.
  assert (HnB : 2 <= nB <= 28127).
  { subst nB. unfold fp_nB. pose proof (Z.div_pos nb 32 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound nb 32 28125 ltac:(lia) ltac:(lia)). lia. }
  rewrite (zw32_split_at bh0 nB 65537) in FTB by lia.
  apply (proj1 (u32arr_app a0segs _ _ _ _)) in FTB. destruct FTB as [_ FTBb].
  rewrite zw32_length_nat in FTBb. replace (FT + 4 * Z.of_nat (Z.to_nat nB)) with (FT + 4 * nB) in FTBb by lia.
  eapply (memset_call G PMc FDO MST Σ1 FT (4 * nB) z8 m9); [exact MSET| exact SOK| lia| lia| | exact ART9| exact MI9| exact ST9| exact Hc9|].
  { apply (cdst_live AF G Σ1 m9 FT 262148 FT (4 * nB) ART9 LVF); lia. }
  clear Hc9. intros c10 m10 w0_10 w1_10 w2_10 d1_10 d2_10 d3_10 d4_10 d5_10 d6_10 d7_10 w3_10 w4_10 w5_10 w6_10 F10 fc10 Hc10 ART10 MI10 ST10 WM10 BY10 STEP10.
  pose proof (pres_step G Σ1 _ m9 m10 SOK PR9 STEP10 ltac:(per_interval; right; cbn [outside]; lia)) as PR10.
  xfer_rt G SOK STEP10 WM10 m9 m10. clear STEP10 WM10.
  rewrite (KMState.ret_pc_even 634608 ltac:(lia) eq_refl) in Hc10.
  set (bhz := fs_bh_zero (Z.to_nat nB) bh0 0).
  assert (FTB : u32arr a0segs m10 FT (zw32 bhz 65537)).
  { destruct (af_acc_live RT AF Σ1 m10 FT 262148 ART10 LVF) as [WRFT _].
    pose proof (n_rw_CB_of_bytes m10 FT (repeat z8 (Z.to_nat (4 * nB))) BY10
                  ltac:(rewrite repeat_length; apply (wr_at_sub asegs m10 FT 262148 FT _ WRFT); lia)) as FTZ.
    rewrite repeat_length in FTZ.
    rewrite (zw32_split_at bhz nB 65537) by lia. apply (proj2 (u32arr_app a0segs _ _ _ _)). split.
    - rewrite (zw32_ext bhz znew nB). 2:{ intros i Hi. subst bhz. rewrite fs_bh_zero_get, zget_znew. destruct (_ && _) eqn:E; [reflexivity|]. exfalso.
          apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E| apply Z.ltb_ge in E]; lia. }
      eapply (zw32_init a0segs _ _ nB _ FTZ); [lia| apply repeat_zero_nth].
    - rewrite zw32_length_nat. replace (FT + 4 * Z.of_nat (Z.to_nat nB)) with (FT + 4 * nB) by lia.
      rewrite (zw32_skipn_ext bhz bh0 nB 65537); [exact FTBb| lia|].
      intros i Hi. subst bhz. rewrite fs_bh_zero_get. destruct (_ && _) eqn:E; [| reflexivity]. exfalso.
      apply Bool.andb_true_iff in E. destruct E as [_ E]. apply Z.ltb_lt in E. lia. }
  clear FTBb BY10.

  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m10 SLO 400 (wr_at_sub asegs m10 FB 4088 SLO 400 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (Jlo & SJ).
  destruct (n_wr_at_rw_CB m10 SHI 400 (wr_at_sub asegs m10 FB 4088 SHI 400 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (Jhi & HJ).
  assert (LJlo : Z.of_nat (length Jlo) = 400) by (pose proof (proj1 (proj1 (proj1 SJ))) as W; cbn in W; lia).
  assert (LJhi : Z.of_nat (length Jhi) = 400) by (pose proof (proj1 (proj1 (proj1 HJ))) as W; cbn in W; lia).
  change (Z.to_nat 400) with (Z.to_nat (4 * 100)) in SJ, HJ.
  pose proof (ovw_init a0segs m10 SLO 100 Jlo SJ ltac:(lia)) as SLOc. pose proof (ovw_init a0segs m10 SHI 100 Jhi HJ ltac:(lia)) as SHIc. clear SJ HJ.
  destruct (fs_readers6 m10 ART10 SHZ) as (SH1 & SH2 & SHFt & SHCp).
  destruct (AF_DRV Σ1 m10 ART10) as ((GS & _) & _). pose proof (ro_C8_KN m10 _ _ GS) as GOTS. clear GS.
  eapply (l1_realizes RT AF Σ1 PMc _ T c10 MST Hc10).
  eapply (A0_fs_S6 (xFs X F10 fc10) Y _ XOK XSEP YOK YSEP YOFF AX Jlo Jhi LJlo LJhi m10); [exact IMGF| exact FF4| exact FFM| exact FEC| exact FBK| exact FRB| exact SLa| exact SLb| exact AR1| exact AR2| exact FTB| exact FTL| exact FCB| exact SHIc| exact SLOc| exact SHC| exact GOTS| exact (kmem_inv_N _ _ MI10)| exact SH1| exact SH2| exact SHFt| exact SHCp|]. clear SLa SLb AR1 AR2 FTB FTL FCB SHIc SLOc SHC GOTS SH1 SH2 SHFt SHCp.
  intros m11 w56 w64 w72 lq nd rr Hh u144 u160 u176 u200 u208 y0_11 y1_11 y2_11 y3_11 y4_11 y5_11 y6_11 y7_11 y10_11 y11_11 y12_11 y13_11 y14_11 y15_11 y16_11 y17_11 y18_11 y19_11 SLa SLb AR1 AR2 FTB FTL FCB SHIc SLOc SHC NMI11 MU11 WM11 . apply evt_done. intros c11 Hc11.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in Hh, SLa, SLb, AR1, AR2, FTB, FTL, FCB, SHIc, SLOc, SHC, NMI11, MU11, WM11.
  change (SCq (xFs X F10 fc10) Y lq nd u144 rr u160 Hh u176 u200 u208) with (SCq X Y lq nd u144 rr u160 Hh u176 u200 u208) in SLb.
  lazymatch type of MU11 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m10 m11 SOK ART10 MI10 ST10 PR10 NMI11 MU11 WM11 ltac:(fp_ours)) as (ART11 & MI11 & ST11 & PR11 & _) end.
  xfer_l1 m10 m11 MU11 WM11. clear NMI11 MU11 WM11.

  clear SHZ.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 120 128 m11); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART11| exact MI11| exact ST11| exact WRS| exact Hc11|].
  clear Hc11. intros c12 m12 w0_12 w1_12 w2_12 r0_12 d1_12 d2_12 d3_12 d4_12 d5_12 d6_12 d7_12 w3_12 w4_12 w5_12 w6_12 F12 fc12 Hc12 ART12 MI12 ST12 WM12 BY12 STEP12.
  pose proof (pres_step_ours G Σ1 _ _ m11 m12 SOK PR11 STEP12 ltac:(right; right; lia)) as PR12.
  xfer_rt G SOK STEP12 WM12 m11 m12.
  clear STEP12 WM12 BY12.
  rewrite (KMState.ret_pc_even 0x9c258 ltac:(lia) eq_refl) in Hc12.

  (* [comment removed for export] *)
  destruct (rw_cells_cutZ a0segs _ FB _ 1%nat HD) as [HD0 HDr]. cbn [firstn skipn cells_size csize Nat.add] in HD0, HDr. clear HD.
  eapply (l1_realizes RT AF Σ1 PMc _ T c12 MST Hc12).
  eapply (A0_fs_S7 (xFs X F12 fc12) Y _ XOK XSEP YOK YSEP YOFF m12); [exact SLa| exact HD0| exact (kmem_inv_N _ _ MI12)|]. clear SLa HD0.
  intros m13 SLa HD0 NMI13 MU13 WM13 . apply evt_done. intros c13 Hc13.
  cbn [xFs fe_A1 fe_A2 fe_FT fe_nb fe_ec fe_fm fe_bh fe_sp fe_lo] in SLa, HD0, NMI13, MU13, WM13.
  lazymatch type of MU13 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m12 m13 SOK ART12 MI12 ST12 PR12 NMI13 MU13 WM13 ltac:(fp_ours)) as (ART13 & MI13 & ST13 & PR13 & _) end.
  xfer_l1 m12 m13 MU13 WM13. clear NMI13 MU13 WM13.
  (* [comment removed for export] *)
  eapply (sfree_call G PMc FDO MST Σ1 2112 m13); [exact SFREE| left; reflexivity| exact SOK| reflexivity| exact ART13| exact MI13| exact ST13| exact PR13| exact Hc13|].
  clear Hc13. intros c14 Σ2 m14 q0 q1 q2 vr g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 F14 fc14 Hc14 FRS2 LVE2 SP2 CR2 ART14 MI14 ST14 WM14 PR14 STEP14.
  rewrite (KMState.ret_pc_even 0x9c278 ltac:(lia) eq_refl) in Hc14.
  assert (LIVa : In (A1, ARR1_SIZE) (rt_live RT Σ2)) by (rewrite LVE2; exact LV1).
  assert (LIVb : In (A2, ARR2_SIZE) (rt_live RT Σ2)) by (rewrite LVE2; exact LV2).
  assert (LIVc : In (FT, 262148) (rt_live RT Σ2)) by (rewrite LVE2; exact LVF).
  clear HD0 HDr FCB SHIc SLOc SHC WRF WRS.
  xfer_rt G I STEP14 WM14 m13 m14.
  (* [comment removed for export] *)
  unfold SCq in SLb.
  eapply (l1_realizes RT AF Σ2 PMc _ T c14 MST Hc14).
  eapply (A0_fs_S8 (xFs X F14 fc14) Y _ XOK YOK m14); [exact SLa| exact SLb| exact SLc| exact FTL| exact GAP| exact SAV| exact ST14|].
  intros STu. apply evt_done. intros c15 Hc15.
  eapply (Hk c15 Σ2 m14); [exact Hc15| exact FRS2| exact LVE2| exact SP2| exact CR2| exact ART14| exact MI14| exact STu| exact AR1| exact AR2| exact FTB| exact PR14].

Qed.
End Act.
End FSG.
