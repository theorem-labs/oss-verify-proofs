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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act A0_hm_L2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCHuff BzArrD CmpMem CmpHmKit AsanKit AsanCut A0_cmp_hmV A0_cmp_hmP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

Lemma In_f8 : In 248 set_shadow_vals. Proof. unfold set_shadow_vals. do 12 right. left. reflexivity. Qed.
Lemma In_00 : In 0 set_shadow_vals. Proof. left. reflexivity. Qed.

Section HMG.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SSH : forall v, In v set_shadow_vals -> set_shadow_contract RT v.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis SFREE : stack_free_contract RT 7.

Variable X : hmenv.
Hypothesis XOK : hmenv_ok X.
Notation usp := (bv_unsigned (he_sp X)).
Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
Notation NL := (he_NL X). Notation NF := (he_NF X). Notation gp := (he_gp X). Notation tp := (he_tp X). Notation lo := (he_lo X).
Notation Jl := (he_Jl X). Notation Jf := (he_Jf X). Notation len0 := (he_len X). Notation freq := (he_freq X).
Notation Wlen := [(El + lb, El + lb + A)].
Notation SAVED := [C8 (he_s11 X); C8 (he_s10 X); C8 (he_s9 X); C8 (he_s8 X); C8 (he_s7 X); C8 (he_s6 X); C8 (he_s5 X); C8 (he_s4 X); C8 (he_s3 X);
                   C8 (he_s2 X); C8 (he_s1 X); C8 (he_s0 X); C8 (he_ra X)].

(* [comment removed for export] *)
Lemma aconsts_of_art : forall Σ (m : mem), ART RT Σ m -> aconsts A0C m /\ aconsts_uar A0C m.
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
Variables (Σ1 : rts RT) (PMc : Model -> Prop) (Y : ahenv) (fr : list (Z * nat)) (live0 : list (Z * Z)) (sp0 pl nl : Z).
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Hypothesis YOK : ahenv_ok X Y. Hypothesis YSX : ahenv_sepx X Y. Hypothesis AX : sanchor (ah_FB Y) (ah_SHF Y). Hypothesis YOFF : ahenv_offsh X Y.
Notation P := (ah_P Y). Notation FB := (ah_FB Y). Notation SHF := (ah_SHF Y).
Notation HP := (ah_HP Y). Notation WT := (ah_WT Y). Notation PR := (ah_PR Y).
Hypothesis G : act_geom RT lo P usp sp0 true 7 FB SHF 8192 1024 fr live0 Wlen.
Hypothesis SOK : sig_ok RT sp0 true 7 FB fr live0 Σ1.
Hypothesis LIV0 : In (pl, nl) live0.
Hypothesis LIV1 : pl <= El. Hypothesis LIV2 : El + NL + 7 <= pl + nl. Hypothesis LIV3 : pl <= Ef. Hypothesis LIV4 : Ef + 4 * NF + 7 <= pl + nl.
(* [comment removed for export] *)
Hypothesis GSELF : FB + 8192 <= SHF \/ SHF + 1024 <= FB.
Hypothesis GLIVF : FB + 8192 <= pl \/ pl + nl <= FB.
Hypothesis GLIVS : pl + nl <= SHF \/ SHF + 1024 <= pl.
Variable mi : mem.   (* [comment removed for export] *)
Notation PRESI := (PRESI usp fr live0 Wlen mi).

Lemma LIVS : In (pl, nl) (rt_live RT Σ1). Proof. exact (proj2 (proj2 SOK) _ LIV0). Qed.

(* [comment removed for export] *)
Definition hm_shsep : Prop :=
  (FB + 8192 <= SHF \/ SHF + 1024 <= FB) /\ (HP + 1040 <= SHF \/ SHF + 1024 <= HP) /\ (WT + 2064 <= SHF \/ SHF + 1024 <= WT) /\
  (PR + 2064 <= SHF \/ SHF + 1024 <= PR) /\ (El + NL <= SHF \/ SHF + 1024 <= El) /\ (Ef + 4 * NF <= SHF \/ SHF + 1024 <= Ef) /\
  (El + NL <= FB \/ FB + 8192 <= El) /\ (Ef + 4 * NF <= FB \/ FB + 8192 <= Ef) /\
  FB + 24 <= HP /\ FB + 24 <= WT /\ FB + 24 <= PR /\ SHF + 1024 <= P /\ FB + 8192 <= P.
Lemma hm_shsep_ok : hm_shsep.
Proof.
  hmenv_open XOK. ahenv_open YOK. pose proof G as [_ _ _ _ GLOW GLOR _ _ _ GFR GSH _ _ _]. unfold RT_STACK in *.
  unfold hm_shsep. repeat split; lia.
Qed.
Ltac shsep_open :=
  let H := fresh "SHS" in pose proof hm_shsep_ok as H; unfold hm_shsep in H;
  let S1 := fresh "XS1" in let S2 := fresh "XS2" in let S3 := fresh "XS3" in let S4 := fresh "XS4" in let S5 := fresh "XS5" in let S6 := fresh "XS6" in
  let S7 := fresh "XS7" in let S8 := fresh "XS8" in
  destruct H as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & ?XHf & ?XWf & ?XPf & ?XSP & ?XFP);
  ah_box S1; ah_box S2; ah_box S3; ah_box S4; ah_box S5; ah_box S6; ah_box S7; ah_box S8.
(* [comment removed for export] *)
Ltac hm_keys :=
  pose proof (ck_intro P CStack) as KP; pose proof (ck_intro usp CStack) as KU; pose proof (ck_intro FB CFrame) as KFB; pose proof (ck_intro HP CFrame) as KHP;
  pose proof (ck_intro WT CFrame) as KWT; pose proof (ck_intro PR CFrame) as KPR; pose proof (ck_intro SHF CShadow) as KSH;
  pose proof (ck_intro El (CLive pl nl)) as KEl; pose proof (ck_intro Ef (CLive pl nl)) as KEf.
Ltac fp_ours := per_interval; cbn [outside]; lia.

Lemma hm_act_pro : forall (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v96 v104 v112 : word) (u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 : word) F1 fc1 T c1,
  rw_cells a0segs mi P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 (Z_to_bv 64 (El + lb)); C8 (Z_to_bv 64 A);
                        C8 v96; C8 v104; C8 v112] ->
  stk a0segs mi (P + 120) (usp + -104) -> rw_cells a0segs mi (usp + -104) SAVED ->
  u8arr a0segs mi El (ovb len0 Jl NL) -> u32arr a0segs mi Ef (ovw freq Jf NF) ->
  ART RT Σ1 mi -> KMem.mem_inv asegs mi -> stk asegs mi lo P -> wr_at asegs mi FB 8184 -> wr_at asegs mi SHF 1024 ->
  ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x9d148) (Z_to_bv 64 P) gp tp u0 u1 u2 (he_sp X) (Z_to_bv 64 P) (Z_to_bv 64 FB) e1 e2 e3 e4 e5 e6 e7
                              (he_s2 X) (Z_to_bv 64 17) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (Z_to_bv 64 (Ef + 4 * fb)) (he_s9 X) (he_s10 X)
                              (Z_to_bv 64 2147450880) u3 u4 u5 u6)
                         F1 (Z_to_bv 64 0x9d148) fc1 None mi (seg_rom a0segs))) c1 ->
  (* [comment removed for export] *)
  (forall c' (m' : mem) (w0 w1 w2 r0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 : word) F' fc',
     ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x9d2ec) (Z_to_bv 64 P) gp tp w0 w1 w2 (he_sp X) (Z_to_bv 64 P) r0 d1 d2 d3 d4 d5 d6 d7
                                 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 17) (Z_to_bv 64 FB) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (FB + 1200))
                                 (Z_to_bv 64 (Ef + 4 * fb)) (Z_to_bv 64 (SHF + 150)) (he_s10 X) (Z_to_bv 64 2147450880) w3 w4 w5 w6)
                            F' (Z_to_bv 64 0x9d2ec) fc' None m' (seg_rom a0segs))) c' ->
     ART RT Σ1 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo P -> wr_at asegs m' FB 8184 -> wr_at asegs m' SHF 1024 -> PRESI m' ->
     rw_cells a0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 (Z_to_bv 64 FB); C8 v56; C8 v64; C8 v72; C8 (Z_to_bv 64 (El + lb)); C8 (Z_to_bv 64 A);
                           C8 v96; C8 v104; C8 (Z_to_bv 64 FB)] ->
     rw_cells a0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1af99); C8 (Z_to_bv 64 0x9d0c8)] ->
     stk a0segs m' (P + 120) (usp + -104) -> rw_cells a0segs m' (usp + -104) SAVED ->
     u8arr a0segs m' El (ovb len0 Jl NL) -> u32arr a0segs m' Ef (ovw freq Jf NF) ->
     bytes_at a0segs m' (SHF + 4) (repeat z8 130) -> bytes_at a0segs m' (SHF + 150) (repeat z8 258) -> bytes_at a0segs m' (SHF + 424) (repeat z8 258) ->
     realizes asegs c' T) ->
  realizes asegs c1 T.
Proof.
  intros v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v96 v104 v112 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F1 fc1 T c1
    SL GAP SAV LEN FREQ ART1 MI1 ST1 WRF1 WRS1 Hc1 Hk.
  hmenv_open XOK. ahenv_open YOK. shsep_open. hm_keys.
  destruct YSX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & YHf & YWf & YPf & YLf & YFf).
  pose proof alloc_ceiling_range as ACR. unfold CEILh in *.
  assert (PR1 : PRESI mi) by (intros a _; reflexivity).
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB mi FB 24 (wr_at_sub asegs mi FB 8184 FB 24 WRF1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & HDj).
  change (Z.to_nat 24) with 24%nat in HDj.
  apply (rw_cells_split_CB a0segs _ _ [] 24 _ [] [8;8;8]%nat) in HDj; [| reflexivity]. cbn [mk_CB_cells app] in HDj. cb8_all HDj.
  destruct (n_wr_at_rw_CB mi SHF 4 (wr_at_sub asegs mi SHF 1024 SHF 4 WRS1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (j4 & SH4).
  change (Z.to_nat 4) with 4%nat in SH4.
  eapply (l1_realizes RT AF Σ1 PMc _ T c1 MST Hc1).
  eapply (A0_hm_P2 (xF X F1 fc1) Y _ XOK YOK YOFF AX mi); [exact SL| exact HDj| exact SH4| exact (kmem_inv_N _ _ MI1)|]. clear SL HDj SH4.
  intros m2 x12 x13 SL HD NMI2 MU2 WM2. apply evt_done. intros c2 Hc2.
  lazymatch type of MU2 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W mi m2 SOK ART1 MI1 ST1 PR1 NMI2 MU2 WM2 ltac:(fp_ours)) as (ART2 & MI2 & ST2 & PR2 & _) end.
  xfer_l1 mi m2 MU2 WM2. clear NMI2 MU2 WM2.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 4 130 m2); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART2| exact MI2| exact ST2| exact WRS1| exact Hc2|].
  clear Hc2. intros c3 m3 w0_3 w1_3 w2_3 r0_3 d1_3 d2_3 d3_3 d4_3 d5_3 d6_3 d7_3 w3_3 w4_3 w5_3 w6_3 F3 fc3 Hc3 ART3 MI3 ST3 WM3 BY3 STEP3.
  pose proof (pres_step_ours G Σ1 _ _ m2 m3 SOK PR2 STEP3 ltac:(right; right; lia)) as PR3.
  xfer_rt G SOK STEP3 WM3 m2 m3.
  clear STEP3 WM3 BY3.
  rewrite (KMState.ret_pc_even 0x9d1d8 ltac:(lia) eq_refl) in Hc3.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m3 (SHF + 134) 16 (wr_at_sub asegs m3 SHF 1024 (SHF + 134) 16 WRS1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz3 & RZ).
  change (Z.to_nat 16) with 16%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c3 MST Hc3).
  eapply (A0_hm_P3 (xF X F3 fc3) Y _ XOK YOK YOFF m3); [exact RZ| exact (kmem_inv_N _ _ MI3)|]. clear RZ.
  intros m4  NMI4 MU4 WM4. apply evt_done. intros c4 Hc4.
  lazymatch type of MU4 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m3 m4 SOK ART3 MI3 ST3 PR3 NMI4 MU4 WM4 ltac:(fp_ours)) as (ART4 & MI4 & ST4 & PR4 & _) end.
  xfer_l1 m3 m4 MU4 WM4. clear NMI4 MU4 WM4.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 150 258 m4); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART4| exact MI4| exact ST4| exact WRS1| exact Hc4|].
  clear Hc4. intros c5 m5 w0_5 w1_5 w2_5 r0_5 d1_5 d2_5 d3_5 d4_5 d5_5 d6_5 d7_5 w3_5 w4_5 w5_5 w6_5 F5 fc5 Hc5 ART5 MI5 ST5 WM5 BY5 STEP5.
  pose proof (pres_step_ours G Σ1 _ _ m4 m5 SOK PR4 STEP5 ltac:(right; right; lia)) as PR5.
  xfer_rt G SOK STEP5 WM5 m4 m5.
  clear STEP5 WM5 BY5.
  rewrite (KMState.ret_pc_even 0x9d22c ltac:(lia) eq_refl) in Hc5.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m5 (SHF + 408) 16 (wr_at_sub asegs m5 SHF 1024 (SHF + 408) 16 WRS1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz5 & RZ).
  change (Z.to_nat 16) with 16%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c5 MST Hc5).
  eapply (A0_hm_P4 (xF X F5 fc5) Y _ XOK YOK YOFF m5); [exact RZ| exact (kmem_inv_N _ _ MI5)|]. clear RZ.
  intros m6  NMI6 MU6 WM6. apply evt_done. intros c6 Hc6.
  lazymatch type of MU6 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m5 m6 SOK ART5 MI5 ST5 PR5 NMI6 MU6 WM6 ltac:(fp_ours)) as (ART6 & MI6 & ST6 & PR6 & _) end.
  xfer_l1 m5 m6 MU6 WM6. clear NMI6 MU6 WM6.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 424 258 m6); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART6| exact MI6| exact ST6| exact WRS1| exact Hc6|].
  clear Hc6. intros c7 m7 w0_7 w1_7 w2_7 r0_7 d1_7 d2_7 d3_7 d4_7 d5_7 d6_7 d7_7 w3_7 w4_7 w5_7 w6_7 F7 fc7 Hc7 ART7 MI7 ST7 WM7 BY7 STEP7.
  pose proof (pres_step_ours G Σ1 _ _ m6 m7 SOK PR6 STEP7 ltac:(right; right; lia)) as PR7.
  xfer_rt G SOK STEP7 WM7 m6 m7.
  clear STEP7 WM7 BY7.
  rewrite (KMState.ret_pc_even 0x9d27c ltac:(lia) eq_refl) in Hc7.
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m7 (SHF + 682) 18 (wr_at_sub asegs m7 SHF 1024 (SHF + 682) 18 WRS1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jz7 & RZ).
  change (Z.to_nat 18) with 18%nat in RZ.
  eapply (l1_realizes RT AF Σ1 PMc _ T c7 MST Hc7).
  eapply (A0_hm_P5 (xF X F7 fc7) Y _ XOK YOK YOFF m7); [exact RZ| exact (kmem_inv_N _ _ MI7)|]. clear RZ.
  intros m8 y12_8 NMI8 MU8 WM8. apply evt_done. intros c8 Hc8.
  lazymatch type of MU8 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m7 m8 SOK ART7 MI7 ST7 PR7 NMI8 MU8 WM8 ltac:(fp_ours)) as (ART8 & MI8 & ST8 & PR8 & _) end.
  xfer_l1 m7 m8 MU8 WM8. clear NMI8 MU8 WM8.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 0 4 130 m8); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART8| exact MI8| exact ST8| exact WRS1| exact Hc8|].
  clear Hc8. intros c9 m9 w0_9 w1_9 w2_9 r0_9 d1_9 d2_9 d3_9 d4_9 d5_9 d6_9 d7_9 w3_9 w4_9 w5_9 w6_9 F9 fc9 Hc9 ART9 MI9 ST9 WM9 BY9 STEP9.
  pose proof (pres_step_ours G Σ1 _ _ m8 m9 SOK PR8 STEP9 ltac:(right; right; lia)) as PR9.
  xfer_rt G SOK STEP9 WM9 m8 m9.
  change (bytes_at a0segs m9 (SHF + 4) (repeat z8 130)) in BY9. rename BY9 into SHH.
  clear STEP9 WM9.
  rewrite (KMState.ret_pc_even 0x9d2d4 ltac:(lia) eq_refl) in Hc9.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c9 MST Hc9). eapply (A0_hm_P6 (xF X F9 fc9) Y _ m9). clear Hc9. apply evt_done. intros c9z Hc9.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 0 150 258 m9); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART9| exact MI9| exact ST9| exact WRS1| exact Hc9|].
  clear Hc9. intros c10 m10 w0_10 w1_10 w2_10 r0_10 d1_10 d2_10 d3_10 d4_10 d5_10 d6_10 d7_10 w3_10 w4_10 w5_10 w6_10 F10 fc10 Hc10 ART10 MI10 ST10 WM10 BY10 STEP10.
  pose proof (pres_step_ours G Σ1 _ _ m9 m10 SOK PR9 STEP10 ltac:(right; right; lia)) as PR10.
  xfer_rt G SOK STEP10 WM10 m9 m10.
  change (bytes_at a0segs m10 (SHF + 150) (repeat z8 258)) in BY10. rename BY10 into SHW.
  clear STEP10 WM10.
  rewrite (KMState.ret_pc_even 0x9d2e0 ltac:(lia) eq_refl) in Hc10.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c10 MST Hc10). eapply (A0_hm_P7 (xF X F10 fc10) Y _ m10). clear Hc10. apply evt_done. intros c10z Hc10.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 0 424 258 m10); [exact SSH| exact SOK| exact In_00| reflexivity| exact ART10| exact MI10| exact ST10| exact WRS1| exact Hc10|].
  clear Hc10. intros c11 m11 w0_11 w1_11 w2_11 r0_11 d1_11 d2_11 d3_11 d4_11 d5_11 d6_11 d7_11 w3_11 w4_11 w5_11 w6_11 F11 fc11 Hc11 ART11 MI11 ST11 WM11 BY11 STEP11.
  pose proof (pres_step_ours G Σ1 _ _ m10 m11 SOK PR10 STEP11 ltac:(right; right; lia)) as PR11.
  xfer_rt G SOK STEP11 WM11 m10 m11.
  change (bytes_at a0segs m11 (SHF + 424) (repeat z8 258)) in BY11. rename BY11 into SHP.
  clear STEP11 WM11.
  rewrite (KMState.ret_pc_even 0x9d2ec ltac:(lia) eq_refl) in Hc11.
  eapply Hk; [exact Hc11| exact ART11| exact MI11| exact ST11| exact WRF1| exact WRS1| exact PR11| exact SL| exact HD| exact GAP| exact SAV| exact LEN| exact FREQ| exact SHH| exact SHW| exact SHP].
Qed.


Lemma hm_act_body : forall (v0 v8 v16 v24 v32 v40 v56 v64 v72 v96 v104 : word) (w0 w1 w2 r0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 : word) F11 fc11 T c11 (m11 : mem),
  hm_facts len0 freq lb fb A ->
  ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0x9d2ec) (Z_to_bv 64 P) gp tp w0 w1 w2 (he_sp X) (Z_to_bv 64 P) r0 d1 d2 d3 d4 d5 d6 d7
                              (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 17) (Z_to_bv 64 FB) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (FB + 1200))
                              (Z_to_bv 64 (Ef + 4 * fb)) (Z_to_bv 64 (SHF + 150)) (he_s10 X) (Z_to_bv 64 2147450880) w3 w4 w5 w6)
                         F11 (Z_to_bv 64 0x9d2ec) fc11 None m11 (seg_rom a0segs))) c11 ->
  ART RT Σ1 m11 -> KMem.mem_inv asegs m11 -> stk asegs m11 lo P -> wr_at asegs m11 FB 8184 -> wr_at asegs m11 SHF 1024 -> PRESI m11 ->
  rw_cells a0segs m11 P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 (Z_to_bv 64 FB); C8 v56; C8 v64; C8 v72; C8 (Z_to_bv 64 (El + lb)); C8 (Z_to_bv 64 A);
                         C8 v96; C8 v104; C8 (Z_to_bv 64 FB)] ->
  rw_cells a0segs m11 FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1af99); C8 (Z_to_bv 64 0x9d0c8)] ->
  stk a0segs m11 (P + 120) (usp + -104) -> rw_cells a0segs m11 (usp + -104) SAVED ->
  u8arr a0segs m11 El (ovb len0 Jl NL) -> u32arr a0segs m11 Ef (ovw freq Jf NF) ->
  bytes_at a0segs m11 (SHF + 4) (repeat z8 130) -> bytes_at a0segs m11 (SHF + 150) (repeat z8 258) -> bytes_at a0segs m11 (SHF + 424) (repeat z8 258) ->
  (forall c' (Σ2 : rts RT) (m' : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
     ASTA RT Σ2 PMc (eq (MS (mkR (he_ra X) (he_sp X) gp tp t0 t1 t2 (he_s0 X) (he_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                                 (he_s2 X) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X) (he_s9 X) (he_s10 X) (he_s11 X) t3 t4 t5 t6)
                            F' (ret_pc (he_ra X)) fc' None m' (seg_rom a0segs))) c' ->
     rt_frames RT Σ2 = fr -> rt_live RT Σ2 = rt_live RT Σ1 -> rt_sp0 RT Σ2 = sp0 -> rt_credit RT Σ2 = rt_credit RT Σ1 ->
     ART RT Σ2 m' -> KMem.mem_inv asegs m' -> stk asegs m' lo usp ->
     u8arr a0segs m' El (ovb (hs_len (hm_rounds 40 A 17 lb (hp_rs len0 freq lb fb A 0))) Jl NL) -> PRESI m' ->
     realizes asegs c' T) ->
  realizes asegs c11 T.
Proof.
  intros v0 v8 v16 v24 v32 v40 v56 v64 v72 v96 v104 w0 w1 w2 r0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F11 fc11 T c11 m11
    HMF Hc11 ART11 MI11 ST11 WRF11 WRS1 PR11 SL HD GAP SAV LEN FREQ SHH SHW SHP Hk.
  hmenv_open XOK. ahenv_open YOK. shsep_open. hm_keys.
  destruct YSX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & YHf & YWf & YPf & YLf & YFf).
  pose proof alloc_ceiling_range as ACR. unfold CEILh in *.
  pose proof G as [_ _ _ _ GLOW GLOR GPUS GSPT GSPA GFR GSH GSP0 _ _].
  pose proof SOK as (FRM & SP0E & _). pose proof LIVS as LIV.
  pose proof AX as [AX1 AX2]. pose proof YOFF as (_ & _ & YOF). unfold SH_LO, SH_HI in YOF.
  destruct HMF as [DN FACTS].
  (* [comment removed for export] *)
  destruct (n_wr_at_rw_CB m11 HP 1040 (wr_at_sub asegs m11 FB 8184 HP 1040 WRF11 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (Jh & HJ).
  destruct (n_wr_at_rw_CB m11 WT 2064 (wr_at_sub asegs m11 FB 8184 WT 2064 WRF11 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (Jw & WJ).
  destruct (n_wr_at_rw_CB m11 PR 2064 (wr_at_sub asegs m11 FB 8184 PR 2064 WRF11 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (Jp & PJ).
  change (Z.to_nat 1040) with (Z.to_nat (4 * 260)) in HJ. change (Z.to_nat 2064) with (Z.to_nat (4 * 516)) in WJ, PJ.
  pose proof (ovw_init a0segs m11 HP 260 Jh HJ ltac:(lia)) as HEAP. pose proof (ovw_init a0segs m11 WT 516 Jw WJ ltac:(lia)) as WGT.
  pose proof (ovw_init a0segs m11 PR 516 Jp PJ ltac:(lia)) as PAR. clear HJ WJ PJ.
  destruct (af_acc_live RT AF Σ1 m11 pl nl ART11 LIV) as [_ ACCL].
  pose proof (af_live_range RT AF Σ1 m11 pl nl ART11 LIV) as (PL0 & PL1 & _). rewrite SP0E in PL1.
  assert (TOP47 : sp0 - STACK_WIN <= 2^47) by (unfold STACK_WIN, USTACK_TOP in *; lia).
  pose proof (af_live_offshadow RT AF Σ1 m11 pl nl ART11 LIV) as LHI.
  assert (AFW : app_fp [(WT, WT + 2064)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [lia| exact I]).
  pose proof (acc_of_zero_shadow a0segs m11 FB SHF 150 258 AX1 AX2 ltac:(lia) ltac:(lia) SHW) as ACCW.
  assert (SHw : shzW a0segs [(WT, WT + 2064)] m11 WT (WT + 2064)).
  { apply (shzW_of_acc a0segs _ m11 _ _ WT (WT + 2064) ACCW AFW); [lia| lia| lia|]. clear - YWT AX1. Z.div_mod_to_equations. lia. }
  assert (SHf : shzW a0segs [(WT, WT + 2064)] m11 Ef (Ef + 4 * NF)).
  { apply (shzW_of_acc a0segs _ m11 pl nl Ef (Ef + 4 * NF) ACCL AFW); [lia| lia| lia|]. clear - LIV4. Z.div_mod_to_equations. lia. }
  eapply (l1_realizes RT AF Σ1 PMc _ T c11 MST Hc11).
  eapply (A0_hm_G (xF X F11 fc11) Y _ XOK YOK YOFF YSX Jh Jw Jp m11); [exact SL| exact HEAP| exact WGT| exact PAR| exact FREQ| exact (kmem_inv_N _ _ MI11)| exact SHw| exact SHf|]. clear SL HEAP WGT PAR FREQ SHw SHf.
  intros m12 x5 x6 x7 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 SL0 SLr HEAP WGT PAR FREQ NMI12 MU12 WM12. apply evt_done. intros c12 Hc12.
  cbn [xF he_El he_Ef he_lb he_fb he_A he_NL he_NF he_Jl he_Jf he_len he_freq he_sp he_lo he_gp he_tp] in SL0, SLr, HEAP, WGT, PAR, FREQ, MU12, WM12, NMI12.
  change (SLh (xF X F11 fc11) Y v96 v104) with (SLh X Y v96 v104) in SLr.
  lazymatch type of MU12 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m11 m12 SOK ART11 MI11 ST11 PR11 NMI12 MU12 WM12 ltac:(fp_ours)) as (ART12 & MI12 & ST12 & PR12 & _) end.
  xfer_l1 m11 m12 MU12 WM12. clear NMI12 MU12 WM12.
  (* [comment removed for export] *)
  assert (EX0 : hm_exec len0 freq lb fb A 0) by (intros r' Hr'; replace r' with 0%nat by lia; reflexivity).
  refine (cps_realizes asegs _ _ T c12
            (hm_rounds_cps RT AF MSET X Y Jh Jw Jp XOK YOK YSX AX Σ1 PMc fr pl nl m12 FDO MST FRM LIV LIV1 LIV2 ltac:(rewrite SP0E; exact GLOW) GLOR GSPT GSPA
               40 0 m12 v96 v104 F11 fc11 _ _ _ _ _ _ _ _ _ _ _ _ _ EX0 DN FACTS ART12 MI12 ST12
               (conj HEAP (conj WGT (conj PAR (conj LEN (conj SLr (conj SHH (conj SHW SHP))))))) (agree_refl _ _)) Hc12 _).
  intros c13 (m13 & hF & wF & pF & F13 & fc13 & z5 & z6 & z7 & z12 & z13 & z14 & z15 & z16 & z17 & z21 & z28 & z29 & z30 & z31 & Hc13 & ART13 & MI13 & ST13 & HI13 & AG13).
  clear HEAP WGT PAR LEN SLr SHH SHW SHP Hc12.
  destruct HI13 as (HEAP & WGT & PAR & LEN & SLr & SHH & SHW & SHP). unfold hmAG in AG13.
  (* [comment removed for export] *)
  assert (STEP13 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) P [(El + lb, El + lb + A); (HP, HP + 1040); (WT, WT + 2064); (PR, PR + 2064)] m12 m13)
    by (intros a Ha Ho; exact (AG13 a (conj Ha Ho))).
  pose proof (pres_step G Σ1 _ m12 m13 SOK PR12 STEP13 ltac:(per_interval; unfold ours; cbn [outside]; lia)) as PR13.
  clear WRF11 AG13.
  xfer_rtf G SOK STEP13 m12 m13. clear STEP13.
  (* [comment removed for export] *)
  clear SHP.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 424 258 m13); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART13| exact MI13| exact ST13| exact WRS1| exact Hc13|].
  clear Hc13. intros c14 m14 w0_14 w1_14 w2_14 r0_14 d1_14 d2_14 d3_14 d4_14 d5_14 d6_14 d7_14 w3_14 w4_14 w5_14 w6_14 F14 fc14 Hc14 ART14 MI14 ST14 WM14 BY14 STEP14.
  pose proof (pres_step_ours G Σ1 _ _ m13 m14 SOK PR13 STEP14 ltac:(right; right; lia)) as PR14.
  xfer_rt G SOK STEP14 WM14 m13 m14.
  clear STEP14 WM14 BY14.
  rewrite (KMState.ret_pc_even 0x9dd7c ltac:(lia) eq_refl) in Hc14.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c14 MST Hc14). eapply (A0_hm_E1 (xF X F14 fc14) Y _ m14 v96 v104); [exact SLr|]. clear Hc14. apply evt_done. intros c14z Hc14.
  clear SHW.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 150 258 m14); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART14| exact MI14| exact ST14| exact WRS1| exact Hc14|].
  clear Hc14. intros c15 m15 w0_15 w1_15 w2_15 r0_15 d1_15 d2_15 d3_15 d4_15 d5_15 d6_15 d7_15 w3_15 w4_15 w5_15 w6_15 F15 fc15 Hc15 ART15 MI15 ST15 WM15 BY15 STEP15.
  pose proof (pres_step_ours G Σ1 _ _ m14 m15 SOK PR14 STEP15 ltac:(right; right; lia)) as PR15.
  xfer_rt G SOK STEP15 WM15 m14 m15.
  clear STEP15 WM15 BY15.
  rewrite (KMState.ret_pc_even 0x9dd88 ltac:(lia) eq_refl) in Hc15.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ1 PMc _ T c15 MST Hc15). eapply (A0_hm_E2 (xF X F15 fc15) Y _ m15 v96 v104); [exact SLr|]. clear Hc15. apply evt_done. intros c15z Hc15.
  clear SHH.
  (* [comment removed for export] *)
  eapply (ss_call G PMc FDO MST Σ1 248 4 130 m15); [exact SSH| exact SOK| exact In_f8| reflexivity| exact ART15| exact MI15| exact ST15| exact WRS1| exact Hc15|].
  clear Hc15. intros c16 m16 w0_16 w1_16 w2_16 r0_16 d1_16 d2_16 d3_16 d4_16 d5_16 d6_16 d7_16 w3_16 w4_16 w5_16 w6_16 F16 fc16 Hc16 ART16 MI16 ST16 WM16 BY16 STEP16.
  pose proof (pres_step_ours G Σ1 _ _ m15 m16 SOK PR15 STEP16 ltac:(right; right; lia)) as PR16.
  xfer_rt G SOK STEP16 WM16 m15 m16.
  clear STEP16 WM16 BY16.
  rewrite (KMState.ret_pc_even 0x9dd94 ltac:(lia) eq_refl) in Hc16.
  (* [comment removed for export] *)
  destruct (rw_cells_cut a0segs _ FB _ 1%nat HD) as [HD0 HDr]. cbn [firstn skipn cells_size csize Nat.add] in HD0, HDr. clear HD.
  eapply (l1_realizes RT AF Σ1 PMc _ T c16 MST Hc16).
  eapply (A0_hm_E3 (xF X F16 fc16) Y _ XOK YOK YOFF m16 v96 v104); [exact SLr| exact HD0| exact (kmem_inv_N _ _ MI16)|]. clear SLr HD0.
  intros m17 SLr HD0 NMI17 MU17 WM17. apply evt_done. intros c17 Hc17.
  change (SLh (xF X F16 fc16) Y v96 v104) with (SLh X Y v96 v104) in SLr.
  lazymatch type of MU17 with munch ?W _ _ => destruct (after_l1 AF G Σ1 W m16 m17 SOK ART16 MI16 ST16 PR16 NMI17 MU17 WM17 ltac:(fp_ours)) as (ART17 & MI17 & ST17 & PR17 & _) end.
  xfer_l1 m16 m17 MU17 WM17. clear NMI17 MU17 WM17.
  (* [comment removed for export] *)
  eapply (sfree_call G PMc FDO MST Σ1 5600 m17); [exact SFREE| right; reflexivity| exact SOK| reflexivity| exact ART17| exact MI17| exact ST17| exact PR17| exact Hc17|].
  clear Hc17. intros c18 Σ2 m18 q0 q1 q2 vr g1 g2 g3 g4 g5 g6 g7 q3 q4 q5 q6 F18 fc18 Hc18 FRS2 LV2 SP2 CR2 ART18 MI18 ST18 WM18 PR18 STEP18.
  rewrite (KMState.ret_pc_even 0x9ddb8 ltac:(lia) eq_refl) in Hc18.
  assert (LIVΣ2 : In (pl, nl) (rt_live RT Σ2)) by (rewrite LV2; exact LIV).
  clear HD0 HDr HEAP WGT PAR FREQ WRS1.
  xfer_rt G I STEP18 WM18 m17 m18.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ2 PMc _ T c18 MST Hc18).
  eapply (A0_hm_E4 (xF X F18 fc18) Y _ XOK YOK YOFF m18 v0 v96 v104); [exact SL0| exact SLr| exact GAP| exact SAV| exact ST18|].
  intros STu. apply evt_done. intros c19 Hc19.
  eapply (Hk c19 Σ2 m18); [exact Hc19| exact FRS2| exact LV2| exact SP2| exact CR2| exact ART18| exact MI18| exact STu| exact LEN| exact PR18].
Qed.

End Act.
End HMG.

