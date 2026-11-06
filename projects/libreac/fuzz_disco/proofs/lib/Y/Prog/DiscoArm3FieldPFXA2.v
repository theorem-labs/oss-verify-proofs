(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA2.v, with its module names and numbers changed; 494 of its 575 lines of code are new or changed and 585 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YC88 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit DiscoArm3FieldPFXK DiscoArm3JtokSpec DiscoArm3FieldCall
DiscoArm3FieldMDKit DiscoArm3FieldMDFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel ReacHuntRole.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_json_text disco_json_reader_model reac_disco_table_json_c reac_disco_table_age_c
slot_ser_defs slot_ser_tokb disco_jscalar_model jtok_is_c printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require ConstsViewDef.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Notation XP := 2%Z (only parsing).

#[local] Ltac pfx_preg SR5 HP SR regs4 R r z :=
  transitivity (getr regs4 r); [exact (SR5 r ltac:(cbv; tauto)) |];
  transitivity (getr R r); [exact (HP z ltac:(unfold acallee_saved; lia)) | exact (SR r ltac:(cbv; tauto))].
#[local] Ltac pfx_kb := intros kk Hkk; cbn in Hkk; split; [|split]; lia.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis DBCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis MCRO : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Theorem a3f_pfxa_2 : seg_pfa_p_spec B MT XM_LIB RLO RHI tfib_K XP.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad W c Hs.
unfold f_pfx, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R24 & R22) & (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & R27).
pose proof HY as (HSLOTS & H408 & HUSED).
pose proof HSLOTS as (Hpc & H368 & H360).
pose proof HTAB as ((removed & Hage & Hpost) & HOT).
pose proof Hpost as (LT1 & _ & _ & _ & _ & _ & TOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os LT1 TOK1 Hnow HJR)
  as (Ecnt & Hc8 & Los & H6 & Hinb & Hg33 & Hlen).
assert (Hrole : disco_table_c.role_of_e T1 XP = 0 \/ disco_table_c.role_of_e T1 XP = 1 \/
  disco_table_c.role_of_e T1 XP = 2) by (pose proof TOK1 as (_ & T2 & _); apply T2; lia).
assert (Hr02 : 0 <= disco_table_c.role_of_e T1 XP <= 2) by lia.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HBASE | split; [exact HJ | exact HFRS]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (Tb & Gb & Lkb & HHb & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HdE & HREG & HFLAG & H184 & H120 & H136 & H376 & H280 & H232 & H264).
pose proof HdE as (HER & HE32 & HEI0 & HEA & HEF & HESH).
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
assert (HA64 : 0 <= d_A cx < 2 ^ 64) by lia.
assert (HFU : bv_unsigned (ew E AT_F) = d_FB cx)
  by (rewrite HEF; unfold w64; apply unsigned_lit_small; lia).
set (vals := a3f_vals regs ++ [Z_to_bv 64 (dnot (d_obj cx OUSED)); Z_to_bv 64 (dnot (d_obj cx OT))]).
assert (Lv : length vals = 34%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (E563 : ew (d_env cx E vals) 563 = Z_to_bv 64 (dnot (d_obj cx OUSED)))
  by exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia)).
assert (E564 : ew (d_env cx E vals) 564 = Z_to_bv 64 (dnot (d_obj cx OT)))
  by exact (d_env_x cx E vals 33 ltac:(rewrite Lv; lia)).
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HdE)))).
assert (VU : val_mem SEGS (rd W mem3) (d_FB cx + 1664 + 4 * XP) 4 0).
{ assert (EU : a3f_used XP = map (fun b : byte => bv_unsigned b) (map (Z_to_bv 8) (a3f_used XP)))
    by (vm_compute; reflexivity).
  pose proof HUSED as HU0. rewrite EU in HU0.
  pose proof (ReacHuntRole.hunt_val4 SEGS (rd W mem3) (d_obj cx OUSED) _ (4 * XP) HU0 ltac:(lia)
    ltac:(rewrite length_map, a3f_used_bytes by lia; lia)) as V.
  replace (disco_table_c.u_at (map (Z_to_bv 8) (a3f_used XP)) (4 * XP) 4) with 0 in V by (vm_compute; reflexivity).
  unfold d_obj, dobj_off in V. exact V. }
assert (VR : val_mem SEGS (rd W mem3) (d_FB cx + 2168 + 48 * XP) 4 (disco_table_c.role_of_e T1 XP)).
{ rewrite <- (a3f_role_u T1 XP) by lia.
  pose proof (ReacHuntRole.hunt_val4 SEGS (rd W mem3) (d_obj cx OT) T1 (48 * XP + 8) HOT ltac:(lia)
    ltac:(rewrite LT1; lia)) as V.
  unfold d_obj, dobj_off in V. replace (d_FB cx + 2160 + (48 * XP + 8)) with (d_FB cx + 2168 + 48 * XP) in V by lia.
  exact V. }
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) (a3f_xacs XP)).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - eapply chunk_ok_val with (v := dnot (d_obj cx OUSED)).
    + cbn [sv_denot]. rewrite E563, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold dnot, d_obj, dobj_off. lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H264.
  - eapply chunk_ok_val with (v := dnot (d_obj cx OT)).
    + cbn [sv_denot]. rewrite E564, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold dnot, d_obj, dobj_off. lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H280.
  - eapply chunk_ok_val with (v := d_obj cx OO + 144 * XP).
    + cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
      unfold d_obj, dobj_off. f_equal. lia.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold d_obj, dobj_off. lia.
    + cbv. intros Hq. discriminate Hq.
    + change (N.to_nat 8) with 8%nat. exact H408. }
assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx))
  (a3f_xfcs XP (disco_table_c.role_of_e T1 XP))).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply chunk_ok_val with (v := 0); [reflexivity | lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. rewrite Z.add_assoc. exact VU.
  - eapply chunk_ok_val with (v := disco_table_c.role_of_e T1 XP);
      [reflexivity | change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia | cbv; intros Hq; discriminate Hq |].
    change (N.to_nat 4) with 4%nat. rewrite Z.add_assoc. exact VR. }
assert (HGf : facts_ok (d_env cx E vals) (d_facts a3f_xfa [])).
{ apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals a3f_xfa [] HCTX HdE); [|exact I].
  cbn [a3f_xfa atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E563, E564, !unsigned_lit_small by (unfold dnot, d_obj, dobj_off; lia).
  rewrite Z.pow_0_r, !Z.mod_1_r. unfold dnot, d_obj, dobj_off. repeat split; lia. }
assert (HHS : d_hslots cx h W mem3) by exact (d_hslots_of_frame cx h dsh_ser2 W mem3 HFRM).
assert (CONT : forall ms mat,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_FB cx + 1664 + 4 * XP <= a < d_FB cx + 1668 + 4 * XP) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  mem_grows (rd W mem3) (rd W (ms_mem ms)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 8004) ->
  getr (ms_regs ms) 10 = Z_to_bv 64 (d_FB cx + 264 + 144 * XP) ->
  getr (ms_regs ms) 11 = Z_to_bv 64 1 ->
  getr (ms_regs ms) 12 = w64 (VAL (A_OBJ (a3f_roleobj (disco_table_c.role_of_e T1 XP)))) ->
  getr (ms_regs ms) 22 = Z_to_bv 64 (d_FB cx + 2160 + 48 * XP) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 24; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  d_frame cx h dsh_ser2 W (ms_mem ms) -> d_shadow cx dsh_ser2 W (ms_mem ms) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_FB cx + 1664 + 4 * XP) 4 1 ->
  SRr SEGS W (mkCfg (YK11.mkst (fx := fq) (ms_regs ms) (Z_to_bv 64 (BASE + AF_both3_jtok_is)) (ms_mem ms)
    (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md3) mat md3))
    (f_r1 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad XP)).
{ intros ms mat HJr KC HG Q1 Q10 Q11 Q12x Q22 SR HFRMc HSHDc VUc.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
set (R := ms_regs ms) in *.
assert (SpR : spZ R = d_A cx) by (unfold spZ; rewrite (SR 2%bv ltac:(cbv; tauto)); exact Rsp).
assert (KV : forall a nn v, (forall kk, 0 <= kk < Z.of_nat nn -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1664 + 4 * XP <= a + kk < d_FB cx + 1668 + 4 * XP)) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v).
{ intros a nn v Hb V. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms) a nn v); [|exact V].
  intros kk Hkk. destruct (Hb kk Hkk) as [Hb1 Hb2]. exact (KC _ Hb1 Hb2). }
assert (KG : forall a l, (forall kk, 0 <= kk < Z.of_nat (length l) -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1664 + 4 * XP <= a + kk < d_FB cx + 1668 + 4 * XP)) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l).
{ intros a l Hb Gx. apply (a3f_g8_kept (w_H W) (w_H W) mem3 (ms_mem ms) a l); [|exact Gx].
  intros kk Hkk. destruct (Hb kk Hkk) as [Hb1 Hb2]. exact (KC _ Hb1 Hb2). }
destruct (a3f_used_split XP ltac:(lia)) as (Lpre & Esp2 & Esp3).
assert (GU : garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OUSED) (a3f_used (XP + 1))).
{ rewrite Esp3. pose proof HUSED as G0. rewrite Esp2 in G0.
  apply garr8_app in G0 as [Gp G0]. apply garr8_app in G0 as [_ Gs].
  apply garr8_app. split.
  - apply KG; [|exact Gp]. intros kk Hkk. rewrite Lpre in Hkk. unfold d_obj, dobj_off. split; lia.
  - apply garr8_app. split.
    + rewrite Lpre. replace (d_obj cx OUSED + Z.of_nat (Z.to_nat (4 * XP))) with (d_FB cx + 1664 + 4 * XP)
        by (unfold d_obj, dobj_off; lia).
      exact (a3f_g8_w1 _ _ VUc).
    + apply KG; [|exact Gs]. intros kk Hkk.
      rewrite length_skipn, a3f_used_bytes in Hkk by lia. rewrite Lpre. unfold d_obj, dobj_off. cbn [length].
      split; lia. }
assert (HBODYc : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem ms)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx)
    (fun a => d_FB cx + 1664 + 4 * XP <= a < d_FB cx + 1668 + 4 * XP) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. intros Hrd. cbv beta in Ha.
    unfold d_rdset, d_objr in Hrd. unfold d_obj in Hrd. cbn [dobj_off dobj_size] in Hrd.
    pose proof HGEO as (Gf0 & Gfc & Gh0 & Ghc & Gcs & Gpl & Gfh & Gin).
    pose proof HCAN as (_ & _ & Gcan).
    destruct Hrd as [Hx | [Hx | [Hx | [Hx | [Hx | [(Hn0 & Hx) | [(Hro & _ & _) | Hx]]]]]]].
    + lia.
    + lia.
    + lia.
    + lia.
    + clear - Ha Hx Gfh. unfold HUNT_SIZE in *. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Gfh.
      destruct Gfh; lia.
    + destruct (Gin Hn0) as (_ & _ & Gd & _). clear - Ha Hx Gd.
      change (fs_frame_bytes DFRAME_CLASS) with 4096 in Gd. lia.
    + pose proof (a3f_roP_img a Hro) as Hai. unfold off_img in HOFF. lia.
    + pose proof (pa_img_range a (Gcan a Hx)) as Hai. unfold off_img in HOFF. lia.
  - intros a Ha Hna. exact (KC a Ha Hna).
  - intros a _ Hpr. eapply apresent_grows; [exact HG | exact Hpr].
  - exact HFRMc.
  - exact HSHDc.
  - lia. }
assert (HCTXc : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k) by exact (conj HBASE (conj HJr HFRS)).
pose proof (proj1 HJr) as HARc.
pose proof HBODYc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HIMGc & _).
pose proof (mc_cv_ok B W (ms_mem ms) MCRO MCUN HIMGc) as HCV.
pose proof (DCRO LAWS DROH ly3 S3 W (ms_mem ms) md' HARc HIMGc) as (_ & _ & _ & HSTR & _).
pose proof (a3f_rolestr W (ms_mem ms) _ Hr02 HSTR) as HRS.
destruct (mdf_rostr_x W (ms_mem ms) _ _ HRS) as (slack & XNZ & XG & XSL & X0 & X63 & X32 & XAM & XRA & XSH & XLE).
pose proof HRS as ((FR & _ & _ & _ & _ & _ & _ & _ & _ & XIMG) & _).
pose proof (DiscoArm3FieldModel.a3f_obj T1 now count os XP LT1 TOK1 Hnow HJR ltac:(lia)) as HOB. cbv zeta in HOB.
destruct HOB as (_ & JTR & _).
change (disco_json_text.e_role (reac_disco_table_json_c.tj_entry T1 XP)) with (disco_table_c.role_of_e T1 XP) in JTR.
set (tk := nth 1 (nth (Z.to_nat XP) os []) disco_json_reader_model.tok_none) in *.
pose proof HBLK as (HPm & _ & _ & _).
assert (Inb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPm)). unfold a3_xb. cbn [app In]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Inb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ DFRAME_CLASS (c_fpos cx) HARc Inb HFin3)
  as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EFA3 in Hsep.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsep.
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as Hrq.
pose proof HBUF as (Hr2 & GBUF). unfold a3_r in Hr2.
assert (GOOc : garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OO)
  (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))).
{ apply KG; [|exact HOO]. intros kk Hkk. rewrite length_map, (mdk_objs_len buf vpad os HVP H6), Los in Hkk.
  unfold d_obj, dobj_off. split; lia. }
assert (GBUFc : garr8 SEGS (rd W (ms_mem ms)) buf (a3_text T1 now ++ [0])).
{ apply KG; [|exact GBUF]. intros kk Hkk. rewrite length_app in Hkk. cbn [length] in Hkk. split; lia. }
destruct (mdk_site SEGS (rd W (ms_mem ms)) T1 now count os XP 1 (d_obj cx OO) buf
  (d_obj cx OO + 144 * XP + 24 * Z.of_nat 1) 1 vpad (disco_json_text.rolename (disco_table_c.role_of_e T1 XP)) tk
  LT1 TOK1 Hnow HJR ltac:(lia) ltac:(lia) HVP GOOc GBUFc ltac:(lia) ltac:(lia) eq_refl ltac:(lia) FR JTR eq_refl)
  as (J1 & J2 & J3 & F1 & F2 & F3 & Hvp & Hvn & JM & HlenP & GP & Hvp0 & Hvp63).
destruct (mdk_obj_tok os count XP 1 Los H6 ltac:(lia) ltac:(lia)) as (Ho & Ht0 & Ho6).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Hinb _ (nth_error_In _ _ Ho)) tk
  (nth_error_In _ _ Ht0)) as Hib.
destruct Hib as [Hz | (Hs0 & Hl0 & Hsl)]; [rewrite J1 in Hz; discriminate Hz|].
unfold disco_jscalar_model.jlen in Hsl.
destruct (mdf_frame_range B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md' k h n (a3_xb buf op) dsh_ser2
  240 1296 (d_obj cx OO + 144 * XP + 24 * Z.of_nat 1) 20 HCTXc HBODYc ltac:(vm_compute; reflexivity) ltac:(lia)
  ltac:(unfold DFRAME_SIZE; lia) ltac:(unfold d_obj; cbn [dobj_off]; lia) ltac:(unfold d_obj; cbn [dobj_off]; lia)
  ltac:(lia)) as (AMv & RAv & SHv).
assert (LTr : length (printf_facts_c.pf_bytes (disco_json_text.rolename (disco_table_c.role_of_e T1 XP))) =
  length (disco_json_text.rolename (disco_table_c.role_of_e T1 XP))) by (unfold printf_facts_c.pf_bytes; apply length_map).
assert (Lr7 : (length (disco_json_text.rolename (disco_table_c.role_of_e T1 XP)) <= 7)%nat).
{ unfold disco_json_text.rolename. destruct (_ =? 1); [|destruct (_ =? 2)]; cbn; lia. }
pose proof (pa_img_range _ (XIMG (VAL (A_OBJ (a3f_roleobj (disco_table_c.role_of_e T1 XP))) +
  Z.of_nat (length (disco_json_text.rolename (disco_table_c.role_of_e T1 XP)))) ltac:(lia))) as XR.
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
eapply SRr_bind.
{ apply (aj_jtok_at B LAWS TJTOK fq W R (ms_mem ms) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md' k (d_A cx - d_S cx) (d_obj cx OO + 144 * XP + 24 * Z.of_nat 1)
    (VAL (A_OBJ (a3f_roleobj (disco_table_c.role_of_e T1 XP)))) 1 (disco_json_reader_model.tv_kind tk)
    (buf + snd (fst tk)) (snd tk) (map (Z_to_bv 8) (disco_json_text.rolename (disco_table_c.role_of_e T1 XP)))
    slack (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (a3_text T1 now) tk)) HJr HFRM0).
  - rewrite SpR. lia.
  - lia.
  - lia.
  - unfold TJTOK_IS_STK, ESTACK, LLVMF_STK. lia.
  - rewrite (SR 3%bv ltac:(cbv; tauto)). exact Rgp.
  - rewrite (SR 4%bv ltac:(cbv; tauto)). exact Rtp.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - exact HIMGc.
  - exact HCV.
  - rewrite Q10. unfold w64, d_obj, dobj_off. f_equal. lia.
  - exact Q11.
  - exact Q12x.
  - lia.
  - rewrite J1. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact F1.
  - exact F2.
  - exact F3.
  - exact Hvp.
  - exact Hvn.
  - exact AMv.
  - exact RAv.
  - exact SHv.
  - left. rewrite SpR. unfold d_obj, dobj_off, TJTOK_IS_STK, ESTACK. lia.
  - exact XNZ.
  - exact XG.
  - exact XSL.
  - exact X0.
  - exact X63.
  - exact X32.
  - exact XAM.
  - exact XRA.
  - exact XSH.
  - left. rewrite SpR. rewrite length_map in XLE |- *. unfold TJTOK_IS_STK, ESTACK, IMG_TOP in *. lia.
  - intros _ _.
    assert (LP : length (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (a3_text T1 now) tk)) =
      length (map (Z_to_bv 8) (disco_json_text.rolename (disco_table_c.role_of_e T1 XP)))) by exact HlenP.
    rewrite LP. rewrite length_map.
    split; [reflexivity|]. split; [exact GP|]. split; [exact Hvp0|].
    split; [rewrite <- LTr; exact Hvp63|].
    rewrite J2 in Hsl.
    split.
    { apply (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ _ _ HARc Inb); lia. }
    split.
    { apply (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ _ _ HARc Inb); lia. }
    split.
    { intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md' buf _ _ _ HARc Inb); lia. }
    left. rewrite SpR. unfold TJTOK_IS_STK, ESTACK. lia. }
cbv beta. intros W2 c2 HWW2 (fx2 & ly4 & S4 & regs4 & mem4 & md4 & -> & HFq2 & _ & HJ4 & HJc & HP & HPerm & Hfr & Hres).
clear dependent fq. rename fx2 into fq. rename HFq2 into HFRM0.
destruct Hres as [(_ & R10') | (Hnm & _)].
2: { exfalso. apply Hnm. unfold printf_facts_c.pf_bytes in JM. exact JM. }
clear HG.
pose proof HJc as (_ & _ & _ & HWle & _ & HfrC & _).
assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFRS).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 8240 <= a < d_A cx) ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha Hna. apply Hfr; [exact Ha | rewrite SpR; unfold TJTOK_IS_STK, ESTACK; lia]. }
assert (KG4 : forall a l, (forall kk, 0 <= kk < Z.of_nat (length l) -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_A cx - 8240 <= a + kk < d_A cx)) ->
  garr8 SEGS (rd W (ms_mem ms)) a l -> garr8 SEGS (rd W2 mem4) a l).
{ intros a l Hb Gx. apply (a3f_g8_kept (w_H W) (w_H W2) (ms_mem ms) mem4 a l); [|exact Gx].
  intros kk Hkk. destruct (Hb kk Hkk) as [Hb1 Hb2]. exact (KM _ Hb1 Hb2). }
pose proof HFRMc as (E2 & HdE2 & HREG2 & HFLAG2 & _).
pose proof HdE2 as (EE2 & E322 & HEI2 & E602 & EF2 & ESH2).
pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W R (ms_mem ms) md' k E2 AF_both3_jtok_is
  (SLit 0 :: SOff A_TEXT 8004 :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTXc HdE2 HREG2 HFLAG2 (a3f_regs2 cx E2 R 8004 HEI2 Q1)
  (DFACTS LAWS cx ly3 S3 W (ms_mem ms) md' k E2 (map (getr R) (tl all_regs)) [] [] HCTXc HdE2 I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
assert (HEId : img_env VAL A_LIM (d_env cx E2 (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI2 | unfold AT_FL, A_LIM; lia]).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W2) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict YK11.mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (a3f_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite (EE2 2%nat 2%bv eq_refl). reflexivity.
    + intros a Ha. apply KM; lia.
    + intros a Ha. lia.
  - eapply (a3f_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). change 60%nat with AT_A. rewrite E602. unfold w64.
      apply unsigned_lit_small. lia.
    + intros a Ha. apply KM; lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (a3f_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite EF2. unfold w64.
      apply unsigned_lit_small. lia.
    + intros a Ha. apply KM; lia.
    + intros a Ha. apply GFpres4. unfold DFRAME_SIZE in Ha. lia.
  - eapply (a3f_kept _ (w_H W) (w_H W2) (ms_mem ms) mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite ESH2. unfold w64.
      apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KM; unfold shadow_addr, SHADOW_OFF in *; lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. unfold DFRAME_SH in Ha. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2' : d_E cx (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply a3f_dE_hi; [apply d_E_env; exact HdE2 | unfold AT_FL; lia]).
assert (HFL2 : ew (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (HHS4 : d_hslots cx h W2 mem4).
{ apply (d_hslots_kept cx h W W2 mem3 mem4); [|exact HHS].
  intros a Ha. rewrite (KM a ltac:(lia) ltac:(lia)). apply KC; lia. }
pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_ser2 ly4 S4 W2 md4 k _ _
  (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + 8004)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2' HFL2 HS2 ltac:(vm_compute; reflexivity) HHS4) as (HFRM4 & HSHD4).
pose proof (DBCK LAWS cx h n (a3_xb buf op) dsh_ser2 dsh_ser2 ly3 S3 W (ms_mem ms) ly4 S4 W2 mem4 md4 k
  (d_A cx - 8240) (d_A cx) HBODYc (conj HBASE HJ4) ltac:(unfold LLVMF_STK; lia) ltac:(lia)
  ltac:(intros a Ha Hna; exact (KM a Ha Hna)) HPerm HFRM4 HSHD4) as HBODY4.
rewrite Q1.
pose proof (ast_ok_pi_set_reg_fp _ _ _ (10%bv : bv 5) (SLit 1) HS2 eq_refl) as HS3.
match type of HS3 with ?Q -> _ => assert (H10 : Q) end.
{ cbn [sv_denot ms_regs restrict YK11.mkst]. rewrite R10'. reflexivity. }
specialize (HS3 H10). clear H10.
pose proof (st_ok_pi_submem _ _ _ [] HS3 (submem_nil _) eq_refl) as HS4.
cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS4. norm_ss HS4. clear HS2 HS3.
pose proof HS4 as HS4c.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
assert (SHOK4 : sh_ok SEGS (SOff 32 0) [] (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562
  (map (getr regs4) CLOB)) (mrestrict (w_H W2) mem4)) by apply Forall_nil.
assert (HEI4 : img_env VAL A_LIM (havoc (d_env cx E2 (map (getr R) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply img_env_havoc_hi; [exact HEId | unfold A_LIM; lia]).
paj_run_to_tok RUNTO HS4 HJ4 SHOK4 (0, 0) R1_OFF.
{ intros a (r & Hin & _). destruct Hin. }
match goal with Hf : frame_of _ _ mem4 (ms_mem ?m5) |- _ =>
  assert (Emem5 : ms_mem m5 = mem4)
    by (apply functional_extensionality; intros x; apply Hf; intros (r & Hin & _); destruct Hin) end.
pmkst HS4.
assert (SR5 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 27]%bv ->
  getr (ms_regs ms0) r = getr regs4 r).
{ intros r Hr. apply (a3f_same_reg fq _ _ _ _ _ (w_H W2) (w_H W2) r HS4c HS4).
  cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
assert (P2 : getr (ms_regs ms0) 2 = getr regs 2) by pfx_preg SR5 HP SR regs4 R (2%bv : bv 5) 2%Z.
assert (P3 : getr (ms_regs ms0) 3 = getr regs 3) by pfx_preg SR5 HP SR regs4 R (3%bv : bv 5) 3%Z.
assert (P4 : getr (ms_regs ms0) 4 = getr regs 4) by pfx_preg SR5 HP SR regs4 R (4%bv : bv 5) 4%Z.
assert (P8 : getr (ms_regs ms0) 8 = getr regs 8) by pfx_preg SR5 HP SR regs4 R (8%bv : bv 5) 8%Z.
assert (P9 : getr (ms_regs ms0) 9 = getr regs 9) by pfx_preg SR5 HP SR regs4 R (9%bv : bv 5) 9%Z.
assert (P18 : getr (ms_regs ms0) 18 = getr regs 18) by pfx_preg SR5 HP SR regs4 R (18%bv : bv 5) 18%Z.
assert (P19 : getr (ms_regs ms0) 19 = getr regs 19) by pfx_preg SR5 HP SR regs4 R (19%bv : bv 5) 19%Z.
assert (P20 : getr (ms_regs ms0) 20 = getr regs 20) by pfx_preg SR5 HP SR regs4 R (20%bv : bv 5) 20%Z.
assert (P24 : getr (ms_regs ms0) 24 = getr regs 24) by pfx_preg SR5 HP SR regs4 R (24%bv : bv 5) 24%Z.
assert (P27 : getr (ms_regs ms0) 27 = getr regs 27) by pfx_preg SR5 HP SR regs4 R (27%bv : bv 5) 27%Z.
assert (P22 : getr (ms_regs ms0) 22 = w64 (d_obj cx OT + 48 * XP)).
{ transitivity (getr regs4 22); [exact (SR5 22%bv ltac:(cbv; tauto))|].
  transitivity (getr R 22); [exact (HP 22 ltac:(unfold acallee_saved; lia))|].
  rewrite Q22. unfold w64, d_obj, dobj_off. f_equal. }
assert (K34 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_FB cx + 1664 + 4 * XP <= a < d_FB cx + 1668 + 4 * XP) ->
  ~ (d_A cx - 8240 <= a < d_A cx) -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hb1 Hb2. rewrite (KM a Ha Hb2). exact (KC a Ha Hb1). }
assert (KV34 : forall a nn v, (forall kk, 0 <= kk < Z.of_nat nn -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1664 + 4 * XP <= a + kk < d_FB cx + 1668 + 4 * XP) /\ ~ (d_A cx - 8240 <= a + kk < d_A cx)) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W2 mem4) a nn v).
{ intros a nn v Hb V. apply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4 a nn v); [|exact V].
  intros kk Hkk. destruct (Hb kk Hkk) as (Hb1 & Hb2 & Hb3). exact (K34 _ Hb1 Hb2 Hb3). }
assert (KG34 : forall a l, (forall kk, 0 <= kk < Z.of_nat (length l) -> 0 <= a + kk < 2 ^ 64 /\
    ~ (d_FB cx + 1664 + 4 * XP <= a + kk < d_FB cx + 1668 + 4 * XP) /\ ~ (d_A cx - 8240 <= a + kk < d_A cx)) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W2 mem4) a l).
{ intros a l Hb Gx. apply (a3f_g8_kept (w_H W) (w_H W2) mem3 mem4 a l); [|exact Gx].
  intros kk Hkk. destruct (Hb kk Hkk) as (Hb1 & Hb2 & Hb3). exact (K34 _ Hb1 Hb2 Hb3). }
pose proof HSP1 as ((S208 & S320) & S192 & S200).
assert (M208 : val_mem SEGS (rd W2 mem4) (d_A cx + 208) 8 i) by (apply KV34; [pfx_kb | exact S208]).
assert (M320 : val_mem SEGS (rd W2 mem4) (d_A cx + 320) 8 now) by (apply KV34; [pfx_kb | exact S320]).
assert (M192 : val_mem SEGS (rd W2 mem4) (d_A cx + 192) 8 n) by (apply KV34; [pfx_kb | exact S192]).
assert (M200 : val_mem SEGS (rd W2 mem4) (d_A cx + 200) 8 (d_cur cx n)) by (apply KV34; [pfx_kb | exact S200]).
assert (M368 : val_mem SEGS (rd W2 mem4) (d_A cx + 368) 8 XP) by (apply KV34; [pfx_kb | exact H368]).
assert (M360 : val_mem SEGS (rd W2 mem4) (d_A cx + 360) 8 count) by (apply KV34; [pfx_kb | exact H360]).
assert (M408 : val_mem SEGS (rd W2 mem4) (d_A cx + 408) 8 (d_obj cx OO + 144 * XP))
  by (apply KV34; [pfx_kb | exact H408]).
assert (GOT4 : garr8 SEGS (rd W2 mem4) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1)).
{ apply KG34; [|exact HOT]. intros kk Hkk. rewrite length_map, LT1 in Hkk. unfold d_obj, dobj_off.
  split; [|split]; lia. }
assert (GBUF4 : garr8 SEGS (rd W2 mem4) buf (a3_text T1 now ++ [0])).
{ apply KG4; [|exact GBUFc]. intros kk Hkk. rewrite length_app in Hkk. cbn [length] in Hkk.
  unfold LLVMF_STK in *. split; lia. }
assert (GOO4 : garr8 SEGS (rd W2 mem4) (d_obj cx OO)
  (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))).
{ apply KG4; [|exact GOOc]. intros kk Hkk. rewrite length_map, (mdk_objs_len buf vpad os HVP H6), Los in Hkk.
  unfold d_obj, dobj_off. split; lia. }
assert (GU4 : garr8 SEGS (rd W2 mem4) (d_obj cx OUSED) (a3f_used (XP + 1))).
{ apply KG4; [|exact GU]. intros kk Hkk. rewrite (a3f_used_bytes (XP + 1) ltac:(lia)) in Hkk.
  unfold d_obj, dobj_off. split; lia. }
rewrite Emem5.
apply SRr_ret.
unfold f_r1, a3f_st. split.
{ destruct HFROM as (HA3 & HW0 & HLT0 & HEX).
  exact (conj HA3 (conj (wle_trans _ _ _ _ HW0 HWle) (conj HLT0 HEX))). }
unfold d_arm_at_pf, d_at.
exists fq, ly4, S4, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), k, acc.
split; [unfold cfg_at, w64, R1_OFF; reflexivity|].
split; [exact HFRM0|].
split; [exact HBASE|].
split; [rewrite <- Emem5; exact HJ4|].
split; [exact HFR4|]. split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rL. split; [unfold spZ; rewrite P2; exact Rsp|]. split; [rewrite P3; exact Rgp|].
  split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact R8|]. split; [rewrite P9; exact R9|].
  split; [rewrite P19; exact R19|]. split; [rewrite P18; exact R18|]. split; [rewrite P20; exact R20|].
  rewrite P27; exact R27. }
split; [split; [rewrite P24; exact R24 | exact P22]|].
split.
{ split; [split; [split; [exact M208 | exact M320] | split; [exact M192 | exact M200]]|].
  split; [split; [exact (ex_intro _ removed (conj Hage Hpost)) | exact GOT4]|].
  split; [split; [exact Hr2 | exact GBUF4]|].
  split; [exact HJR|]. split; [exact HVP|]. split; [exact GOO4|].
  unfold a3f_pyk, a3f_slots. split; [split; [exact Hpc | split; [exact M368 | exact M360]]|].
  split; [exact M408|]. exact GU4. }
split; [split; [exact M208 | exact M320]|].
exact HBODY4.
}
rewrite Ec. unfold cfg_at. change (w64 (BASE + PFX_OFF)) with (Z_to_bv 64 (BASE + PFX_OFF)).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals) (mrestrict (w_H W) mem3)) by apply Forall_nil.
destruct Hrole as [Er | [Er | Er]]; rewrite Er in HFCS.
all: pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E PFX_OFF (a3f_sr 0) vals
  (a3f_xacs XP) _ [] (d_facts a3f_xfa []) HCTX HdE HREG HFLAG
  (a3f_regs_ok cx E 0 regs _ HdE HA64 ltac:(rewrite Z.add_0_r; exact Rsp) R8 R9 R19 R18 R20)
  HGf HACS HFCS (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
all: unfold ss_d in HS0.
all: rewrite app_nil_r in HS0.
all: pose proof (st_ok_pi_submem _ _ _ _ HS0
  (a3f_narrow_sub (1664 + 4 * XP) (1668 + 4 * XP) dsh_ser2 (a3f_xacs XP) _ ltac:(lia) ltac:(unfold DFRAME_SIZE; lia))
  ltac:(vm_compute; reflexivity)) as HS1.
all: clear HS0.
all: cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
all: pose proof (ast_ok_pi_set_reg_fp _ _ _ (22%bv : bv 5) (SLit XP) HS1 eq_refl
  ltac:(rewrite restrict_mkst_fx; cbn [ms_regs YK11.mkst sv_denot]; rewrite R22; reflexivity)) as HS.
all: clear HS1.
all: norm_ss HS.
all: pose proof HS as HS0c.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ =>
  assert (WR : forall a, in_wrange Ex (ss_mem ssx) a -> d_FB cx + 1664 + 4 * XP <= a < d_FB cx + 1668 + 4 * XP)
    by (intros a (r & Hin & Ha); cbn [ss_mem In] in Hin;
        destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; try lia;
        rewrite d_env_old in Ha by (unfold AT_FL; lia); change 516%nat with AT_F in Ha; rewrite HFU in Ha; lia) end.
all: paj_run_tok RUN HS HJ SHOK (0, 0).
all: try solve [
  lazymatch goal with |- awr_ok ?Ex ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a b c d e f g) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_gen with (n := 516%nat) (b := d_FB cx);
  [ reflexivity
  | rewrite d_env_old by (cbv; lia); exact HFU
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; exact (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia)))
  | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ] ].
all: rewrite pa_sigma_jtok_is in HS.
all: pose proof (a3f_kept_of _ _ (w_H W) mem3 (ms_mem ms) _ _ HF WR) as KC.
all: pmkst HS.
all: lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  pose proof (HS : st_ok_pi SEGS VAL Ex (setpc ssx AF_both3_jtok_is) msx) as HSp end.
all: prreg HS (1%bv : bv 5) Q1.
all: prreg HS (10%bv : bv 5) Q10.
all: prreg HS (11%bv : bv 5) Q11.
all: prreg HS (12%bv : bv 5) Q12.
all: prreg HS (22%bv : bv 5) Q22.
all: try rewrite d_env_old in Q10 by (unfold AT_FL; lia).
all: try rewrite d_env_old in Q22 by (unfold AT_FL; lia).
all: try change 516%nat with AT_F in Q10.
all: try change 516%nat with AT_F in Q22.
all: try rewrite HFU in Q10.
all: try rewrite HFU in Q22.
all: assert (SR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 24; 27]%bv -> getr (ms_regs ms) r = getr regs r)
  by (intros r Hr; apply (a3f_same_reg fq _ _ _ _ _ (w_H W) (w_H W) r HS0c HS); cbv [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr).
all: assert (Q12x : getr (ms_regs ms) 12 = w64 (VAL (A_OBJ (a3f_roleobj (disco_table_c.role_of_e T1 XP)))))
  by (rewrite Q12, Er; unfold w64; lazymatch goal with |- ew ?Ex ?nn = _ =>
        transitivity (Z_to_bv 64 (bv_unsigned (ew Ex nn))); [symmetry; apply Z_to_bv_bv_unsigned|] end;
      f_equal; apply HEI; cbv; lia).
all: assert (HHS1 : d_hslots cx h W (ms_mem ms))
  by (apply (d_hslots_kept cx h W W mem3 (ms_mem ms)); [intros a Ha; apply KC; lia | exact HHS]).
all: pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W
  (with_vm_backing (m_vm_lazy md3) mat md3) k (d_env cx E vals) _ ms (conj HBASE (conj HJ HFRS))
  (d_E_env cx E vals HdE) (d_env_fl cx E vals) HSp ltac:(vm_compute; reflexivity) HHS1) as (HFRMc & HSHDc).
all: lazymatch type of HSp with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx msx 2 r HSp ltac:(vm_compute; reflexivity)) as RF end.
all: assert (VUc : val_mem SEGS (rd W (ms_mem ms)) (d_FB cx + 1664 + 4 * XP) 4 1)
  by (rewrite <- Z.add_assoc; change 4%nat with (N.to_nat 4);
      change (rd W (ms_mem ms)) with (ms_mem (restrict (w_H W) ms));
      eapply (field_of_region _ _ 516%nat (d_FB cx) _ _ _ _ _ (1664 + 4 * XP) 4 (SLit 1) 1 RF);
      [rewrite d_env_old by (unfold AT_FL; lia); change 516%nat with AT_F; exact HFU | left; reflexivity |
       reflexivity | lia | lia]).
all: exact (CONT ms mat HJ KC HG Q1 ltac:(rewrite Q10; f_equal; lia) Q11 Q12x ltac:(rewrite Q22; f_equal; lia)
  SR HFRMc HSHDc VUc).
Qed.

End h.
End f.
End d.
