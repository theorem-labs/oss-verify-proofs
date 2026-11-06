(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 377 of its 415 lines of code are new or changed and 7 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC81 YC45 YC88 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoRo JtokIs DiscoArm3
DiscoArm3FieldCut DiscoArm3FieldCall DiscoArm3FieldMDFacts DiscoArm3FieldMDKit DiscoArm3FieldMDA.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c jtok_is_c printf_facts_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
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
Hypothesis TJTOK : tjtok_is_spec B.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis MCRO : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, McConsts.MC_CONSTS_LO <= a < McConsts.MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DCAN : d_can_hyps B tfib_K.

Lemma md_a2_0 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m2 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 0 mp W c ->
  SRr SEGS W c (md_m4 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 0 mp).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m2, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
pose proof HSLOTS as (Hpc & H368 & H336).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HBASE | split; [exact HJ | exact HFRS]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HSTKF & HAWRF).
pose proof HFRM as (E & HdE & HREG & HFLAG & H216 & H152).
pose proof HdE as (HER & HE32 & HEI0 & HEA & HEF & HESH).
assert (HA64 : 0 <= d_A cx < 2 ^ 64) by lia.
assert (HFU : bv_unsigned (ew E 516%nat) = d_FB cx)
  by (change 516%nat with AT_F; rewrite HEF; unfold w64; apply unsigned_lit_small; lia).
assert (HFUA : bv_unsigned (ew E AT_F) = d_FB cx) by exact HFU.
assert (HEAU : bv_unsigned (ew E 60%nat) = d_A cx)
  by (change 60%nat with AT_A; rewrite HEA; unfold w64; apply unsigned_lit_small; lia).
assert (HESHU : bv_unsigned (ew E 529%nat) = shadow_addr (d_FB cx)).
{ change 529%nat with AT_SH. rewrite HESH. unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 20)
  (md_sr (2160 + 48 * 0) (240 + 144 * 0) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 0) (240 + 144 * 0) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 20))) with (Z_to_bv 64 (BASE + (MD_OFF + 20))).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ. rewrite pa_sigma_jtok_is in HS.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
assert (QO1 : (d_A cx - d_S cx) mod 16 = 0).
{ pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
  rewrite GA32 in DA. rewrite GS16 in DS.
  replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult. }
assert (QRA : YK0s.ret_ok (getr R 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (QRZ : 4096 <= raZ R).
{ unfold raZ. rewrite Q1. pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
  rewrite unsigned_lit_small by (pose proof pa_B_ok as (PB0 & PB1 & _); lia). lia. }
assert (QGP : getr R 3 = w64 (as_gp B))
  by (rewrite Q3, (md_atom_reg cx E regs 534%nat 3%nat 3%bv eq_refl ltac:(lia) eq_refl); exact Rgp).
assert (QTP : getr R 4 = w64 (as_tp B))
  by (rewrite Q4, (md_atom_reg cx E regs 535%nat 4%nat 4%bv eq_refl ltac:(lia) eq_refl); exact Rtp).
assert (QS0 : getr R 8 = w64 (d_S cx)).
{ rewrite Q8, d_env_old by (unfold AT_FL, AT_STK; lia). rewrite (HER 2%nat 2%bv eq_refl).
  unfold d_S, spZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (QS1 : getr R 9 = w64 (d_A cx)) by (rewrite Q9, d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QS2 : getr R 18 = w64 SHADOW_OFF) by (rewrite Q18, d_env_old by (unfold AT_FL; lia); exact HE32).
assert (QS4 : getr R 20 = w64 slot_inv.WS_MASK)
  by (rewrite Q20, (md_atom_reg cx E regs 551%nat 20%nat 20%bv eq_refl ltac:(lia) eq_refl); exact R20).
assert (QS9 : getr R 25 = w64 32)
  by (rewrite Q25, (md_atom_reg cx E regs 556%nat 25%nat 25%bv eq_refl ltac:(lia) eq_refl); exact R25).
assert (QX22 : getr R 22 = w64 mp)
  by (rewrite Q22, (md_atom_reg cx E regs 553%nat 22%nat 22%bv eq_refl ltac:(lia) eq_refl); exact R22).
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 0)).
{ rewrite Q21, d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU. unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 0)).
{ rewrite Q24, d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU. unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX10 : getr R 10 = w64 (d_obj cx OO + 144 * 0 + 24 * 3)).
{ rewrite Q10, d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU. unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX12 : getr R 12 = w64 (d_obj cx OWID)).
{ rewrite Q12, d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU. unfold d_obj, dobj_off, w64. f_equal; lia. }
assert (HCTX2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md' k)
  by (split; [exact HBASE | split; [exact HJ | exact HFRS]]).
assert (HARO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem3)) by exact HIMG.
assert (HCV : ConstsViewDef.consts_view SEGS McConsts.MC_CONSTS_LO McConsts.MC_CONSTS_HI W mem3)
  by (exact (mc_cv_ok B W mem3 MCRO MCUN HARO)).
destruct (mdf_wid_x B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k h n (a3_xb buf op) T1 0
  HCTX HBODY HWID) as (sl & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
destruct (mdf_tok_v B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k h n (a3_xb buf op) 0 3
  HCTX HBODY ltac:(lia) ltac:(lia)) as (VT1 & VT2 & VT3).
pose proof HTAB as (Hage0 & HTg0).
destruct Hage0 as (removed0 & Hagem0 & Hpost0).
pose proof Hpost0 as (LT & _ & _ & _ & _ & _ & TOK & _).
pose proof HBUF as (Hbr0 & Hbg0).
assert (Hbufb : 4096 <= buf /\ buf + req_size (Z.max (slot_ser_defs.ser_cap op) 1) <= alloc_ceiling /\
  In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ pose proof HBLK as (HPerm0 & _ & _ & _).
  assert (Hin : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hb4 & Hbc & _).
  exact (conj Hb4 (conj Hbc Hin)). }
destruct Hbufb as (Hbuf4 & Hbufc & Hbufin).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as Hrq.
destruct (mdf_model_txt T1 0) as (_ & _ & FT & LFT).
destruct (a3f_obj T1 now count os 0 LT TOK Hnow HJR ltac:(lia)) as (_ & _ & _ & Hwidth & _ & _).
destruct (a3f_count T1 now count os LT TOK Hnow HJR) as (_ & Hc8 & Los & Lo6 & Inb & B33 & LX).
destruct (mdk_site SEGS (rd W mem3) T1 now count os 0 3%nat (d_obj cx OO) buf
  (d_obj cx OO + 144 * 0 + 24 * 3) 1 vpad (snd (a3f_model T1 0)) (nth 3 (nth 0 os []) disco_json_reader_model.tok_none)
  LT TOK Hnow HJR ltac:(lia) ltac:(lia) HVP HOO Hbg0 ltac:(lia) ltac:(unfold a3_r in Hbr0; lia)
  eq_refl ltac:(lia) FT Hwidth eq_refl)
  as (EK & EN & ETX & MV1 & MV2 & MV3 & RVP & RVN & JM & LPT & GVP & VP0 & VP63).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbufin) as (HbSh & HbHull).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbufin) as (_ & _ & Hbceil & Hbapp & _ & _ & _).
rewrite Hreq in Hbceil, Hbapp, HbSh, HbHull.
destruct (mdk_obj_tok os count 0 3%nat Los Lo6 ltac:(lia) ltac:(lia)) as (Ho0 & Ht0 & _).
assert (Hoi : In (nth (Z.to_nat 0) os []) os) by (eapply nth_error_In; exact Ho0).
assert (Hti : In (nth 3 (nth (Z.to_nat 0) os []) disco_json_reader_model.tok_none)
  (nth (Z.to_nat 0) os [])) by (eapply nth_error_In; exact Ht0).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Inb _ Hoi) _ Hti) as Hib.
change (Z.to_nat 0) with 0%nat in Hib.
set (tk := nth 3 (nth 0 os []) disco_json_reader_model.tok_none) in *.
eapply SRr_mono.
- eapply (aj_jtok_at B LAWS TJTOK) with (o := d_A cx - d_S cx) (v := d_obj cx OO + 144 * 0 + 24 * 3)
    (x := d_obj cx OWID) (kind := 1) (vk := disco_json_reader_model.tv_kind tk) (vp := buf + snd (fst tk))
    (vn := snd tk) (T := map (Z_to_bv 8) (snd (a3f_model T1 0))) (slack := sl)
    (P := printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (a3_text T1 now) tk)).
  + exact HJ.
  + rewrite QSP. lia.
  + exact QO1.
  + lia.
  + unfold TJTOK_IS_STK, ESTACK, LLVMF_STK. lia.
  + exact QGP.
  + exact QTP.
  + exact QRA.
  + exact QRZ.
  + exact HARO.
  + exact HCV.
  + exact QX10.
  + rewrite Q11. reflexivity.
  + exact QX12.
  + lia.
  + rewrite EK. lia.
  + unfold d_obj, dobj_off. lia.
  + unfold d_obj, dobj_off.
    pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)) as DF. rewrite GF32 in DF.
    replace (d_FB cx + 240 + 144 * 0 + 24 * 3) with ((4 * (d_FB cx / 32) + 39) * 8) by lia. apply Z_mod_mult.
  + unfold d_obj, dobj_off. lia.
  + exact MV1.
  + exact MV2.
  + exact MV3.
  + exact RVP.
  + exact RVN.
  + exact VT1.
  + exact VT2.
  + exact VT3.
  + left. rewrite QSP. unfold d_obj, dobj_off, TJTOK_IS_STK, ESTACK. lia.
  + exact X1.
  + exact X2.
  + exact X3.
  + exact X4.
  + exact X5.
  + exact X6.
  + exact X7.
  + exact X8.
  + exact X9.
  + assert (HTl7 : (length (map (Z_to_bv 8) (snd (a3f_model T1 0))) <= 7)%nat)
      by (rewrite length_map; lia).
    left. rewrite QSP. unfold d_obj, dobj_off, TJTOK_IS_STK, ESTACK in *. lia.
  + intros Hvk Hvn.
    assert (Hbt : 0 <= snd (fst tk) /\ snd (fst tk) + Z.of_nat (length (snd (a3f_model T1 0))) <=
      Z.of_nat (length (a3_text T1 now))).
    { destruct Hib as [Hz | (Ho1 & Hn1 & Hsl)]; [rewrite EK in Hz; exfalso; lia|].
      unfold disco_jscalar_model.jlen in Hsl. rewrite EN in Hsl. exact (conj Ho1 Hsl). }
    destruct Hbt as (Hbt0 & Hbt1).
    assert (HLm : Z.of_nat (length (map (Z_to_bv 8) (snd (a3f_model T1 0)))) =
      Z.of_nat (length (snd (a3f_model T1 0)))) by (rewrite length_map; reflexivity).
    unfold a3_r in Hbr0.
    split; [exact LPT|]. split; [exact GVP|]. split; [exact VP0|]. split; [exact VP63|].
    split.
    { rewrite HLm. apply (amem_range_sub_app buf (Z.max (slot_ser_defs.ser_cap op) 1)
        (buf + snd (fst tk)) (Z.of_nat (length (snd (a3f_model T1 0))))); [exact Hbapp | lia | lia | lia | lia]. }
    split.
    { rewrite HLm. apply (block_shadow_range _ _ buf (Z.max (slot_ser_defs.ser_cap op) 1)
        (buf + snd (fst tk)) (Z.of_nat (length (snd (a3f_model T1 0)))) HbSh); lia. }
    split.
    { intros Hpos s Hs. apply HbHull. rewrite HLm in Hs.
      pose proof (YCbq.shadow_mono buf (buf + snd (fst tk)) ltac:(lia)) as Sm1.
      pose proof (YCbq.shadow_mono (buf + snd (fst tk) + Z.of_nat (length (snd (a3f_model T1 0))) - 1)
        (buf + Z.max (slot_ser_defs.ser_cap op) 1 - 1) ltac:(lia)) as Sm2.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm1) as Sd1.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm2) as Sd2. lia. }
    left. rewrite QSP, HLm. unfold TJTOK_IS_STK, ESTACK. lia.
- cbv beta. intros W2 c2 _ Hpost.
  destruct Hpost as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hcsr2 & HJ4 & HJc & HPr & HPerm & HKeep & Hres).
  pose proof HJc as (_ & _ & _ & HWLE & _ & HfrC & _).
  assert (HFR4 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFRS).
  assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
    by (split; [exact HBASE | split; [exact HJ4 | exact HFR4]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly2 S2 W2 mem2 md2 k HCTX4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GSHpres4 & GSTK4 & _ & _ & _ & _).
  assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply HKeep; [lia | rewrite QSP; lia]. }
  assert (KB : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply HKeep; [lia | rewrite QSP; unfold TJTOK_IS_STK, ESTACK; lia]. }
  assert (KS : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha. apply HKeep; [unfold SHADOW_OFF in *; lia
    | rewrite QSP; unfold TJTOK_IS_STK, ESTACK, SHADOW_OFF in *; lia]. }
  assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (ES2 : bv_unsigned (ew E 2%nat) = d_S cx) by (rewrite (HER 2%nat 2%bv eq_refl); reflexivity).
  assert (KV : forall a nb v, d_A cx <= a -> a + Z.of_nat nb <= d_S cx ->
    val_mem SEGS (rd W mem3) a nb v -> val_mem SEGS (rd W2 mem2) a nb v).
  { intros a nb v Hlo Hhi Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact Hv].
    intros kk Hkk. apply KA. lia. }
  assert (KG : forall a L, 0 <= a -> a + Z.of_nat (length L) <= alloc_ceiling ->
    garr8 SEGS (rd W mem3) a L -> garr8 SEGS (rd W2 mem2) a L).
  { intros a L Hlo Hhi Hg. eapply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact Hg].
    intros x Hx. apply KB. lia. }
  pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W R mem3 md' k E AF_jtok_is
    (SLit 0 :: SOff A_TEXT (MD_OFF + 40) :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
    HCTX2 HdE HREG HFLAG (md_regs_ok_call cx E R (MD_OFF + 40) HEI0 ltac:(change (MD_OFF + 40) with 8432; exact Q1))
    (DFACTS LAWS cx ly3 S3 W mem3 md' k E (map (getr R) (tl all_regs)) [] [] HCTX2 HdE I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
  unfold ss_d in HS1.
  assert (HEIC : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
  jafter_call_keep_hi HS1 562%nat regs2 (mrestrict (w_H W2) mem2) HPr [0;1;2;3]%nat HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
  { cbn [ms_mem restrict YK11.mkst]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (md_kept _ (w_H W) (w_H W2) mem3 mem2 _ (d_S cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
      + intros a Ha. apply KA. lia.
      + intros a Ha. lia.
    - eapply (md_kept _ (w_H W) (w_H W2) mem3 mem2 _ (d_A cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). exact HEAU.
      + intros a Ha. apply KA. lia.
      + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
    - eapply (md_kept _ (w_H W) (w_H W2) mem3 mem2 _ (d_FB cx)).
      + rewrite d_env_old by (unfold AT_FL; lia). exact HFU.
      + intros a Ha. apply KB. lia.
      + intros a Ha. apply GFpres4. lia.
    - eapply (md_kept _ (w_H W) (w_H W2) mem3 mem2 _ (shadow_addr (d_FB cx))).
      + rewrite d_env_old by (unfold AT_FL; lia). exact HESHU.
      + intros a Ha. apply KS. unfold shadow_addr, SHADOW_OFF in *. lia.
      + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
        apply GSHpres4. lia. }
  specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
  assert (HE2 : d_E cx (havoc (d_env cx E (map (getr R) (tl all_regs))) 562 (map (getr regs2) CLOB)))
    by (apply md_dE_havoc; [apply d_E_env; exact HdE | lia]).
  assert (HFL2 : ew (havoc (d_env cx E (map (getr R) (tl all_regs))) 562 (map (getr regs2) CLOB)) AT_FL =
    Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
  assert (H216' : val_mem SEGS (rd W2 mem2) (d_A cx + 216) 8 h) by (apply KV; [lia | cbn; lia | exact H216]).
  assert (H152' : val_mem SEGS (rd W2 mem2) (d_A cx + 152) 8 (h + 440)) by (apply KV; [lia | cbn; lia | exact H152]).
  destruct (DLAND LAWS FFL fq cx h dsh_md ly2 S2 W2 md2 k _ _
    (YK11.mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + 8432)) mem2 (YK11.seg_rom SEGS))
    HCTX4 HE2 HFL2 HS2 ltac:(vm_compute; reflexivity) H216' H152') as (HFRM4 & HSHD4).
  pose proof (DBPC LAWS (conj DRO (conj GM (HV))) DCAN cx h n (a3_xb buf op) dsh_md dsh_md ly3 S3 W mem3 md'
    ly2 S2 W2 mem2 md2 k TJTOK_IS_STK (spZ R) [] 0 HBODY (conj HBASE HJ4) HJc
    ltac:(rewrite QSP; unfold LLVMF_STK, TJTOK_IS_STK, ESTACK; lia) ltac:(rewrite QSP; lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
    ltac:(intros (a & Ha & _); exfalso; exact (inFP_nil a Ha))
    HPerm HFRM4 HSHD4) as HBODY4.
  assert (Hblen : buf + Z.of_nat (length (a3_text T1 now ++ [0])) <= alloc_ceiling).
  { rewrite length_app. cbn [length]. unfold a3_r in Hbr0. lia. }
  pose proof HTAB as (Hage & HTg).
  unfold md_m4, a3f_st. cbv beta.
  split.
  { pose proof HFROM as (HA1 & HA2 & HA3 & HA4). split; [exact HA1|].
    split; [exact (wle_trans _ _ _ _ HA2 HWLE)|]. split; [exact HA3 | exact HA4]. }
  unfold d_arm_at_pf, d_at. cbv beta.
  exists fq2, ly2, S2, regs2, mem2, md2, k, acc.
  split; [unfold cfg_at, w64; rewrite Q1; change (MD_OFF + 40) with 8432; reflexivity|].
  split; [destruct Hcsr2 as [Hcs | Hcs]; [rewrite Hcs; assumption | exact Hcs]|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
  split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
  split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  assert (P2 : getr regs2 2 = getr R 2) by (exact (HPr 2 ltac:(unfold acallee_saved; lia))).
  split.
  { split; [unfold spZ; rewrite P2; exact QSP|].
    split; [transitivity (getr R 3); [exact (HPr 3 ltac:(unfold acallee_saved; lia)) | exact QGP]|].
    split; [transitivity (getr R 4); [exact (HPr 4 ltac:(unfold acallee_saved; lia)) | exact QTP]|].
    split; [transitivity (getr R 8); [exact (HPr 8 ltac:(unfold acallee_saved; lia)) | exact QS0]|].
    split; [transitivity (getr R 9); [exact (HPr 9 ltac:(unfold acallee_saved; lia)) | exact QS1]|].
    split; [transitivity (getr R 18); [exact (HPr 18 ltac:(unfold acallee_saved; lia)) | exact QS2]|].
    split; [transitivity (getr R 20); [exact (HPr 20 ltac:(unfold acallee_saved; lia)) | exact QS4]|].
    transitivity (getr R 25); [exact (HPr 25 ltac:(unfold acallee_saved; lia)) | exact QS9]. }
  split.
  { split; [transitivity (getr R 26); [exact (HPr 26 ltac:(unfold acallee_saved; lia)) | exact QX26]|].
    split.
    { destruct Hres as [(_ & H10') | (Hnm & _)]; [exact H10'|]. exfalso. apply Hnm. exact JM. }
    split; [transitivity (getr R 21); [exact (HPr 21 ltac:(unfold acallee_saved; lia)) | exact QX21]|].
    split; [transitivity (getr R 22); [exact (HPr 22 ltac:(unfold acallee_saved; lia)) | exact QX22]|].
    transitivity (getr R 24); [exact (HPr 24 ltac:(unfold acallee_saved; lia)) | exact QX24]. }
  split.
  { split.
    { pose proof HSP1 as ((H232 & H344) & H224 & H248).
      split; [split; [apply KV; [lia | cbn; lia | exact H232] | apply KV; [lia | cbn; lia | exact H344]]|].
      split; [apply KV; [lia | cbn; lia | exact H224] | apply KV; [lia | cbn; lia | exact H248]]. }
    split.
    { split; [exact Hage|]. apply KG; [unfold d_obj, dobj_off; lia| |exact HTg].
      rewrite length_map, LT. unfold d_obj, dobj_off. cbn. lia. }
    split; [split; [exact Hbr0 | apply KG; [lia | exact Hblen | exact Hbg0]]|].
    split; [exact HJR|]. split; [exact HVP|].
    split.
    { apply KG; [unfold d_obj, dobj_off; lia| |exact HOO].
      rewrite length_map, (mdk_objs_len buf vpad os HVP Lo6).
      unfold d_obj, dobj_off. rewrite Los. lia. }
    unfold md_Y.
    split.
    { pose proof HSLOTS as (Hp0 & H368' & H336').
      split; [exact Hp0|].
      split; [apply KV; [lia | cbn; lia | exact H368'] | apply KV; [lia | cbn; lia | exact H336']]. }
    split; [apply KV; [lia | cbn; lia | exact H392]|].
    split; [apply KV; [lia | cbn; lia | exact H408]|].
    split.
    { apply KG; [unfold d_obj, dobj_off; lia| |exact HUSED].
      replace (length (a3f_used (0 + 1))) with 32%nat by (vm_compute; reflexivity).
      unfold d_obj, dobj_off. lia. }
    split.
    { apply KG; [unfold d_obj, dobj_off; lia| |exact HWID].
      rewrite length_app. cbn [length]. unfold d_obj, dobj_off. lia. }
    destruct HMSTR as [(Hmp & Hs) | (Hmp & Hg)]; [left; exact (conj Hmp Hs)|].
    right. split; [exact Hmp|]. apply KG; [rewrite Hmp; unfold d_obj, dobj_off; lia| |exact Hg].
    rewrite Hmp, length_app. cbn [length]. destruct (mdf_model_txt T1 0) as (_ & Lf & _ & _).
    unfold d_obj, dobj_off. lia. }
  split.
  { pose proof HSP0 as (H232b & H344b).
    split; [apply KV; [lia | cbn; lia | exact H232b] | apply KV; [lia | cbn; lia | exact H344b]]. }
  exact HBODY4.
Qed.

End h.
End f.
End d.
