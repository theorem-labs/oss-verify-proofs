(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 338 of its 373 lines of code are new or changed and 1243 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProC.v, with its module paths and module names changed; 796 of its 839 lines of code are new or changed and 330 lines of the source are left out. *)
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
DiscoArm3FieldCut DiscoArm3FieldCall DiscoArm3FieldMDFacts DiscoArm3FieldMDKit DiscoArm3FieldMDA DiscoArm3FieldMDA3.
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
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.

Lemma md_a4_0 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 0 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 0).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
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
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 0)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 0)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Lemma md_a4_1 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 1 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 1).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
  (md_sr (2160 + 48 * 1) (240 + 144 * 1) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 1) (240 + 144 * 1) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 1)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 1)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Lemma md_a4_2 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 2 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 2).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
  (md_sr (2160 + 48 * 2) (240 + 144 * 2) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 2) (240 + 144 * 2) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 2)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 2)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Lemma md_a4_3 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 3 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 3).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
  (md_sr (2160 + 48 * 3) (240 + 144 * 3) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 3) (240 + 144 * 3) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 3)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 3)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Lemma md_a4_4 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 4 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 4).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
  (md_sr (2160 + 48 * 4) (240 + 144 * 4) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 4) (240 + 144 * 4) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 4)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 4)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Lemma md_a4_5 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 5 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 5).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
  (md_sr (2160 + 48 * 5) (240 + 144 * 5) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 5) (240 + 144 * 5) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 5)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 5)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Lemma md_a4_6 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 6 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 6).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
  (md_sr (2160 + 48 * 6) (240 + 144 * 6) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 6) (240 + 144 * 6) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 6)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 6)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Lemma md_a4_7 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
  (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 7 mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad 7).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
unfold md_m6, a3f_st in Hs. cbv beta in Hs.
destruct Hs as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Ec & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & (R26 & R10 & R21 & R22 & R24) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R20 & R25).
pose proof HY as (HSLOTS & H392 & H408 & HUSED & HWID & HMSTR).
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
assert (HEI : img_env VAL A_LIM (d_env cx E (md_vals regs)))
  by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 104)
  (md_sr (2160 + 48 * 7) (240 + 144 * 7) true) (md_vals regs) [] [] [] (d_facts [] [])
  HCTX HdE HREG HFLAG
  (md_regs_ok cx E regs (2160 + 48 * 7) (240 + 144 * 7) true HdE Rsp R8 R9 R18
     ltac:(unfold d_obj, dobj_off in R24; rewrite R24; f_equal; lia)
     ltac:(intros _; unfold d_obj, dobj_off in R21; rewrite R21; f_equal; lia)
     ltac:(intros _; exact R10) HA64 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (md_vals regs) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
rewrite Ec. unfold cfg_at. change (w64 (BASE + (MD_OFF + 104))) with (Z_to_bv 64 (BASE + (MD_OFF + 104))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (R := ms_regs ms) in *.
assert (QA : getr R 2 = w64 (d_A cx)) by (rewrite Q2; rewrite d_env_old by (unfold AT_FL, AT_A; lia); exact HEA).
assert (QSP : spZ R = d_A cx) by (unfold spZ; rewrite QA; unfold w64; apply unsigned_lit_small; lia).
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
assert (QX26 : getr R 26 = w64 buf)
  by (rewrite Q26, (md_atom_reg cx E regs 557%nat 26%nat 26%bv eq_refl ltac:(lia) eq_refl); exact R26).
assert (QX21 : getr R 21 = w64 (d_obj cx OO + 144 * 7)).
{ rewrite Q21. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
assert (QX24 : getr R 24 = w64 (d_obj cx OT + 48 * 7)).
{ rewrite Q24. cbn [sv_denot]. rewrite d_env_old by (unfold AT_FL, AT_F; lia). rewrite HFU.
  unfold d_obj, dobj_off, w64. f_equal. lia. }
apply SRr_ret.
unfold f_mo, a3f_st. cbv beta.
split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [assumption|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFRS|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [exact QSP|]. split; [exact QGP|]. split; [exact QTP|]. split; [exact QS0|].
  split; [exact QS1|]. split; [exact QS2|]. split; [exact QS4 | exact QS9]. }
split; [split; [exact QX26 | split; [exact QX21 | exact QX24]]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  unfold a3f_pyk. split; [exact HSLOTS|]. split; [exact H392|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0 | exact HBODY].
Qed.

Theorem md_a4 : forall p, 0 <= p < 8 ->
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
    (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (mp : Z)
    (W : world SEGS) (c : config),
  md_m6 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p).
Proof.
intros p Hp.
assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- exact md_a4_0.
- exact md_a4_1.
- exact md_a4_2.
- exact md_a4_3.
- exact md_a4_4.
- exact md_a4_5.
- exact md_a4_6.
- exact md_a4_7.
Qed.

End h.
End f.
End d.
