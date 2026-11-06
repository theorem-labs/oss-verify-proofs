(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module names changed; 336 of its 375 lines of code are new or changed and 6 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoArm3 DiscoEntSeatStmt DiscoEntSeat DiscoRo DiscoEntBodyStmt DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model
slot_ser_defs slot_ser_tokb.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoArm3FieldCut DiscoArm3FieldPH DiscoArm3FieldPFKit DiscoArm3FieldCall.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfa45_fin_sr (j : Z) : list sv :=
  [SLit 0; SOff A_TEXT PFR1_OFF; SOff 60 (-16); SOff 533 0; SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0;
   SOff 538 0; SOff 60 0; SOff 516 1728; SLit 18; SOff (A_OBJ 10) 0; SOff 562 0; SOff 563 0; SOff 564 0;
   SOff 565 0; SOff 566 0; SOff 32 0; SOff 516 1728; SOff 550 0; SOff 529 (270 + 6 * (j - 1));
   SOff 516 (2160 + 48 * (j - 1)); SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0;
   SOff 516 (2162 + 48 * (j - 1)); SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0].

Definition pfa45_stkf : YP09.region :=
  YP09.mkRegion (Some AT_A) (-16) 0 (-16) 0 [YP09.mkChunk (-16) (CVal 8 (SOff 567 0))].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfa45_pi : forall (fq : YK11.FPState) (E : env) (ss : sstate) (ms : machine_state),
  st_ok (fx := fq) SEGS E ss ms -> st_ok_pi (fx := fq) SEGS VAL E (setpc ss (ss_pc ss - BASE)) ms.
Proof.
  intros fq E ss ms H. unfold st_ok_pi, abs_ss.
  destruct ss as [pc0 rg fr mm rv fs]. cbn [setpc ss_pc].
  replace (BASE + (pc0 - BASE)) with pc0 by lia. exact H.
Qed.

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

Theorem a3f_pfa_45 : forall j, j = 4 \/ j = 5 -> pfA_stmt B MT XM_LIB RLO RHI tfib_K j.
Proof.
intros j Hj cx h i n now op W0 c0 T0 T1 buf count os vpad p W c (Hfrom & Hd).
assert (Hj45 : 4 <= j <= 5) by (destruct Hj; lia).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R26 & R11 & R21 & R22 & R23 & R24 & R27) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & (HSL & Hjb & H392 & H408 & HUSED)).
destruct HSL as (Hp & H368 & H336).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & _).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTKpres & GAR & GFin & GEFA & GEFL).
pose proof alloc_ceiling_lt as Hceil0.
pose proof asan_consts as (Hac & HkHSE & HkHMB & HkHME & HkLME).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA2).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (HSHr : kLowMemEnd <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= kHighShadowEnd).
{ pose proof (shadow_addr_bounds (d_FB cx) ltac:(lia)) as Q1.
  pose proof (shadow_addr_bounds (d_FB cx + 4096) ltac:(lia)) as Q2.
  pose proof (shadow_range_end (d_FB cx) 4096 ltac:(lia)) as Q3. change (4096 / 8) with 512 in Q3. lia. }
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LU : length (a3f_used p) = 32%nat) by (unfold a3f_used; reflexivity).
destruct (a3f_count T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296).
{ rewrite (ph_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (Hkwf : regions_wf (d_kregions dsh_ser2 [] (pfa_fcs j) ++ [pfa_stk]) = true)
  by (destruct Hj as [-> | ->]; vm_compute; reflexivity).
assert (Hwf : regions_wf (pfa_rs j) = true) by (destruct Hj as [-> | ->]; vm_compute; reflexivity).
pose proof (pfa_seat B MT XM_LIB RLO RHI tfib_K DSEAT DFACTS LAWS PAL fq cx ly3 S3 W regs mem3 md3 k E T1 j
  HCTX HE HREG HFLAG HRL R11 R21 R22 R27 HGT HLT1 ltac:(lia) Hkwf Hwf) as HS.
remember (d_env cx E (pfa_vals regs T1 j)) as E1 eqn:HE1.
assert (HE1' : d_E cx E1) by (rewrite HE1; exact (d_E_env cx E _ HE)).
pose proof HE1' as (EE' & E32' & HEI & E60' & EF' & ESH').
assert (EFL1 : ew E1 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite HE1; apply d_env_fl).
assert (U60 : bv_unsigned (ew E1 60) = d_A cx).
{ rewrite (E60' : ew E1 60 = w64 (d_A cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew E1 516) = d_FB cx).
{ rewrite (EF' : ew E1 516 = w64 (d_FB cx)). unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew E1 529) = shadow_addr (d_FB cx)).
{ rewrite (ESH' : ew E1 529 = w64 (shadow_addr (d_FB cx))). unfold w64.
  apply unsigned_lit_small. unfold kLowMemEnd, kHighShadowEnd in HSHr. lia. }
assert (MB : forall kk, 0 <= kk < 6 -> 0 <= pf_mb T1 j kk < 256).
{ intros kk Hkk. unfold pf_mb.
  exact (proj2 (garr8_nthZ SEGS (rd W mem3) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T1)
           (48 * (j - 1) + kk) HGT ltac:(lia) ltac:(rewrite length_map, HLT1; lia))). }
assert (E562 : ew E1 562%nat = Z_to_bv 64 (pf_mb T1 j 0))
  by (rewrite HE1; exact (pfa_byte cx E regs T1 j 0%nat ltac:(lia))).
assert (E563 : ew E1 563%nat = Z_to_bv 64 (pf_mb T1 j 1))
  by (rewrite HE1; exact (pfa_byte cx E regs T1 j 1%nat ltac:(lia))).
assert (E564 : ew E1 564%nat = Z_to_bv 64 (pf_mb T1 j 2))
  by (rewrite HE1; exact (pfa_byte cx E regs T1 j 2%nat ltac:(lia))).
assert (E565 : ew E1 565%nat = Z_to_bv 64 (pf_mb T1 j 3))
  by (rewrite HE1; exact (pfa_byte cx E regs T1 j 3%nat ltac:(lia))).
assert (E566 : ew E1 566%nat = Z_to_bv 64 (pf_mb T1 j 4))
  by (rewrite HE1; exact (pfa_byte cx E regs T1 j 4%nat ltac:(lia))).
assert (E567 : ew E1 567%nat = Z_to_bv 64 (pf_mb T1 j 5))
  by (rewrite HE1; exact (pfa_byte cx E regs T1 j 5%nat ltac:(lia))).
assert (POST : forall (ms : machine_state) (mat : list word) (ss0 : sstate),
  st_ok (fx := fq) SEGS E1 ss0 (restrict (w_H W) ms) ->
  ss_pc ss0 = SIGMA DS___interceptor_trampoline_snprintf ->
  ss_resv ss0 = None ->
  ss_regs ss0 = pfa45_fin_sr j ->
  d_land_chk dsh_mac (ss_mem ss0) = true ->
  nth_error (ss_mem ss0) 6%nat = Some pfa45_stkf ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  frame_of E1 (pfa_rs j) (rd W mem3) (rd W (ms_mem ms)) ->
  mem_grows (rd W mem3) (rd W (ms_mem ms)) ->
  SRr SEGS W (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3))
    (pf_c1 B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p j)).
{ intros ms mat ss0 HS0 Hpc Hrv Hregs0 Hchk Hnth HJ1 HFr1 HG1.
  pose proof (pfa45_pi fq E1 ss0 (restrict (w_H W) ms) HS0) as HSP.
  assert (KM : forall a, 0 <= a < 2 ^ 64 ->
    ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
    ~ (d_A cx - 16 <= a < d_A cx) -> rd W (ms_mem ms) (Z_to_bv 64 a) = rd W mem3 (Z_to_bv 64 a)).
  { intros a Ha H1 H2. apply HFr1. rewrite unsigned_lit_small by lia. intros Hw.
    apply (pfa_inw _ j) in Hw.
    change (base_val E1 (Some AT_SH)) with (bv_unsigned (ew E1 AT_SH)) in Hw.
    change (base_val E1 (Some AT_A)) with (bv_unsigned (ew E1 AT_A)) in Hw.
    change AT_SH with 529%nat in Hw. change AT_A with 60%nat in Hw.
    rewrite U60, U529 in Hw. destruct Hw as [Hw|Hw]; [apply H1 | apply H2]; lia. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 ->
    ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
    ~ (d_A cx - 16 <= a < d_A cx) -> mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a).
  { intros a Ha H1 H2. unfold mbyte. rewrite (KM a Ha H1 H2). reflexivity. }
  assert (KHP : forall q len a, in_app q len -> q + len <= alloc_ceiling -> q <= a < q + len ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a).
  { intros q len a Hq Hlen Ha. pose proof Hq as Hq'. unfold in_app in Hq'.
    apply KB; [lia| |].
    - intros Hc. exfalso.
      apply (fshadow_not_app (d_FB cx) 512 q len a ltac:(lia) ltac:(lia) Hq);
        [unfold shadow_addr, SHADOW_OFF in Hc; lia | lia].
    - unfold LLVMF_STK in *. lia. }
  assert (KFR : forall a, d_FB cx <= a < d_FB cx + 4096 ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a)
    by (intros a Ha; exact (KHP (d_FB cx) 4096 a GFapp GFc Ha)).
  assert (KST : forall a, d_A cx <= a < d_A cx + 472 ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a).
  { intros a Ha. apply KB; [lia| |].
    - unfold kLowMemEnd, kHighShadowEnd in HSHr. lia.
    - lia. }
  assert (KVS : forall off v, 0 <= off -> off + 8 <= 472 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v).
  { intros off v H1 H2 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
    intros x Hx. apply KST. cbn [Z.of_nat] in Hx. lia. }
  assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l).
  { intros a l H1 H2 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx. apply KFR. lia. }
  assert (Q : forall r : bv 5, getr (ms_regs ms) r = sv_denot E1 (sr_get (pfa45_fin_sr j) r)).
  { intros r. rewrite <- Hregs0. exact (st_ok_pi_restrict_reg _ _ _ _ r HSP). }
  assert (Q1 : getr (ms_regs ms) 1 = w64 (BASE + PFR1_OFF)).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 1) with (SOff A_TEXT PFR1_OFF).
    rewrite (codeptr_val _ PFR1_OFF HEI). reflexivity. }
  assert (Q2 : getr (ms_regs ms) 2 = w64 (d_A cx + -16)).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 2) with (SOff 60 (-16)).
    rewrite (pfa_soff _ _ _ _ U60). reflexivity. }
  assert (Q9 : getr (ms_regs ms) 9 = w64 (d_A cx)).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 9) with (SOff 60 0).
    rewrite (pfa_soff _ _ _ _ U60). unfold w64. f_equal; lia. }
  assert (Q10 : getr (ms_regs ms) 10 = w64 (d_obj cx OMAC)).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 10) with (SOff 516 1728).
    rewrite (pfa_soff _ _ _ _ U516). unfold w64, d_obj, dobj_off. f_equal; lia. }
  assert (Q11 : getr (ms_regs ms) 11 = w64 18).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 11) with (SLit 18). reflexivity. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (VAL (A_OBJ 10))).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 12) with (SOff (A_OBJ 10) 0).
    rewrite (pfa_soff _ _ _ (VAL (A_OBJ 10))).
    - unfold w64. f_equal; lia.
    - rewrite (img_env_atomP E1 (A_OBJ 10) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
      apply unsigned_lit_small. apply pa_val_range. }
  assert (QB : forall (r : bv 5) (nn : nat) (kk : Z), sr_get (pfa45_fin_sr j) r = SOff nn 0 ->
    ew E1 nn = Z_to_bv 64 (pf_mb T1 j kk) -> 0 <= kk < 6 ->
    getr (ms_regs ms) r = w64 (pf_mb T1 j kk)).
  { intros r nn kk Hr Hnn Hkk. rewrite Q, Hr. cbn [sv_denot]. rewrite Hnn.
    rewrite unsigned_lit_small by (pose proof (MB kk Hkk); lia). rewrite Z.add_0_r. reflexivity. }
  assert (Q13 : getr (ms_regs ms) 13 = w64 (pf_mb T1 j 0)) by exact (QB 13%bv 562%nat 0 eq_refl E562 ltac:(lia)).
  assert (Q14 : getr (ms_regs ms) 14 = w64 (pf_mb T1 j 1)) by exact (QB 14%bv 563%nat 1 eq_refl E563 ltac:(lia)).
  assert (Q15 : getr (ms_regs ms) 15 = w64 (pf_mb T1 j 2)) by exact (QB 15%bv 564%nat 2 eq_refl E564 ltac:(lia)).
  assert (Q16 : getr (ms_regs ms) 16 = w64 (pf_mb T1 j 3)) by exact (QB 16%bv 565%nat 3 eq_refl E565 ltac:(lia)).
  assert (Q17 : getr (ms_regs ms) 17 = w64 (pf_mb T1 j 4)) by exact (QB 17%bv 566%nat 4 eq_refl E566 ltac:(lia)).
  assert (Q19 : getr (ms_regs ms) 19 = w64 (d_obj cx OMAC)).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 19) with (SOff 516 1728).
    rewrite (pfa_soff _ _ _ _ U516). unfold w64, d_obj, dobj_off. f_equal; lia. }
  assert (Q21 : getr (ms_regs ms) 21 = w64 (shadow_addr (d_FB cx) + 270 + 6 * (j - 1))).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 21) with (SOff 529 (270 + 6 * (j - 1))).
    rewrite (pfa_soff _ _ _ _ U529). unfold w64. f_equal; lia. }
  assert (Q22 : getr (ms_regs ms) 22 = w64 (d_obj cx OT + 48 * (j - 1))).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 22) with (SOff 516 (2160 + 48 * (j - 1))).
    rewrite (pfa_soff _ _ _ _ U516). unfold w64, d_obj, dobj_off. f_equal; lia. }
  assert (Q27 : getr (ms_regs ms) 27 = w64 (d_obj cx OT + 48 * (j - 1) + 2)).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 27) with (SOff 516 (2162 + 48 * (j - 1))).
    rewrite (pfa_soff _ _ _ _ U516). unfold w64, d_obj, dobj_off. f_equal; lia. }
  assert (QX : forall (r : bv 5) (q : nat), sr_get (pfa45_fin_sr j) r = SOff (AT_X + q) 0 ->
    nth q (tl all_regs) 0%bv = r -> (q < 31)%nat -> getr (ms_regs ms) r = getr regs r).
  { intros r q Hr Hq1 Hq2. rewrite Q, Hr, HE1, (pfa_atom cx E regs T1 j q Hq2), Hq1. reflexivity. }
  assert (Q3 : getr (ms_regs ms) 3 = getr regs 3) by exact (QX 3%bv 2%nat eq_refl eq_refl ltac:(lia)).
  assert (Q4 : getr (ms_regs ms) 4 = getr regs 4) by exact (QX 4%bv 3%nat eq_refl eq_refl ltac:(lia)).
  assert (Q8 : getr (ms_regs ms) 8 = getr regs 8) by exact (QX 8%bv 7%nat eq_refl eq_refl ltac:(lia)).
  assert (Q18 : getr (ms_regs ms) 18 = w64 SHADOW_OFF).
  { rewrite Q. change (sr_get (pfa45_fin_sr j) 18) with (SOff 32 0).
    cbn [sv_denot]. rewrite (E32' : ew E1 32 = w64 SHADOW_OFF).
    unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. reflexivity. }
  assert (Q20 : getr (ms_regs ms) 20 = getr regs 20) by exact (QX 20%bv 19%nat eq_refl eq_refl ltac:(lia)).
  assert (Q23 : getr (ms_regs ms) 23 = getr regs 23) by exact (QX 23%bv 22%nat eq_refl eq_refl ltac:(lia)).
  assert (Q24 : getr (ms_regs ms) 24 = getr regs 24) by exact (QX 24%bv 23%nat eq_refl eq_refl ltac:(lia)).
  assert (Q25 : getr (ms_regs ms) 25 = getr regs 25) by exact (QX 25%bv 24%nat eq_refl eq_refl ltac:(lia)).
  assert (Q26 : getr (ms_regs ms) 26 = getr regs 26) by exact (QX 26%bv 25%nat eq_refl eq_refl ltac:(lia)).
  pose proof (st_ok_pi_region_nth _ _ _ 6%nat pfa45_stkf HSP Hnth) as RA.
  change (ms_mem (restrict (w_H W) ms)) with (rd W (ms_mem ms)) in RA. unfold pfa45_stkf in RA.
  assert (V16 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx - 16) 8 (pf_mb T1 j 5)).
  { replace (d_A cx - 16) with (d_A cx + -16) by lia.
    apply (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ (-16) 8%N (SOff 567 0) (pf_mb T1 j 5) RA U60
      (in_eq _ _)).
    - cbn [sv_denot]. rewrite E567, unsigned_lit_small by (pose proof (MB 5 ltac:(lia)); lia).
      rewrite Z.add_0_r. reflexivity.
    - cbn [Z.of_N]. pose proof (MB 5 ltac:(lia)). lia.
    - cbn [Z.of_N]. lia. }
  assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3) k) by exact (conj HBASE (conj HJ1 HFR)).
  assert (H216' : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 h)
    by (apply KVS; [lia | lia | exact H216]).
  assert (H152' : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (h + 440))
    by (apply KVS; [lia | lia | exact H152]).
  pose proof (DLAND LAWS FFL fq cx h dsh_mac ly3 S3 W (with_vm_backing (m_vm_lazy md3) mat md3) k
    E1 (setpc ss0 (ss_pc ss0 - BASE)) ms HCTX1 HE1' EFL1 HSP Hchk H216' H152') as (HFRM1 & HSHD1).
  assert (HhA : in_app h 480).
  { assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm0)). apply in_or_app. right. left. reflexivity. }
    exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hin))))). }
  assert (HpA : 0 < c_n cx -> in_app (c_p cx) (c_n cx)).
  { intros Hc. pose proof HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
    destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
    pose proof (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))) as Ha.
    replace (req_size (c_n cx)) with (c_n cx) in Ha by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
    exact Ha. }
  assert (Hro : forall a0, in_roP SEGS pa_relro_lo pa_relro_hi a0 -> 0 <= a0 < kLowMemEnd).
  { intros a0 [(s & Hs & _ & Hsa) | Hr0]; apply pa_segs_low;
      [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a0 Hr0)]. }
  assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_mac ly3 S3 W (ms_mem ms)).
  { apply (d_body_rt B cx h n n (a3_xb buf op) dsh_ser2 dsh_mac ly3 S3 W mem3 (ms_mem ms) (d_A cx - 16) (d_A cx)
      (fun a => (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) \/ (d_A cx - 16 <= a < d_A cx)) HBODY).
    - unfold LLVMF_STK. lia.
    - lia.
    - intros a [Ha|Ha]; [right | left; lia].
      intros Hr. unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hr.
      unfold HUNT_SIZE in Hr. unfold shadow_addr, SHADOW_OFF in Ha.
      destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
      + apply (fshadow_not_app (d_FB cx) 512 (d_FB cx) 4096 a ltac:(lia) ltac:(lia) GFapp); lia.
      + apply (fshadow_not_app (d_FB cx) 512 (d_FB cx) 4096 a ltac:(lia) ltac:(lia) GFapp); lia.
      + apply (fshadow_not_app (d_FB cx) 512 (d_FB cx) 4096 a ltac:(lia) ltac:(lia) GFapp); lia.
      + apply (fshadow_not_app (d_FB cx) 512 (d_FB cx) 4096 a ltac:(lia) ltac:(lia) GFapp); lia.
      + apply (fshadow_not_app (d_FB cx) 512 h 480 a ltac:(lia) ltac:(lia) HhA); lia.
      + apply (fshadow_not_app (d_FB cx) 512 (c_p cx) (c_n cx) a ltac:(lia) ltac:(lia) (HpA Hc)); lia.
      + specialize (Hro a (proj1 Hr)). unfold kLowMemEnd in Hro. lia.
      + unfold AE2k.FF_canary in Hr. pose proof (proj1 GFapp) as HF4096. lia.
    - intros a Ha Hna. apply (aview_eq_of SEGS). apply KM; [exact Ha| |]; intros Hc; apply Hna;
        [left | right]; exact Hc.
    - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
    - exact HFRM1.
    - exact HSHD1.
    - lia. }
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSP Hrv).
  cbn [ss_pc setpc]. rewrite Hpc.
  apply SRr_ret.
  unfold pf_c1, a3f_stg. split; [exact Hfrom|].
  unfold d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
  split.
  { unfold cfg_at, w64.
    replace (BASE + (SIGMA DS___interceptor_trampoline_snprintf - BASE))
      with (SIGMA DS___interceptor_trampoline_snprintf) by lia.
    reflexivity. }
  split; [assumption|]. split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rLs. split; [unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia|].
    split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
    split; [exact Q9|]. split; [exact Q18|]. split; [rewrite Q20; exact Rs4|].
    rewrite Q25; exact Rs9. }
  split; [rewrite Q26; exact R26|].
  split.
  { cbv beta. split; [exact Q1|].
    split.
    { unfold pf_Rj. split; [exact Q21|]. split; [exact Q22|].
      split; [rewrite Q23; exact R23|]. split; [rewrite Q24; exact R24|]. exact Q27. }
    split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|].
    split; [exact Q13|]. split; [exact Q14|]. split; [exact Q15|]. split; [exact Q16|].
    split; [exact Q17|]. exact Q19. }
  split.
  { cbv beta. pose proof HSP1 as ((H232 & H344) & H224 & H248).
    split; [split; [split|split]|].
    - apply KVS; [lia | lia | exact H232].
    - apply KVS; [lia | lia | exact H344].
    - apply KVS; [lia | lia | exact H224].
    - apply KVS; [lia | lia | exact H248].
    - split; [split; [exact (proj1 HTAB)|]|].
      + apply KGF; [unfold d_obj, dobj_off; lia | | exact HGT].
        rewrite length_map, HLT1. unfold d_obj, dobj_off. lia.
      + split; [split; [exact Hr2|]|].
        * apply (garr8_frame SEGS (rd W mem3)); [exact HGB|].
          intros x Hx. rewrite Lb in Hx.
          apply (KHP buf (req_size (Z.max (slot_ser_defs.ser_cap op) 1)) x Hbapp Hbceil). lia.
        * split; [exact HJR|]. split; [exact HVP|]. split.
          -- apply KGF; [unfold d_obj, dobj_off; lia | | exact HOO].
             rewrite length_map. unfold d_obj, dobj_off. lia.
          -- split.
             ++ unfold pf_Y. split; [split; [exact Hp|]; split|].
                ** apply KVS; [lia | lia | exact H368].
                ** apply KVS; [lia | lia | exact H336].
                ** split; [exact Hjb|]. split; [apply KVS; [lia | lia | exact H392]|].
                   split; [apply KVS; [lia | lia | exact H408]|].
                   apply KGF; [unfold d_obj, dobj_off; lia | | exact HUSED].
                   rewrite LU. unfold d_obj, dobj_off. lia.
             ++ exact V16. }
  split.
  { pose proof HSP0 as (H232 & H344). split.
    - apply KVS; [lia | lia | exact H232].
    - apply KVS; [lia | lia | exact H344]. }
  exact HBODY1. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E1 (rd W mem3)) by (unfold sh_ok; apply Forall_nil).
pose proof (paj_run (fx := fq) B LAWS) as RUN.
unfold cfg_at, w64.
destruct Hj as [-> | ->];
 (paj_run_tok RUN HS HJ SHOK (0, 0);
  [ cbn [ss_mem];
    apply (pfa_awr E1 _ LLVMF_STK (d_S cx) [] _ _ ly3 DFRAME_CLASS (c_fpos cx) [] (d_A cx) (shadow_addr (d_FB cx))
      U60 U529); [unfold LLVMF_STK; lia | lia | rewrite GEFA; reflexivity |
      change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia]
  | eapply POST;
    [ exact HS | reflexivity | reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ | exact HFr | exact HG ] ]).
Qed.

End h.
End f.
End d.
