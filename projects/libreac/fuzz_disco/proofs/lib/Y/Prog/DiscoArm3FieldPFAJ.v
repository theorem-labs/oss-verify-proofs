(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 21 of its 45 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFA4.v, with its module paths and module names changed; 307 of its 342 lines of code are new or changed and 10 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFKit DiscoArm3FieldPFXKit DiscoArm3FieldPFK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_age_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfa_fin_sr (j : Z) : list sv :=
  [SLit 0; SOff A_TEXT PFR1_OFF; SOff AT_A (-16); SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0;
   SOff AT_STK 0; SOff AT_A 0; SOff AT_F 1728; SLit 18; SOff (A_OBJ 10) 0; SOff 563 0; SOff 564 0; SOff 565 0;
   SOff 566 0; SOff 567 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff AT_SH 0; SOff 553 0; SOff 554 0;
   SOff 555 0; SLit j; SOff AT_F (pfa_o j + 2); SOff AT_F 1728; SOff 559 0; SOff 560 0; SOff 561 0; SOff 562 0].
Definition pfa_xr : YP09.region := YP09.mkRegion (Some AT_A) (-16) 0 (-16) (-8) [pfa_xc].

Lemma pfa_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.

Lemma pfa_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, pfa_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfa_pi : forall (fq : YK11.FPState) (E : env) (ss : sstate) (ms : machine_state) (pc : Z),
  st_ok (fx := fq) SEGS E (setpc ss pc) ms -> st_ok_pi (fx := fq) SEGS VAL E (setpc ss (pc - BASE)) ms.
Proof.
  intros fq E ss ms pc H. unfold st_ok_pi, abs_ss.
  destruct ss as [pc0 rg fr mm rv fs]. cbn [setpc ss_pc].
  replace (BASE + (pc - BASE)) with pc by lia. exact H.
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
Hypothesis DBRT : d_body_rt_stmt B.

Definition pfa_run_stmt (j : Z) : Prop :=
  forall (fq : YK11.FPState) (W : world SEGS) (E : env) (ms : machine_state) (mdc : Model)
    STK sp0 FP ly S W0 mem md own lyc Sc k (Q : world SEGS -> config -> Prop),
  img_env VAL A_LIM E ->
  st_ok_pi (fx := fq) SEGS VAL E (pfa_ss0 j) (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (pfa_rs j) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall (ss : sstate) (ms' : machine_state) (mat' : list word),
     ss_regs ss = pfa_fin_sr j -> ss_resv ss = None ->
     d_land_chk dsh_mac (ss_mem ss) = true ->
     nth_error (ss_mem ss) 6 = Some pfa_xr ->
     st_ok (fx := fq) SEGS E (setpc ss (SIGMA AS___interceptor_trampoline_snprintf)) (restrict (w_H W) ms') ->
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (pfa_rs j) (rd W (ms_mem ms)) (rd W (ms_mem ms')) ->
     mem_grows (rd W (ms_mem ms)) (rd W (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.

Lemma pfa_main : forall j, 1 <= j <= 8 -> pfa_run_stmt j -> pfA_stmt B MT XM_LIB RLO RHI tfib_K j.
Proof.
intros j Hj8 RUNJ cx h i n now op W0 c0 T0 T1 buf count os vpad p W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R22 & R23 & R25 & R26) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & (HSL & Hjp & H408 & HUSED)).
destruct HSL as (Hp & H368 & H360).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296)
  by (rewrite (pfa_objs_len buf vpad os HVP Lo6), Los; lia).
assert (LU : length (a3f_used p) = 32%nat) by (unfold a3f_used; reflexivity).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as (Hceil & _). pose proof YM05.alloc_ceiling_lt as Hceil47.
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
assert (Hinh : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. right. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh) as (_ & _ & _ & HhA & _).
change (req_size HUNT_SIZE) with 480 in HhA.
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. destruct HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HMB : forall kk, 0 <= kk < 6 -> 0 <= pf_mb T1 j kk < 256).
{ intros kk Hkk. unfold pf_mb.
  exact (proj2 (garr8_nthZ SEGS _ _ _ (48 * (j - 1) + kk) HGT ltac:(lia) ltac:(rewrite length_map, HLT1; lia))). }
pose proof (pfa_seat B MT XM_LIB RLO RHI tfib_K DSEAT DFACTS LAWS PAL fq cx ly3 S3 W regs mem3 md3 k E T1 j
  HCTX HE HREG HFLAG HRL R25 R26 HGT HLT1 Hj8) as HS.
set (vals := pfa_vals regs T1 j) in HS.
pose proof (d_E_env cx E vals HE) as HE'.
pose proof HE' as (EE' & E32' & HEI' & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E vals) AT_A) = d_A cx)
  by (rewrite E60'; unfold w64; apply unsigned_lit_small; lia).
assert (U516 : bv_unsigned (ew (d_env cx E vals) AT_F) = d_FB cx)
  by (rewrite EF'; unfold w64; apply unsigned_lit_small; lia).
assert (U529 : bv_unsigned (ew (d_env cx E vals) AT_SH) = shadow_addr (d_FB cx)).
{ rewrite ESH'. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (U2 : bv_unsigned (ew (d_env cx E vals) AT_STK) = d_S cx).
{ unfold AT_STK. rewrite (EE' 2%nat 2%bv eq_refl). reflexivity. }
assert (U32 : bv_unsigned (ew (d_env cx E vals) 32) = SHADOW_OFF).
{ rewrite E32'. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (Hawr : awr_ok (d_env cx E vals) (pfa_rs j) LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx))
  (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ unfold pfa_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_SH (shadow_addr (d_FB cx))); [reflexivity | exact U529 | |].
  { unfold fshadow_region. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (d_A cx - d_S cx));
    [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
unfold cfg_at, w64.
apply (RUNJ fq W (d_env cx E vals) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PF_OFF)) mem3 (YK11.seg_rom SEGS)) md3
  LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 k _
  HEI' HS HJ Hawr).
intros ss ms1 mat1 Hsr Hrv Hchk Hxr HS1 HJ1 HFr1 HG1.
cbn [ms_mem YK11.mkst] in HFr1, HG1.
set (md' := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx - 8) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  rd W (ms_mem ms1) (Z_to_bv 64 a) = rd W mem3 (Z_to_bv 64 a)).
{ intros a Ha H1 H2. apply HFr1. rewrite unsigned_lit_small by lia. intros Hw. apply pfa_inw in Hw.
  change (base_val (d_env cx E vals) (Some AT_A)) with (bv_unsigned (ew (d_env cx E vals) AT_A)) in Hw.
  change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) AT_SH)) in Hw.
  rewrite U60, U529 in Hw. lia. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx - 8) ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  mbyte SEGS (rd W (ms_mem ms1)) a = mbyte SEGS (rd W mem3) a).
{ intros a Ha H1 H2. unfold mbyte. rewrite (KM a Ha H1 H2). reflexivity. }
assert (KV : forall a (nn : nat) v, d_A cx <= a -> a + Z.of_nat nn <= d_A cx + 472 ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms1)) a nn v).
{ intros a nn v H0 H1 Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
  intros x Hx. apply KB; [lia | lia | unfold shadow_addr, SHADOW_OFF; lia]. }
assert (KGF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms1)) a l).
{ intros a l H0 H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (pfa_app_nsh (d_FB cx) (d_FB cx) 4096 x GFapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (KGB : forall l, Z.of_nat (length l) <= req_size (Z.max (slot_ser_defs.ser_cap op) 1) ->
  garr8 SEGS (rd W mem3) buf l -> garr8 SEGS (rd W (ms_mem ms1)) buf l).
{ intros l H1 Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|]. intros x Hx.
  apply KB; [lia | lia |]. exact (pfa_app_nsh (d_FB cx) buf _ x Hbapp ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (QR : forall r, getr (ms_regs ms1) r = sv_denot (d_env cx E vals) (sr_get (pfa_fin_sr j) r)).
{ intros r. rewrite (st_ok_restrict_reg SEGS (w_H W) (d_env cx E vals) _ ms1 r HS1). cbn [ss_regs setpc].
  rewrite Hsr. reflexivity. }
assert (XR : forall (r : bv 5) (a : nat), a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  sv_denot (d_env cx E vals) (SOff a 0) = getr regs r).
{ intros r a Ha. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. unfold vals, pfa_vals.
  exact (pfa_env_reg cx E regs _ r a Ha). }
assert (XB : forall (q : nat) kk, (q < 6)%nat -> kk = Z.of_nat q ->
  sv_denot (d_env cx E vals) (SOff (563 + q) 0) = w64 (pf_mb T1 j kk)).
{ intros q kk Hq ->. cbn [sv_denot]. unfold vals. rewrite pfa_byte by exact Hq.
  rewrite unsigned_lit_small by (pose proof (HMB (Z.of_nat q) ltac:(lia)); lia). rewrite Z.add_0_r. reflexivity. }
assert (Q1 : getr (ms_regs ms1) 1 = w64 (BASE + PFR1_OFF)).
{ rewrite (QR (1%bv : bv 5)). exact (codeptr_val _ PFR1_OFF HEI'). }
assert (Q2s : spZ (ms_regs ms1) = d_A cx + -16).
{ unfold spZ. rewrite (QR (2%bv : bv 5)). change (sr_get (pfa_fin_sr j) 2) with (SOff AT_A (-16)).
  cbn [sv_denot]. rewrite U60. apply unsigned_lit_small. lia. }
assert (Q3 : getr (ms_regs ms1) 3 = getr regs 3) by (rewrite (QR (3%bv : bv 5)); exact (XR 3%bv 534%nat eq_refl)).
assert (Q4 : getr (ms_regs ms1) 4 = getr regs 4) by (rewrite (QR (4%bv : bv 5)); exact (XR 4%bv 535%nat eq_refl)).
assert (Q8 : getr (ms_regs ms1) 8 = w64 (d_S cx)).
{ rewrite (QR (8%bv : bv 5)). change (sr_get (pfa_fin_sr j) 8) with (SOff AT_STK 0).
  cbn [sv_denot]. rewrite U2, Z.add_0_r. reflexivity. }
assert (Q9 : getr (ms_regs ms1) 9 = w64 (d_A cx)).
{ rewrite (QR (9%bv : bv 5)). change (sr_get (pfa_fin_sr j) 9) with (SOff AT_A 0).
  cbn [sv_denot]. rewrite U60, Z.add_0_r. reflexivity. }
assert (Q10 : getr (ms_regs ms1) 10 = w64 (d_obj cx OMAC)).
{ rewrite (QR (10%bv : bv 5)). change (sr_get (pfa_fin_sr j) 10) with (SOff AT_F 1728).
  cbn [sv_denot]. rewrite U516. unfold w64, d_obj, dobj_off. f_equal; lia. }
assert (Q11 : getr (ms_regs ms1) 11 = w64 18) by (rewrite (QR (11%bv : bv 5)); reflexivity).
assert (Q12 : getr (ms_regs ms1) 12 = w64 (VAL (A_OBJ 10))).
{ rewrite (QR (12%bv : bv 5)). change (sr_get (pfa_fin_sr j) 12) with (SOff (A_OBJ 10) 0).
  cbn [sv_denot]. rewrite (HEI' (A_OBJ 10) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r. reflexivity. }
assert (Q13 : getr (ms_regs ms1) 13 = w64 (pf_mb T1 j 0)) by (rewrite (QR (13%bv : bv 5)); exact (XB 0%nat 0 ltac:(lia) eq_refl)).
assert (Q14 : getr (ms_regs ms1) 14 = w64 (pf_mb T1 j 1)) by (rewrite (QR (14%bv : bv 5)); exact (XB 1%nat 1 ltac:(lia) eq_refl)).
assert (Q15 : getr (ms_regs ms1) 15 = w64 (pf_mb T1 j 2)) by (rewrite (QR (15%bv : bv 5)); exact (XB 2%nat 2 ltac:(lia) eq_refl)).
assert (Q16 : getr (ms_regs ms1) 16 = w64 (pf_mb T1 j 3)) by (rewrite (QR (16%bv : bv 5)); exact (XB 3%nat 3 ltac:(lia) eq_refl)).
assert (Q17 : getr (ms_regs ms1) 17 = w64 (pf_mb T1 j 4)) by (rewrite (QR (17%bv : bv 5)); exact (XB 4%nat 4 ltac:(lia) eq_refl)).
assert (Q18 : getr (ms_regs ms1) 18 = w64 WS_MASK) by (rewrite (QR (18%bv : bv 5)); reflexivity).
assert (Q19 : getr (ms_regs ms1) 19 = w64 SHADOW_OFF).
{ rewrite (QR (19%bv : bv 5)). change (sr_get (pfa_fin_sr j) 19) with (SOff 32 0).
  cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity. }
assert (Q20 : getr (ms_regs ms1) 20 = w64 32) by (rewrite (QR (20%bv : bv 5)); reflexivity).
assert (Q21 : getr (ms_regs ms1) 21 = w64 (shadow_addr (d_FB cx))).
{ rewrite (QR (21%bv : bv 5)). change (sr_get (pfa_fin_sr j) 21) with (SOff AT_SH 0).
  cbn [sv_denot]. rewrite U529, Z.add_0_r. reflexivity. }
assert (Q22 : getr (ms_regs ms1) 22 = getr regs 22) by (rewrite (QR (22%bv : bv 5)); exact (XR 22%bv 553%nat eq_refl)).
assert (Q23 : getr (ms_regs ms1) 23 = getr regs 23) by (rewrite (QR (23%bv : bv 5)); exact (XR 23%bv 554%nat eq_refl)).
assert (Q24 : getr (ms_regs ms1) 24 = getr regs 24) by (rewrite (QR (24%bv : bv 5)); exact (XR 24%bv 555%nat eq_refl)).
assert (Q25 : getr (ms_regs ms1) 25 = w64 j) by (rewrite (QR (25%bv : bv 5)); reflexivity).
assert (Q26 : getr (ms_regs ms1) 26 = w64 (d_obj cx OT + 48 * (j - 1) + 2)).
{ rewrite (QR (26%bv : bv 5)). change (sr_get (pfa_fin_sr j) 26) with (SOff AT_F (pfa_o j + 2)).
  cbn [sv_denot]. rewrite U516. unfold w64, pfa_o, d_obj, dobj_off. f_equal; lia. }
assert (Q27 : getr (ms_regs ms1) 27 = w64 (d_obj cx OMAC)).
{ rewrite (QR (27%bv : bv 5)). change (sr_get (pfa_fin_sr j) 27) with (SOff AT_F 1728).
  cbn [sv_denot]. rewrite U516. unfold w64, d_obj, dobj_off. f_equal; lia. }
pose proof (pfa_pi fq _ _ _ _ HS1) as HS1p.
pose proof (st_ok_pi_region_nth _ _ _ 6%nat pfa_xr HS1p Hxr) as RX.
cbn [ms_mem restrict] in RX.
assert (V16 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx - 16) 8 (pf_mb T1 j 5)).
{ replace (d_A cx - 16) with (d_A cx + -16) by lia.
  apply (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ (-16) 8%N (SOff 568 0) (pf_mb T1 j 5) RX U60 (in_eq _ _)).
  - exact (XB 5%nat 5 ltac:(lia) eq_refl).
  - cbn [Z.of_N]. pose proof (HMB 5 ltac:(lia)). lia.
  - cbn [Z.of_N]. lia. }
assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms1) md' k) by exact (conj HBASE (conj HJ1 HFR)).
assert (HHS1 : d_hslots cx h W (ms_mem ms1)).
{ apply (d_hslots_kept cx h W W mem3 (ms_mem ms1)); [|exact (d_hslots_of_frame cx h dsh_ser2 W mem3 HFRM)].
  intros a Ha. apply (aview_eq_of SEGS). apply KM; [lia | lia | unfold shadow_addr, SHADOW_OFF; lia]. }
destruct (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_mac ly3 S3 W md' k
  (d_env cx E vals) _ ms1 HCTX1 HE' (d_env_fl cx E vals) HS1p Hchk HHS1) as (HFRM1 & HSHD1).
assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_mac ly3 S3 W (ms_mem ms1)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_ser2 dsh_mac ly3 S3 W mem3 (ms_mem ms1) (d_A cx - 16) (d_A cx - 8)
    (fun a => (d_A cx - 16 <= a < d_A cx - 8) \/ d_fsh cx a) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a [Ha | Ha]; [left; exact Ha | right].
    unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
    exact (pfa_fsh_nrd B cx h a GFapp ltac:(lia) ltac:(lia) HhA HpA Hro Ha).
  - intros a Ha Hna. apply (aview_eq_of SEGS). apply KM; [exact Ha | |].
    + intros H'. apply Hna. left. exact H'.
    + intros H'. apply Hna. right. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. exact H'.
  - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
  - exact HFRM1.
  - exact HSHD1.
  - lia. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
rewrite (st_ok_restrict_mkst SEGS (w_H W) (d_env cx E vals) _ ms1 HS1 Hrv).
apply SRr_ret.
unfold pf_c1, a3f_stg. split; [exact Hfrom|].
unfold d_at.
exists fq, ly3, S3, (ms_regs ms1), (ms_mem ms1), md', k, acc.
split.
{ unfold cfg_at, w64. cbn [ss_pc setpc].
  replace (BASE + (SIGMA AS___interceptor_trampoline_snprintf - BASE))
    with (SIGMA AS___interceptor_trampoline_snprintf) by lia.
  reflexivity. }
split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rLs. split; [exact Q2s|]. split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|].
  split; [exact Q8|]. split; [exact Q9|]. split; [exact Q19|]. split; [exact Q18|]. exact Q20. }
split; [rewrite Q24; exact R24|].
split.
{ split; [exact Q1|]. split.
  { unfold pf_Rj. split; [exact Q21|]. split; [rewrite Q22; exact R22|]. split; [rewrite Q23; exact R23|].
    split; [exact Q25|]. exact Q26. }
  split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|].
  split; [exact Q14|]. split; [exact Q15|]. split; [exact Q16|]. split; [exact Q17|]. exact Q27. }
split.
{ split.
  { split; [split|].
    - apply KV; [lia | cbn [Z.of_nat]; lia | exact H208].
    - apply KV; [lia | cbn [Z.of_nat]; lia | exact H320].
    - split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H192] | apply KV; [lia | cbn [Z.of_nat]; lia | exact H200]]. }
  split.
  { split; [exact (proj1 HTAB)|].
    apply KGF; [unfold d_obj, dobj_off; lia | | exact HGT].
    rewrite length_map, HLT1. unfold d_obj, dobj_off. lia. }
  split.
  { split; [exact Hr2|]. apply KGB; [|exact HGB]. rewrite Lb. lia. }
  split; [exact HJR|]. split; [exact HVP|].
  split.
  { apply KGF; [unfold d_obj, dobj_off; lia | | exact HOO].
    rewrite length_map. unfold d_obj, dobj_off. lia. }
  split.
  { unfold pf_Y, a3f_slots. split.
    { split; [exact Hp|]. split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H368]
                                 | apply KV; [lia | cbn [Z.of_nat]; lia | exact H360]]. }
    split; [exact Hjp|]. split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H408]|].
    apply KGF; [unfold d_obj, dobj_off; lia | | exact HUSED].
    rewrite LU. unfold d_obj, dobj_off. lia. }
  exact V16. }
split.
{ split; [apply KV; [lia | cbn [Z.of_nat]; lia | exact H208] | apply KV; [lia | cbn [Z.of_nat]; lia | exact H320]]. }
exact HBODY1.
Qed.

End h.
End f.
End d.
