(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
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
DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit DiscoArm3JtokSpec DiscoArm3FieldCall
DiscoArm3FieldMDFacts DiscoArm3FieldMDKit DiscoArm3FieldMDA.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c jtok_is_c printf_facts_c
disco_json_reader_model disco_jscalar_model disco_json_text slot_ser_defs slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition md_acs : list YP09.chunk := [YP09.mkChunk 408 (CVal 8 (SOff 563 0))].
Definition md_sr3 (c : Z) : list sv :=
  map (fun r : nat => if (r =? 10)%nat then SLit 1 else if (r =? 22)%nat then SOff AT_F c else a3f_srx 0 r) (seq 0 32).
Definition md_fcs3 (p v : Z) : list YP09.chunk := [YP09.mkChunk (2184 + 48 * p) (CVal 4 (SLit v))].

Lemma md_owned01 : forall (T : list byte) p,
  disco_table_c.owned_of T p = 0 \/ disco_table_c.owned_of T p = 1 ->
  disco_table_c.u_at T (48 * p + 24) 4 = 0 \/ disco_table_c.u_at T (48 * p + 24) 4 = 1.
Proof.
  intros T p H. pose proof (mdf_u_at_range T (48 * p + 24) 4) as R.
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in R.
  unfold disco_table_c.owned_of, disco_table_c.s32_at in H.
  set (u := disco_table_c.u_at T (48 * p + 24) 4) in *.
  unfold bv_swrap, bv_wrap in H. change (bv_half_modulus 32) with 2147483648 in H.
  change (bv_modulus 32) with 4294967296 in H.
  lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition md_ostr (T1 : list byte) (p : Z) : Z :=
  if disco_table_c.u_at T1 (48 * p + 24) 4 =? 0 then VAL (A_OBJ 16) else VAL (A_OBJ 15).

Section h.
Variable B : asyms.

Lemma md_regs_ok3 : forall cx E regs ex c, d_E cx E -> d_rL B cx regs -> getr regs 10 = w64 1 ->
  getr regs 22 = w64 (d_FB cx + c) ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (md_sr3 c) regs.
Proof.
  intros cx E regs ex c HE HL H10 H22.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & HF516 & HSH). unfold AT_A in HA60. unfold AT_SH in HSH. unfold AT_F in HF516.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | exact H10
    | rewrite HF516, H22; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned;
      unfold bv_wrap; rewrite Zplus_mod_idemp_l; reflexivity
    | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned;
      first [ rewrite <- Hsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
    | exact H18
    | exact H20
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (md_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

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
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis MCRO : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Lemma md_run1 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (p mp : Z) (W : world SEGS) (c : config),
  f_md B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (md_call B MT XM_LIB RLO RHI tfib_K (MD_OFF + 20) 2 1 mp (fst (a3f_model T1 p))
    cx h i n now op W0 c0 T0 T1 buf count os vpad p mp).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R23 & R22) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
pose proof HY as (HSL & H408 & HUSED & HWID & HMSTR).
pose proof HSL as (Hp & H368 & H360).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1; unfold LLVMF_STK in GSlo.
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as Hceil0.
set (vals := a3f_vals regs ++ [Z_to_bv 64 (d_obj cx OO + 144 * p)]).
assert (Lv : length vals = 33%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (E563 : ew (d_env cx E vals) 563 = Z_to_bv 64 (d_obj cx OO + 144 * p))
  by exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia)).
assert (U563 : bv_unsigned (ew (d_env cx E vals) 563) = d_obj cx OO + 144 * p)
  by (rewrite E563; apply unsigned_lit_small; unfold d_obj, dobj_off; lia).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
    by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (U60w : ew (d_env cx E vals) AT_A = w64 (d_A cx))
    by (rewrite EO by (unfold AT_FL, AT_A; lia); exact E60).
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx)
    by (rewrite EO by (unfold AT_FL; lia); change 516%nat with AT_F; rewrite EF; apply unsigned_lit_small; lia).
assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
    by (rewrite EO by (unfold AT_FL; lia); exact E32).
assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
    by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
        unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3) by exact (md_env_reg cx E regs _ (3%bv : bv 5) 534%nat eq_refl).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4) by exact (md_env_reg cx E regs _ (4%bv : bv 5) 535%nat eq_refl).
assert (X22 : ew (d_env cx E vals) 553 = getr regs 22) by exact (md_env_reg cx E regs _ (22%bv : bv 5) 553%nat eq_refl).
assert (X23 : ew (d_env cx E vals) 554 = getr regs 23) by exact (md_env_reg cx E regs _ (23%bv : bv 5) 554%nat eq_refl).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24) by exact (md_env_reg cx E regs _ (24%bv : bv 5) 555%nat eq_refl).
assert (X27 : ew (d_env cx E vals) 558 = getr regs 27) by exact (md_env_reg cx E regs _ (27%bv : bv 5) 558%nat eq_refl).
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] []))
  by (apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE); exact I).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) md_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 408 8%N (SOff 563 0) (d_obj cx OO + 144 * p)).
  - cbn [sv_denot]. rewrite U563, Z.add_0_r. reflexivity.
  - cbn. unfold d_obj, dobj_off. lia.
  - cbn. lia.
  - exact H408. }
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E MD_OFF (a3f_sr 0) vals md_acs [] []
  (d_facts [] []) HCTX HE HREG HFLAG (md_regs_ok B cx E regs _ HE HRL) HGf Hacs (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
unfold cfg_at. change (w64 (BASE + MD_OFF)) with (Z_to_bv 64 (BASE + MD_OFF)).
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ. rewrite pa_sigma_jtok_is in HS.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24; prreg HS (27%bv : bv 5) Q27.
set (R := ms_regs ms) in *.
destruct (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HIMG) as (_ & _ & _ & HSTR & _).
destruct (mdf_mstr_x B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k h n (a3_xb buf op) mp T1 p
  HCTX HBODY HSTR HMSTR) as (sl & HXA).
pose proof HXA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XL).
destruct (mdf_model_txt T1 p) as (FT & LFT & _ & _).
destruct (DiscoArm3FieldModel.a3f_obj T1 now count os p HLT1 HTOK1 Hnow HJR Hp) as (_ & _ & Hmodel & _ & _ & _).
assert (HDS : mp + Z.of_nat (length (map (Z_to_bv 8) (fst (a3f_model T1 p))) + 1 + length sl) <=
  d_A cx - TJTOK_IS_STK \/ d_A cx <= mp).
{ left. rewrite length_map in XL |- *. destruct HMSTR as [(Hmp & _) | (Hmp & _)].
  - pose proof HSTR as (_ & _ & _ & _ & _ & _ & _ & S11 & _).
    destruct S11 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & HimgS) & _).
    assert (Himg : in_img SEGS mp) by (rewrite Hmp; apply HimgS; cbn [length]; lia).
    pose proof (pa_segs_low mp Himg) as Hlo.
    unfold YG0f.kLowMemEnd, TJTOK_IS_STK, ESTACK in *. lia.
  - rewrite Hmp in XL |- *. unfold d_obj, dobj_off, TJTOK_IS_STK, ESTACK in *. lia. }
apply SRr_ret.
unfold md_call, a3f_stg.
split; [exact Hfrom|].
unfold d_at.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split;
    [ unfold spZ; rewrite Q2; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; unfold w64;
      rewrite Z.add_0_r; apply unsigned_lit_small; lia|];
    split; [rewrite Q3, X3; exact Rgp|];
    split; [rewrite Q4, X4; exact Rtp|];
    split; [rewrite Q8, U2w; reflexivity|];
    split; [rewrite Q9; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; reflexivity|];
    split; [rewrite Q19, U32w; reflexivity|];
    split; [rewrite Q18; unfold w64, slot_inv.WS_MASK; reflexivity|];
    rewrite Q20; reflexivity. }
split; [rewrite Q24, X24; exact R24|].
split.
{ split; [rewrite Q1; unfold w64; reflexivity|].
  split; [rewrite Q10, U563; unfold w64; f_equal; cbn [Z.of_nat]; lia|].
  split; [rewrite Q11; reflexivity|].
  split; [rewrite Q12, X23; exact R23|].
  split; [rewrite Q22, X22; exact R22|].
  split; [rewrite Q23, X23; exact R23|].
  rewrite Q27, X27; exact Rs27. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  split; [exact HY|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FT|]. split; [exact Hmodel|].
  exists sl. exact (conj HXA HDS). }
split; [exact HSP0|]. exact HBODY.
Qed.

Lemma md_run2 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (p mp : Z) (W : world SEGS) (c : config),
  md_ret B MT XM_LIB RLO RHI tfib_K (MD_OFF + 20) cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (md_call B MT XM_LIB RLO RHI tfib_K (MD_OFF + 44) 3 1 (d_obj cx OWID) (snd (a3f_model T1 p))
    cx h i n now op W0 c0 T0 T1 buf count os vpad p mp).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R10 & R22 & R23) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
pose proof HY as (HSL & H408 & HUSED & HWID & HMSTR).
pose proof HSL as (Hp & H368 & H360).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1; unfold LLVMF_STK in GSlo.
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as Hceil0.
set (vals := a3f_vals regs ++ [Z_to_bv 64 (d_obj cx OO + 144 * p)]).
assert (Lv : length vals = 33%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (E563 : ew (d_env cx E vals) 563 = Z_to_bv 64 (d_obj cx OO + 144 * p))
  by exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia)).
assert (U563 : bv_unsigned (ew (d_env cx E vals) 563) = d_obj cx OO + 144 * p)
  by (rewrite E563; apply unsigned_lit_small; unfold d_obj, dobj_off; lia).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
    by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (U60w : ew (d_env cx E vals) AT_A = w64 (d_A cx))
    by (rewrite EO by (unfold AT_FL, AT_A; lia); exact E60).
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx)
    by (rewrite EO by (unfold AT_FL; lia); change 516%nat with AT_F; rewrite EF; apply unsigned_lit_small; lia).
assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
    by (rewrite EO by (unfold AT_FL; lia); exact E32).
assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
    by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
        unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3) by exact (md_env_reg cx E regs _ (3%bv : bv 5) 534%nat eq_refl).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4) by exact (md_env_reg cx E regs _ (4%bv : bv 5) 535%nat eq_refl).
assert (X22 : ew (d_env cx E vals) 553 = getr regs 22) by exact (md_env_reg cx E regs _ (22%bv : bv 5) 553%nat eq_refl).
assert (X23 : ew (d_env cx E vals) 554 = getr regs 23) by exact (md_env_reg cx E regs _ (23%bv : bv 5) 554%nat eq_refl).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24) by exact (md_env_reg cx E regs _ (24%bv : bv 5) 555%nat eq_refl).
assert (X27 : ew (d_env cx E vals) 558 = getr regs 27) by exact (md_env_reg cx E regs _ (27%bv : bv 5) 558%nat eq_refl).
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] []))
  by (apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE); exact I).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) md_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 408 8%N (SOff 563 0) (d_obj cx OO + 144 * p)).
  - cbn [sv_denot]. rewrite U563, Z.add_0_r. reflexivity.
  - cbn. unfold d_obj, dobj_off. lia.
  - cbn. lia.
  - exact H408. }
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 20) md_sr1 vals md_acs [] []
  (d_facts [] []) HCTX HE HREG HFLAG (md_regs_ok1 B cx E regs _ HE HRL R10) HGf Hacs (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
unfold cfg_at. change (w64 (BASE + (MD_OFF + 20))) with (Z_to_bv 64 (BASE + (MD_OFF + 20))).
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ. rewrite pa_sigma_jtok_is in HS.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24; prreg HS (27%bv : bv 5) Q27.
set (R := ms_regs ms) in *.
destruct (mdf_wid_x B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k h n (a3_xb buf op) T1 p
  HCTX HBODY HWID) as (sl & HXA).
pose proof HXA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XL).
destruct (mdf_model_txt T1 p) as (_ & _ & FT & LFT).
destruct (DiscoArm3FieldModel.a3f_obj T1 now count os p HLT1 HTOK1 Hnow HJR Hp) as (_ & _ & _ & Hwidth & _ & _).
assert (HDS : d_obj cx OWID + Z.of_nat (length (map (Z_to_bv 8) (snd (a3f_model T1 p))) + 1 + length sl) <=
  d_A cx - TJTOK_IS_STK \/ d_A cx <= d_obj cx OWID).
{ left. rewrite length_map in XL |- *. unfold d_obj, dobj_off, TJTOK_IS_STK, ESTACK in *. lia. }
apply SRr_ret.
unfold md_call, a3f_stg.
split; [exact Hfrom|].
unfold d_at.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split;
    [ unfold spZ; rewrite Q2; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; unfold w64;
      rewrite Z.add_0_r; apply unsigned_lit_small; lia|];
    split; [rewrite Q3, X3; exact Rgp|];
    split; [rewrite Q4, X4; exact Rtp|];
    split; [rewrite Q8, U2w; reflexivity|];
    split; [rewrite Q9; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; reflexivity|];
    split; [rewrite Q19, U32w; reflexivity|];
    split; [rewrite Q18; unfold w64, slot_inv.WS_MASK; reflexivity|];
    rewrite Q20; reflexivity. }
split; [rewrite Q24, X24; exact R24|].
split.
{ split; [rewrite Q1; unfold w64; reflexivity|].
  split; [rewrite Q10, U563; unfold w64; f_equal; cbn [Z.of_nat]; lia|].
  split; [rewrite Q11; reflexivity|].
  split; [rewrite Q12, U516; unfold w64, d_obj, dobj_off; reflexivity|].
  split; [rewrite Q22, X22; exact R22|].
  split; [rewrite Q23, X23; exact R23|].
  rewrite Q27, X27; exact Rs27. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  split; [exact HY|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FT|]. split; [exact Hwidth|].
  exists sl. exact (conj HXA HDS). }
split; [exact HSP0|]. exact HBODY.
Qed.

Lemma md_run3 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (p mp : Z) (W : world SEGS) (c : config),
  md_ret B MT XM_LIB RLO RHI tfib_K (MD_OFF + 44) cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (md_call B MT XM_LIB RLO RHI tfib_K (MD_OFF + 112) 4 3 (md_ostr T1 p)
    (disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T1 p))
    cx h i n now op W0 c0 T0 T1 buf count os vpad p mp).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R10 & R22 & R23) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
pose proof HY as (HSL & H408 & HUSED & HWID & HMSTR).
pose proof HSL as (Hp & H368 & H360).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as Hceil0.
assert (Hu01 : disco_table_c.u_at T1 (48 * p + 24) 4 = 0 \/ disco_table_c.u_at T1 (48 * p + 24) 4 = 1).
{ apply md_owned01. pose proof HTOK1 as (_ & _ & _ & T4). exact (proj2 (proj2 (T4 p ltac:(lia)))). }
destruct (mdk_slice SEGS (rd W mem3) (d_obj cx OT) (48 * p + 24) T1 4 HGT ltac:(lia) ltac:(rewrite HLT1; lia))
  as (VU & RU).
change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in RU.
set (vals := a3f_vals regs ++ [Z_to_bv 64 (d_obj cx OO + 144 * p)]).
assert (Lv : length vals = 33%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (E563 : ew (d_env cx E vals) 563 = Z_to_bv 64 (d_obj cx OO + 144 * p))
  by exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia)).
assert (U563 : bv_unsigned (ew (d_env cx E vals) 563) = d_obj cx OO + 144 * p)
  by (rewrite E563; apply unsigned_lit_small; unfold d_obj, dobj_off; lia).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (U60w : ew (d_env cx E vals) AT_A = w64 (d_A cx))
  by (rewrite EO by (unfold AT_FL, AT_A; lia); exact E60).
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx)
  by (rewrite EO by (unfold AT_FL; lia); change 516%nat with AT_F; rewrite EF; apply unsigned_lit_small; lia).
assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
  by (rewrite EO by (unfold AT_FL; lia); exact E32).
assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3) by exact (md_env_reg cx E regs _ (3%bv : bv 5) 534%nat eq_refl).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4) by exact (md_env_reg cx E regs _ (4%bv : bv 5) 535%nat eq_refl).
assert (X23 : ew (d_env cx E vals) 554 = getr regs 23) by exact (md_env_reg cx E regs _ (23%bv : bv 5) 554%nat eq_refl).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24) by exact (md_env_reg cx E regs _ (24%bv : bv 5) 555%nat eq_refl).
assert (X27 : ew (d_env cx E vals) 558 = getr regs 27) by exact (md_env_reg cx E regs _ (27%bv : bv 5) 558%nat eq_refl).
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] []))
  by (apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE); exact I).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) md_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 408 8%N (SOff 563 0) (d_obj cx OO + 144 * p)).
  - cbn [sv_denot]. rewrite U563, Z.add_0_r. reflexivity.
  - cbn. unfold d_obj, dobj_off. lia.
  - cbn. lia.
  - exact H408. }
assert (Hfcs : forall v, v = disco_table_c.u_at T1 (48 * p + 24) 4 ->
  Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) (md_fcs3 p v)).
{ intros v Ev. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) (2184 + 48 * p) 4%N (SLit v) v).
  - reflexivity.
  - cbn. lia.
  - cbn. lia.
  - replace (d_FB cx + (2184 + 48 * p)) with (d_obj cx OT + (48 * p + 24)) by (unfold d_obj, dobj_off; lia).
    rewrite Ev. exact VU. }
destruct (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HIMG) as (_ & _ & _ & HSTR & _).
destruct (mdf_owned_str W mem3 T1 p HSTR) as (HS15 & HS16).
pose proof (mdf_owned_text_ok (reac_disco_table_json_c.tj_entry T1 p)) as (FT & LFT).
assert (HXS : exists sl, mdf_xarg W mem3 (md_ostr T1 p)
    (map (Z_to_bv 8) (disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T1 p))) sl /\
  (md_ostr T1 p + Z.of_nat (length (map (Z_to_bv 8) (disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T1 p)))
     + 1 + length sl) <= d_A cx - TJTOK_IS_STK \/ d_A cx <= md_ostr T1 p)).
{ unfold md_ostr. destruct (Z.eqb_spec (disco_table_c.u_at T1 (48 * p + 24) 4) 0) as [Hz | Hz].
  - pose proof (HS16 Hz) as Hr. destruct (mdf_rostr_x W mem3 _ _ Hr) as (sl & HXA). exists sl. split; [exact HXA|].
    pose proof HXA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XL).
    destruct Hr as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & HimgS) & _).
    assert (Himg : in_img SEGS (VAL (A_OBJ 16))) by (apply HimgS; lia).
    pose proof (pa_segs_low _ Himg) as Hlo.
    left. rewrite length_map in XL |- *. unfold YG0f.kLowMemEnd, TJTOK_IS_STK, ESTACK in *. lia.
  - pose proof (HS15 Hz) as Hr. destruct (mdf_rostr_x W mem3 _ _ Hr) as (sl & HXA). exists sl. split; [exact HXA|].
    pose proof HXA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XL).
    destruct Hr as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & HimgS) & _).
    assert (Himg : in_img SEGS (VAL (A_OBJ 15))) by (apply HimgS; lia).
    pose proof (pa_segs_low _ Himg) as Hlo.
    left. rewrite length_map in XL |- *. unfold YG0f.kLowMemEnd, TJTOK_IS_STK, ESTACK in *. lia. }
destruct (DiscoArm3FieldModel.a3f_obj T1 now count os p HLT1 HTOK1 Hnow HJR Hp) as (_ & _ & _ & _ & Howned & _).
assert (R22' : getr regs 22 = w64 (d_FB cx + (2160 + 48 * p)))
  by (rewrite R22; unfold d_obj, dobj_off; f_equal; lia).
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
unfold cfg_at. change (w64 (BASE + (MD_OFF + 44))) with (Z_to_bv 64 (BASE + (MD_OFF + 44))).
assert (Hp8 : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
destruct Hu01 as [Hu | Hu]; pose proof (Hfcs _ (eq_sym Hu)) as Hfcs'; clear Hfcs.
all: destruct Hp8 as [Ep|[Ep|[Ep|[Ep|[Ep|[Ep|[Ep|Ep]]]]]]].
all: rewrite Ep in Hfcs', R22'.
all: pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 44) _ vals md_acs _ []
  (d_facts [] []) HCTX HE HREG HFLAG (md_regs_ok3 cx E regs [Z_to_bv 64 (d_obj cx OO + 144 * p)] _ HE HRL R10 R22')
  HGf Hacs Hfcs' (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
all: unfold ss_d in HS.
all: md_ro_base HS 60%nat.
all: md_ro_base HS 516%nat.
all: md_ro_base HS 529%nat.
all: reshok_bx HS 32%nat.
all: paj_run_tok RUN HS HJ SHOK Bspan.
all: try (solve [cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil]).
all: assert (Emem : ms_mem ms = mem3)
  by (cbn [ms_mem YK11.mkst] in HF; exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity))).
all: rewrite Emem in HJ.
all: rewrite pa_sigma_jtok_is in HS.
all: set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
all: pmkst HS.
all: rewrite Emem.
all: prreg HS (1%bv : bv 5) Q1.
all: prreg HS (2%bv : bv 5) Q2.
all: prreg HS (3%bv : bv 5) Q3.
all: prreg HS (4%bv : bv 5) Q4.
all: prreg HS (8%bv : bv 5) Q8.
all: prreg HS (9%bv : bv 5) Q9.
all: prreg HS (10%bv : bv 5) Q10.
all: prreg HS (11%bv : bv 5) Q11.
all: prreg HS (12%bv : bv 5) Q12.
all: prreg HS (18%bv : bv 5) Q18.
all: prreg HS (19%bv : bv 5) Q19.
all: prreg HS (20%bv : bv 5) Q20.
all: prreg HS (22%bv : bv 5) Q22.
all: prreg HS (23%bv : bv 5) Q23.
all: prreg HS (24%bv : bv 5) Q24.
all: prreg HS (27%bv : bv 5) Q27.
all: set (R := ms_regs ms) in *.
all: assert (RLs : d_rLs B cx 0 R)
  by (unfold d_rLs;
      split; [unfold spZ; rewrite Q2; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; unfold w64;
              rewrite Z.add_0_r; apply unsigned_lit_small; lia|];
      split; [rewrite Q3, X3; exact Rgp|];
      split; [rewrite Q4, X4; exact Rtp|];
      split; [rewrite Q8, U2w; reflexivity|];
      split; [rewrite Q9; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; reflexivity|];
      split; [rewrite Q19, U32w; reflexivity|];
      split; [rewrite Q18; unfold w64, slot_inv.WS_MASK; reflexivity|];
      rewrite Q20; reflexivity).
all: assert (Q12' : getr R 12 = w64 (md_ostr T1 p))
  by (rewrite Q12; unfold md_ostr; rewrite Hu; cbn [Z.eqb]; rewrite EO by (unfold AT_FL; lia); unfold w64;
      first [ rewrite <- (HEI0 (A_OBJ 16)) by (unfold A_OBJ, A_TEXT, A_LIM; lia)
            | rewrite <- (HEI0 (A_OBJ 15)) by (unfold A_OBJ, A_TEXT, A_LIM; lia) ];
      rewrite Z_to_bv_bv_unsigned; reflexivity).
all: assert (Q22' : getr R 22 = w64 (d_obj cx OT + 48 * p))
  by (rewrite Q22, U516; unfold w64, d_obj, dobj_off; f_equal; lia).
all: apply SRr_ret.
all: unfold md_call, a3f_stg.
all: split; [exact Hfrom|].
all: unfold d_at.
all: exists fq, ly3, S3, R, mem3, md', k, acc.
all: split; [unfold cfg_at, w64; reflexivity|].
all: split; [exact HFRM0|].
all: split; [exact HBASE|].
all: split; [exact HJ|].
all: split; [exact HFR|].
all: split; [exact Hk|].
all: split; [exact Hnev|].
all: split; [exact HMO|].
all: split; [exact Hacc|].
all: split; [exact Hi|].
all: split; [exact Hn|].
all: split; [exact Hnow|].
all: split; [exact RLs|].
all: split; [rewrite Q24, X24; exact R24|].
all: split;
  [ split; [rewrite Q1; unfold w64; reflexivity|];
    split; [rewrite Q10, U563; unfold w64; f_equal; cbn [Z.of_nat]; lia|];
    split; [rewrite Q11; reflexivity|];
    split; [exact Q12'|];
    split; [exact Q22'|];
    split; [rewrite Q23, X23; exact R23|];
    rewrite Q27, X27; exact Rs27 |].
all: split;
  [ split; [exact HSP1|]; split; [exact HTAB|]; split; [exact HBUF|]; split; [exact HJR|];
    split; [exact HVP|]; split; [exact HOO|];
    split; [exact HY|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [exact FT|];
    split; [exact Howned|]; exact HXS |].
all: split; [exact HSP0|].
all: exact HBODY.
Qed.

Lemma md_run4 : forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (p mp : Z) (W : world SEGS) (c : config),
  md_ret B MT XM_LIB RLO RHI tfib_K (MD_OFF + 112) cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (f_mo B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p).
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R10 & R22 & R23) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HY).
pose proof HY as (HSL & H408 & HUSED & HWID & HMSTR).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (vals := a3f_vals regs ++ []).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (U60w : ew (d_env cx E vals) AT_A = w64 (d_A cx))
  by (rewrite EO by (unfold AT_FL, AT_A; lia); exact E60).
assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
  by (rewrite EO by (unfold AT_FL; lia); exact E32).
assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3) by exact (md_env_reg cx E regs _ (3%bv : bv 5) 534%nat eq_refl).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4) by exact (md_env_reg cx E regs _ (4%bv : bv 5) 535%nat eq_refl).
assert (X22 : ew (d_env cx E vals) 553 = getr regs 22) by exact (md_env_reg cx E regs _ (22%bv : bv 5) 553%nat eq_refl).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24) by exact (md_env_reg cx E regs _ (24%bv : bv 5) 555%nat eq_refl).
assert (X27 : ew (d_env cx E vals) 558 = getr regs 27) by exact (md_env_reg cx E regs _ (27%bv : bv 5) 558%nat eq_refl).
assert (HGf : facts_ok (d_env cx E vals) (d_facts [] []))
  by (apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HCTX HE); exact I).
pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W regs mem3 md3 k E (MD_OFF + 112) md_sr1 vals [] [] []
  (d_facts [] []) HCTX HE HREG HFLAG (md_regs_ok1 B cx E regs [] HE HRL R10) HGf (Forall_nil _) (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
md_ro_base HS 60%nat. md_ro_base HS 516%nat. md_ro_base HS 529%nat.
unfold cfg_at. change (w64 (BASE + (MD_OFF + 112))) with (Z_to_bv 64 (BASE + (MD_OFF + 112))).
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
reshok_bx HS 32%nat.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MO_OFF.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem3).
{ cbn [ms_mem YK11.mkst] in HF. exact (md_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)). }
rewrite Emem in HJ.
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pmkst HS. rewrite Emem.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
set (R := ms_regs ms) in *.
apply SRr_ret.
unfold f_mo, a3f_st.
split; [exact Hfrom|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, R, mem3, md', k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ; rewrite Q2; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; unfold w64;
          apply unsigned_lit_small; lia|].
  split; [rewrite Q3, X3; exact Rgp|].
  split; [rewrite Q4, X4; exact Rtp|].
  split; [rewrite Q8, U2w; reflexivity|].
  split; [rewrite Q9; change (ew _ 60) with (ew (d_env cx E vals) AT_A); rewrite U60w; reflexivity|].
  split; [rewrite Q19, U32w; reflexivity|].
  split; [rewrite Q18; unfold w64, slot_inv.WS_MASK; reflexivity|].
  split; [rewrite Q20; reflexivity|].
  rewrite Q27, X27; exact Rs27. }
split; [split; [rewrite Q24, X24; exact R24 | rewrite Q22, X22; exact R22]|].
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|]. split; [exact HJR|].
  split; [exact HVP|]. split; [exact HOO|].
  split; [exact HSL|]. split; [exact H408 | exact HUSED]. }
split; [exact HSP0|]. exact HBODY.
Qed.

Theorem a3f_mda : forall p, seg_mda_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p cx h i n now op W0 c0 T0 T1 buf count os vpad mp W c Hs.
pose proof (md_call_ok B MT XM_LIB RLO RHI tfib_K DSEAT DFACTS DLAND LAWS PAL FFL MT_TRIV TJTOK DBPC DROH DCAN MCRO MCUN)
  as MC.
eapply SRr_bind; [exact (md_run1 cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c Hs)|].
intros W1 c1 _ H1.
eapply SRr_bind; [exact (MC (MD_OFF + 20) 2%nat 1 mp (fst (a3f_model T1 p)) cx h i n now op W0 c0 T0 T1 buf count os vpad
  p mp W1 c1 ltac:(unfold MD_OFF; lia) eq_refl H1)|].
intros W2 c2 _ H2.
eapply SRr_bind; [exact (md_run2 cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W2 c2 H2)|].
intros W3 c3 _ H3.
eapply SRr_bind; [exact (MC (MD_OFF + 44) 3%nat 1 (d_obj cx OWID) (snd (a3f_model T1 p)) cx h i n now op W0 c0 T0 T1
  buf count os vpad p mp W3 c3 ltac:(unfold MD_OFF; lia) eq_refl H3)|].
intros W4 c4 _ H4.
eapply SRr_bind; [exact (md_run3 cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W4 c4 H4)|].
intros W5 c5 _ H5.
eapply SRr_bind; [exact (MC (MD_OFF + 112) 4%nat 3 (md_ostr T1 p)
  (disco_json_text.owned_text (reac_disco_table_json_c.tj_entry T1 p)) cx h i n now op W0 c0 T0 T1
  buf count os vpad p mp W5 c5 ltac:(unfold MD_OFF; lia) eq_refl H5)|].
intros W6 c6 _ H6.
exact (md_run4 cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W6 c6 H6).
Qed.

End h.
End f.
End d.
