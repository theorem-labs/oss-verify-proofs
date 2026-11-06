(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 458 of its 493 lines of code are new or changed and 3975 lines of the source are left out. *)
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
DiscoArm3FieldMDFacts DiscoArm3FieldMDKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c jtok_is_c printf_facts_c
disco_json_reader_model disco_jscalar_model slot_ser_defs.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac md_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Definition md_sr1 : list sv := map (fun r : nat => if (r =? 10)%nat then SLit 1 else a3f_srx 0 r) (seq 0 32).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma md_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E (a3f_vals regs ++ ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, length_map, length_seq; lia).
  unfold a3f_vals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
    by (rewrite length_map, length_seq; lia).
  pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
    (Z.to_nat (bv_unsigned r))) as Hm.
  cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma md_frame_ro : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> m' = m.
Proof.
intros E rs m m' HF Hro. apply functional_extensionality. intros x. apply HF.
intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma md_regs_ok_call : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ret : Z),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + ret) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT ret :: atom_regs 532 30) R.
Proof.
intros cx E R ret HEI H1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                              | rewrite H1; symmetry; exact (codeptr_val _ ret HEId) ]).
Qed.

Lemma md_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

Lemma md_dE_havoc : forall (cx : dcx) E j ws, d_E cx E -> (530 <= j)%nat -> d_E cx (havoc E j ws).
Proof.
intros cx E j ws (H1 & H32 & HI & H60 & H516 & H529) Hj.
split; [|split; [|split; [|split; [|split]]]].
- intros nn r Hr. pose proof (bv_unsigned_in_range 5 r) as Hb. change (bv_modulus 5) with 32 in Hb.
  rewrite ew_havoc_old by lia. exact (H1 nn r Hr).
- rewrite ew_havoc_old by lia. exact H32.
- apply img_env_havoc_hi; [exact HI | unfold A_LIM; lia].
- rewrite ew_havoc_old by (unfold AT_A; lia). exact H60.
- rewrite ew_havoc_old by (unfold AT_F; lia). exact H516.
- rewrite ew_havoc_old by (unfold AT_SH; lia). exact H529.
Qed.

Section h.
Variable B : asyms.

Lemma md_regs_ok : forall cx E regs ex, d_E cx E -> d_rL B cx regs ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (a3f_sr 0) regs.
Proof.
  intros cx E regs ex HE HL.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & HSH). unfold AT_A in HA60. unfold AT_SH in HSH.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
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

Lemma md_regs_ok1 : forall cx E regs ex, d_E cx E -> d_rL B cx regs -> getr regs 10 = w64 1 ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) md_sr1 regs.
Proof.
  intros cx E regs ex HE HL H10.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & HSH). unfold AT_A in HA60. unfold AT_SH in HSH.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | exact H10
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

Definition md_Y (cx : dcx) (T1 : list byte) (p count mp : Z) : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => a3f_slots cx p count W m /\
    val_mem SEGS (rd W m) (d_A cx + 408) 8 (d_obj cx OO + 144 * p) /\
    garr8 SEGS (rd W m) (d_obj cx OUSED) (a3f_used (p + 1)) /\
    garr8 SEGS (rd W m) (d_obj cx OWID) (snd (a3f_model T1 p) ++ [0]) /\
    a3f_mstr cx W m mp (fst (a3f_model T1 p)).

Definition md_ret (ra : Z) (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte)
  (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte) (p mp : Z)
  : world SEGS -> config -> Prop :=
  a3f_st B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad ra dsh_md
    (fun regs => getr regs 10 = w64 1 /\ getr regs 22 = w64 (d_obj cx OT + 48 * p) /\ getr regs 23 = w64 mp)
    (md_Y cx T1 p count mp).

Definition md_cY (cx : dcx) (T1 : list byte) (now count : Z) (os : list disco_json_reader_model.jobj) (p mp : Z)
  (j : nat) (kind x : Z) (text : list Z) : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => md_Y cx T1 p count mp W m /\ (j < 6)%nat /\ kind <> 0 /\ - 2 ^ 31 <= kind < 2 ^ 31 /\
    Forall (fun c => 0 < c < 256) text /\
    disco_json_reader_model.jtok_is (a3_text T1 now)
      (nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) kind text = true /\
    exists sl, mdf_xarg W m x (map (Z_to_bv 8) text) sl /\
      (x + Z.of_nat (length (map (Z_to_bv 8) text) + 1 + length sl) <= d_A cx - TJTOK_IS_STK \/ d_A cx <= x).

Definition md_call (ra : Z) (j : nat) (kind x : Z) (text : list Z) (cx : dcx) (h i n now op : Z) (W0 : world SEGS)
  (c0 : config) (T0 T1 : list byte) (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte)
  (p mp : Z) : world SEGS -> config -> Prop :=
  a3f_stg B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad AF_both3_jtok_is 0 dsh_md
    (fun regs => getr regs 1 = w64 (BASE + ra) /\
       getr regs 10 = w64 (d_obj cx OO + 144 * p + 24 * Z.of_nat j) /\
       getr regs 11 = w64 kind /\ getr regs 12 = w64 x /\
       getr regs 22 = w64 (d_obj cx OT + 48 * p) /\ getr regs 23 = w64 mp /\
       getr regs 27 = w64 (shadow_addr (d_FB cx)))
    (md_cY cx T1 now count os p mp j kind x text).

Lemma md_call_ok : forall (ra : Z) (j : nat) (kind x : Z) (text : list Z) (cx : dcx) (h i n now op : Z)
  (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf count : Z) (os : list disco_json_reader_model.jobj)
  (vpad : list byte) (p mp : Z) (W : world SEGS) (c : config),
  MD_OFF <= ra <= MD_OFF + 112 -> ra mod 4 = 0 ->
  md_call ra j kind x text cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c ->
  SRr SEGS W c (md_ret ra cx h i n now op W0 c0 T0 T1 buf count os vpad p mp).
Proof.
intros ra j kind x text cx h i n now op W0 c0 T0 T1 buf count os vpad p mp W c Hra Hra4 (HFROM & Hd).
destruct Hd as (fq & ly3 & S3 & R & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFRS & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRLs & R24 & (Q1 & QX10 & Q11 & QX12 & QX22 & QX23 & QX27) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HCY).
destruct HCY as (HY & Hj6 & Hk0 & Hkr & FT & JT & sl & HXA & HDSx).
pose proof HY as (HSLOTS & H408 & HUSED & HWID & HMSTR).
pose proof HSLOTS as (Hpc & H368 & H360).
pose proof HRLs as (QSP0 & QGP & QTP & QS0 & QS1 & QS19 & QS18 & QS20).
assert (QSP : spZ R = d_A cx) by lia.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFRS)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HdE & HREG & HFLAG & _).
pose proof HdE as (HER & HE32 & HEI0 & HEA & HEF & HESH).
assert (HFU : bv_unsigned (ew E 516%nat) = d_FB cx)
  by (change 516%nat with AT_F; rewrite HEF; unfold w64; apply unsigned_lit_small; lia).
assert (HEAU : bv_unsigned (ew E 60%nat) = d_A cx)
  by (change 60%nat with AT_A; rewrite HEA; unfold w64; apply unsigned_lit_small; lia).
assert (HESHU : bv_unsigned (ew E 529%nat) = shadow_addr (d_FB cx)).
{ change 529%nat with AT_SH. rewrite HESH. unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (QO1 : (d_A cx - d_S cx) mod 16 = 0).
{ pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
  rewrite GA32 in DA. rewrite GS16 in DS.
  replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult. }
assert (Q1' : getr R 1 = Z_to_bv 64 (BASE + ra)) by exact Q1.
assert (QRA : YK0s.ret_ok (getr R 1))
  by (rewrite Q1'; apply ret_ok_codeptr_v; unfold MD_OFF in *; lia).
assert (QRZ : 4096 <= raZ R).
{ unfold raZ. rewrite Q1'. pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
  rewrite unsigned_lit_small by (pose proof pa_B_ok as (PB0 & PB1 & _); unfold MD_OFF in *; lia).
  unfold MD_OFF in *. lia. }
assert (HARO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem3)) by exact HIMG.
assert (HCV : ConstsViewDef.consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem3)
  by exact (mc_cv_ok B W mem3 MCRO MCUN HARO).
destruct HXA as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
pose proof HTAB as (Hage0 & HTg0).
destruct Hage0 as (removed0 & Hagem0 & Hpost0).
pose proof Hpost0 as (LT & _ & _ & _ & _ & _ & TOK & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os LT TOK Hnow HJR) as (_ & Hc8 & Los & Lo6 & Inb & B33 & LX).
destruct (mdf_tok_v B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k h n (a3_xb buf op) p (Z.of_nat j)
  HCTX HBODY ltac:(lia) ltac:(lia)) as (VT1 & VT2 & VT3).
pose proof HBUF as (Hbr0 & Hbg0).
pose proof HBLK as (HPerm0 & _).
assert (Hbufin : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as Hrq.
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbufin) as (HbSh & HbHull).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbufin) as (_ & Hbuf4 & Hbceil & Hbapp & _ & _ & _).
rewrite Hreq in Hbceil, Hbapp, HbSh, HbHull.
destruct (mdk_site SEGS (rd W mem3) T1 now count os p j (d_obj cx OO) buf
  (d_obj cx OO + 144 * p + 24 * Z.of_nat j) kind vpad text
  (nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none)
  LT TOK Hnow HJR Hpc Hj6 HVP HOO Hbg0 ltac:(lia) ltac:(unfold a3_r in Hbr0; lia)
  eq_refl Hk0 FT JT eq_refl)
  as (EK & EN & ETX & MV1 & MV2 & MV3 & RVP & RVN & JM & LPT & GVP & VP0 & VP63).
destruct (mdk_obj_tok os count p j Los Lo6 Hpc Hj6) as (Ho0 & Ht0 & _).
assert (Hoi : In (nth (Z.to_nat p) os []) os) by (eapply nth_error_In; exact Ho0).
assert (Hti : In (nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) (nth (Z.to_nat p) os []))
  by (eapply nth_error_In; exact Ht0).
pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Inb _ Hoi) _ Hti) as Hib.
set (tk := nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) in *.
assert (HTl : Z.of_nat (length (map (Z_to_bv 8) text)) = Z.of_nat (length text)) by (rewrite length_map; reflexivity).
eapply SRr_mono.
- eapply (aj_jtok_at B LAWS TJTOK) with (o := d_A cx - d_S cx) (v := d_obj cx OO + 144 * p + 24 * Z.of_nat j)
    (x := x) (kind := kind) (vk := disco_json_reader_model.tv_kind tk) (vp := buf + snd (fst tk)) (vn := snd tk)
    (T := map (Z_to_bv 8) text) (slack := sl)
    (P := printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (a3_text T1 now) tk)).
  + exact HJ.
  + exact HFRM0.
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
  + exact Q11.
  + exact QX12.
  + lia.
  + rewrite EK. lia.
  + unfold d_obj, dobj_off. lia.
  + unfold d_obj, dobj_off. lia.
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
  + rewrite QSP. exact HDSx.
  + intros Hvk Hvn.
    assert (Hbt : 0 <= snd (fst tk) /\ snd (fst tk) + Z.of_nat (length text) <= Z.of_nat (length (a3_text T1 now))).
    { destruct Hib as [Hz | (Ho1 & Hn1 & Hsl)]; [rewrite EK in Hz; exfalso; lia|].
      unfold disco_jscalar_model.jlen in Hsl. rewrite EN in Hsl. exact (conj Ho1 Hsl). }
    destruct Hbt as (Hbt0 & Hbt1).
    unfold a3_r in Hbr0.
    split; [exact LPT|]. split; [exact GVP|]. split; [exact VP0|]. split; [exact VP63|].
    split.
    { rewrite HTl. apply (amem_range_sub_app buf (Z.max (slot_ser_defs.ser_cap op) 1)
        (buf + snd (fst tk)) (Z.of_nat (length text))); [exact Hbapp | lia | lia | lia | lia]. }
    split.
    { rewrite HTl. apply (block_shadow_range _ _ buf (Z.max (slot_ser_defs.ser_cap op) 1)
        (buf + snd (fst tk)) (Z.of_nat (length text)) HbSh); lia. }
    split.
    { intros Hpos s Hs. apply HbHull. rewrite HTl in Hs.
      pose proof (YCbq.shadow_mono buf (buf + snd (fst tk)) ltac:(lia)) as Sm1.
      pose proof (YCbq.shadow_mono (buf + snd (fst tk) + Z.of_nat (length text) - 1)
        (buf + Z.max (slot_ser_defs.ser_cap op) 1 - 1) ltac:(lia)) as Sm2.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm1) as Sd1.
      pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Sm2) as Sd2. lia. }
    left. rewrite QSP, HTl. unfold TJTOK_IS_STK, ESTACK. lia.
- cbv beta. intros W2 c2 _ Hpost.
  destruct Hpost as (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFRMc & _ & HJ4 & HJc & HPr & HPerm & HKeep & Hres).
  clear dependent fq. rename fx2 into fq. rename HFRMc into HFRM0.
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
    intros y Hy. apply KB. lia. }
  pose proof (DSEAT LAWS PAL fq cx dsh_md ly3 S3 W R mem3 md3 k E AF_both3_jtok_is
    (SLit 0 :: SOff A_TEXT ra :: atom_regs 532 30) (map (getr R) (tl all_regs)) [] [] [] (d_facts [] [])
    HCTX HdE HREG HFLAG (md_regs_ok_call cx E R ra HEI0 Q1')
    (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr R) (tl all_regs)) [] [] HCTX HdE I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
  unfold ss_d in HS1.
  assert (HEIC : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
    by (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
  assert (Hra40 : 0 <= ra < 2 ^ 40) by (unfold MD_OFF in Hra; lia).
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
  assert (HHS2 : d_hslots cx h W2 mem2).
  { apply (d_hslots_kept cx h W W2 mem3 mem2); [intros a Ha; apply KA; lia|].
    exact (d_hslots_of_frame cx h dsh_md W mem3 HFRM). }
  destruct (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_md ly2 S2 W2 md2 k _ _
    (YK11.mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + ra)) mem2 (YK11.seg_rom SEGS))
    HCTX4 HE2 HFL2 HS2 ltac:(vm_compute; reflexivity) HHS2) as (HFRM4 & HSHD4).
  pose proof (DBPC LAWS DROH DCAN cx h n (a3_xb buf op) dsh_md dsh_md ly3 S3 W mem3 md3
    ly2 S2 W2 mem2 md2 k TJTOK_IS_STK (spZ R) [] 0 HBODY (conj HBASE HJ4) HJc
    ltac:(rewrite QSP; unfold LLVMF_STK, TJTOK_IS_STK, ESTACK; lia) ltac:(rewrite QSP; lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
    ltac:(intros (a & Ha & _); exfalso; exact (inFP_nil a Ha))
    HPerm HFRM4 HSHD4) as HBODY4.
  assert (Hblen : buf + Z.of_nat (length (a3_text T1 now ++ [0])) <= alloc_ceiling).
  { rewrite length_app. cbn [length]. unfold a3_r in Hbr0. lia. }
  pose proof HTAB as (Hage & HTg).
  unfold md_ret, a3f_st. cbv beta.
  split.
  { pose proof HFROM as (HA1 & HA2 & HA3 & HA4). split; [exact HA1|].
    split; [exact (wle_trans _ _ _ _ HA2 HWLE)|]. split; [exact HA3 | exact HA4]. }
  unfold d_arm_at_pf, d_at. cbv beta.
  exists fq, ly2, S2, regs2, mem2, md2, k, acc.
  split; [unfold cfg_at, w64; rewrite Q1'; reflexivity|].
  split; [exact HFRM0|].
  split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|]. split; [exact Hk|].
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
    split; [transitivity (getr R 19); [exact (HPr 19 ltac:(unfold acallee_saved; lia)) | exact QS19]|].
    split; [transitivity (getr R 18); [exact (HPr 18 ltac:(unfold acallee_saved; lia)) | exact QS18]|].
    split; [transitivity (getr R 20); [exact (HPr 20 ltac:(unfold acallee_saved; lia)) | exact QS20]|].
    transitivity (getr R 27); [exact (HPr 27 ltac:(unfold acallee_saved; lia)) | exact QX27]. }
  split.
  { split; [transitivity (getr R 24); [exact (HPr 24 ltac:(unfold acallee_saved; lia)) | exact R24]|].
    split.
    { destruct Hres as [(_ & H10') | (Hnm & _)]; [exact H10'|]. exfalso. apply Hnm. exact JM. }
    split; [transitivity (getr R 22); [exact (HPr 22 ltac:(unfold acallee_saved; lia)) | exact QX22]|].
    transitivity (getr R 23); [exact (HPr 23 ltac:(unfold acallee_saved; lia)) | exact QX23]. }
  split.
  { split.
    { pose proof HSP1 as ((H208 & H320) & H192 & H200).
      split; [split; [apply KV; [lia | cbn; lia | exact H208] | apply KV; [lia | cbn; lia | exact H320]]|].
      split; [apply KV; [lia | cbn; lia | exact H192] | apply KV; [lia | cbn; lia | exact H200]]. }
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
    { split; [exact Hpc|]. split; [apply KV; [lia | cbn; lia | exact H368] | apply KV; [lia | cbn; lia | exact H360]]. }
    split; [apply KV; [lia | cbn; lia | exact H408]|].
    split.
    { apply KG; [unfold d_obj, dobj_off; lia| |exact HUSED].
      replace (length (a3f_used (p + 1))) with 32%nat by (unfold a3f_used; reflexivity).
      unfold d_obj, dobj_off. lia. }
    split.
    { apply KG; [unfold d_obj, dobj_off; lia| |exact HWID].
      rewrite length_app. cbn [length]. destruct (mdf_model_txt T1 p) as (_ & _ & _ & Lw).
      unfold d_obj, dobj_off. lia. }
    destruct HMSTR as [(Hmp & Hs) | (Hmp & Hg)]; [left; exact (conj Hmp Hs)|].
    right. split; [exact Hmp|]. apply KG; [rewrite Hmp; unfold d_obj, dobj_off; lia| |exact Hg].
    rewrite Hmp, length_app. cbn [length]. destruct (mdf_model_txt T1 p) as (_ & Lf & _ & _).
    unfold d_obj, dobj_off. lia. }
  split.
  { pose proof HSP0 as (H208b & H320b).
    split; [apply KV; [lia | cbn; lia | exact H208b] | apply KV; [lia | cbn; lia | exact H320b]]. }
  exact HBODY4.
Qed.

End h.
End f.
End d.
