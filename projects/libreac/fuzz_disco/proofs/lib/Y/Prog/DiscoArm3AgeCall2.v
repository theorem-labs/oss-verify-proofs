(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 885 of its 952 lines of code are new or changed and 3943 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YC88 YCjr YCj1 YCja YXcalls YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YL05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoArm3TailK DiscoYEntBodyStmt DiscoYEntryShapes DiscoArm3 DiscoArm3AgeSt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjSpecLift.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
reac_disco_table_age_c reac_disco_table_json_c slot_ser_defs slot_ser_pure.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac a3c_in := repeat (first [left; reflexivity | right]).

Lemma a3c_cap : forall op, 2 <= a3_cap op <= 1280.
Proof.
intros op. unfold a3_cap, slot_ser_defs.ser_cap, slot_ser_defs.ser_k.
pose proof (Z_land_upper (Z.shiftr op 2) 31 ltac:(lia)) as Hk.
destruct (Z.eqb_spec (Z.land (Z.shiftr op 2) 31) 0); lia.
Qed.

Lemma a3c_mod8 : forall s, s mod 16 = 0 -> s mod 8 = 0.
Proof.
intros s Hs. apply Z.mod_divide in Hs; [|lia]. apply Z.mod_divide; [lia|].
destruct Hs as [q Hq]. exists (2 * q). lia.
Qed.

Lemma a3c_mod16 : forall a s, a mod 32 = 0 -> s mod 16 = 0 -> (a - s) mod 16 = 0.
Proof.
intros a s Ha Hs. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hs; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [p Hp], Hs as [q Hq]. exists (2 * p - q). lia.
Qed.

Lemma a3c_dsh_in_hi : forall o k c, (dobj_off o + dobj_size o + 7) / 8 = c -> c <= k -> dsh_in o k = false.
Proof. intros o k c Hc H. unfold dsh_in. apply andb_false_iff. right. apply Z.ltb_ge. rewrite Hc. exact H. Qed.

Lemma a3c_dsh_loop_T : forall j, 270 <= j < 320 -> dsh_loop j = 0.
Proof.
intros j Hj. unfold dsh_loop, dsh, dobjs. cbn [dsh_look].
rewrite (a3c_dsh_in_hi OCUR j 22 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OO j 192 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OUSED j 212 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OMAC j 219 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi ONM j 227 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OTOK j 235 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi ODISP j 246 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OWID j 253 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OAGE j 261 ltac:(vm_compute; reflexivity) ltac:(lia)).
rewrite (a3c_dsh_in_hi OOUR j 267 ltac:(vm_compute; reflexivity) ltac:(lia)).
unfold dsh_in, dsh_live. cbn [dobj_off dobj_size live_loop].
replace ((2160 + 400 + 7) / 8) with 320 by (vm_compute; reflexivity).
replace ((2160 + 400) / 8) with 320 by (vm_compute; reflexivity).
replace (2160 / 8) with 270 by (vm_compute; reflexivity).
rewrite (proj2 (Z.leb_le 270 j) ltac:(lia)), (proj2 (Z.ltb_lt j 320) ltac:(lia)).
cbn [andb]. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma a3c_kept : forall (E : env) (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
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

Lemma a3c_dE : forall (cx : dcx) E j ws, d_E cx E -> (530 <= j)%nat -> d_E cx (havoc E j ws).
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

Lemma a3c_regs_ok : forall (cx : dcx) (E : env) (R : bvmap 5 word) (ra : Z),
  img_env VAL A_LIM E -> getr R 1 = Z_to_bv 64 (BASE + ra) ->
  regs_ok (d_env cx E (map (getr R) (tl all_regs))) (SLit 0 :: SOff A_TEXT ra :: atom_regs 532 30) R.
Proof.
intros cx E R ra HEI H1.
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr R) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEI | unfold AT_FL, A_LIM; lia]).
regs_ok_cases_pre ltac:(first [ rewrite getr_zero; reflexivity
                             | rewrite H1; symmetry; exact (codeptr_val _ ra HEId) ]).
Qed.

Lemma a3c_garr8_aview : forall (H : word -> bool) (m : word -> option byte) p l j,
  garr8 SEGS (mrestrict H m) p l -> (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j HG Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j HG Hj). cbn [option_map].
destruct (HG j Hj) as [_ Hr]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. lia.
Qed.

Lemma a3c_chunk_extent_mod8 : forall (B : asyms) ly S rv k,
  ARm B ly S rv -> In k (st_chunks S) -> ck_extent k mod 8 = 0.
Proof.
intros B ly S rv k M Hk.
pose proof (chunk_facts B ly S rv k M Hk) as (_ & _ & _ & _ & _ & _ & G7 & _ & GG).
destruct (ck_beg k) as [|o|r o|c q]; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & _). rewrite Gext.
  pose proof (YG0a.class_ok (prim_class o) ltac:(lia)) as (_ & K & _). Z.div_mod_to_equations. lia.
- destruct GG as (_ & Gp & _ & Gext & _). rewrite Gext.
  pose proof (secondary_geometry (ck_req k) ltac:(lia) Gp) as (_ & _ & _ & _ & SG & _).
  unfold kPage in *. Z.div_mod_to_equations. lia.
Qed.

Lemma a3c_blk_vis8 : forall (B : asyms), AR_laws SEGS B ->
  forall ly S (W : world SEGS) mem md p n a,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < 8 * ((p + req_size n + 7) / 8) -> aview SEGS (w_H W) mem a <> None.
Proof.
intros B LAWS ly S W mem md p n a HA Hin Ha.
destruct (Z.lt_ge_cases a (p + req_size n)) as [Hlt|Hge].
- pose proof (al_blocks _ _ LAWS ly S W mem md p n HA Hin) as (_ & _ & _ & _ & HP & _).
  apply aview_some_of_apresent. exact (proj1 (HP a ltac:(lia))).
- destruct HA as (M & _).
  apply In_ablocks in Hin as (k & Hk & _ & Hu & Hn).
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & G3 & G4 & _ & G6 & G7 & G8 & _).
  pose proof (a3c_chunk_extent_mod8 B ly S _ k M Hk) as EXT.
  assert (SP : forall e', sptr_exp (ck_beg k) <> ASh e') by (destruct (ck_beg k); discriminate).
  assert (E0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
  assert (IJ : In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S)).
  { unfold ajunk. right; right. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left.
    apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_junk. cbv zeta.
    apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; right. left; reflexivity. }
  pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ M) _ IJ) as RV.
  unfold range_vis in RV. cbn [fst snd] in RV.
  unfold ck_n in RV. rewrite Hn in G8, RV. subst p.
  assert (LT : a < ck_base B ly k + ck_extent k).
  { clear - Ha G3 G4 G6 G8 EXT. Z.div_mod_to_equations. lia. }
  pose proof (RV (a - (ck_base B ly k + ck_rz k + req_size n)) ltac:(lia)) as V.
  rewrite aeval_aoff in V by exact SP. rewrite E0 in V.
  replace (ck_base B ly k + (ck_rz k + req_size n) + (a - (ck_base B ly k + ck_rz k + req_size n))) with a in V by lia.
  exact V.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis DUNIV : duniv_ok B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis AMALLOC : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis TTJ : tj_specPF B TJ_STK 0 dimg_tj.
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis DBMAL : d_body_malloc_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBPC : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Lemma a3c_tgeo : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_shadow cx dsh_loop W3 mem3 ->
  d_obj cx OT mod 8 = 0 /\ range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (d_obj cx OT) 400.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HC HSH.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
apply Z.mod_divide in HFal; [|lia]. destruct HFal as (q & Hq).
assert (HD8 : d_FB cx / 8 = 4 * q).
{ rewrite Hq. replace (q * 32) with (4 * q * 8) by lia. apply Z.div_mul. lia. }
assert (HT : d_obj cx OT = d_FB cx + 2160) by reflexivity.
split.
{ rewrite HT, Hq. replace (q * 32 + 2160) with ((4 * q + 270) * 8) by lia. apply Z_mod_mult. }
intros x Hx. exists 0. unfold shadow_of_addr.
assert (Hkk : SHADOW_OFF + x / 8 = shadow_addr (d_FB cx) + (x / 8 - d_FB cx / 8)).
{ unfold shadow_addr. lia. }
assert (Hb : 270 <= x / 8 - d_FB cx / 8 < 320).
{ rewrite HD8. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  rewrite HT, Hq in Hx. lia. }
rewrite Hkk. split.
- rewrite (HSH (x / 8 - d_FB cx / 8) ltac:(unfold DFRAME_SH; lia)). f_equal. apply a3c_dsh_loop_T. exact Hb.
- unfold saddr_ok. left. reflexivity.
Qed.

Lemma a3c_save : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k E shf,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k -> d_E cx E ->
  Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx shf) ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 8) = Some RA_LLVMF /\
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 16) = Some (s0Z (c_regs cx)).
Proof.
intros cx ly3 S3 W3 mem3 md3 k E shf HC HE HREG.
pose proof HC as (HB & HJ & HFR).
pose proof HB as ((HPRE & HRA & _) & _).
pose proof HE as (EE & _).
pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hs0r. change (bv_modulus 64) with (2 ^ 64) in Hs0r.
split.
{ apply (rdword_of_val_mem SEGS); [|unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + -8) by lia.
  apply (slot_of_region E (rd W3 mem3) (d_S cx) dsave_chunks (-104) 0 0 0 (-8) (SOff 1 0) RA_LLVMF).
  - exact (Forall_inv HREG).
  - rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  - vm_compute. left. reflexivity.
  - cbn [sv_denot]. rewrite (EE 1%nat 1%bv eq_refl). rewrite Z.add_0_r. unfold raZ in HRA. rewrite HRA. reflexivity.
  - unfold RA_LLVMF. lia. }
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; lia].
  replace (d_S cx - 16) with (d_S cx + -16) by lia.
  apply (slot_of_region E (rd W3 mem3) (d_S cx) dsave_chunks (-104) 0 0 0 (-16) (SOff 8 0) (s0Z (c_regs cx))).
  - exact (Forall_inv HREG).
  - rewrite (EE 2%nat 2%bv eq_refl). reflexivity.
  - vm_compute. right. left. reflexivity.
  - cbn [sv_denot]. rewrite (EE 8%nat 8%bv eq_refl). rewrite Z.add_0_r. reflexivity.
  - unfold s0Z. lia. }
Qed.

Lemma a3c_achain : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k E shf,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k -> d_E cx E ->
  Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx shf) ->
  exists ch, achain ly3 (aview SEGS (w_H W3) mem3) (d_A cx) (d_S cx) ch.
Proof.
intros cx ly3 S3 W3 mem3 md3 k E shf HC HE HREG.
destruct (a3c_save cx ly3 S3 W3 mem3 md3 k E shf HC HE HREG) as (Hw8 & Hw16).
pose proof HC as (HB & HJ & HFR).
pose proof HB as ((HPRE & HRA & _) & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC)
  as (GS16 & GSlo & GShi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
change (spZ (c_regs cx)) with (d_S cx) in Hch, Hal16, Hslo, Hshi, Hbot, Htop.
destruct (Z_lt_le_dec (d_S cx) (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
- exists [(d_S cx, RA_LLVMF, s0Z (c_regs cx))].
  apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
  apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem3)
    (d_S cx) (s0Z (c_regs cx)) RA_LLVMF [] (d_A cx) Hch).
  + lia.
  + intros a Ha. exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha).
  + exact Hw8.
  + exact Hw16.
  + unfold RA_LLVMF. lia.
  + lia.
  + exact (a3c_mod8 _ GS16).
  + exact Hlt.
  + lia.
- exists []. left. split; [|reflexivity]. right. left. rewrite Etop. lia.
Qed.

Lemma a3c_strlen_at : forall (fq : YK11.FPState) lo hi pc, astrlen_realizesM (fx := fq) SEGS B lo hi pc ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x r o raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> 0 < x -> 0 <= r -> r + 1 < 2 ^ 32 -> x + r + 1 <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  first_byte SEGS W memT x (r + 1) 0 r -> src_ok SEGS W regsT memT x (r + 1) -> amem_range x (r + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (r + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x (r + 1) ->
  (forall a, x + r < a < x + r - (x + r) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
  consts_view SEGS lo hi W memT ->
  SRr SEGS W (mkCfg (YK11.mkst (fx := fq) regsT (Z_to_bv 64 pc) memT (YK11.seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (YK11.mkst (fx := fq) regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 r /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros fq lo hi pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x r o raw HJ Ha0 Hx0 Hr0 Hr32 Hxr
  Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsrc Hmr Hrng Hhull Hslack Hrom.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x r HPRE Ha0 Hx0 Hr0 Hr32 Hxr Hfb Hsrc Hmr Hrng Hhull Hslack Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; unfold ESTACK in *; lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

Theorem c_mal : c_mal_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 W c (HFROM & HST).
unfold a3_st, d_at in HST.
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R1 & R10 & R21 & R27) & (HSP1 & HTAB) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HROD & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H184 & H120 & H136 & H376 & H280 & H232 & H264).
pose proof (d_hslots_of_frame cx h dsh_loop W mem3 HFRM) as HHS.
pose proof HBLK as (HPerm0 & HNot0 & Hbb & HOFFb).
pose proof HTAB as ((rem & Hage & HAP) & HgT1).
pose proof HAP as (HlenT1 & _ & _ & _ & _ & _ & HokT1 & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBASE as ((HPRE & _ & _ & _ & _ & _ & _ & _ & HEV0 & HBB0 & _) & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _ & Hach0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & H47 & _ & HtopS & Htophi).
pose proof HJ as (_ & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr regs) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
pose proof (a3c_cap op) as Hcap.
assert (Exb : forall p, a3_xb p op = [(p, a3_cap op)]).
{ intros p. unfold a3_xb, a3_cap in *. rewrite Z.max_l by lia. reflexivity. }
set (cap := a3_cap op) in *.
assert (Rq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
pose proof (pal_rt_below B TL) as (_ & Hpc0).
assert (Hra : raZ regs = BASE + P_MAL_RA)
  by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; unfold P_MAL_RA; lia).
assert (Hs0 : s0Z regs = d_S cx) by (unfold s0Z; rewrite Rs0; unfold w64; apply unsigned_lit_small; lia).
destruct (a3c_save cx ly3 S3 W mem3 md3 k E dsh_loop HCTX HE HREG) as (Hw8 & Hw16).
assert (Hrd : forall a, d_S cx <= a < 2 ^ 64 -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
  by (intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha)).
assert (HCH : exists ch, chain_pre ly3 (aview SEGS (w_H W) mem3) regs ch /\
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regs ch) (as_universe B)).
{ destruct (Z_lt_ge_dec (d_S cx) (ly_top (c_ly cx) - 16)) as [Htop | Htop].
  - exists [(d_S cx, RA_LLVMF, s0Z (c_regs cx))]. split.
    + apply (achain_chain_pre ly3 _ (d_A cx) (d_S cx)); [| lia | exact Hs0 | rewrite Hra; unfold P_MAL_RA; lia].
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
      apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) _ (d_S cx) (s0Z (c_regs cx)) RA_LLVMF [] (d_A cx)
        Hach0 ltac:(lia) Hrd Hw8 Hw16); first [exact (a3c_mod8 _ GS16) | unfold RA_LLVMF; lia].
    + apply DUNIV. unfold call_trace0, unwind_of_chain. cbn [flat_map app]. rewrite Hra.
      rewrite (proj2 (Z.eqb_neq (BASE + P_MAL_RA) (pc_malloc_ra0 (as_code B))) ltac:(unfold P_MAL_RA; lia)).
      unfold d_sites. destruct (RA_LLVMF =? pc_malloc_ra0 (as_code B)); cbn [app firstn]; a3c_in.
  - exists []. split.
    + apply (achain_chain_pre ly3 _ (d_A cx) (d_S cx)); [| lia | exact Hs0 | rewrite Hra; unfold P_MAL_RA; lia].
      left. split; [right; left; rewrite Etop; lia | reflexivity].
    + apply DUNIV. unfold call_trace0, unwind_of_chain. cbn [flat_map app]. rewrite Hra.
      rewrite (proj2 (Z.eqb_neq (BASE + P_MAL_RA) (pc_malloc_ra0 (as_code B))) ltac:(unfold P_MAL_RA; lia)).
      unfold d_sites. cbn [app firstn]. a3c_in. }
destruct HCH as (ch & Hcp & Htr).
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E (SIGMA AS_malloc - BASE)
  (SLit 0 :: SOff A_TEXT P_MAL_RA :: atom_regs 532 30) (map (getr regs) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (a3c_regs_ok cx E regs P_MAL_RA HEIE R1)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
unfold ss_d in HS1.
replace (BASE + (SIGMA AS_malloc - BASE)) with (pc_wrap_malloc (as_code B))
  by (rewrite (pal_malloc B TL); lia).
unfold cfg_at, w64.
eapply SRr_mono.
{ apply (aj_malloc_at04 (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AMALLOC fq) W regs mem3 LLVMF_STK
    (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k cap
    (d_A cx - d_S cx) (getr regs 1) ch HJ).
  - exact R10.
  - unfold MALLOC_MAX. lia.
  - cbn [fold_right] in Hbb. unfold LIVE_MAX. unfold LIVE_LIB, LIVE_MAX in HBB0. unfold HUNT_SIZE in Hbb. lia.
  - rewrite SpR. lia.
  - exact (a3c_mod16 _ _ GA32 GS16).
  - lia.
  - unfold ASTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold P_MAL_RA; lia | reflexivity].
  - clear - Hk Hnev HEV0 Hi. unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, EV_MAX, MAX_OPS in *. lia.
  - exact Hcp.
  - exact Htr. }
cbv beta. intros W2 c2 HW2 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP & Hres & Hfrs & H4096 & Eab & HK).
assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfrs; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 (k + 1)) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 (k + 1) HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & HAR4 & HFin4 & EFA4 & _).
assert (Hnew : In (res, cap) (ablocks B ly4 S4)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR4 Hnew) as (Hr16 & _ & Hrceil & Hrapp & _ & _ & _).
rewrite Rq in Hrceil, Hrapp.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply K1; [lia | unfold ASTACK; lia]. }
assert (KFR : forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a HFin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - intros Hfp.
    pose proof (sep_block_frame SEGS B LAWS ly4 S4 W2 mem4 md4 res cap DFRAME_CLASS (c_fpos cx) HAR4 Hnew HFin4) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA4, Rq in Hd. rewrite Rq in Hfp.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. lia. }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a HFin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - intros Hfp. rewrite Rq in Hfp.
    apply (fshadow_not_app (d_FB cx) 512 res cap a); [lia | lia | exact Hrapp | | lia].
    unfold shadow_addr, SHADOW_OFF in Ha. lia. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W2) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EF. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KFR. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
    + intros a Ha. apply GFpres4. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KSH. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2d : d_E cx (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply a3c_dE; [apply d_E_env; exact HE | lia]).
assert (HFL2 : ew (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (HSL4 : d_hslots cx h W2 mem4).
{ apply (d_hslots_kept cx h W W2 mem3 mem4); [intros a Ha; apply KA; lia | exact HHS]. }
pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_loop ly4 S4 W2 md4 (k + 1) _ _
  (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + P_MAL_RA)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2d HFL2 HS2 ltac:(vm_compute; reflexivity) HSL4) as (HFRM4 & HSHD4).
pose proof (DBMAL LAWS DROH DCAN cx h n [] dsh_loop dsh_loop ly3 S3 W mem3 md3 k ly4 S4 W2 mem4 md4 (k + 1)
  (d_S cx + (d_A cx - d_S cx) - ASTACK) (d_S cx + (d_A cx - d_S cx)) [(res, cap)]
  HBODY (conj HBASE HJ) (conj HBASE HJ4) ltac:(cbn; lia) ltac:(unfold ASTACK, LLVMF_STK; lia) ltac:(lia) Eab
  ltac:(constructor; [exact (blk_off_imgP B ly4 S4 W2 mem4 md4 res cap HAR4 Hnew) | constructor])
  ltac:(eapply acall_kept_mono_E; [exact HK | intros a Ha; exists res, cap; split; [left; reflexivity | exact Ha]])
  HFRM4 HSHD4) as HBODY4.
cbn [app] in HBODY4.
assert (PR : forall rr : Z, acallee_saved rr -> getr regs4 (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) by exact HP.
assert (P2 : getr regs4 2 = getr regs 2) by exact (PR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs4 3 = getr regs 3) by exact (PR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs4 4 = getr regs 4) by exact (PR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs4 8 = getr regs 8) by exact (PR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs4 9 = getr regs 9) by exact (PR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs4 18 = getr regs 18) by exact (PR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs4 19 = getr regs 19) by exact (PR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs4 20 = getr regs 20) by exact (PR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs4 21 = getr regs 21) by exact (PR 21 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs4 27 = getr regs 27) by exact (PR 27 ltac:(unfold acallee_saved; lia)).
assert (KV : forall off v, 0 <= off <= 360 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W2 mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
exists res. split.
{ destruct HFROM as (Harm & Hwle & HlenT0 & Hex). split; [exact Harm|]. split; [eapply wle_trans; eassumption|].
  split; [exact HlenT0 | exact Hex]. }
unfold a3_st, d_at.
exists fq, ly4, S4, regs4, mem4, md4, (k + 1), acc.
split; [unfold cfg_at, w64; rewrite R1; reflexivity|].
split; [exact Hfrm|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|].
split; [lia|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P19; exact Rs3|]. split; [rewrite P18; exact Rs2|].
  split; [rewrite P20; exact Rs4|]. rewrite P27; exact Rs11. }
split.
{ split; [exact Hres|]. split; [rewrite P21; exact R21|]. rewrite P27; exact R27. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
split.
{ split; [exact H4096|]. split.
  { split; [split; [apply KV; [lia | exact H208] | apply KV; [lia | exact H320]]|].
    split; [apply KV; [lia | exact H192] | apply KV; [lia | exact H200]]. }
  split; [exists rem; split; [exact Hage | exact HAP]|].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact HgT1].
  intros a Ha. rewrite length_map, HlenT1 in Ha. apply KFR. unfold d_obj, dobj_off in Ha. lia. }
split.
{ split; [apply KV; [lia | exact H208] | apply KV; [lia | exact H320]]. }
rewrite Exb. exact HBODY4.
Qed.

Theorem c_tj : c_tj_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf W c (HFROM & HST).
unfold a3_st, d_at in HST.
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R1 & R10 & R11 & R12 & R13 & R21 & R24 & R27) & (Hb4096 & HSP1 & HTAB) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HROD & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H184 & H120 & H136 & H376 & H280 & H232 & H264).
pose proof (d_hslots_of_frame cx h dsh_loop W mem3 HFRM) as HHS.
pose proof HBLK as (HPerm0 & HNot0 & Hbb & HOFFb).
pose proof HTAB as ((rem & Hage & HAP) & HgT1).
pose proof HAP as (HlenT1 & _ & _ & _ & _ & _ & HokT1 & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBASE as ((_ & _ & _ & _ & _ & _ & _ & _ & HEV0 & _) & _).
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr regs) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (HFBm8 : d_FB cx mod 8 = 0).
{ pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)) as D. rewrite GF32 in D.
  replace (d_FB cx) with ((4 * (d_FB cx / 32)) * 8) by lia. apply Z_mod_mult. }
pose proof (a3c_tgeo cx ly3 S3 W mem3 md3 k HCTX HSHD) as (GT8 & GTra).
pose proof (a3c_cap op) as Hcap.
assert (Exb : a3_xb buf op = [(buf, a3_cap op)]).
{ unfold a3_xb, a3_cap in *. rewrite Z.max_l by lia. reflexivity. }
set (cap := a3_cap op) in *.
assert (Rq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
rewrite Exb in HPerm0, HNot0.
assert (Hinbuf : In (buf, cap) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hb16 & Hb4096' & Hbceil & Hbapp & _ & _ & _).
rewrite Rq in Hbceil, Hbapp.
destruct (a3c_achain cx ly3 S3 W mem3 md3 k E dsh_loop HCTX HE HREG) as (ch & Hach).
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E AF_both3_reac_disco_table_json
  (SLit 0 :: SOff A_TEXT P_TJ_RA :: atom_regs 532 30) (map (getr regs) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (a3c_regs_ok cx E regs P_TJ_RA HEIE R1)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
unfold ss_d in HS1.
pose proof (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HROD) as (_ & _ & _ & _ & _ & _ & HDTJ & _).
assert (HAFN : afn_pre SEGS B TJ_STK ly3 S3 W regs mem3 md3 ch).
{ eapply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k regs TJ_STK (d_A cx - d_S cx) ch HJ).
  - rewrite SpR. lia.
  - exact (a3c_mod16 _ _ GA32 GS16).
  - lia.
  - unfold TJ_STK. lia.
  - unfold TJ_STK, LLVMF_STK. lia.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold P_TJ_RA; lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold P_TJ_RA; lia). unfold P_TJ_RA. lia.
  - exact Rgp.
  - exact Rtp.
  - rewrite SpR. replace (s0Z regs) with (d_S cx) by (unfold s0Z; rewrite Rs0; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    exact Hach. }
assert (HFPbuf : forall a, inFP (tj_fp buf cap) a -> buf <= a < buf + cap).
{ intros a (r & Hr & Ha). unfold tj_fp in Hr. destruct (cap <? 3); [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha. lia. }
eapply SRr_mono.
{ apply (TTJ fq ly3 S3 W regs mem3 md3 ch (d_obj cx OT) now buf cap cap T1 HAFN Hfrm).
  - rewrite HFR. cbn. lia.
  - exact HROD.
  - exact HDTJ.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - exact Hnow.
  - lia.
  - split; [|split].
    + exists DFRAME_CLASS, (c_fpos cx). split; [exact HFin3|]. rewrite EFA3.
      change (fs_frame_bytes DFRAME_CLASS) with 4096. unfold d_obj, dobj_off, DFRAME_CLASS.
      split; [lia|]. split; [exact HFBm8|]. lia.
    + exact GT8.
    + exact GTra.
  - exact HgT1.
  - exact HlenT1.
  - exact HokT1.
  - intros _. split; [exact Hinbuf | rewrite Rq; lia].
  - clear - Hk Hnev HEV0 Hi. unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, EV_MAX, MAX_OPS in *. lia. }
cbv beta. intros W2 c2 HW2 Hpost.
unfold tj_postPF, apost_base in Hpost.
destruct Hpost as (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & Hfp4 & Hcsr4 & HJc & HP & HPerm & HC3 & HLT & HGE).
assert (HNotb : ~ In (buf, cap) (ablocks B (c_ly cx) (c_S cx))).
{ inversion HNot0 as [|x l Hx Hl]. inversion Hl as [|y l' Hy _]. exact Hy. }
pose proof (ajournal_sub SEGS B LAWS pa_segs_low LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k TJ_STK (spZ regs) (tj_fp buf cap) [] ly4 S4 W2 mem4 md4 0 HJ HJc
  ltac:(rewrite SpR; unfold LLVMF_STK, TJ_STK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; right; exists buf, cap; split; [exact Hinbuf|]; split; [exact HNotb|];
        rewrite Rq; exact (HFPbuf a Ha))) as HJ4.
cbn [app] in HJ4. rewrite Z.add_0_r in HJ4.
pose proof HJc as (_ & _ & _ & _ & _ & HfrC & _ & _ & KF1 & _ & _ & KF4 & _).
assert (HFR4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HfrC; cbn [app]; exact HFR).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR4)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KF1; [lia | rewrite SpR; lia]. }
assert (KFR : forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (KF4 DFRAME_CLASS (c_fpos cx) a HFin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - intros Hfp. apply HFPbuf in Hfp.
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 buf cap DFRAME_CLASS (c_fpos cx) HAR3 Hinbuf HFin3) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA3, Rq in Hd.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. lia. }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply (KF4 DFRAME_CLASS (c_fpos cx) a HFin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - intros Hfp. apply HFPbuf in Hfp.
    apply (fshadow_not_app (d_FB cx) 512 buf cap a); [lia | lia | exact Hbapp | | lia].
    unfold shadow_addr, SHADOW_OFF in Ha. lia. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W2) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EF. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KFR. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
    + intros a Ha. apply GFpres4. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W2) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KSH. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia. }
specialize (HS2 HQ). clear HQ.
lazymatch type of HS2 with st_ok_pi _ _ ?E2 ?ss2 (mkst ?rg ?pc ?mm ?rom) =>
  pose proof (YL05.st_ok_xfx fq fx' _ _ _ _ _ _ HS2 : st_ok_pi (fx := fx') SEGS VAL E2 ss2 (mkst (fx := fx') rg pc mm rom))
    as HS3 end.
clear HS2. rename HS3 into HS2. rewrite <- restrict_mkst_fx in HS2.
assert (HE2d : d_E cx (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply a3c_dE; [apply d_E_env; exact HE | lia]).
assert (HFL2 : ew (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (HSL4 : d_hslots cx h W2 mem4).
{ apply (d_hslots_kept cx h W W2 mem3 mem4); [intros a Ha; apply KA; lia | exact HHS]. }
pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fx' cx h dsh_loop ly4 S4 W2 md4 k _ _
  (YK11.mkst (fx := fx') regs4 (Z_to_bv 64 (BASE + P_TJ_RA)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2d HFL2 HS2 ltac:(vm_compute; reflexivity) HSL4) as (HFRM4 & HSHD4).
pose proof (DBPC LAWS DROH DCAN cx h n (a3_xb buf op) dsh_loop dsh_loop ly3 S3 W mem3 md3 ly4 S4 W2 mem4 md4 k TJ_STK
  (spZ regs) (tj_fp buf cap) 0 HBODY (conj HBASE HJ4) HJc
  ltac:(rewrite SpR; unfold LLVMF_STK, TJ_STK; lia) ltac:(rewrite SpR; lia)
  ltac:(intros a Ha; left; rewrite Exb; exists buf, cap; split; [left; reflexivity|]; rewrite Rq; exact (HFPbuf a Ha))
  ltac:(intros (a & Ha & Hh); exfalso; apply HFPbuf in Ha;
        pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W mem3 md3 (buf, cap) (h, HUNT_SIZE)
          (ablocks B (c_ly cx) (c_S cx)) HAR3 HPerm0) as Hd;
        unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; rewrite Rq in Hd;
        change (req_size HUNT_SIZE) with 480 in Hd; unfold HUNT_SIZE in Hh; lia)
  HPerm HFRM4 HSHD4) as HBODY4.
assert (PR : forall rr : Z, acallee_saved rr -> getr regs4 (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) by exact HP.
assert (P2 : getr regs4 2 = getr regs 2) by exact (PR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs4 3 = getr regs 3) by exact (PR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs4 4 = getr regs 4) by exact (PR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs4 8 = getr regs 8) by exact (PR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs4 9 = getr regs 9) by exact (PR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs4 18 = getr regs 18) by exact (PR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs4 19 = getr regs 19) by exact (PR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs4 20 = getr regs 20) by exact (PR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs4 21 = getr regs 21) by exact (PR 21 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs4 24 = getr regs 24) by exact (PR 24 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs4 27 = getr regs 27) by exact (PR 27 ltac:(unfold acallee_saved; lia)).
assert (KV : forall off v, 0 <= off <= 360 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W2 mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
assert (HRES : exists r, getr regs4 10 = w64 r /\ a3_jres op T1 now r /\
  (r = a3_r T1 now -> garr8 SEGS (mrestrict (w_H W2) mem4) buf (a3_text T1 now ++ [0]))).
{ unfold a3_jres, a3_r, a3_text. fold cap.
  pose proof (Zle_0_nat (length (reac_disco_table_json_c.tj_text T1 now))) as HL0.
  destruct (Z_lt_le_dec cap 3) as [Hc | Hc].
  - exists (-1). split; [exact (HC3 Hc)|]. split; [left; split; [reflexivity | left; exact Hc]|].
    intros Hr. lia.
  - destruct (Z_lt_le_dec (tj_len T1 now) cap) as [Hl | Hl].
    + destruct (HLT Hc Hl) as (Hr10 & Hg). exists (tj_len T1 now). split; [exact Hr10|].
      unfold tj_len in *. split; [right; split; [reflexivity | split; lia]|]. intros _. exact Hg.
    + exists (-1). split; [exact (HGE Hc Hl)|]. unfold tj_len in Hl.
      split; [left; split; [reflexivity | right; exact Hl]|]. intros Hr. lia. }
destruct HRES as (r & Hr10 & Hjres & Hgarr).
exists r. split.
{ destruct HFROM as (Harm & Hwle & HlenT0 & Hex). split; [exact Harm|]. split; [eapply wle_trans; eassumption|].
  split; [exact HlenT0 | exact Hex]. }
unfold a3_st, d_at.
exists fx', ly4, S4, regs4, mem4, md4, k, acc.
split; [unfold cfg_at, w64; rewrite R1; reflexivity|].
split; [destruct Hcsr4 as [Hc4|Hc4]; [rewrite Hc4; exact Hfrm | exact Hc4]|].
split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR4|].
split; [exact Hk|].
split; [pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P19; exact Rs3|]. split; [rewrite P18; exact Rs2|].
  split; [rewrite P20; exact Rs4|]. rewrite P27; exact Rs11. }
split.
{ split; [exact Hr10|]. split; [rewrite P21; exact R21|]. split; [rewrite P24; exact R24|]. rewrite P27; exact R27. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
split.
{ split; [exact Hb4096|]. split.
  { split; [split; [apply KV; [lia | exact H208] | apply KV; [lia | exact H320]]|].
    split; [apply KV; [lia | exact H192] | apply KV; [lia | exact H200]]. }
  split.
  { split; [exists rem; split; [exact Hage | exact HAP]|].
    apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem4); [|exact HgT1].
    intros a Ha. rewrite length_map, HlenT1 in Ha. apply KFR. unfold d_obj, dobj_off in Ha. lia. }
  split; [exact Hjres | exact Hgarr]. }
split.
{ split; [apply KV; [lia | exact H208] | apply KV; [lia | exact H320]]. }
exact HBODY4.
Qed.

Theorem c_sl : c_sl_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf W c (HFROM & HST).
unfold a3_st, d_at in HST.
destruct HST as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R1 & R10 & R24 & R25 & R26 & R27) & (Hb4096 & HSP1 & HTAB & HBUF) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
pose proof HBODY as (T & G & Lk & HL & HFRM & HSHD & HOBJ & HBLK & HINP & HROD & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H184 & H120 & H136 & H376 & H280 & H232 & H264).
pose proof (d_hslots_of_frame cx h dsh_loop W mem3 HFRM) as HHS.
pose proof HBLK as (HPerm0 & HNot0 & Hbb & HOFFb).
pose proof HTAB as ((rem & Hage & HAP) & HgT1).
pose proof HAP as (HlenT1 & _ & _ & _ & _ & _ & HokT1 & _).
pose proof HBUF as (Hrr & Hgb).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _ & _ & _ & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
assert (SpR : spZ regs = d_A cx) by exact Rsp.
assert (HEIE : img_env VAL A_LIM E) by exact (proj1 (proj2 (proj2 HE))).
assert (HEId : img_env VAL A_LIM (d_env cx E (map (getr regs) (tl all_regs))))
  by (apply img_env_havoc_hi; [exact HEIE | unfold AT_FL, A_LIM; lia]).
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
pose proof (a3c_cap op) as Hcap.
assert (Exb : a3_xb buf op = [(buf, a3_cap op)]).
{ unfold a3_xb, a3_cap in *. rewrite Z.max_l by lia. reflexivity. }
assert (Hrcap : a3_r T1 now < a3_cap op) by (unfold a3_cap; lia).
set (cap := a3_cap op) in *.
assert (Rq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
rewrite Exb in HPerm0.
assert (Hinbuf : In (buf, cap) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hb16 & Hb4096' & Hbceil & Hbapp & _ & _ & _).
rewrite Rq in Hbceil, Hbapp.
pose proof (slot_ser_pure.ser_text_g33 _ _ now slot_ser_pure.ser_tok_ok
  (proj2 (slot_ser_pure.ser_tj_ok T1 HlenT1 HokT1)) Hnow) as Hg33.
change (Forall (fun c => 33 <= c <= 255) (a3_text T1 now)) in Hg33.
assert (Hlen1 : (length (a3_text T1 now ++ [0%Z]) = S (length (a3_text T1 now)))%nat) by (rewrite length_app; cbn; lia).
assert (Haview : forall j, (j < length (a3_text T1 now ++ [0%Z]))%nat ->
  aview SEGS (w_H W) mem3 (buf + Z.of_nat j) = Some (nth j (a3_text T1 now ++ [0]) 0))
  by (intros j Hj; exact (a3c_garr8_aview (w_H W) mem3 buf _ j Hgb Hj)).
assert (Er : a3_r T1 now = Z.of_nat (length (a3_text T1 now))) by reflexivity.
set (r := a3_r T1 now) in *.
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E (SIGMA AS___interceptor_trampoline_strlen - BASE)
  (SLit 0 :: SOff A_TEXT P_SL_RA :: atom_regs 532 30) (map (getr regs) (tl all_regs)) [] [] [] (d_facts [] [])
  HCTX HE HREG HFLAG (a3c_regs_ok cx E regs P_SL_RA HEIE R1)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (map (getr regs) (tl all_regs)) [] [] HCTX HE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS1.
unfold ss_d in HS1.
replace (BASE + (SIGMA AS___interceptor_trampoline_strlen - BASE)) with (SIGMA AS___interceptor_trampoline_strlen) by lia.
unfold cfg_at, w64.
assert (HMC : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem3).
{ intros a Ha. exact (HROD a (de_mc_ro a Ha) (proj1 (de_mc_un a Ha)) (proj2 (de_mc_un a Ha))). }
eapply SRr_mono.
{ apply (a3c_strlen_at fq MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen) (ASTRLEN fq) W regs mem3
    LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k
    buf r (d_A cx - d_S cx) (getr regs 1) HJ).
  - exact R10.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite SpR. lia.
  - exact (a3c_mod16 _ _ GA32 GS16).
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold P_SL_RA; lia | reflexivity].
  - split; [lia|]. split.
    + intros j Hj. exists (nth (Z.to_nat j) (a3_text T1 now ++ [0]) 0). split.
      * replace (buf + j) with (buf + Z.of_nat (Z.to_nat j)) by lia. apply Haview. rewrite Hlen1. lia.
      * rewrite app_nth1 by lia.
        assert (Hjl : (Z.to_nat j < length (a3_text T1 now))%nat) by lia.
        pose proof (proj1 (Forall_forall _ _) Hg33 _ (nth_In (a3_text T1 now) 0 Hjl)) as Hb.
        intros E0. rewrite E0 in Hb. lia.
    + intros _. replace (buf + r) with (buf + Z.of_nat (length (a3_text T1 now))) by lia.
      rewrite Haview by (rewrite Hlen1; lia). rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - intros a Ha. split.
    + replace a with (buf + Z.of_nat (Z.to_nat (a - buf))) by lia. rewrite Haview by (rewrite Hlen1; lia). discriminate.
    + rewrite SpR. unfold ESTACK. lia.
  - apply (amem_range_of_block SEGS B LAWS ly3 S3 W mem3 md3 buf cap buf (r + 1) HAR3 Hinbuf); rewrite ?Rq; lia.
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W mem3 md3 buf cap buf (r + 1) HAR3 Hinbuf); rewrite ?Rq; lia.
  - apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W mem3 md3 buf cap buf (r + 1) HAR3 Hinbuf); rewrite ?Rq; lia.
  - intros a Ha. apply (a3c_blk_vis8 B LAWS ly3 S3 W mem3 md3 buf cap a HAR3 Hinbuf). rewrite Rq. lia.
  - exact HMC. }
cbv beta. intros W2 c2 HW2 (-> & regs4 & mem4 & md4 & -> & HJ4 & HP & Hres & Hfr & Hpres).
assert (HCTX4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem4 md4 k) by exact (conj HBASE (conj HJ4 HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem4 md4 k HCTX4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres4 & GFsh4 & GSTK4 & _ & _ & _ & _).
assert (KL : forall a, 0 <= a < d_A cx - ESTACK -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. unfold ESTACK in *. apply Hfr; [lia | lia]. }
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply Hfr; [lia | unfold ESTACK; lia]. }
assert (KFR : forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KL. unfold ESTACK. lia. }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KL. unfold shadow_addr, SHADOW_OFF, ESTACK in *. lia. }
assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
assert (EA : ew E 60 = w64 (d_A cx)) by exact (proj1 (proj2 (proj2 (proj2 HE)))).
assert (EF : ew E 516 = w64 (d_FB cx)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HE))))).
assert (ESH : ew E 529 = w64 (shadow_addr (d_FB cx))) by exact (proj2 (proj2 (proj2 (proj2 (proj2 HE))))).
jafter_call_keep_hi HS1 562%nat regs4 (mrestrict (w_H W) mem4) HP [0;1;2;3]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (a3c_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_S cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). exact ES2.
    + intros a Ha. apply KA. lia.
    + intros a Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_A cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EA. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KA. lia.
    + intros a Ha. apply GSTK4. unfold LLVMF_STK. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W) mem3 mem4 _ (d_FB cx)).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite EF. unfold w64. apply unsigned_lit_small. lia.
    + intros a Ha. apply KFR. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
    + intros a Ha. apply GFpres4. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
  - eapply (a3c_kept _ (w_H W) (w_H W) mem3 mem4 _ (shadow_addr (d_FB cx))).
    + rewrite d_env_old by (unfold AT_FL; lia). rewrite ESH. unfold w64. apply unsigned_lit_small.
      unfold shadow_addr, SHADOW_OFF. lia.
    + intros a Ha. apply KSH. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia.
    + intros a Ha. replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia.
      apply GFsh4. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2.
assert (HE2d : d_E cx (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)))
  by (apply a3c_dE; [apply d_E_env; exact HE | lia]).
assert (HFL2 : ew (havoc (d_env cx E (map (getr regs) (tl all_regs))) 562 (map (getr regs4) CLOB)) AT_FL =
  Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite ew_havoc_old by (unfold AT_FL; lia); apply d_env_fl).
assert (HSL4 : d_hslots cx h W mem4).
{ apply (d_hslots_kept cx h W W mem3 mem4); [intros a Ha; apply KA; lia | exact HHS]. }
pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_loop ly3 S3 W md4 k _ _
  (YK11.mkst (fx := fq) regs4 (Z_to_bv 64 (BASE + P_SL_RA)) mem4 (YK11.seg_rom SEGS))
  HCTX4 HE2d HFL2 HS2 ltac:(vm_compute; reflexivity) HSL4) as (HFRM4 & HSHD4).
pose proof (DBRT cx h n n (a3_xb buf op) dsh_loop dsh_loop ly3 S3 W mem3 mem4
  (d_S cx + (d_A cx - d_S cx) - ESTACK) (d_S cx + (d_A cx - d_S cx))
  (fun a => d_S cx + (d_A cx - d_S cx) - ESTACK <= a < d_S cx + (d_A cx - d_S cx))
  HBODY ltac:(unfold ESTACK, LLVMF_STK; lia) ltac:(lia) ltac:(intros a Ha; left; exact Ha) Hfr
  ltac:(intros a _ Hp; exact (Hpres a Hp)) HFRM4 HSHD4 ltac:(lia)) as HBODY4.
assert (PR : forall rr : Z, acallee_saved rr -> getr regs4 (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) by exact HP.
assert (P2 : getr regs4 2 = getr regs 2) by exact (PR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs4 3 = getr regs 3) by exact (PR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs4 4 = getr regs 4) by exact (PR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs4 8 = getr regs 8) by exact (PR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs4 9 = getr regs 9) by exact (PR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs4 18 = getr regs 18) by exact (PR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs4 19 = getr regs 19) by exact (PR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs4 20 = getr regs 20) by exact (PR 20 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs4 24 = getr regs 24) by exact (PR 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs4 25 = getr regs 25) by exact (PR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs4 26 = getr regs 26) by exact (PR 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs4 27 = getr regs 27) by exact (PR 27 ltac:(unfold acallee_saved; lia)).
assert (KV : forall off v, 0 <= off <= 360 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W mem4) (d_A cx + off) 8 v).
{ intros off v Hoff Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply KA. lia. }
split; [exact HFROM|].
unfold a3_st, d_at.
exists fq, ly3, S3, regs4, mem4, md4, k, acc.
split; [unfold cfg_at, w64; rewrite R1; reflexivity|].
split; [exact Hfrm|]. split; [exact HBASE|]. split; [exact HJ4|]. split; [exact HFR|].
split; [exact Hk|]. split; [exact Hnev|].
split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact Rsp|].
  split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|]. split; [rewrite P8; exact Rs0|].
  split; [rewrite P9; exact Rs1|]. split; [rewrite P19; exact Rs3|]. split; [rewrite P18; exact Rs2|].
  split; [rewrite P20; exact Rs4|]. rewrite P27; exact Rs11. }
split.
{ split; [exact Hres|]. split; [rewrite P24; exact R24|]. split; [rewrite P25; exact R25|].
  split; [rewrite P26; exact R26|]. rewrite P27; exact R27. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
split.
{ split; [exact Hb4096|]. split.
  { split; [split; [apply KV; [lia | exact H208] | apply KV; [lia | exact H320]]|].
    split; [apply KV; [lia | exact H192] | apply KV; [lia | exact H200]]. }
  split.
  { split; [exists rem; split; [exact Hage | exact HAP]|].
    apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact HgT1].
    intros a Ha. rewrite length_map, HlenT1 in Ha. apply KFR. unfold d_obj, dobj_off in Ha. lia. }
  split; [exact Hrr|].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem4); [|exact Hgb].
  intros a Ha. rewrite Hlen1 in Ha. apply KL. unfold ESTACK. lia. }
split.
{ split; [apply KV; [lia | exact H208] | apply KV; [lia | exact H320]]. }
exact HBODY4.
Qed.

End h.
End f.
End d.
