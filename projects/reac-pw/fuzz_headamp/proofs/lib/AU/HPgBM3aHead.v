(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v, with its module paths, module names and numbers changed; 614 of its 699 lines of code are new or changed and 929 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the head of the checking
   segment M03 of LLVMFuzzerTestOneInput, lib/AU/HPgSegM.v hqu_piece_M3a_head_stmt (C5 0x82f38 to X 0x82fdc and
   FIRST 0x838e4). Proves function LLVMFuzzerTestOneInput (this piece of its walk).

   lib/AU/HPgBM3aHeadK.v walks C5 to the parse's return 0x82f94 (blocks A, B, C) and ends in the state mb_mid.
   This file walks the rest:
     block D  0x82f94 .. check_no_overrun's return 0x82fa8: `not a1,s6; bltu a1,s2` to `unimp` 0x83a14 is not taken
              (the run assumes the condition `not out >=u 3 cap`, true because out + 3 cap < 2 ^ 64: HPgSegM's
              hqu_t_ptr family); s9 = rc; a0 = out + 3 cap; check_no_overrun (0x83e7c, CK_NO);
     block E  0x82fa8 .. check_count's return 0x82fb8 (0x83f2c, CK_COUNT);
     block F  0x82fb8 .. check_cells_valid's return 0x82fc4 (0x83fcc, CK_CV);
     block G  0x82fc4 .. X 0x82fdc / FIRST 0x838e4: the instrumented 4-byte check of pp->corrupt (its slow block
              0x83a3c not taken: the pp block's shadow is 0) and `bnez` on the word (Pod/Layout.v pp_read_corrupt).
   Each check runs at the parse's float state (the check texts keep it), and the two cuts are rebuilt from mb_mid:
   HPgSegM.hqu_base3 (the segment's journal and kept clause with hqu_E3, hqu_fxk from the parse's hd_fxk [14; 15],
   the frame's shadow hi_shB, rom_view through ERRNO_RW, the pp and pod blocks, the parse's cells and res, errno
   readable) and the cut lists. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09 YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgMem HPgSteps HPgIntrinU HPgSiteB HPgBM3aHeadK.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* `not rd,rs`: the one's complement of a 64-bit value *)
Lemma mb_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
pose proof (Z.sub_lxor_2rlandn (2 ^ 64 - 1) x) as H.
assert (Z.land (Z.lnot (2 ^ 64 - 1)) x = 0).
{ replace (Z.lnot (2 ^ 64 - 1)) with (- (2 ^ 64)) by reflexivity.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_dec n 64).
  - replace (- (2 ^ 64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
    destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Z.lxor_comm. lia.
Qed.
Lemma mb_U_not : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu, U_SLit, (U_atom E n v Hn Hv). cbn [zalu_raw].
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite mb_lxor_ones by lia. apply zcanon_id. unfold M64. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a run with no region left every byte as it was *)
Lemma mb_frame_nil : forall E (H : word -> bool) (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E H m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & _). destruct Hin.
Qed.
(* a run whose regions write nothing left every byte as it was *)
Lemma mb_frame_ro : forall E c (H : word -> bool) (m m' : word -> option byte),
frame_of E [YP09.mkRegion (Some 24%nat) 0 4 0 0 c] (mrestrict H m) (mrestrict H m') ->
forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E c H m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]]. cbn in Hr. lia.
Qed.

Section s.
Variable B : asyms.
Variable MT : ameter_ops.
(* =================== Section hypotheses =================== *)
(* the runtime's __asan_memset at any float state (YG0d's AsanAPI field aa_asan_memset) *)
Hypothesis AMEMSET : forall fx' : YK11.FPState, aintrin_realizes (fx := fx') rsegs B OSet B_ASAN_MEMSET.
(* the meter's laws *)
Hypothesis MTL : ameter_laws MT.
(* the parse's contract at image B's entry, literals, stack-guard cells and doubles, at the extra read-only range
   0 .. 0 (the one instance the walk applies) *)
Hypothesis PARSE : hd_parse_result_specX rsegs B MT 0x849ac 0 0 0x214a0 0x214c0 0x214e0 0x21500
  0x9d478 0x5f8210 headamp_B_dcs.
(* the three check texts at image B's entries, at any float state *)
Hypothesis CK_NO : forall fx' : YK11.FPState, hd_check_no_overrun_specX (fx := fx') rsegs B MT 0x83e7c.
Hypothesis CK_COUNT : forall fx' : YK11.FPState, hd_check_count_specX (fx := fx') rsegs B MT 0x83f2c.
Hypothesis CK_CV : forall fx' : YK11.FPState, hd_check_cells_valid_specX (fx := fx') rsegs B MT 0x83fcc.
(* the errno cell lies in the image (YCbq.v api_env), and in no read-only segment *)
Hypothesis ERRNO : api_env rsegs B.
Hypothesis ERRNO_RW : forall a, as_errno B <= a < as_errno B + 4 -> ~ in_rom rsegs a.

(* hc_core after a run that kept sp, gp and tp and the journal *)
Lemma mb_core_run : forall STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R mem3 md3 (regs3 : bvmap 5 word),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem3 md3 k ->
getr regs3 (2%bv : bv 5) = getr regs2 (2%bv : bv 5) -> getr regs3 (3%bv : bv 5) = getr regs2 (3%bv : bv 5) ->
getr regs3 (4%bv : bv 5) = getr regs2 (4%bv : bv 5) ->
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem3 md3 regs3 R.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R mem3 md3 regs3
  (HJ & Hev & H2 & H3 & H4 & Hal & Hwin & HRs) HJ3 E2 E3 E4.
split; [exact HJ3|]. split; [exact Hev|]. split; [rewrite E2; exact H2|]. split; [rewrite E3; exact H3|].
split; [rewrite E4; exact H4|]. split; [exact Hal|]. split; [exact Hwin | exact HRs].
Qed.

(* the state mb_mid survives a step that keeps the callee-saved registers but s9 and every byte outside the
   check functions' stack [R - T_check_STK, R) *)
Lemma mb_mid_kept : forall cx r ev v9 v9' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
@mb_f fx rc SK B cx r ev -> mb_mid B MT cx r v9 ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  (x_k cx) ly3 S3 W3 mem3 md3 regs3 (e_R (x_e cx)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 ->
mo_le MT S2 S3 0 ->
(forall n, In n [8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27] -> getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
getr regs3 (Z_to_bv 5 25) = w64 v9' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_check_STK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
mb_mid B MT cx r v9' ly3 S3 W3 regs3 mem3 md3.
Proof using MTL ERRNO.
intros cx r ev v9 v9' ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HC HM HC3 Hfr Hperm Hio Hmo Hrg H25 K.
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (@mb_seps fx rc SK B cx r ev ERRNO HC) as (Z1 & Z2 & Z3 & Z4 & NIo & NIp & NIq & NIf & Ee0 & Ee4 & Eimg).
pose proof (f_cap B cx r ev HC) as Hcap.
destruct HM as (HC2 & Hfr2 & Hperm2 & Hio2 & Hmo2 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 &
  R27 & KF & H140 & H150 & H158 & Hfsh & Hg & Ho & Hres & Hev).
unfold T_check_STK in K. unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. unfold kLowMemEnd in Ee4.
assert (Hfq : 0 <= e_F (x_e cx) / 8) by (apply Z.div_pos; lia).
assert (F8 : e_F (x_e cx) = 8 * (e_F (x_e cx) / 8)).
{ pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)) as D.
  assert (e_F (x_e cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide (e_F (x_e cx)) 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
pose proof (mb_cells_le (hd_props (e_null (x_e cx)) (Model.buf r)) (e_cap (x_e cx)) Hcap) as Hlc.
split; [exact HC3|]. split; [rewrite Hfr; exact Hfr2|]. split; [exact (Permutation_trans Hperm Hperm2)|].
split; [exact (same_io_trans _ _ _ Hio2 Hio)|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo2 Hmo)|].
split; [rewrite (Hrg 8) by (cbn [In]; tauto); exact R8|].
split; [rewrite (Hrg 9) by (cbn [In]; tauto); exact R9|].
split; [rewrite (Hrg 18) by (cbn [In]; tauto); exact R18|].
split; [rewrite (Hrg 19) by (cbn [In]; tauto); exact R19|].
split; [rewrite (Hrg 20) by (cbn [In]; tauto); exact R20|].
split; [rewrite (Hrg 21) by (cbn [In]; tauto); exact R21|].
split; [rewrite (Hrg 22) by (cbn [In]; tauto); exact R22|].
split; [rewrite (Hrg 23) by (cbn [In]; tauto); exact R23|].
split; [rewrite (Hrg 24) by (cbn [In]; tauto); exact R24|].
split; [exact H25|].
split; [rewrite (Hrg 26) by (cbn [In]; tauto); exact R26|].
split; [rewrite (Hrg 27) by (cbn [In]; tauto); exact R27|].
split.
{ intros a Ha Hs Hz. rewrite K by (unfold T_SEG_STK, ASTACK in Hs; lia). exact (KF a Ha Hs Hz). }
split; [eapply (hd_val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3); [|exact H140]; intros i Hi; apply K; lia|].
split; [eapply (hd_val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3); [|exact H150]; intros i Hi; apply K; lia|].
split; [eapply (hd_val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3); [|exact H158]; intros i Hi; apply K; lia|].
split.
{ apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 (e_F (x_e cx)) headamp_B_shB Hfsh).
  intros i Hi. change (length headamp_B_shB) with 116%nat in Hi. change (Z.of_nat 116) with 116 in Hi.
  apply K; unfold shadow_addr, SHADOW_OFF; lia. }
split.
{ apply (hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3); [|exact Hg].
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map, repeat_length in Hj. apply K; lia. }
split.
{ apply (hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3); [|exact Ho].
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map, length_ha_cells_bytes in Hj. unfold mb_ans in Hj.
  apply K; lia. }
split.
{ apply (hd_garr8_kept rsegs (w_H W2) (w_H W3) mem2 mem3); [|exact Hres].
  intros j Hj. unfold hd_zbytes, ans_res_bytes in Hj. rewrite length_map, length_ha_res_bytes in Hj. apply K; lia. }
destruct Hev as [ev' Hev]. exists ev'. intros kk Hkk. rewrite K by lia. exact (Hev kk Hkk).
Qed.

(* the pieces of mb_mid a check's premises read, at a state equal to it in memory *)
Ltac mb_mid_parts HM :=
  destruct HM as (HC2 & Hfr2 & Hperm2 & Hio2 & Hmo2 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 &
    R27 & KF & H140 & H150 & H158 & Hfsh & Hg & Ho & Hres & Hev).

(* ===================== block D: 0x82f94 .. check_no_overrun's return 0x82fa8 ===================== *)
Definition mb_condD : acond := mkAC BC_GEU (SAlu ALU_XOR (SOff 22 0) (SLit (-1))) (SOff 18 0).

Lemma mb_D : forall cx r ev (Q : world rsegs -> config -> Prop), @mb_f fx rc SK B cx r ev ->
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
mb_mid B MT cx r (e_pod (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 (Z_to_bv 5 10) = w64 (e_rc (x_e cx)) ->
(forall ly3 S3 W3 regs3 mem3 md3, mb_mid B MT cx r (e_rc (x_e cx)) ly3 S3 W3 regs3 mem3 md3 ->
 SRr rsegs W3 (@cfg_at fx2 rsegs MB_D1 regs3 mem3 md3) Q) ->
SRr rsegs W2 (@cfg_at fx2 rsegs MB_C1 regs2 mem2 md2) Q.
Proof using MTL ERRNO CK_NO.
intros cx r ev Q HC fx2 ly2 S2 W2 regs2 mem2 md2 HM H10 K.
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (f_cap B cx r ev HC) as Hcap. pose proof (f_outf B cx r ev HC) as (_ & Hoin & _).
pose proof HM as HM0. mb_mid_parts HM.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HC2 as (HJ & _).
assert (E22 : ew (Ereg regs2 []) 22 = Z_to_bv 64 (e_out (x_e cx)))
  by (rewrite (ew_Ereg_nat regs2 _ 22 (Z_to_bv 5 22) eq_refl); exact R22).
assert (E18 : ew (Ereg regs2 []) 18 = Z_to_bv 64 (3 * e_cap (x_e cx)))
  by (rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl); exact R18).
assert (HS : @st_ok rsegs fx2 (Ereg regs2 []) (mkSS 0x82f94 sr_atoms [] None (mkFacts [] [mb_condD] []))
  (restrict (w_H W2) (@mkst fx2 regs2 (Z_to_bv 64 0x82f94) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [exact I|]. split; [|exact I]. split; [|exact I].
    unfold acond_ok, mb_condD. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
    rewrite (mb_U_not _ 22 (e_out (x_e cx)) E22 ltac:(lia)), (U_atom _ 18 (3 * e_cap (x_e cx)) E18 ltac:(lia)).
    apply negb_true_iff, Z.ltb_ge. lia. }
unfold cfg_at, MB_C1. change (w64 0x82f94) with (Z_to_bv 64 0x82f94).
aj_run_to mb_tbl_ok HS HJ 0x83e7c.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs2 []) (Ereg regs2 [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Rd1.
assert (Rd10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (e_out (x_e cx) + 3 * e_cap (x_e cx))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 10)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 10)) with v end.
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
  rewrite (U_atom _ 18 _ E18 ltac:(lia)), (U_atom _ 22 _ E22 ltac:(lia)), zcanon_id by (unfold M64; lia).
  unfold w64. f_equal. lia. }
assert (Rd25 : getr (ms_regs ms) (Z_to_bv 5 25) = getr regs2 (Z_to_bv 5 10))
  by (eapply (mb_reg_is _ _ _ ms (w_H W2) regs2 [] _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W2) regs2 [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
pose proof (mb_frame_nil _ _ _ _ HFr) as KD.
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
set (md2' := with_vm_backing (m_vm_lazy md2) mat md2) in *.
assert (HCD : hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_k cx) ly2 S2 W2 (ms_mem ms) md2' (ms_regs ms) (e_R (x_e cx))).
{ apply (mb_core_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC2 HJ);
  [ rewrite <- !(mb_getr_z _ 2 2 eq_refl) | rewrite <- !(mb_getr_z _ 3 3 eq_refl) | rewrite <- !(mb_getr_z _ 4 4 eq_refl)];
  apply Rk; cbn [In]; tauto. }
assert (HinD : In (e_out (x_e cx), 3 * (e_cap (x_e cx) + 1)) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) Hoin).
eapply (@hc_call_ck fx2 rc SK rsegs B MT 0x83e7c MB_D1 Q _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) md2'
  (ms_regs ms) (e_R (x_e cx)) HCD).
- rewrite <- (mb_getr_z (ms_regs ms) 1 1 eq_refl). exact Rd1.
- unfold MB_D1. lia.
- reflexivity.
- intros HP.
  pose proof (headamp_A_site_block rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HinD)
    as (_ & _ & _ & _ & _ & Hra).
  assert (Hrq : req_size (3 * (e_cap (x_e cx) + 1)) = 3 * (e_cap (x_e cx) + 1))
    by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap (x_e cx) + 1)) 0); lia).
  rewrite Hrq in Hra.
  apply (CK_NO fx2 _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) md2' _ (ms_regs ms)
    (e_out (x_e cx) + 3 * e_cap (x_e cx)) HP).
  + rewrite <- (mb_getr_z (ms_regs ms) 10 10 eq_refl). exact Rd10.
  + apply (hd_garr8_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem ms)); [intros j _; apply KD | exact Hg].
  + apply (proj1 (Hra (e_out (x_e cx) + 3 * e_cap (x_e cx)) 3 ltac:(lia) ltac:(lia))).
  + apply (proj2 (Hra (e_out (x_e cx) + 3 * e_cap (x_e cx)) 3 ltac:(lia) ltac:(lia))).
  + apply (headamp_A_site_block_app rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HinD);
      [lia | lia | rewrite Hrq; lia].
- intros W3 ly3 S3 regs3 mem3 md3 Hle HC3 Hpres Hfr3 Hperm3 Hio3 Hmo3 Hkeep3.
  apply (K ly3 S3 W3 regs3 mem3 md3).
  apply (mb_mid_kept cx r ev (e_pod (x_e cx)) (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    HC HM0 HC3 Hfr3 Hperm3).
  + eapply same_io_trans; [apply same_io_wvb | exact Hio3].
  + exact Hmo3.
  + intros n Hn. rewrite (Hpres n) by (unfold acallee_saved; cbn [In] in Hn; lia).
    apply Rk. cbn [In] in Hn |- *. tauto.
  + rewrite (Hpres 25) by (unfold acallee_saved; lia). rewrite Rd25. exact H10.
  + intros a Ha Hs. rewrite (Hkeep3 a Ha Hs). apply KD.
Qed.

(* the frame for locals at a state of the journal: the position the start names *)
Lemma mb_F_at : forall cx r ev ly2 S2 W2 mem2 md2, @mb_f fx rc SK B cx r ev ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
  ly2 S2 W2 mem2 md2 (x_k cx) ->
e_F (x_e cx) = frame_addr ly2 (hi_cid headamp_himg_B) (x_pos cx).
Proof.
intros cx r ev ly2 S2 W2 mem2 md2 HC HJ2. rewrite (f_F B cx r ev HC).
rewrite (hc_frame_addr_j rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (f_J B cx r ev HC)).
rewrite (hc_frame_addr_j rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2). reflexivity.
Qed.

(* ===================== block E: 0x82fa8 .. check_count's return 0x82fb8 ===================== *)
Lemma mb_E : forall cx r ev (Q : world rsegs -> config -> Prop), @mb_f fx rc SK B cx r ev ->
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
mb_mid B MT cx r (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ->
(forall ly3 S3 W3 regs3 mem3 md3, mb_mid B MT cx r (e_rc (x_e cx)) ly3 S3 W3 regs3 mem3 md3 ->
 SRr rsegs W3 (@cfg_at fx2 rsegs MB_E1 regs3 mem3 md3) Q) ->
SRr rsegs W2 (@cfg_at fx2 rsegs MB_D1 regs2 mem2 md2) Q.
Proof using MTL ERRNO CK_COUNT.
intros cx r ev Q HC fx2 ly2 S2 W2 regs2 mem2 md2 HM K.
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (f_cap B cx r ev HC) as Hcap. pose proof (f_outf B cx r ev HC) as (_ & Hoin & _).
pose proof HM as HM0. mb_mid_parts HM.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HC2 as (HJ & _).
assert (HS : @st_ok rsegs fx2 (Ereg regs2 []) (mkSS 0x82fa8 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@mkst fx2 regs2 (Z_to_bv 64 0x82fa8) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [exact I|]. split; exact I. }
unfold cfg_at, MB_D1. change (w64 0x82fa8) with (Z_to_bv 64 0x82fa8).
aj_run_to mb_tbl_ok HS HJ 0x83f2c.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs2 []) (Ereg regs2 [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Re1.
assert (Re10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs2 (Z_to_bv 5 25))
  by (eapply (mb_reg_is _ _ _ ms (w_H W2) regs2 [] _ _ 25 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Re11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr regs2 (Z_to_bv 5 20))
  by (eapply (mb_reg_is _ _ _ ms (w_H W2) regs2 [] _ _ 20 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Re12 : getr (ms_regs ms) (Z_to_bv 5 12) = getr regs2 (Z_to_bv 5 26))
  by (eapply (mb_reg_is _ _ _ ms (w_H W2) regs2 [] _ _ 26 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W2) regs2 [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
pose proof (mb_frame_nil _ _ _ _ HFr) as KD.
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
set (md2' := with_vm_backing (m_vm_lazy md2) mat md2) in *.
assert (HCD : hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_k cx) ly2 S2 W2 (ms_mem ms) md2' (ms_regs ms) (e_R (x_e cx))).
{ apply (mb_core_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC2 HJ);
  [ rewrite <- !(mb_getr_z _ 2 2 eq_refl) | rewrite <- !(mb_getr_z _ 3 3 eq_refl) | rewrite <- !(mb_getr_z _ 4 4 eq_refl)];
  apply Rk; cbn [In]; tauto. }
eapply (@hc_call_ck fx2 rc SK rsegs B MT 0x83f2c MB_E1 Q _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) md2'
  (ms_regs ms) (e_R (x_e cx)) HCD).
- rewrite <- (mb_getr_z (ms_regs ms) 1 1 eq_refl). exact Re1.
- unfold MB_E1. lia.
- reflexivity.
- intros HP.
  assert (HFa : e_F (x_e cx) = frame_addr ly2 (hi_cid headamp_himg_B) (x_pos cx))
    by exact (mb_F_at cx r ev ly2 S2 W2 (ms_mem ms) md2' HC HJ).
  assert (Hsh : hd_fsh rsegs (w_H W2) (ms_mem ms) (e_F (x_e cx)) (hi_shB headamp_himg_B))
    by (apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ Hfsh); intros i _; apply KD).
  assert (Hrs : garr8 rsegs (mrestrict (w_H W2) (ms_mem ms)) (e_F (x_e cx) + 672) (hd_zbytes (ans_res_bytes (mb_ans cx r))))
    by (apply (hd_garr8_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem ms)); [intros j _; apply KD | exact Hres]).
  destruct (headamp_B_site_count rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x_e cx) (x_pos cx) r (mb_ans cx r)
    HP (f_own B cx r ev HC) HFa Hsh (f_wf B cx r ev HC) Hcap eq_refl Hrs) as (Hr1 & Hr2 & Hr3).
  apply (CK_COUNT fx2 _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) md2' _ (ms_regs ms) (ans_rc (mb_ans cx r))
    (e_cap (x_e cx)) (ans_keys (mb_ans cx r)) (e_F (x_e cx) + 672) HP).
  + rewrite <- (mb_getr_z (ms_regs ms) 10 10 eq_refl), Re10, R25, (f_rc B cx r ev HC). reflexivity.
  + rewrite <- (mb_getr_z (ms_regs ms) 11 11 eq_refl), Re11. exact R20.
  + rewrite <- (mb_getr_z (ms_regs ms) 12 12 eq_refl), Re12. exact R26.
  + exact Hr1.
  + exact Hr2.
  + exact Hr3.
- intros W3 ly3 S3 regs3 mem3 md3 Hle HC3 Hpres Hfr3 Hperm3 Hio3 Hmo3 Hkeep3.
  apply (K ly3 S3 W3 regs3 mem3 md3).
  apply (mb_mid_kept cx r ev (e_rc (x_e cx)) (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    HC HM0 HC3 Hfr3 Hperm3).
  + eapply same_io_trans; [apply same_io_wvb | exact Hio3].
  + exact Hmo3.
  + intros n Hn. rewrite (Hpres n) by (unfold acallee_saved; cbn [In] in Hn; lia).
    apply Rk. cbn [In] in Hn |- *. tauto.
  + rewrite (Hpres 25) by (unfold acallee_saved; lia). rewrite Rk by (cbn [In]; tauto). exact R25.
  + intros a Ha Hs. rewrite (Hkeep3 a Ha Hs). apply KD.
Qed.

(* ===================== block F: 0x82fb8 .. check_cells_valid's return 0x82fc4 ===================== *)
Lemma mb_F : forall cx r ev (Q : world rsegs -> config -> Prop), @mb_f fx rc SK B cx r ev ->
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
mb_mid B MT cx r (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ->
(forall ly3 S3 W3 regs3 mem3 md3, mb_mid B MT cx r (e_rc (x_e cx)) ly3 S3 W3 regs3 mem3 md3 ->
 SRr rsegs W3 (@cfg_at fx2 rsegs MB_F1 regs3 mem3 md3) Q) ->
SRr rsegs W2 (@cfg_at fx2 rsegs MB_E1 regs2 mem2 md2) Q.
Proof using MTL ERRNO CK_CV.
intros cx r ev Q HC fx2 ly2 S2 W2 regs2 mem2 md2 HM K.
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (f_cap B cx r ev HC) as Hcap. pose proof (f_outf B cx r ev HC) as (_ & Hoin & _).
pose proof HM as HM0. mb_mid_parts HM.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HC2 as (HJ & _).
assert (HS : @st_ok rsegs fx2 (Ereg regs2 []) (mkSS 0x82fb8 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@mkst fx2 regs2 (Z_to_bv 64 0x82fb8) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (@entry_st_ok_full fx2 rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [exact I|]. split; exact I. }
unfold cfg_at, MB_E1. change (w64 0x82fb8) with (Z_to_bv 64 0x82fb8).
aj_run_to mb_tbl_ok HS HJ 0x83fcc.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs2 []) (Ereg regs2 [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Rf1.
assert (Rf10 : getr (ms_regs ms) (Z_to_bv 5 10) = getr regs2 (Z_to_bv 5 22))
  by (eapply (mb_reg_is _ _ _ ms (w_H W2) regs2 [] _ _ 22 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rf11 : getr (ms_regs ms) (Z_to_bv 5 11) = getr regs2 (Z_to_bv 5 25))
  by (eapply (mb_reg_is _ _ _ ms (w_H W2) regs2 [] _ _ 25 HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W2) regs2 [] (Z_to_bv 5 r0) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
pose proof (mb_frame_nil _ _ _ _ HFr) as KD.
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
set (md2' := with_vm_backing (m_vm_lazy md2) mat md2) in *.
assert (HCD : hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_k cx) ly2 S2 W2 (ms_mem ms) md2' (ms_regs ms) (e_R (x_e cx))).
{ apply (mb_core_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC2 HJ);
  [ rewrite <- !(mb_getr_z _ 2 2 eq_refl) | rewrite <- !(mb_getr_z _ 3 3 eq_refl) | rewrite <- !(mb_getr_z _ 4 4 eq_refl)];
  apply Rk; cbn [In]; tauto. }
assert (HinD : In (e_out (x_e cx), 3 * (e_cap (x_e cx) + 1)) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) Hoin).
eapply (@hc_call_ck fx2 rc SK rsegs B MT 0x83fcc MB_F1 Q _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) md2'
  (ms_regs ms) (e_R (x_e cx)) HCD).
- rewrite <- (mb_getr_z (ms_regs ms) 1 1 eq_refl). exact Rf1.
- unfold MB_F1. lia.
- reflexivity.
- intros HP.
  assert (Hos : garr8 rsegs (mrestrict (w_H W2) (ms_mem ms)) (e_out (x_e cx))
    (hd_zbytes (ha_cells_bytes (ans_cells (mb_ans cx r)))))
    by (apply (hd_garr8_kept rsegs (w_H W2) (w_H W2) mem2 (ms_mem ms)); [intros j _; apply KD | exact Ho]).
  destruct (headamp_B_site_cells_valid rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x_e cx)
    (hd_props (e_null (x_e cx)) (Model.buf r)) (mb_ans cx r) HP HinD Hcap eq_refl Hos) as (Hr1 & Hr2).
  apply (CK_CV fx2 _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ms) md2' _ (ms_regs ms) (ans_rc (mb_ans cx r))
    (e_out (x_e cx)) (ans_cells (mb_ans cx r)) HP).
  + rewrite <- (mb_getr_z (ms_regs ms) 10 10 eq_refl), Rf10. exact R22.
  + rewrite <- (mb_getr_z (ms_regs ms) 11 11 eq_refl), Rf11, R25, (f_rc B cx r ev HC). reflexivity.
  + exact Hr1.
  + exact Hr2.
- intros W3 ly3 S3 regs3 mem3 md3 Hle HC3 Hpres Hfr3 Hperm3 Hio3 Hmo3 Hkeep3.
  apply (K ly3 S3 W3 regs3 mem3 md3).
  apply (mb_mid_kept cx r ev (e_rc (x_e cx)) (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    HC HM0 HC3 Hfr3 Hperm3).
  + eapply same_io_trans; [apply same_io_wvb | exact Hio3].
  + exact Hmo3.
  + intros n Hn. rewrite (Hpres n) by (unfold acallee_saved; cbn [In] in Hn; lia).
    apply Rk. cbn [In] in Hn |- *. tauto.
  + rewrite (Hpres 25) by (unfold acallee_saved; lia). rewrite Rk by (cbn [In]; tauto). exact R25.
  + intros a Ha Hs. rewrite (Hkeep3 a Ha Hs). apply KD.
Qed.

(* ===================== the two cuts, from mb_mid ===================== *)
(* the pp and pod blocks are as at C5 *)
Lemma mb_pp_now : forall cx r ev v9 ly2 S2 W2 regs2 mem2 md2, @mb_f fx rc SK B cx r ev ->
mb_mid B MT cx r v9 ly2 S2 W2 regs2 mem2 md2 ->
garr8 rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx)) (hd_zbytes (Layout.pp_bytes r)) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (e_pod (x_e cx)) (hd_zbytes (Model.buf r)).
Proof using ERRNO.
intros cx r ev v9 ly2 S2 W2 regs2 mem2 md2 HC HM.
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (@mb_seps fx rc SK B cx r ev ERRNO HC) as (Z1 & Z2 & Z3 & Z4 & NIo & NIp & NIq & NIf & Ee0 & Ee4 & Eimg).
pose proof (f_cap B cx r ev HC) as Hcap. pose proof (f_dj B cx r ev HC) as Hdj. pose proof (f_len B cx r ev HC) as Hlen.
pose proof (Layout.length_pp_bytes r (f_wf B cx r ev HC)) as Hlp.
mb_mid_parts HM.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Papp, Qapp.
assert (Hfq : 0 <= e_F (x_e cx) / 8) by (apply Z.div_pos; lia).
assert (F8 : e_F (x_e cx) = 8 * (e_F (x_e cx) / 8)).
{ pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)) as D.
  assert (e_F (x_e cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide (e_F (x_e cx)) 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
split.
- apply (hd_garr8_kept rsegs (w_H (x_W cx)) (w_H W2) (x_memc cx) mem2); [|exact (f_pp B cx r ev HC)].
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj. unfold Layout.PP_SIZE in Hlp.
  apply KF; [lia | unfold T_SEG_STK, ASTACK; lia |]. unfold mb_Z. intros [Hz|[Hz|[Hz|[Hz|Hz]]]];
  [lia | lia | unfold shadow_addr, SHADOW_OFF in Hz; lia | lia | exact (NIp (e_pp (x_e cx) + Z.of_nat j) ltac:(lia) (Eimg _ Hz))].
- apply (hd_garr8_kept rsegs (w_H (x_W cx)) (w_H W2) (x_memc cx) mem2); [|exact (f_pod B cx r ev HC)].
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
  apply KF; [lia | unfold T_SEG_STK, ASTACK; lia |]. unfold mb_Z. intros [Hz|[Hz|[Hz|[Hz|Hz]]]];
  [lia | lia | unfold shadow_addr, SHADOW_OFF in Hz; lia | lia | exact (NIq (e_pod (x_e cx) + Z.of_nat j) ltac:(lia) (Eimg _ Hz))].
Qed.

(* HPgSegM.hqu_base3 with the shadow pattern hi_shB, at the parse's float state fx2 *)
Lemma mb_base3 : forall cx r ev, @mb_f fx rc SK B cx r ev ->
forall (fx2 : YK11.FPState) v9 ly2 S2 W2 regs2 mem2 md2, hd_fxk [14; 15] fx fx2 ->
mb_mid B MT cx r v9 ly2 S2 W2 regs2 mem2 md2 ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r (hi_shB headamp_himg_B) ly2 S2 W2 regs2 mem2 md2.
Proof using ERRNO ERRNO_RW.
intros cx r ev HC fx2 v9 ly2 S2 W2 regs2 mem2 md2 Hfx HM.
pose proof (mb_pp_now cx r ev v9 ly2 S2 W2 regs2 mem2 md2 HC HM) as (Hpp2 & Hpod2).
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (@mb_seps fx rc SK B cx r ev ERRNO HC) as (Z1 & Z2 & Z3 & Z4 & NIo & NIp & NIq & NIf & Ee0 & Ee4 & Eimg).
pose proof (f_r2 B cx r ev HC) as H2s. pose proof (f_r3 B cx r ev HC) as H3s. pose proof (f_r4 B cx r ev HC) as H4s.
pose proof (f_rom B cx r ev HC) as Hrom.
mb_mid_parts HM.
pose proof HC2 as (HJ2 & _ & H2 & H3 & H4 & _).
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. unfold kLowMemEnd in Ee4.
assert (Hfq : 0 <= e_F (x_e cx) / 8) by (apply Z.div_pos; lia).
assert (F8 : e_F (x_e cx) = 8 * (e_F (x_e cx) / 8)).
{ pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)) as D.
  assert (e_F (x_e cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide (e_F (x_e cx)) 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
unfold hqu_base3. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- unfold hsu_core, hsu_mid.
  split; [exact HJ2|].
  split.
  { intros r0 [-> | [-> | -> ] ].
    - rewrite (mb_getr_z regs2 2 2 eq_refl), (mb_getr_z (x_regs cx) 2 2 eq_refl), H2, H2s. reflexivity.
    - rewrite (mb_getr_z regs2 3 3 eq_refl), (mb_getr_z (x_regs cx) 3 3 eq_refl), H3, H3s. reflexivity.
    - rewrite (mb_getr_z regs2 4 4 eq_refl), (mb_getr_z (x_regs cx) 4 4 eq_refl), H4, H4s. reflexivity. }
  split; [exact Hfr2|]. split; [exact Hperm2|]. split; [exact Hio2|]. split; [exact Hmo2|].
  intros a Ha Hs He. apply KF; [exact Ha | |].
  + unfold spZ in Hs. rewrite H2s in Hs. unfold w64 in Hs. rewrite unsigned_lit_small in Hs by lia.
    unfold T_SEG_STK, ASTACK. exact Hs.
  + intros Hz. apply He. unfold hqu_E3. unfold mb_Z in Hz.
    destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]];
    [right; left; exact Hz | left; apply mb_inw; right; right; lia | left; apply mb_inw; right; left; lia
    | left; apply mb_inw; left; lia | right; right; exact Hz].
- unfold hqu_fxk, HQU_FXK. destruct Hfx as [Hk Hz]. split; [|exact Hz].
  intros k0 Hn. apply Hk. intros Hin. apply Hn. cbn [In] in Hin |- *. tauto.
- unfold hsu_fsh_at. exact Hfsh.
- intros a Hro.
  assert (Himg : in_img rsegs a) by (destruct Hro as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (img_segs_low a Himg) as Hl. unfold kLowMemEnd in Hl.
  rewrite KF; [exact (Hrom a Hro) | lia | unfold T_SEG_STK, ASTACK; lia |].
  unfold mb_Z. intros [Hz|[Hz|[Hz|[Hz|Hz]]]];
  [exact (NIo a Hz Himg) | lia | unfold shadow_addr, SHADOW_OFF in Hz; lia | exact (NIf a ltac:(lia) Himg)
  | exact (ERRNO_RW a Hz Hro)].
- unfold hsu_pp_at. exact Hpp2.
- exact Hpod2.
- exact Ho.
- exact Hres.
- exact Hev.
Qed.

(* a real-frame cell the head does not write (below R + 0x140, or R + 0x148) is as at C5 *)
Lemma mb_cell : forall cx r ev v9 ly2 S2 W2 regs2 mem2 md2 o v, @mb_f fx rc SK B cx r ev ->
mb_mid B MT cx r v9 ly2 S2 W2 regs2 mem2 md2 -> 0 <= o -> (o + 8 <= 0x140 \/ 0x148 <= o /\ o + 8 <= 0x150) ->
val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + o) 8 v ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + o) 8 v.
Proof using ERRNO.
intros cx r ev v9 ly2 S2 W2 regs2 mem2 md2 o v HC HM Ho1 Ho2 Hv.
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (@mb_seps fx rc SK B cx r ev ERRNO HC) as (Z1 & Z2 & Z3 & Z4 & NIo & NIp & NIq & NIf & Ee0 & Ee4 & Eimg).
mb_mid_parts HM.
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. unfold kLowMemEnd in Ee4.
assert (Hfq : 0 <= e_F (x_e cx) / 8) by (apply Z.div_pos; lia).
assert (F8 : e_F (x_e cx) = 8 * (e_F (x_e cx) / 8)).
{ pose proof (Z.div_mod (e_F (x_e cx)) 8 ltac:(lia)) as D.
  assert (e_F (x_e cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide (e_F (x_e cx)) 32 8) by (exists 4; reflexivity); rewrite Fm32; reflexivity).
  lia. }
apply (hd_val_mem_kept rsegs (w_H (x_W cx)) (w_H W2) (x_memc cx) mem2); [|exact Hv].
intros i Hi. apply KF; [lia | unfold T_SEG_STK, ASTACK; lia |].
unfold mb_Z. intros [Hz|[Hz|[Hz|[Hz|Hz]]]]; [lia | lia | unfold shadow_addr, SHADOW_OFF in Hz; lia | lia | lia].
Qed.

(* the list of X *)
Lemma mb_atX : forall cx r ev ly2 S2 W2 regs2 mem2 md2, @mb_f fx rc SK B cx r ev ->
mb_mid B MT cx r (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ->
hsu_at_cx rsegs cx W2 mem2 regs2
  (hqu_L_seg rsegs cx ++
   [(LReg 21, e_F (x_e cx)); (LReg 23, 1 - e_null (x_e cx));
    (LCell XR 0x8, e_pp (x_e cx) + Layout.OFF_IS_PROPS);
    (LCell XR 0x18, e_F (x_e cx)); (LCell XR 0x48, e_F (x_e cx));
    (LCell XR 0xe0, Z.shiftr (e_pp (x_e cx) + Layout.OFF_N_ENT) 3);
    (LCell XR 0x108, - 16381); (LCell XR 0x120, e_pp (x_e cx) + Layout.OFF_N_ENT);
    (LCell XR 0x140, hd_xv (x_e cx) XProps); (LCell XR 0x148, e_pp (x_e cx));
    (LCell XR 0x150, 3 * e_cap (x_e cx) + 3); (LCell XR 0x158, e_pod (x_e cx))]).
Proof using ERRNO.
intros cx r ev ly2 S2 W2 regs2 mem2 md2 HC HM.
pose proof HM as HM0. mb_mid_parts HM.
pose proof (f_c8 B cx r ev HC) as C8. pose proof (f_c18 B cx r ev HC) as C18. pose proof (f_c48 B cx r ev HC) as C48.
pose proof (f_ce0 B cx r ev HC) as Ce0. pose proof (f_c108 B cx r ev HC) as C108.
pose proof (f_c120 B cx r ev HC) as C120. pose proof (f_c148 B cx r ev HC) as C148.
rewrite Z.add_0_r in C18, C48, C148.
unfold hsu_at_cx, hsu_at, hqu_L_seg, hqu_L_frame, HQU_RES. cbn [app].
repeat (apply Forall_cons; [cbv beta; cbn [fst snd hd_at hd_xv] |]); [..| apply Forall_nil];
first [ assumption
      | apply (mb_cell cx r ev _ ly2 S2 W2 regs2 mem2 md2 _ _ HC HM0); [lia | lia | assumption] ].
Qed.

(* the list of FIRST *)
Lemma mb_atFIRST : forall cx r ev ly2 S2 W2 regs2 mem2 md2, @mb_f fx rc SK B cx r ev ->
mb_mid B MT cx r (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ->
hsu_at_cx rsegs cx W2 mem2 regs2
  (hqu_L_frame rsegs cx ++
   [(LReg 20, e_cap (x_e cx)); (LReg 21, e_F (x_e cx)); (LReg 22, e_out (x_e cx));
    (LReg 25, e_rc (x_e cx));
    (LCell XR 0x18, e_F (x_e cx));
    (LCell XR 0x140, hd_xv (x_e cx) XProps); (LCell XR 0x148, e_pp (x_e cx));
    (LCell XR 0x150, 3 * e_cap (x_e cx) + 3); (LCell XR 0x158, e_pod (x_e cx))]).
Proof using ERRNO.
intros cx r ev ly2 S2 W2 regs2 mem2 md2 HC HM.
pose proof HM as HM0. mb_mid_parts HM.
pose proof (f_c18 B cx r ev HC) as C18. pose proof (f_c148 B cx r ev HC) as C148.
rewrite Z.add_0_r in C18, C148.
unfold hsu_at_cx, hsu_at, hqu_L_frame. cbn [app].
repeat (apply Forall_cons; [cbv beta; cbn [fst snd hd_at hd_xv] |]); [..| apply Forall_nil];
first [ assumption
      | apply (mb_cell cx r ev _ ly2 S2 W2 regs2 mem2 md2 _ _ HC HM0); [lia | lia | assumption] ].
Qed.

(* ===================== block G: 0x82fc4 .. X 0x82fdc / FIRST 0x838e4 ===================== *)
Definition mb_rG (c : Z) : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit c))].
Definition mb_factsG : facts := mkFacts [(27%nat, mkAF 0x7fff8000 0x7fff8000 0); (24%nat, mkAF 4096 MBCEIL 3)] [] [].

Lemma mb_G_entry : forall (fx2 : YK11.FPState) (W2 : world rsegs) regs2 mem2 c pp,
getr regs2 (Z_to_bv 5 24) = w64 (pp + 0x4d18) -> getr regs2 (Z_to_bv 5 27) = w64 SHADOW_OFF ->
4096 <= pp + 0x4d18 <= MBCEIL -> pp mod 16 = 0 -> 0 <= c < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d18) 4 c ->
@st_ok rsegs fx2 (Ereg regs2 []) (mkSS 0x82fc4 sr_atoms [mb_rG c] None mb_factsG)
  (restrict (w_H W2) (@mkst fx2 regs2 (Z_to_bv 64 0x82fc4) mem2 (seg_rom rsegs))).
Proof.
intros fx2 W2 regs2 mem2 c pp H24 H27 Hpp Hpp16 Hc Hv.
assert (E24 : bv_unsigned (ew (Ereg regs2 []) 24) = pp + 0x4d18).
{ rewrite (ew_Ereg_nat regs2 _ 24 (Z_to_bv 5 24) eq_refl), H24. unfold w64. apply unsigned_lit_small.
  unfold MBCEIL in Hpp. lia. }
assert (E27 : bv_unsigned (ew (Ereg regs2 []) 27) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
rewrite restrict_mkst_fx. apply (@entry_st_ok_full fx2 rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold mb_rG.
  apply (hm_ro_region rsegs _ (w_H W2) mem2 24 (pp + 0x4d18) 0 4); [exact E24 | lia | unfold MBCEIL in Hpp; lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ (pp + 0x4d18) 0 4 (SLit c) c); [reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Hv.
- cbn. tauto.
- unfold facts_ok, mb_factsG. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E24, E27. unfold SHADOW_OFF, MBCEIL in *.
  change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
  assert (H8p : pp mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide pp 16 8) by (exists 2; reflexivity); rewrite Hpp16; reflexivity).
  assert (H8 : (pp + 0x4d18) mod 8 = 0) by (rewrite Zplus_mod, H8p; reflexivity).
  repeat split; lia.
Qed.

Lemma mb_G : forall cx r ev POST, @mb_f fx rc SK B cx r ev ->
hqu_from_X rsegs B MT cx r POST -> hqu_from_FIRST rsegs B MT cx r POST ->
forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2, hd_fxk [14; 15] fx fx2 ->
mb_mid B MT cx r (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs MB_F1 regs2 mem2 md2) POST.
Proof using MTL ERRNO ERRNO_RW.
intros cx r ev POST HC HX HFI fx2 ly2 S2 W2 regs2 mem2 md2 Hfx HM.
pose proof (@mb_bounds fx rc SK B cx r ev HC) as (Om16 & O4096 & Oc & Oapp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Pm16 & P4096 & Pc & Papp & Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (mb_pp_now cx r ev _ ly2 S2 W2 regs2 mem2 md2 HC HM) as (Hpp2 & _).
pose proof (f_wf B cx r ev HC) as Hwf.
pose proof (f_ppf B cx r ev HC) as (_ & Hppin & _).
pose proof HM as HM0. mb_mid_parts HM.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HC2 as (HJ & _).
unfold MBCEIL, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
(* pp->corrupt *)
assert (Hcor : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4d18) 4 (Z.b2z (Model.corrupt r))).
{ pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hbl).
  destruct (Model.ents_wf r Hwf) as (He & Hew).
  apply (hm_pp_corrupt rsegs (Model.buf r) (Model.is_props r) (Model.has_params r) (Model.params_struct r)
    (Model.ents r) (Model.corrupt r)); [unfold Layout.POD_BUF_MAX; lia | exact He | |].
  - rewrite Forall_forall in Hew |- *. intros x0 Hx0. destruct (Hew x0 Hx0) as (_ & Hb & Hs). rewrite Hb. lia.
  - exact Hpp2. }
assert (Hppin2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) Hppin).
destruct (hm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (e_pp (x_e cx)) Layout.PP_SIZE (e_pp (x_e cx) + 0x4d18) 8 (proj1 HJ)
  Hppin2 ltac:(lia) ltac:(unfold req_size, Layout.PP_SIZE; cbn; lia)) as (Hra & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Papp.
assert (SHOK : sh_ok rsegs MBBx MBSH (Ereg regs2 []) (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range rsegs (w_H W2) mem2 (Ereg regs2 []) MBBx 24 (e_pp (x_e cx) + 0x4d18) 8
    (e_pp (x_e cx) + 0x4d18) 0 8 Hra).
  - apply (U_atom _ 27 SHADOW_OFF); [rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact R27 | unfold SHADOW_OFF; lia].
  - apply (U_atom _ 24 (e_pp (x_e cx) + 0x4d18)); [rewrite (ew_Ereg_nat regs2 _ 24 (Z_to_bv 5 24) eq_refl); exact R24 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. unfold SHADOW_OFF. lia. }
assert (HAE : env_agree 32 (Ereg regs2 []) (Ereg regs2 [])) by apply env_agree_refl.
unfold cfg_at, MB_F1. change (w64 0x82fc4) with (Z_to_bv 64 0x82fc4).
destruct (Model.corrupt r) eqn:Hcr; cbn [Z.b2z] in Hcor.
- (* pp->corrupt = 1: to FIRST *)
  pose proof (mb_G_entry fx2 W2 regs2 mem2 1 (e_pp (x_e cx)) R24 R27 ltac:(unfold MBCEIL; lia) Pm16 ltac:(lia) Hcor)
    as HS.
  aj_run_tok mb_tbl_ok HS HJ SHOK MBspan.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
  { intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W2) regs2 [] (Z_to_bv 5 r0) HS HAE).
    cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
  pose proof (mb_frame_ro _ _ _ _ _ HFr) as KG.
  pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  assert (HCx : hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) (ms_regs ms) (e_R (x_e cx))).
  { apply (mb_core_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC2 HJ);
    [ rewrite <- !(mb_getr_z _ 2 2 eq_refl) | rewrite <- !(mb_getr_z _ 3 3 eq_refl) | rewrite <- !(mb_getr_z _ 4 4 eq_refl)];
    apply Rk; cbn [In]; tauto. }
  assert (HMx : mb_mid B MT cx r (e_rc (x_e cx)) ly2 S2 W2 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md2) mat md2)).
  { apply (mb_mid_kept cx r ev (e_rc (x_e cx)) (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms)
      (ms_mem ms) _ HC HM0 HCx eq_refl (Permutation_refl _) (same_io_wvb _ _ _) (mo_le_refl MT MTL S2)).
    + intros n Hn. apply Rk. cbn [In] in Hn |- *. tauto.
    + rewrite Rk by (cbn [In]; tauto). exact R25.
    + intros a _ _. apply KG. }
  apply (HFI fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2)).
  split; [exact (mb_base3 cx r ev HC fx2 _ ly2 S2 W2 _ _ _ Hfx HMx)|].
  exact (mb_atFIRST cx r ev ly2 S2 W2 _ _ _ HC HMx).
- (* pp->corrupt = 0: to X *)
  pose proof (mb_G_entry fx2 W2 regs2 mem2 0 (e_pp (x_e cx)) R24 R27 ltac:(unfold MBCEIL; lia) Pm16 ltac:(lia) Hcor)
    as HS.
  aj_run_tok mb_tbl_ok HS HJ SHOK MBspan.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
  { intros r0 Hr. eapply (mb_reg_atom _ _ _ ms (w_H W2) regs2 [] (Z_to_bv 5 r0) HS HAE).
    cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
  pose proof (mb_frame_ro _ _ _ _ _ HFr) as KG.
  pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
  assert (HCx : hc_core rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    (x_own cx) (x_k cx) ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) (ms_regs ms) (e_R (x_e cx))).
  { apply (mb_core_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC2 HJ);
    [ rewrite <- !(mb_getr_z _ 2 2 eq_refl) | rewrite <- !(mb_getr_z _ 3 3 eq_refl) | rewrite <- !(mb_getr_z _ 4 4 eq_refl)];
    apply Rk; cbn [In]; tauto. }
  assert (HMx : mb_mid B MT cx r (e_rc (x_e cx)) ly2 S2 W2 (ms_regs ms) (ms_mem ms)
    (with_vm_backing (m_vm_lazy md2) mat md2)).
  { apply (mb_mid_kept cx r ev (e_rc (x_e cx)) (e_rc (x_e cx)) ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms)
      (ms_mem ms) _ HC HM0 HCx eq_refl (Permutation_refl _) (same_io_wvb _ _ _) (mo_le_refl MT MTL S2)).
    + intros n Hn. apply Rk. cbn [In] in Hn |- *. tauto.
    + rewrite Rk by (cbn [In]; tauto). exact R25.
    + intros a _ _. apply KG. }
  apply (HX fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2)).
  split; [exact (mb_base3 cx r ev HC fx2 _ ly2 S2 W2 _ _ _ Hfx HMx)|].
  split; [|exact Hcr].
  exact (mb_atX cx r ev ly2 S2 W2 _ _ _ HC HMx).
Qed.

(* ===================== the piece ===================== *)
Theorem hqu_M3a_head : hqu_piece_M3a_head_stmt rsegs B MT.
Proof using AMEMSET MTL PARSE CK_NO CK_COUNT CK_CV ERRNO ERRNO_RW.
unfold hqu_piece_M3a_head_stmt. intros cx POST r ev Hst HX HFI.
pose proof (@mb_f_of fx rc SK B cx r ev Hst) as HC.
apply (@mb_A fx rc SK B AMEMSET cx r ev POST HC). intros regs1 mem1 md1 HA.
apply (@mb_B fx rc SK B AMEMSET cx r ev regs1 mem1 md1 POST HC HA). intros regs2 mem2 md2 HB.
apply (@mb_C fx rc SK B MT PARSE ERRNO cx r ev regs2 mem2 md2 POST HC HB).
intros fx2 ly3 S3 W3 regs3 mem3 md3 Hfx HM H10.
apply (mb_D cx r ev POST HC fx2 ly3 S3 W3 regs3 mem3 md3 HM H10). intros ly4 S4 W4 regs4 mem4 md4 HM4.
apply (mb_E cx r ev POST HC fx2 ly4 S4 W4 regs4 mem4 md4 HM4). intros ly5 S5 W5 regs5 mem5 md5 HM5.
apply (mb_F cx r ev POST HC fx2 ly5 S5 W5 regs5 mem5 md5 HM5). intros ly6 S6 W6 regs6 mem6 md6 HM6.
exact (mb_G cx r ev POST HC HX HFI fx2 ly6 S6 W6 regs6 mem6 md6 Hfx HM6).
Qed.

End s.
End b.

Print Assumptions hqu_M3a_head.
