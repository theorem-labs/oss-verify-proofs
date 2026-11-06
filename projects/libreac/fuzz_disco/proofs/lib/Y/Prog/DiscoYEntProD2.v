(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 305 of its 340 lines of code are new or changed and 1243 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC85 YC88 YCkd YC1g YC1h YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model reac_hunt_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntSeat DiscoYEntProCuts DiscoYEntProSeat DiscoYEntProDCuts DiscoYEntProDLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacHuntInit.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pd2_hib_our : forall ob now, length ob = 6%nat -> firstn 6 (skipn 412 (hunt_init_bytes ob now)) = ob.
Proof.
intros ob now Hl. destruct ob as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 ob]]]]]]]; cbn [length] in Hl; try discriminate.
reflexivity.
Qed.
Lemma pd2_our_len : forall pl, length (our_of pl) = 6%nat.
Proof. intros pl. unfold our_of. rewrite length_map, length_seq. reflexivity. Qed.
Lemma pd2_mbyte_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof. intros segs H m m' HM a. unfold mbyte, mrestrict. rewrite HM. reflexivity. Qed.
Lemma pd2_aview_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' HM a. unfold aview. rewrite (pd2_mbyte_ext segs H m m' HM). reflexivity. Qed.
Lemma pd2_frame_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.
Ltac pd2_bvneq := let X := fresh "X" in intros X; apply (f_equal bv_unsigned) in X; cbv in X; discriminate X.
Ltac pd2_ro HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Lemma pd2_rok_keep : forall E (m m' : word -> option byte) r,
  region_ok SEGS E m r -> forallb (chunk_inside r) (YP09.r_chunks r) = true ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  region_ok SEGS E m' r.
Proof.
intros E m m' r HR Hci Hw Hk. apply (pd_rok_move E m m' r HR Hw).
intros c Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hci c Hc) as H1. unfold chunk_inside in H1.
apply andb_prop in H1 as [H1 H3]. apply andb_prop in H1 as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
apply Hk. lia.
Qed.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TINIT : ReacHuntInit.treac_hunt_init_spec B.
Lemma pd2_afn_s0 : forall STK ly S (W : world SEGS) regs mem md ch,
  afn_pre SEGS B STK ly S W regs mem md ch -> afn_pre SEGS B STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md [].
Proof.
intros STK ly S W regs mem md ch (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & _ & HQT).
assert (Hsp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite ReacHuntInit.hi_getr_s0z by pd2_bvneq; reflexivity).
assert (Hs0 : s0Z (regupd regs 8 (Z_to_bv 64 0)) = 0).
{ unfold s0Z, getr. change (bv_eqb (8%bv : bv 5) 0) with false. cbv iota. rewrite regupd_same. reflexivity. }
split; [exact HAR|].
split; [rewrite ReacHuntInit.hi_getr_s0z by pd2_bvneq; exact Hra|].
split; [unfold raZ; rewrite ReacHuntInit.hi_getr_s0z by pd2_bvneq; exact Hra4|].
split; [rewrite ReacHuntInit.hi_getr_s0z by pd2_bvneq; exact Hgp|].
split; [rewrite ReacHuntInit.hi_getr_s0z by pd2_bvneq; exact Htp|].
split; [rewrite Hsp; exact Hstk|].
split; [rewrite Hsp; exact Hpres|].
split; [|exact HQT].
rewrite Hs0. apply achain_low. pose proof asan_consts as (C1 & _). lia.
Qed.
Theorem pb_proD2 : pd_seg2 B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold pd_seg2. intros cx h W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & Hcan & HrC3 & _ & Hfr & Hbl & Hhv & Hour & HoT & HoG & HoL).
pose proof Hfr as (E & HdE & HRG & HFL).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC) as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
pose proof HrC3 as (HrB & H18 & H24 & H23).
assert (HAr2 : d_S cx - 607 <= d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr; lia).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
pose proof Hbl as (Hperm & Hnot & Hbb & Hoff).
assert (Hinh : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _ & _ & _).
change (req_size HUNT_SIZE) with 480 in Hhceil, Hhapp.
pose proof (pd_regs_ok cx E regs h B HdE HrB HArange HSHrange) as HROK.
set (Ed := d_env cx E (pd_vals regs h)) in *.
assert (E563 : ew Ed (AT_X + 32) = w64 h).
{ unfold Ed, d_env. replace (AT_X + 32)%nat with (AT_FL + 33)%nat by (unfold AT_X, AT_FL; lia).
  rewrite (ew_havoc_new E AT_FL _ 33 (Z_to_bv 64 0)) by (unfold pd_vals; cbn; lia).
  unfold pd_vals. reflexivity. }
assert (HACS : Forall (YP09.chunk_ok SEGS Ed (rd W mem3) (d_A cx)) pd_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS Ed _ (d_A cx) 184 8%N (SOff (AT_X + 32) 0) h).
  - cbn [sv_denot]. rewrite E563, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. change (2 ^ (8 * 8)) with (2 ^ 64). lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. exact Hhv. }
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C3 ly3 S3 W regs mem3 md3 k E POFF_D1 pd_sr (pd_vals regs h) pd_acs [] [] (d_facts [] []) HC HdE HRG HFL HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (pd_vals regs h) [] [] HC HdE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS. fold Ed in HS.
pd2_ro HS 60%nat. pd2_ro HS 516%nat. pd2_ro HS 529%nat.
pose proof HdE as (EE & E32 & HEI0 & E60 & E516 & E529).
assert (HEI : img_env VAL A_LIM Ed).
{ intros a Ha. unfold Ed, d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HEI0 a Ha). }
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + POFF_D1)) with (Z_to_bv 64 (BASE + POFF_D1)).
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac. }
pose proof (pd2_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M.
pose proof (pd2_aview_ext SEGS (w_H W) mem3 (ms_mem ms) M) as KR.
change (AT_X + 32)%nat with 563%nat in E563.
assert (AGd : forall n0, (n0 < AT_FL)%nat -> ew Ed n0 = ew E n0) by (intros n0 Hn0; apply d_env_old; exact Hn0).
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 1844)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  exact (codeptr_val _ 1844 HEI). }
assert (R10 : getr (ms_regs ms) 10%bv = w64 h).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite E563, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (R11 : getr (ms_regs ms) 11%bv = w64 (d_obj cx OOUR)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite (AGd 516%nat ltac:(unfold AT_FL; lia)). change 516%nat with AT_F. rewrite E516. unfold w64.
  rewrite unsigned_lit_small by lia. unfold d_obj, dobj_off. reflexivity. }
assert (R12 : getr (ms_regs ms) 12%bv = w64 1000000000).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  reflexivity. }
assert (USP2 : bv_unsigned (ew Ed 2) = d_S cx).
{ rewrite (AGd 2%nat ltac:(unfold AT_FL; lia)), (EE 2%nat 2%bv eq_refl). reflexivity. }
pose proof (proj1 Hbase) as (_ & Hra0 & _).
assert (E1v : ew Ed 1 = Z_to_bv 64 RA_LLVMF).
{ rewrite (AGd 1%nat ltac:(unfold AT_FL; lia)), (EE 1%nat 1%bv eq_refl). unfold raZ in Hra0. rewrite <- Hra0. symmetry. apply Z_to_bv_bv_unsigned. }
assert (E8v : ew Ed 8 = Z_to_bv 64 (s0Z (c_regs cx))).
{ rewrite (AGd 8%nat ltac:(unfold AT_FL; lia)), (EE 8%nat 8%bv eq_refl). unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as RSV end.
cbn [ms_mem restrict] in RSV.
assert (HRD8 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 8) = Some RA_LLVMF).
{ apply rdword_of_val_mem; [| unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + (-8)) by lia.
  apply (field_of_region Ed _ 2%nat (d_S cx) _ (-104) 0 0 0 (-8) 8%N (SOff 1 0) RA_LLVMF RSV USP2
    ltac:(cbn; left; reflexivity) ltac:(cbn [sv_denot]; rewrite E1v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold RA_LLVMF; lia) ltac:(cbn; lia)). }
assert (HRD16 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 16) = Some (s0Z (c_regs cx))).
{ apply rdword_of_val_mem; [| unfold s0Z; apply bv_unsigned_in_range].
  replace (d_S cx - 16) with (d_S cx + (-16)) by lia.
  apply (field_of_region Ed _ 2%nat (d_S cx) _ (-104) 0 0 0 (-16) 8%N (SOff 8 0) (s0Z (c_regs cx)) RSV USP2
    ltac:(cbn; right; left; reflexivity) ltac:(cbn [sv_denot]; rewrite E8v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr (c_regs cx) 8))) ltac:(cbn; lia)). }
clear RSV.
assert (HCt : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (pd_achain B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) _ k HCt ltac:(lia) ltac:(lia) HRD8 HRD16) as (ch1 & HCH).
assert (Hs0 : s0Z (ms_regs ms) = d_S cx).
{ unfold s0Z. rewrite (RG 8%bv ltac:(cbv; tauto)). destruct HrB as (_ & _ & _ & H8 & _). rewrite H8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *; lia. }
assert (WS : ReacHuntInit.REAC_HUNT_INIT_STK = 4160) by reflexivity.
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (Hz : (d_obj cx OOUR =? 0) = false) by (apply Z.eqb_neq; unfold d_obj, dobj_off; lia).
assert (HSV : forall kk, 0 <= kk < DFRAME_SH -> aview SEGS (w_H W) (ms_mem ms) (shadow_addr (d_FB cx) + kk) = Some (dsh_loop kk)).
{ intros kk Hkk. rewrite KR. exact (pd_sh_val cx dsh_loop ps_C3 W mem3 ltac:(vm_compute; reflexivity) HSHrange Hfr kk Hkk). }
assert (HRAour : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (d_obj cx OOUR) 6).
{ unfold d_obj, dobj_off. apply (pd_ra_range cx dsh_loop W (ms_mem ms) 2128 6 HSV ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold DFRAME_SH; lia)).
  intros q Hq. assert (Hq8 : (2128 + q) / 8 = 266) by lia. rewrite Hq8, pd_sh_O. unfold saddr_ok. right. lia. }
assert (HGour : garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms)); [intros a _; apply KR | exact Hour]. }
eapply SRr_bind.
{ eapply (pd_aj_callF (fx := fq) B LAWS W Ed _ ms LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k ReacHuntInit.REAC_HUNT_INIT_STK [(h, h + 480)] 0 (d_A cx - d_S cx) (ew Ed 2)
    (Z_to_bv 64 (BASE + 1844)) ch1 _ HS eq_refl HJ).
  - rewrite (RG 2%bv ltac:(cbv; tauto)). cbn [sv_denot]. rewrite USP2.
    replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by lia.
    destruct HrB as (Hsp0 & _). rewrite <- Hsp0. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned.
  - reflexivity.
  - exact USP2.
  - lia.
  - lia.
  - lia.
  - rewrite WS. unfold LLVMF_STK. lia.
  - rewrite (RG 3%bv ltac:(cbv; tauto)). exact (proj1 (proj2 HrB)).
  - rewrite (RG 4%bv ltac:(cbv; tauto)). exact (proj1 (proj2 (proj2 HrB))).
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold IMG_LO in HBLO; lia). unfold IMG_LO in HBLO; lia.
  - replace (d_S cx + (d_A cx - d_S cx)) with (d_A cx) by lia. rewrite Hs0. exact HCH.
  - intros HPRE1. cbn [ss_pc setpc]. rewrite pa_sigma_reac_hunt_init. rewrite <- R1.
    eapply (TINIT fq ly3 S3 W (ms_regs ms) (ms_mem ms) _ [] h (d_obj cx OOUR) 1000000000 h HUNT_SIZE (our_of (c_pl cx))
      (pd2_afn_s0 _ _ _ _ _ _ _ _ HPRE1) R10 R11 R12).
    + unfold d_obj, dobj_off. lia.
    + lia.
    + lia.
    + lia.
    + exact Hinh.
    + lia.
    + change (req_size HUNT_SIZE) with 480. lia.
    + intros _. split; [|split; [exact (pd2_our_len (c_pl cx)) | exact HGour]].
      split; [|split; [unfold d_obj, dobj_off; lia | exact HRAour]].
      exists DFRAME_CLASS, (c_fpos cx). split; [exact Hin3|]. rewrite EFB3. unfold d_obj, dobj_off, DFRAME_CLASS.
      change (fs_frame_bytes 6) with 4096. lia.
  - intros a (r & Hr & Hr2). cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hr2.
    right. exists h, HUNT_SIZE. split; [exact Hinh|]. split; [exact (Forall_inv Hnot)|]. change (req_size HUNT_SIZE) with 480. lia. }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFRG2 & HCSR2 & HJ2 & HJc & HP2 & HK).
rewrite Hz in HK.
destruct HK as (HGH & HOKH & HPermH).
clear HS HF HFr HG RUNP RUNC HROK HCH.
pose proof HJc as (_ & _ & _ & _ & _ & HfrsC & _ & _ & KC9 & _ & _ & KC12 & _).
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 (k + 0))
  by (split; [exact Hbase | split; [exact HJ2 | rewrite HfrsC; exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC2) as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSHpres2 & HWpres2 & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hinh Hin3) as Hsbf.
unfold zdisjoint in Hsbf. cbn [fst snd] in Hsbf. rewrite EFB3 in Hsbf.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsbf. change (req_size HUNT_SIZE) with 480 in Hsbf.
assert (KAS : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. rewrite <- (KR a). apply KC9; [unfold LLVMF_STK in *; lia | rewrite WS; lia]. }
assert (KFS : forall a, (d_FB cx <= a < d_FB cx + 4096 \/ shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. rewrite <- (KR a). apply (KC12 DFRAME_CLASS (c_fpos cx) a Hin3).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - intros (r & Hr & Hr2). cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hr2.
    destruct Ha as [Ha | Ha]; [lia|].
    clear - Ha Hr2 Hhapp HFB1 HFB2 C1.
    unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (U2 : base_val E (Some AT_STK) = d_S cx).
{ cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (U60 : base_val E (Some AT_A) = d_A cx).
{ cbn [base_val]. rewrite E60. apply unsigned_lit_small. lia. }
assert (U516 : base_val E (Some AT_F) = d_FB cx).
{ cbn [base_val]. rewrite E516. apply unsigned_lit_small. lia. }
assert (U529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
{ cbn [base_val]. rewrite E529. apply unsigned_lit_small. lia. }
assert (Hfr2 : p_frame cx dsh_loop ps_C3 W2 mem2).
{ exists E. split; [exact HdE|]. split.
  - unfold p_regions in HRG |- *.
    pose proof (Forall_inv HRG) as Q1. apply Forall_inv_tail in HRG.
    pose proof (Forall_inv HRG) as Q2. apply Forall_inv_tail in HRG.
    pose proof (Forall_inv HRG) as Q3. apply Forall_inv_tail in HRG.
    pose proof (Forall_inv HRG) as Q4. clear HRG.
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (pd2_rok_keep E _ _ _ Q1 ltac:(vm_compute; reflexivity)); cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite U2.
      * intros o Ho. lia.
      * intros a Ha. apply (mbyte_of_aview SEGS). apply KAS. lia.
    + apply (pd2_rok_keep E _ _ _ Q2 ltac:(vm_compute; reflexivity)); cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite U60.
      * intros o Ho. apply (apresent_writable SEGS). apply HWpres2. unfold LLVMF_STK. lia.
      * intros a Ha. apply (mbyte_of_aview SEGS). apply KAS. lia.
    + apply (pd2_rok_keep E _ _ _ Q3 ltac:(vm_compute; reflexivity)); cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite U516.
      * intros o Ho. apply (apresent_writable SEGS). apply HFpres2. unfold DFRAME_SIZE in Ho. lia.
      * intros a Ha. apply (mbyte_of_aview SEGS). apply KFS. left. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha. lia.
    + apply (pd2_rok_keep E _ _ _ Q4 ltac:(vm_compute; reflexivity)); unfold fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite U529.
      * intros o Ho. apply (apresent_writable SEGS). apply HSHpres2. unfold DFRAME_SH in Ho. lia.
      * intros a Ha. apply (mbyte_of_aview SEGS). apply KFS. right. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha. lia.
  - rewrite <- HFL. apply rdword_ext. intros kk Hkk. apply KFS. left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
assert (Hbl2 : d_blocks B cx h [] ly2 S2).
{ split; [exact (Permutation_trans HPermH Hperm)|]. split; [exact Hnot|]. split; [|exact Hoff].
  rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPermH), <- (blocks_bytes_bsum B ly3 S3). exact Hbb. }
assert (Hhv2 : val_mem SEGS (rd W2 mem2) (d_A cx + 184) 8 h).
{ apply (pd_val_kept W mem3 W2 mem2); [|exact Hhv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KAS. lia. }
assert (Hour2 : pd_our cx W2 mem2).
{ unfold pd_our in *. apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact Hour].
  intros a Ha. rewrite length_map, pd2_our_len in Ha. change (Z.of_nat 6) with 6 in Ha. apply KFS. left. unfold d_obj, dobj_off in Ha. lia. }
assert (HoT2 : pd_objT cx W2 mem2).
{ destruct HoT as (T & LT & GT & OKT). exists T. split; [exact LT|]. split; [|exact OKT].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact GT].
  intros a Ha. rewrite length_map, LT in Ha. change (Z.of_nat 400) with 400 in Ha. apply KFS. left. unfold d_obj, dobj_off in Ha. lia. }
assert (HoG2 : pd_objG cx W2 mem2).
{ destruct HoG as (G & LG & GG & OKG). exists G. split; [exact LG|]. split; [|exact OKG].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact GG].
  intros a Ha. rewrite length_map, LG in Ha. change (Z.of_nat 264) with 264 in Ha. apply KFS. left. unfold d_obj, dobj_off in Ha. lia. }
assert (HoL2 : pd_objL cx W2 mem2).
{ destruct HoL as (Lk & LL & GL & OKL). exists Lk. split; [exact LL|]. split; [|exact OKL].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact GL].
  intros a Ha. rewrite length_map, LL in Ha. change (Z.of_nat 12) with 12 in Ha. apply KFS. left. unfold d_obj, dobj_off in Ha. lia. }
assert (HoH2 : pd_objH cx h W2 mem2).
{ exists (hunt_init_bytes (our_of (c_pl cx)) 1000000000). split; [exact (proj1 HOKH)|].
  split; [exact HGH|]. split; [exact HOKH|]. apply pd2_hib_our. apply pd2_our_len. }
assert (RF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite <- (RG r Hr).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [match goal with |- getr _ ?rr = _ => let z := eval vm_compute in (bv_unsigned rr) in exact (HP2 z ltac:(unfold acallee_saved; lia)) end|]). destruct Hr. }
assert (HrC3' : p_rC3 cx B regs2).
{ destruct HrC3 as ((Hsp0 & Hgp0 & Htp0 & H80 & H90 & H190 & H270) & H180 & H240 & H230).
  unfold p_rC3, p_rbase, spZ. rewrite !RF by (cbv; tauto). unfold spZ in Hsp0. repeat split; assumption. }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
apply SRr_ret. unfold pd_K2, pd_at, d_at.
exists fx2, ly2, S2, regs2, mem2, md2, (k + 0), acc.
split; [unfold cfg_at, w64, POFF_D2; reflexivity|]. split; [exact (pd_frm0 fq fx2 HF0 HCSR2)|].
split; [exact Hbase|]. split; [exact HJ2|]. split; [rewrite HfrsC; exact Hfrs|].
split; [unfold EV_PRO in *; lia|]. split; [unfold EV_PRO in *; lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hcan|]. split; [exact HrC3'|]. split; [exact I|]. split; [exact Hfr2|]. split; [exact Hbl2|].
split; [exact Hhv2|]. split; [exact Hour2|]. split; [exact HoT2|]. split; [exact HoG2|]. split; [exact HoL2 | exact HoH2].
Qed.
End h.
End f.
End d.
