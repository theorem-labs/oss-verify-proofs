(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 338 of its 373 lines of code are new or changed and 1243 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoSites DiscoEntSeatStmt DiscoEntSeat DiscoEntProCuts DiscoEntProSeat DiscoEntRec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pc_sr_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | 24%nat => SOff AT_F 0
  | _ => SOff (AT_X + r) 0
  end.
Definition pc_sr : list sv := map pc_sr_x (seq 0 32).
Definition pc_vals (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
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

Lemma pc_regs_ok : forall cx E regs, d_E cx E -> p_rbase cx regs B ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 64 ->
  regs_ok (d_env cx E (pc_vals regs)) pc_sr regs.
Proof.
intros cx E regs HE HL HA HF.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18
          | rewrite HF516; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H24 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth pc_vals map seq Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.
Ltac pc_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma pc_chain : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx)) = true \/
  fpchain (rdword (aview SEGS (w_H W3) mem3)) (s0Z (c_regs cx)) (ly_top ly3) [].
Proof.
intros cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
destruct HB as ((HPRE & _) & _).
destruct HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _ & Hch & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly3 & _ & _ & _ & _ & _ & _ & Hkeep & _).
destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
rewrite Etop. change (spZ (c_regs cx)) with (d_S cx) in *.
pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hs0r. change (bv_unsigned (getr (c_regs cx) 8)) with (s0Z (c_regs cx)) in Hs0r.
destruct Hch as [(Hv & _) | (Hv1 & Hv2 & Hv3 & Hfp & _)].
- left. unfold bad_next. destruct Hv as [Hv | [Hv | Hv]].
  + apply Bool.orb_true_iff; left; apply Bool.orb_true_iff; left; apply Z.leb_le. unfold LLVMF_STK in *. lia.
  + apply Bool.orb_true_iff; left; apply Bool.orb_true_iff; right; apply Z.leb_le. lia.
  + apply Bool.orb_true_iff; right. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hv.
- right. cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hr2). exists r. split; [|exact Hr2].
  rewrite <- Hr. apply rdword_ext. intros kk Hkk. apply Hkeep; unfold LLVMF_STK in *; lia.
Qed.
Lemma pc_garr8_aview : forall H H' (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H' m' x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hx G j Hj. destruct (G j Hj) as (G1 & G2). split; [|exact G2].
intros kk Hkk. rewrite (mbyte_of_aview SEGS H H' m m'). { exact (G1 kk Hkk). }
apply Hx. assert (kk = 0%nat) by lia. subst kk. cbn. lia.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : forall fq : YK11.FPState, amalloc_realizes (fx := fq) SEGS B.
Hypothesis DUNIV : duniv_ok B.
Hypothesis MT_TRIV : MT = ameter_triv.
Theorem pc_segC : pro_segC B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold pro_segC. intros cx W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & Hcan0 & HrC3 & Hfr & Hab & Hour).
destruct Hfr as (E & HdE & HRG & HFL).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC) as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
pose proof HrC3 as (HrB & H19 & H21 & H27).
assert (HAr2 : d_S cx - 607 <= d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr; lia).
assert (HSl2 : alloc_ceiling + 32768 <= d_S cx) by (unfold LLVMF_STK in HSlo; lia).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFBrange : 0 <= d_FB cx < 2 ^ 64) by lia.
pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
pose proof (pc_regs_ok cx E regs HdE HrB HArange HFBrange) as HROK.
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_our ps_C2 ly3 S3 W regs mem3 md3 k E POFF_C3 pc_sr (pc_vals regs) [] [] [] (d_facts [] []) HC HdE HRG HFL HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (pc_vals regs) [] [] HC HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS.
pc_ro_base HS 516%nat.
pose proof HdE as (EE & E32 & HEI0 & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
assert (AGd : forall n0, (n0 < AT_FL)%nat -> ew (d_env cx E (pc_vals regs)) n0 = ew E n0) by (intros n0 Hn0; apply d_env_old; exact Hn0).
assert (HEI : img_env VAL A_LIM (d_env cx E (pc_vals regs))).
{ intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HEI0 a Ha). }
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + POFF_C3)) with (Z_to_bv 64 (BASE + POFF_C3)).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
  [ reflexivity
  | rewrite (AGd 60%nat ltac:(unfold AT_FL; lia)), E60; unfold w64; rewrite unsigned_lit_small by exact HArange; lia
  | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia
  | cbn [YP09.r_whi]; unfold MFRAME in *; lia
  | ].
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx)));
  [ reflexivity
  | rewrite (AGd 529%nat ltac:(unfold AT_FL; lia)), E529; unfold w64; apply unsigned_lit_small; exact HSHrange
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
    exists DFRAME_CLASS, (c_fpos cx); split; [left; reflexivity|]; right;
    unfold in_zr; cbn [fst snd]; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia
  | ].
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  apply awr_ok_nil. }
set (Ed := d_env cx E (pc_vals regs)) in *.
assert (Ka : forall x, d_obj cx OOUR <= x < d_obj cx OOUR + 6 -> aview SEGS (w_H W) (ms_mem ms) x = aview SEGS (w_H W) mem3 x).
{ intros x Hx. unfold d_obj, dobj_off in Hx. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?(AGd 60%nat) , ?(AGd 529%nat), ?E60, ?E529 in Hr by (unfold AT_FL; lia); unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
    unfold shadow_addr, SHADOW_OFF in Hr; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFBapp; lia|]).
  destruct Hin. }
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 1816)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  exact (codeptr_val _ 1816 HEI). }
assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 480).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  reflexivity. }
assert (USP2 : bv_unsigned (ew Ed 2) = d_S cx).
{ subst Ed. rewrite (AGd 2%nat ltac:(unfold AT_FL; lia)), (EE 2%nat 2%bv eq_refl). reflexivity. }
pose proof (proj1 Hbase) as (_ & Hra0 & _).
assert (E1v : ew Ed 1 = Z_to_bv 64 RA_LLVMF).
{ subst Ed. rewrite (AGd 1%nat ltac:(unfold AT_FL; lia)), (EE 1%nat 1%bv eq_refl). unfold raZ in Hra0. rewrite <- Hra0. symmetry. apply Z_to_bv_bv_unsigned. }
assert (E8v : ew Ed 8 = Z_to_bv 64 (s0Z (c_regs cx))).
{ subst Ed. rewrite (AGd 8%nat ltac:(unfold AT_FL; lia)), (EE 8%nat 8%bv eq_refl). unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
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
pose proof (pc_chain cx ly3 S3 W (ms_mem ms) _ k HCt) as HCH.
assert (Hsp : spZ (ms_regs ms) = d_A cx).
{ unfold spZ. rewrite (RG 2%bv ltac:(cbv; tauto)). exact (proj1 HrB). }
assert (Hs0 : s0Z (ms_regs ms) = d_S cx).
{ unfold s0Z. rewrite (RG 8%bv ltac:(cbv; tauto)). destruct HrB as (_ & _ & _ & H8 & _). rewrite H8. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *; lia. }
assert (Hra : raZ (ms_regs ms) = BASE + 0x718).
{ unfold raZ. rewrite R1. apply unsigned_lit_small. pose proof pa_B_ok. pose proof pa_base_lo. lia. }
destruct (d_call_chain B MT XM_LIB RLO RHI tfib_K (pc_malloc_ra0 (as_code B)) 0x718 cx ly3 S3 W (ms_mem ms) _ k (ms_regs ms) (s0Z (c_regs cx)) HCt
  (proj2 (pal_rt_below B TL)) ltac:(lia) ltac:(pose proof pa_base_lo; unfold IMG_LO in *; lia)
  ltac:(apply DUNIV; unfold d_sites; do 6 right; left; reflexivity)
  ltac:(apply DUNIV; unfold d_sites; left; reflexivity)
  Hsp Hs0 ltac:(unfold MFRAME in *; lia) Hra HRD8 HRD16 HCH) as (ch & Hchp & Htr).
rewrite (pal_malloc B TL) in HS. pmkst HS.
pose proof (proj1 Hbase) as (_ & _ & _ & _ & _ & _ & _ & _ & Hnev0 & Hbb0 & _).
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
eapply SRr_bind.
{ eapply (aj_malloc_at04 (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AMALLOC fq) W (ms_regs ms) (ms_mem ms) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k 480 (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 1816)) ch HJ).
  - exact R10.
  - unfold MALLOC_MAX; lia.
  - rewrite (blocks_bytes_bsum B ly3 S3), Hab, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). unfold LIVE_LIB, LIVE_MAX in *. lia.
  - rewrite Hsp. lia.
  - lia.
  - unfold MFRAME in *. lia.
  - unfold ASTACK, LLVMF_STK, MFRAME in *. lia.
  - rewrite (RG 3%bv ltac:(cbv; tauto)). exact (proj1 (proj2 HrB)).
  - rewrite (RG 4%bv ltac:(cbv; tauto)). exact (proj1 (proj2 (proj2 HrB))).
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_LIB in *. lia.
  - exact Hchp.
  - exact Htr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & _ & Eab2 & HK).
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 (k + 1)) by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfrs2; exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSHpres2 & _ & HAR2 & Hin2 & EFB2 & _).
assert (Hnew : In (res, 480) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hnew) as (_ & Hr4096 & Hrceil & Hrapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hnew Hin2) as Hsbf.
assert (HdisF : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (res <= a < res + req_size 480)).
{ intros a Ha Hb. unfold zdisjoint in Hsbf. cbn [fst snd] in Hsbf. rewrite EFB2 in Hsbf. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsbf. lia. }
assert (HdisS : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ (res <= a < res + req_size 480)).
{ intros a Ha Hb. unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. change (req_size 480) with 480 in *. lia. }
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
assert (AG : forall n, (n < 33)%nat -> ew Ed n = ew E n) by (intros n Hn; apply AGd; unfold AT_FL; lia).
assert (Ed60 : ew Ed 60 = Z_to_bv 64 (d_A cx)) by (subst Ed; unfold d_env; rewrite ew_havoc_old by (cbv; lia); exact E60).
assert (Ed516 : ew Ed 516 = Z_to_bv 64 (d_FB cx)) by (subst Ed; unfold d_env; rewrite ew_havoc_old by (cbv; lia); exact E516).
assert (Ed529 : ew Ed 529 = Z_to_bv 64 (shadow_addr (d_FB cx))) by (subst Ed; unfold d_env; rewrite ew_havoc_old by (cbv; lia); exact E529).
assert (Ed530 : ew Ed 530 = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))) by (subst Ed; exact (d_env_fl cx E (pc_vals regs))).
assert (E2v : ew E 2 = Z_to_bv 64 (d_S cx)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E32v : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact E32.
clear AGd.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
  ltac:(idtac; keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2
    ltac:(first [apply HdisF; change (fs_frame_bytes DFRAME_CLASS) with 4096 in *; lia | apply HdisS; lia])
    ltac:(replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia; apply HSHpres2; lia)).
pose proof HS as HS2k.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (E2 := Ev) in * end.
change (req_size 480) with 480 in Hrceil.
assert (Hres64 : res < 2 ^ 64) by (pose proof asan_consts as (Ca & _); lia).
assert (Hu : U E2 (SOff 567 0) = res).
{ unfold U. pose proof (st_ok_pi_restrict_reg (w_H W2) E2 _ _ 10%bv HS) as R. cbn [ms_regs mkst] in R.
  match type of R with context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v in R end.
  rewrite <- R, Ha0. unfold w64. apply unsigned_lit_small. lia. }
pose (BR := paj_branch (fx := fq) (PI := PI)).
psrr_branch_pi RUNP BR HS.
2: { exfalso.
     rewrite branch_ne_U, Hu, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
     apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia. }
norm_ss HS.
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
rename ms into ms1. rename mat into mat1. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
paj_run_to_shc RUNTOP HS HJ2 0x728.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
  [ reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia | cbn [YP09.r_whi]; unfold MFRAME in *; lia | ].
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx)));
  [ reflexivity | evalE AG
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
    exists DFRAME_CLASS, (c_fpos cx); split; [left; reflexivity|]; right;
    unfold in_zr; cbn [fst snd]; rewrite EFB2; change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia
  | ].
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  apply awr_ok_cons_ro; [clear; cbn; lia|].
  apply awr_ok_nil. }
rename ms into ms3. rename mat into mat3. rename HF into HF3. rename HFr into HFr3. rename HG into HG3.
set (md3' := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
assert (HC3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 (ms_mem ms3) md3' (k + 1))
  by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfrs2; exact Hfrs]]).
assert (HdE2 : d_E cx E2).
{ split; [|split; [|split; [|split; [|split]]]].
  - intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr. rewrite (AG n) by lia. exact (EE n r Hn).
  - rewrite (AG 32%nat) by lia. exact E32.
  - lazymatch goal with H : img_env _ _ E2 |- _ => exact H end.
  - exact Ed60.
  - exact Ed516.
  - exact Ed529. }
pose proof (p_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx dsh_loop ps_C4 ly2 S2 W2 md3' (k + 1) E2 _ ms3 HC3 HdE2 Ed530 HS ltac:(vm_compute; reflexivity)) as (Hfr4 & Hsh4).
assert (RF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr (ms_regs ms3) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W2) E2 _ ms3 r HS).
  assert (Hr2 : getr regs2 r = getr regs r).
  { rewrite <- (RG r Hr). cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [match goal with |- getr _ ?rr = _ => let z := eval vm_compute in (bv_unsigned rr) in exact (HP2 z ltac:(unfold acallee_saved; lia)) end|]). destruct Hr. }
  rewrite <- Hr2. pose proof (st_ok_pi_restrict_reg (w_H W2) E2 _ _ r HS2k) as Hk2. cbn [ms_regs mkst] in Hk2. rewrite Hk2.
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R23 : getr (ms_regs ms3) 23%bv = w64 res).
{ rewrite (st_ok_pi_restrict_reg (w_H W2) E2 _ ms3 23%bv HS).
  pose proof (st_ok_pi_restrict_reg (w_H W2) E2 _ _ 10%bv HS2k) as Hk2. cbn [ms_regs mkst] in Hk2. rewrite <- Ha0, Hk2.
  f_equal; vm_compute; reflexivity. }
assert (Kb : forall x, d_obj cx OOUR <= x < d_obj cx OOUR + 6 -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) (ms_mem ms1) x).
{ intros x Hx. unfold d_obj, dobj_off in Hx. destruct HK as (_ & _ & _ & K4 & _). apply (K4 DFRAME_CLASS (c_fpos cx) x Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - apply HdisF. lia. }
assert (Kc : forall x, d_obj cx OOUR <= x < d_obj cx OOUR + 6 -> aview SEGS (w_H W2) (ms_mem ms3) x = aview SEGS (w_H W2) mem2 x).
{ intros x Hx. unfold d_obj, dobj_off in Hx. apply aview_eq_of. apply HFr3. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Ed60, ?Ed529 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
    unfold shadow_addr, SHADOW_OFF in Hr; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFBapp; lia|]).
  destruct Hin. }
assert (Hour4 : garr8 SEGS (rd W2 (ms_mem ms3)) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))).
{ apply (pc_garr8_aview (w_H W) (w_H W2) mem3 (ms_mem ms3)); [|exact Hour].
  change (length (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))) with 6%nat. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  intros x Hx. rewrite (Kc x Hx), (Kb x Hx), (Ka x Hx). reflexivity. }
assert (Hbl4 : d_blocks B cx res [] ly2 S2).
{ split; [|split; [|split]].
  - rewrite Eab2, Hab. cbn [app]. change HUNT_SIZE with 480. apply Permutation_sym, Permutation_cons_append.
  - apply Forall_cons; [|apply Forall_nil]. change HUNT_SIZE with 480. intros Hinb. rewrite <- Hab in Hinb.
    apply in_split in Hinb as (l1 & l2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (res, 480) (res, 480) l1 l2 [] HAR2
      ltac:(rewrite Eab2, El, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size 480) with 480 in Hd. lia.
  - rewrite (blocks_bytes_bsum B ly2 S2), Eab2, bsum_app, Hab, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). cbn. change HUNT_SIZE with 480. lia.
  - apply Forall_cons; [|apply Forall_nil]. change HUNT_SIZE with 480. cbn [fst snd]. exact (blk_off_imgP B _ _ _ _ _ _ _ HAR2 Hnew). }
pose proof (st_ok_pi_restrict_mkst (w_H W2) E2 _ ms3 HS eq_refl) as Hms. cbn [ss_pc] in Hms.
apply SRr_ret. exists res. unfold pro_C4, d_at.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
exists fq, ly2, S2, (ms_regs ms3), (ms_mem ms3), md3', (k + 1), 0.
split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]. split; [exact Hf0|].
split; [exact Hbase|]. split; [exact HJ2|]. split; [rewrite Hfrs2; exact Hfrs|].
split; [unfold EV_PRO; lia|]. split; [unfold EV_PRO; lia|].
split; [rewrite MT_TRIV; exact I|]. split; [unfold ACC_PRO; rewrite MT_TRIV; cbn; lia|].
split; [exact Hcan0|]. split; [|split; [exact Hfr4 | split; [exact Hbl4 | exact Hour4]]].
destruct HrC3 as ((Hsp0 & Hgp0 & Htp0 & H80 & H90 & H180 & H200 & H220 & H240 & H250 & H260) & H190 & H210 & H270).
split; [|exact R23].
unfold p_rC3, p_rbase, spZ.
rewrite !RF by (cbv; tauto).
unfold spZ in Hsp0.
repeat split; assumption.
Qed.
End h.
End f.
End d.
