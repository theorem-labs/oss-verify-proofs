(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Segment lemma cs_S0 of check_step's asan walk (a Theorem Labs lane, 2026-10-29), proved against the cut statement of
   lib/A/P_check_step_cut.v. Rule 24 is met: this file proves one segment of the walk, not the function; the callees
   are lemmas or Section hypotheses.

   Segment S0 of the ASan walk of check_step in fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026): 0x8319c .. 0x832fc.
   prologue, UAR-flag and shadow-base loads, fake-frame decision (the real-stack arm excluded by the UAR flag = 1 from al_const and by SMP with the frames bound), __asan_stack_malloc_2(224) through aj_stack_malloc_atS (A/Prog/YC85.v:292), frame setup by P_check_step_frame.frame_setup at class 2, frame header, frame poison. Donor: cgif_file_fuzzer A/ACk1.v:111-283 (ng_mainX, class 1).
   Pre: the cut state at its first pc; post: cs_st1 at the next cut pc
   (P_check_step_cut.v). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_frame P_check_step_cut P_check_step_S0_aux.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC81 YC45 SceneACjr ACj1 SceneACja.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* The extent goals of the own frame and its shadow against the walk's regions, from one packed hypothesis BND:
   the bounds of sp (astk_ok), of the fake frame (frames_bounds, frm_off_imgP, F 32-aligned) and of the four image
   objects. *)
Local Ltac cs_djtac BND :=
repeat split; revert BND; clear; unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB; intros; lia.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Section h.
Variable B : asyms.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* relocated laws and the glue's bindings (cgif A/ACk1.v:64-74, :82; ScenePaLib.v:307, SceneFrame.v:96). *)
(* LAWS and SMP are theorems, not hypotheses (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803) and
   the model law ml_stack_malloc_progress (YG0d.v:520-521). The UAR flag reads 1 in every AR state by
   al_const (AR_const_law, YG0d.v:461-467), so no flag hypothesis is taken. *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* relocated cgif_file_fuzzer A/AF0u.v:514 stack_malloc2_contract (relocated by two Theorem Labs lanes). *)
Hypothesis ASM2 : astack_malloc_realizes SEGS B CS_CID.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* The shadow span of the symbolic runs: shadow base SB = SHADOW_OFF (atom 32) and the 2^44-byte shadow above it. *)
Definition CSBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma cs_S0 : CS_S0_stmt SK B.
Proof.
unfold CS_S0_stmt.
(* frame_setup is a lemma of P_check_step_frame.v, proved there for every cid and n. `first [...]` accepts it with or
   without the Section's SK as an argument, so this proof is insensitive to that detail of the frame file. *)
assert (FS : forall segs val B0 cid n, frame_setup_stmt segs val B0 cid n) by (first [exact (frame_setup SK) | exact frame_setup]).
intros ly S W regs mem md ch blk body k b HP.
pose proof HP as (HPRE & Hal32 & Htop32 & Hfr7 & HROD & H10 & H11 & H12 & Hk & HFO & Hbody & Hlen & Hbb & Hblk & Hev & Hlive).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_scene)) as HBLO.
pose proof (cs_entry B TL TLF ly S W regs mem md ch HPRE Hal32) as HS.
pose proof (ajournal_init SEGS B TCHECK_STEP_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
remember (Eimg (Ereg regs cs_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 blk) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 body) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 k) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs cs_extra 0)).
img_factsF E. img_hull_factsF.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
unfold cfg_at, A_check_step. change (w64 (BASE + AF_check_step)) with (Z_to_bv 64 (BASE + AF_check_step)).
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) mem).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK CSBspan. { awrFL AG 0 0 EFA0. }
clear_frames.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm2 B TLF).
pose proof (count_cid_le_length 2 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 2 ASM2 ltac:(lia) W (ms_regs msX) (ms_mem msX) TCHECK_STEP_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-128) _ HJ) end.
- unfold spZ at 1. rewrite R2. evalE AG.
- reflexivity.
- lia.
- rewrite FFS, Hes; lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- change (fs_frames 2) with 4096. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJc & (fS2 & ES2)).
rewrite Hes in HK. replace (spZ regs + -128 - 4096) with (spZ regs - 4224) in HK by lia. replace (spZ regs + -128) with (spZ regs - 128) in HK by lia.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4]%nat AG
ltac:(idtac; keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
clear HEv.
pose proof (conj Hslo (conj Hshi (conj H47 (conj Hceil (conj Hstk0 (conj C1 (conj HF4096 (conj HFceil (conj HFhigh
(conj HFhigh_img (conj HFq (conj HF8 (conj HF8lo (conj HF8hi (conj Hob241 (conj Hob242 (conj Hob257 (conj Hob258 FFS)))))))))))))))))) as BND.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
assert (DJ1 : all_disjoint Ev (fframe_region 516 528 2 []) (ss_mem ssv));
[ let rs2 := eval vm_compute in (ss_mem ssv) in change (all_disjoint Ev (fframe_region 516 528 2 []) rs2);
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2) with 256; rewrite RF; evalE AG; cs_djtac BND | ];
assert (DJ2 : all_disjoint Ev (fshadow_region 529 2 0 32 (fzero_chunks 4)) (fframe_region 516 528 2 [] :: ss_mem ssv));
[ let rs2 := eval vm_compute in (ss_mem ssv) in change (all_disjoint Ev (fshadow_region 529 2 0 32 (fzero_chunks 4)) (fframe_region 516 528 2 [] :: rs2));
cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2 / 8) with 32; change (fs_frame_bytes 2) with 256; rewrite RF, E529; evalE AG; cs_djtac BND | ];
pose proof (FS SEGS VAL B 2 256 LAWS W Ev ssv msv md2 ly S2 fpos 516%nat 528%nat 529%nat 32%nat 4%nat 0 32 HS HAR2 Hfin2
RF E528 ltac:(rewrite E32'; reflexivity) ltac:(rewrite E529; reflexivity) Hflag ltac:(change (fs_frame_bytes 2) with 256; lia) eq_refl Hz
ltac:(apply Z.leb_le; reflexivity) ltac:(lia) ltac:(apply Z.leb_le; reflexivity) eq_refl eq_refl DJ1 DJ2) as HS3 end.
clear HS DJ1 DJ2. rename HS3 into HS. unfold frame_ss, fzero_chunks in HS. norm_ss HS.
paj_run_to_shc RUNTOP HS HJ2 0xa84. { awrFL AG fpos F EFA0. }
clear_frames.
destruct (FFL ly S2 W mem2 md2 2 fpos HAR2 Hfin2) as (_ & _ & _ & (HFL4096 & _ & HFLceil)). fold FL in HFL4096, HFLceil.
assert (AG2 : forall n : nat, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))).
{ intros n Hn. apply EE. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HRstk;
let i2 := idx_of_base rs 516%nat in let i2 := eval vm_compute in i2 in
let r2 := eval vm_compute in (nth i2 rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx i2 r2 HS ltac:(vm_compute; reflexivity)) as HRfr;
assert (Usp5 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
cbn [ms_mem restrict] in HRstk, HRfr.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msF) =>
assert (HFW : rdword (aview SEGS (w_H W) (ms_mem msF)) (F + 256 - 8) = Some FL);
[ replace (F + 256 - 8) with (F + 248) by lia; apply rdword_of_val_mem; [| lia];
eapply (field_of_region Ex _ 516 F _ _ _ _ _ 248 8 (SOff 528 0) FL HRfr);
[ rewrite RF; apply unsigned_lit_small; lia | cbn; tauto | cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia ] | ];
assert (HSV : cs_saved regs (aview SEGS (w_H W) (ms_mem msF)));
[ intros j Hj; unfold cs_saved_regs;
do 13 (destruct j as [|j]; [
lazymatch goal with |- rdword _ (spZ regs - 8 - 8 * Z.of_nat ?jj) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth ?jj ?l 0)))) =>
let od := eval vm_compute in (-8 - 8 * Z.of_nat jj) in
let rr := eval vm_compute in (nth jj l 0) in
let nn := eval vm_compute in (Z.to_nat rr) in
replace (spZ regs - 8 - 8 * Z.of_nat jj) with (spZ regs + od) by lia;
change (nth jj l 0) with rr;
apply (cs_slot Ex (w_H W) (ms_mem msF) _ _ _ _ _ (spZ regs) od nn (Z_to_bv 5 rr) regs HRstk Usp5 ltac:(cbn; tauto));
rewrite (AG nn) by lia; apply AG2; lia end | ]); lia | ];
pose proof (st_ok_pi_restrict_reg Hh Ex ssx msF 11 HS) as Q11;
let e := eval vm_compute in (sr_get (ss_regs ssx) 11) in change (sr_get (ss_regs ssx) 11) with e in Q11 end.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (16%bv : bv 5) Q16. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (Rblk : 0 <= blk < 2 ^ 64) by (clear - Hflo Hfhi Hf4096 Hfceil C1; unfold CS_BLK_LEN in *; lia).
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdd |} _ =>
apply SRr_ret; exists ly, S2, rg, mm, mdd, fpos end.
split; [unfold CS_PC1, A_check_step, AF_check_step, w64; replace (BASE + 0x924 + 0x160) with (BASE + 2692) by lia; reflexivity|].
split; [exact HP|]. split.
{ unfold cs_frame. change CS_CID with 2.
split; [exact HJ2|]. split; [exact Eab|]. split; [exact HFW|]. split; [exact HSV|].
split; [rewrite Q2, (AG 2%nat), Usp by lia; unfold w64, CHECK_STEP_FRAME; f_equal; lia|].
split; [rewrite Q3, (AG 3%nat) by lia; exact E3|].
split; [rewrite Q4, (AG 4%nat) by lia; exact E4|].
split; [rewrite Q8; rewrite ?(AG 2%nat) by lia; unfold w64; rewrite <- Usp, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite Q18, RF; reflexivity|].
split; [rewrite Q25, E529; unfold w64, SB; reflexivity|].
split; [rewrite Q26, RF; reflexivity|].
rewrite Q27, E32'; reflexivity. }
split; [rewrite Q9, (AG 2%nat), Usp by lia; unfold w64, CHECK_STEP_FRAME; f_equal; lia|].
split; [rewrite Q19, (AG 10%nat) by lia; exact E10|].
split; [rewrite Q20, (AG 12%nat) by lia; exact E12|].
split; [rewrite Q16, (AG 11%nat) by lia; exact E11|].
rewrite Q11, denot_lit_U, U_srl3, (U_atom _ 10 blk); [reflexivity | rewrite (AG 10%nat) by lia; exact E10 | exact Rblk].
Qed.
End h.
End f.
End d.
Print Assumptions cs_S0.
