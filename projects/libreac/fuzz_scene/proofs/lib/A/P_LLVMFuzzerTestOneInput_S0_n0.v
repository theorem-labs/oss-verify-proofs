(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S0 of the ASan walk of libreac/fuzz_scene's LLVMFuzzerTestOneInput
   on the input lengths n = 0: `s0_case_n0`.  Split out of lib/A/P_LLVMFuzzerTestOneInput_S0.v
   (a working branch 67f0c71b18d): the proof is that file's walk to its case split (lines 624-899)
   and its block for n = 0 (lines 902-1057).  New: the premise Hc0 is hidden from lia (`rs_hold`) until the
   case starts, and the steps marked `rs_hide_all` / `rs_hold` hide context facts from lia where no goal
   needs them.  P_LLVMFuzzerTestOneInput_S0.v assembles scene_seg_S0 from the twelve cases; the leaves, the
   Ltacs and the Section premises are P_LLVMFuzzerTestOneInput_S0_kit.v's. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import
PaRun PaShadow PaStep PaJournal SceneSyms SceneList SceneAddr SceneCode ScenePa ScenePaLib
SceneBase SceneFrame SceneRo SceneImg YC1g YC1h YC45 YC85 YC88 YC4b YC81 YC1i ACbf SceneACja SceneACjr ACj1.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import SceneAsanTop.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx J_StackSz P_check_step_frame P_LLVMFuzzerTestOneInput_seg.
(* A Theorem Labs lane (at d1cfd1a8204): the two caller-side journal steps J_StackSz.v states, PROVED. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import J_StackSzPf.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_S0_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* gate 6h / the sink widening (a Theorem Labs lane, 2026-10-29 01:57Z): the sink head is a Section variable whose type is written
   fully qualified (lib/U/Reusable/YI16.v has the same short name), passed BY NAME to every term that takes it.  The
   composition instantiates it with scene's own head (lib/A/P_LLVMFuzzerTestOneInput.v:150-151, ofl_head 0x5f6e90). *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head). #[local] Existing Instance SK.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Notation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).

Section e.
Variable B : asyms.
Hypothesis TL : PALib (L := scene_listing) (PI := PI_scene) B.
Hypothesis TLF : PALibF (L := scene_listing) (PI := PI_scene) B.

(* ---- the runtime contracts and framework laws this segment needs.  Each is the hypothesis of the same
   name in lib/A/P_LLVMFuzzerTestOneInput.v, with the owner that file names. ---- *)
(* A Theorem Labs lane: the glue's instances. *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.
(* A Theorem Labs lane (968ea35e8f5 proves it; this lane TAKES it). *)
Hypothesis stack_malloc_8_sz : astack_malloc_sz_realizes SEGS B PC_STACK_MALLOC_8 CID8.
(* Two Theorem Labs lanes: __asan_set_shadow_f8. *)
Hypothesis ASHF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
(* AR_laws is a theorem (Reusable/YG0q.v:803), not a hypothesis (ENTRY-REVIEW.md R4). *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the two caller-side journal steps of lib/A/J_StackSz.v, proved by a Theorem Labs lane in lib/A/J_StackSzPf.v. *)
Let AJSM8 : @aj_stack_malloc_sz_at_stmt fx rc SK SEGS B :=
@aj_stack_malloc_sz_at fx rc SK SEGS B LAWS (pa_segs_low (L := scene_listing)) (pal_env B TL) ML
(ml_stack_malloc_progress _ ML).
Let AJSH : @aj_set_shadow_at_stmt fx rc SK SEGS B :=
@aj_set_shadow_at fx rc SK SEGS B LAWS (pa_segs_low (L := scene_listing)).

(* gate 6h: the sink head is passed BY NAME to every term whose Section left it implicit. *)
Let RUN := @paj_run fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNTO := @paj_run_to fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNP := @SRr_run_pi_AJ fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNC := @SRr_run_pi_AJ_call fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let RUNTOP := @SRr_run_to_pi_AJ fx rc SK scene_listing PL_scene PI_scene B LAWS.
Let BR := paj_branch (PI := PI_scene).

(* the kit's lemmas that take Section variables, under their short names *)
#[local] Notation s0_entry := (P_LLVMFuzzerTestOneInput_S0_kit.s0_entry B TL TLF).
#[local] Notation s0_c1 := (P_LLVMFuzzerTestOneInput_S0_kit.s0_c1 SK B).
#[local] Notation s0_byte_now := (P_LLVMFuzzerTestOneInput_S0_kit.s0_byte_now SK B).

(* ---- the walk's constants.  The two read-only-window bindings are a Theorem Labs lane's text (03:35Z ruling), verbatim
   in every segment lane; the composition discharges all five from the record it builds. ---- *)
Variable WK : swalk.
Hypothesis HWRLO : sw_rlo WK = pa_relro_lo.
Hypothesis HWRHI : sw_rhi WK = pa_relro_hi.
(* S0 starts at the contract's entry, reads the n = 0 argument and calls the class-8 side-stack allocator:
   P_LLVMFuzzerTestOneInput.v's HA_LLVMF, HA_EMPTY (0x5d5e60) and HSTK (LLVMF_SPDROP + ASTACK <= LLVMF_STK) in terms
   of WK. *)
Hypothesis HWENT : sw_entry WK = BASE + AF_LLVMFuzzerTestOneInput.
Hypothesis HWEMP : 4096 <= sw_empty WK <= 140737479966720.
Hypothesis HWSTK : 240 + ASTACK <= sw_stk WK.

Lemma s0_case_n0 : @s0_case_stmt fx rc SK B WK (fun n => n = 0).
Proof.
pose proof HWENT as HENT. pose proof HWEMP as HEMP. pose proof HWSTK as HSTK.
assert (HWKro : forall a, sw_rlo WK <= a < sw_rhi WK -> in_img SEGS a)
by (intros a Ha; rewrite HWRLO, HWRHI in Ha; exact (pa_relro_img a Ha)).
unfold s0_case_stmt.
intros ly S W regs mem md p n T POST Hc0 HPRE0 KONT. apply rs_hide in Hc0.
unfold sc_base0 in HPRE0.
destruct HPRE0 as (HPRE & Hra & Hp & Hn & Hpn & Hfr0 & Hev & Hlive & HROD & HSINK & HFD & HFS & HMOK).
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn' _]]; lia).
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof (pa_segs_low (L := scene_listing)) as Hsegs.
pose proof pa_wx as Hwx. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HpR : 4096 <= p /\ p + n <= 140737479966720).
{ destruct Hpn as [[Hn0 HpE] | [Hnr Hin]].
  - rewrite HpE, Hn0. clear - HEMP. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos n ltac:(clear - Hnr; lia)) as [_ Hrq]. clear - Hp4096 Hpceil Hrq C1. lia. }
destruct HpR as (Hp4096 & Hpceil).
destruct (s0_entry (sw_stk WK) ly S W regs mem md p n HPRE ltac:(unfold ASTACK in HSTK; clear - HSTK; lia) Hp Hn Hp4096 Hpceil Hn26) as [HS SHOK].
pose proof (@ajournal_init rc SK SEGS B (sw_stk WK) [] ly S W regs mem md [] HPRE) as HJ.
remember (ELV regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
by (intros k r Hk; subst E; unfold ELV; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite (EE 10%nat 10%bv eq_refl); exact Hp).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (rewrite (EE 11%nat 11%bv eq_refl); exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
by (subst E; unfold ELV; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite HENT. unfold cfg_at. change (w64 (BASE + AF_LLVMFuzzerTestOneInput)) with (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)).
assert (AG : forall k, (k < 33)%nat -> ew E k = ew E k) by (intros; reflexivity).
assert (EFA0 : forall c q, frame_addr ly c q = frame_addr ly c q) by reflexivity.
img_factsF E. img_hull_factsF.
(* the prologue and the 13 saves, to just after `andi sp,sp,-32` (0x828b8; the next pc is 0x828bc). *)
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK LVspan 0x44. { awrFL_with ltac:(idtac; s0_awr_stk HSTK AG) AG 0 0 EFA0. }
upd_aboveW_init HFr AG HUP. clear_frames. s0_md.
(* sp1 = (sp - 224) & -32 becomes atom 60; the machine-stack region keeps only the 13 saved words
   [sp0 - 104, sp0), and region 60 is the spill area [sp1, sp1 + 0x78) the function writes. *)
assert (E2 : ew E 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
set (sp1 := 32 * ((spZ regs + -224) / 32)).
destruct (sp1_facts (spZ regs + -224) ltac:(unfold ASTACK in HSTK; clear - Hceil Hslo Hstk0 HSTK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 240 <= sp1 <= spZ regs - 224) by (clear - Hsp1r; lia). clear Hsp1r.
assert (Hsp1eq : sp1 = 32 * ((spZ regs - 224) / 32))
by (unfold sp1; replace (spZ regs - 224) with (spZ regs + -224) by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-224) ltac:(try (rewrite (AG 2%nat) by lia); rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(unfold ASTACK in HSTK; clear - Hceil Hslo Hstk0 HSTK C1; lia) ltac:(clear - Hshi H47; lia)
ltac:(unfold ASTACK in HSTK; clear - Hceil Hslo Hstk0 HSTK C1 Hshi H47; lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2;
rewrite unsigned_lit_small by (unfold ASTACK in HSTK; clear - Hsp1 Hceil Hslo Hstk0 HSTK C1 Hshi H47; lia); reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60,
unsigned_lit_small by (unfold ASTACK in HSTK; clear - Hsp1 Hceil Hslo Hstk0 HSTK C1 Hshi H47; lia);
change (2 ^ 5) with 32; unfold ASTACK in HSTK; clear - Hsp1 Hsp1al Hceil Hslo Hstk0 HSTK C1 Hshi H47; lia)) as HS3 end.
clear HS; rename HS3 into HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 120 0 120 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by (unfold ASTACK in HSTK; clear - Hsp1 Hceil Hslo Hstk0 HSTK C1 Hshi H47; lia);
split; [unfold ASTACK in HSTK; clear - Hsp1 Hceil Hslo Hstk0 HSTK C1; lia|];
split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; unfold ASTACK in HSTK; clear - Ho Hsp1 HSTK; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; repeat split; zone_lia)) as HS3 end.
clear HJpres. clear HS; rename HS3 into HS. norm_ss HS.
reshok HS.
(* the GOT reads, the use-after-return flag (al_const: 1) and the call of __asan_stack_malloc_8 (0x828ec). *)
hei_havoc HS; paj_run_tok RUN HS HJ SHOK LVspan. { awrFL_with ltac:(idtac; s0_awr_stk HSTK AG) AG 0 0 EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG. s0_md.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
prreg HS (10%bv : bv 5) Ra0.
pmkst HS. rewrite s0_sm8.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (AJSM8 PC_STACK_MALLOC_8 CID8 stack_malloc_8_sz ltac:(unfold CID8; lia)
  W (ms_regs msX) (ms_mem msX) (sw_stk WK) (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ 9408 HJ) end.
  - unfold spZ at 1. rewrite R2. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - clear - Hsp1; lia.
  - rewrite Hes; unfold ASTACK in HSTK; clear - Hsp1 HSTK; lia.
  - rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite Ra0. unfold w64. evalE AG.
  - unfold CID8. change (fs_frame_bytes 8) with 16384. clear; lia.
  - reflexivity.
  - rewrite Hfr0. unfold CID8. clear. first [ vm_compute; reflexivity | cbn; lia ]. }
cbv beta. clear R2 R3 R4 R1 Ra0 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
unfold CID8 in *.
rewrite Hes in HK. replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by (clear; lia).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1;
  [ clear - Ha Hceil Hslo Hstk0 HSTK C1; unfold ASTACK in *; lia | clear - Ha Hsp1; lia ]. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (8, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 8 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 8 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 8) with 16384 in *.
set (F := frame_addr ly 8 fpos) in *. set (FL := flag_addr ly 8 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [ s0_kept_stk HK HJ2 AG HSTK
| keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail) ]).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (AG 32%nat) by lia; exact E32) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E516 : ew Ev 516 = Z_to_bv 64 F) by (rewrite <- RF; reflexivity) end.
(* A Theorem Labs lane's PROVED frame_setup (lib/A/P_check_step_frame.v) at class 8, size 9408: it adds the three frame
   atoms, the shadow alias and the two frame regions.  k = 0 zero chunks: the walk writes every shadow byte of
   [shF, shF + 1176) itself and reads none of them back through the region. *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(clear; lia)); clear - HFal H; lia).
assert (HF8 : F / 8 = 4 * (F / 32))
by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by (clear; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; clear - HF4096; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; clear - HFceil C1; lia).
assert (HFhi2 : F + 16384 <= 2147450880 \/ 17594333495296 <= F)
by (clear - HFhigh; unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh; lia).
assert (HFshdisj : 2147450880 + F / 8 + 2048 <= F \/ F + 16384 <= 2147450880 + F / 8)
by (clear - HFhi2 HFq HF8 HF8lo HF8hi HF4096; lia).
assert (HFmod8 : F mod 8 = 0).
{ pose proof HFal as Hm. apply Z.mod_divide in Hm; [|clear; lia]. destruct Hm as [q Hq].
  rewrite Hq. replace (q * 32) with ((q * 4) * 8) by (clear; lia). apply Z_mod_mult. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
pose proof (frame_setup SEGS VAL B 8 9408 LAWS W Ev ssx msX md2 ly S2 fpos 516%nat 528%nat 529%nat 32%nat 0%nat 0 1176
HS HAR2 Hfin2 E516 E528 E32' E529 Hflag
ltac:(change (fs_frame_bytes 8) with 16384; clear; lia) ltac:(clear; reflexivity) Hz
ltac:(clear; cbn; lia) ltac:(clear; lia) ltac:(change (fs_frame_bytes 8 / 8) with 2048; clear; lia)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E516; evalE AG; change (fs_frame_bytes 8) with 16384; unfold SB;
unfold ASTACK in HSTK; repeat split; s0_disj)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E516, E529; evalE AG; change (fs_frame_bytes 8) with 16384; change (fs_frame_bytes 8 / 8) with 2048; unfold SB;
unfold ASTACK in HSTK; repeat split; s0_disj)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* the frame header (0x82928-0x82954), the 28 inline shadow stores and the call of __asan_set_shadow_f8
   (0x829e0).  The `bnez s7` at 0x82900 is decided by the frame atom's range (F >= 4096). *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; s0_awr_stk HSTK AG) AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG. s0_md.
(* __asan_set_shadow_f8(shF + 0x1c, 1113) at 0x829e0.  Across it the frame-shadow region keeps only its first
   0x1c bytes (the 28 inline stores); the call writes [0x1c, 0x475). *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (s0_trunc 529 28 rs) in
pose proof (st_ok_submem SEGS Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
aconstsF HJ2 Kgot3 Kcell3 Kguar3 Kuar3.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (AJSH (SIGMA SS___asan_set_shadow_f8) 0xf8 ASHF8 W (ms_regs msX) (ms_mem msX) (sw_stk WK) (spZ regs) [] ly S W mem md
  [(8, fpos)] ly S2 _ 0 8 fpos (SB + F / 8 + 28) 1113 (sp1 - spZ regs) _ HJ2) end.
  - left; reflexivity.
  - rewrite Ra0. unfold w64. evalE AG.
  - rewrite Ra1. unfold w64. evalE AG.
  - clear; lia.
  - fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. clear; lia.
  - fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 8 / 8) with 2048. clear; lia.
  - unfold spZ at 1. rewrite Rsp. evalE AG.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - clear - Hsp1; lia.
  - rewrite Hes; unfold ASTACK in HSTK; clear - Hsp1 HSTK; lia.
  - rewrite Rgp. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity]. }
cbv beta. clear Ra0 Ra1 Rra Rsp Rgp Rtp.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HSH3 & HKO3 & HPR3).
assert (HUP3 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). apply HKO3; [clear - Ha Hslo Hceil C1 Hstk0; lia |].
  unfold SB, ASTACK in *. clear - Ha HF8hi Hceil Hslo Hstk0 HSTK C1. lia. }
clear HUP. rename HUP3 into HUP.
aconstsF HJ3 Kgot4 Kcell4 Kguar4 Kuar4.
reseat HS HJ3 HP3 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [ s0_kept_sh HKO3 HPR3 AG
| keptFL HK HJ3 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 ltac:(idtac; fail) ltac:(idtac; fail) ]).
(* the rest of the frame shadow, [0x1c, 0x498): written by the call and by the 35 stores after it. *)
destruct (al_frames _ _ LAWS _ _ _ _ _ 8 fpos (proj1 HJ3) Hfin2) as (_ & _ & _ & HFSpres3).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 529%nat) 1141 1176 1141 1176 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
let o := fresh "o" in let Ho := fresh "Ho" in let Hp := fresh "Hp" in
intros o Ho; apply (apresent_writable SEGS);
pose proof (proj1 (HFSpres3 o ltac:(change (fs_frame_bytes 8 / 8) with 2048; lia))) as Hp;
unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp; fold F in Hp; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB; unfold ASTACK in HSTK; repeat split; s0_disj)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* the 35 stores 0x829ec-0x82a74, the dead early return `bnez a1` 0x82a78 (a1 = n >> 26 = 0), to the
   `beqz s5` of the input parse at 0x82a80. *)
hei_havoc HS; paj_run_shc RUNP RUNC HS HJ3. { awrFL_with ltac:(idtac; s0_awr_stk HSTK AG) AG fpos F EFA0. }
s0_win HFr (fun a => (SB + F / 8 <= a < SB + F / 8 + 28) \/ (SB + F / 8 + 1141 <= a < SB + F / 8 + 1176) \/
(F <= a < F + 16384) \/ (sp1 <= a < sp1 + 120) \/ (spZ regs - 104 <= a < spZ regs)) KN AG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SHf8 : forall o, 28 <= o < 1141 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + o) = Some 248)
by (intros o Ho; rewrite KN;
[ replace (SB + F / 8 + o) with (SB + F / 8 + 28 + (o - 28)) by lia; apply HSH3; lia
| unfold SB in *; lia
| cbv beta; unfold SB in *; lia ]) end.
clear KN.
upd_aboveW HUP HFr AG. clear HF HFr HG. s0_md.
(* the early return `bnez a1` 0x82a78 with a1 = n >> 26: n < 2 ^ 26, so it is not taken. *)
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ne_U in Hc. rewrite U_SAlu, !U_SLit in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom _ 11 n) in Hc by (first [rewrite (AG 11%nat) by lia; exact E11 | exact E11 | lia]).
  change (Z.land (zcanon 26) 63) with 26 in Hc.
  rewrite Z.shiftr_div_pow2 in Hc by lia. rewrite (Z.div_small n (2 ^ 26)) in Hc by lia.
  vm_compute in Hc. discriminate Hc. }
clear Hc.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E11c : ew Ev 11 = Z_to_bv 64 n) by (rewrite (AG 11%nat) by lia; exact E11) end.
(* the whole frame shadow [shF, shF + 1176) as the poison left it, read off the two shadow regions and the
   set-shadow post; then the shadow regions leave the symbolic state (no checked run may write the shadow). *)
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SHtr : forall o, 0 <= o < 28 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + o) = Some (s0_sh0 o))
by (intros o Ho;
assert (Ho' : o = 0 \/ o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7 \/ o = 8 \/ o = 9 \/ o = 10 \/ o = 11 \/ o = 12 \/ o = 13 \/
o = 14 \/ o = 15 \/ o = 16 \/ o = 17 \/ o = 18 \/ o = 19 \/ o = 20 \/ o = 21 \/ o = 22 \/ o = 23 \/ o = 24 \/ o = 25 \/ o = 26 \/ o = 27) by lia;
repeat (destruct Ho' as [-> | Ho']); [..| subst o]; s0_chunk_at HS 1%nat AG);
assert (SHtl : forall o, 1141 <= o < 1176 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + o) = Some 243)
by (intros o Ho;
assert (Ho' : o = 1141 \/ o = 1142 \/ o = 1143 \/ o = 1144 \/ o = 1145 \/ o = 1146 \/ o = 1147 \/ o = 1148 \/ o = 1149 \/ o = 1150 \/
o = 1151 \/ o = 1152 \/ o = 1153 \/ o = 1154 \/ o = 1155 \/ o = 1156 \/ o = 1157 \/ o = 1158 \/ o = 1159 \/ o = 1160 \/
o = 1161 \/ o = 1162 \/ o = 1163 \/ o = 1164 \/ o = 1165 \/ o = 1166 \/ o = 1167 \/ o = 1168 \/ o = 1169 \/ o = 1170 \/
o = 1171 \/ o = 1172 \/ o = 1173 \/ o = 1174 \/ o = 1175) by lia;
repeat (destruct Ho' as [-> | Ho']); [..| subst o]; s0_chunk_at HS 0%nat AG) end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SHV : forall o, 0 <= o < 1176 -> o <> 14 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + o) = Some (s0_shv o))
by (intros o Ho _; unfold s0_shv;
destruct (Z.ltb_spec o 28); [apply SHtr; lia|];
destruct (Z.ltb_spec o 1141); [apply SHf8; lia | apply SHtl; lia]) end.
clear SHtr SHtl SHf8.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (s0_drop 529 rs) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
unfold rs_hold in Hc0.
(* n = 0 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 11%nat (mkAF 0 0 0) HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (AG 11%nat) by lia; rewrite E11, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3; clear HS; rename HS3 into HS
end.
norm_ss HS.
prreg HS (21%bv : bv 5) R21.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (st_ok_pi_pin_reg' Ex ssx msx (21%bv : bv 5) 0 HS
ltac:(cbn [ms_regs restrict mkst]; rewrite R21; evalE AG; first [reflexivity | f_equal; lia]) eq_refl) as HS3 end.
clear HS R21; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E10n : ew Ev 10 = Z_to_bv 64 p) by (rewrite (AG 10%nat) by lia; exact E10);
assert (E32n : ew Ev 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (AG 32%nat) by lia; exact E32) end.
reshok HS.
(* the parse, to the mac unpoison store 0x82b1c *)
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK LVspan 0x2a4.
all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrFL_with ltac:(idtac; s0_awr_stk HSTK AG) AG fpos F EFA0 end).
s0_win HFr (fun a => (F <= a < F + 16384) \/ (sp1 <= a < sp1 + 120) \/ (spZ regs - 104 <= a < spZ regs)) KN AG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SHVn : forall o, 0 <= o < 1176 -> o <> 14 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + o) = Some (s0_shv o))
by (intros o Ho Hne; rewrite KN; [apply SHV; assumption | unfold SB in *; lia | cbv beta; unfold SB in *; lia])
end.
clear SHV; rename SHVn into SHV.
clear KN.
upd_aboveW HUP HFr AG. clear HF HFr HG. s0_md.
rebaseE HS AG HEv. clear HEv.
(* the mac unpoison store `sb a0,0xe(s3)` 0x82b1c, the only shadow write after the poison: cell 0xe := 6. *)
destruct (al_frames _ _ LAWS _ _ _ _ _ 8 fpos (proj1 HJ3) Hfin2) as (_ & _ & _ & HFSpresM).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 529%nat) 14 15 14 15 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
let o := fresh "o" in let Ho := fresh "Ho" in let Hp := fresh "Hp" in
intros o Ho; apply (apresent_writable SEGS);
pose proof (proj1 (HFSpresM o ltac:(change (fs_frame_bytes 8 / 8) with 2048; lia))) as Hp;
unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp; fold F in Hp; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB; unfold ASTACK in HSTK; repeat split; s0_disj)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS. clear HFSpresM.
hei_havoc HS; paj_run_to_sh RUNTOP HS HJ3 0x2b4. { awrFL_with ltac:(idtac; s0_awr_stk HSTK AG) AG fpos F EFA0. }
s0_win HFr (fun a => (F <= a < F + 16384) \/ (sp1 <= a < sp1 + 120) \/ (spZ regs - 104 <= a < spZ regs) \/ (a = SB + F / 8 + 14)) KN AG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SHVn : forall o, 0 <= o < 1176 -> o <> 14 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + o) = Some (s0_shv o))
by (intros o Ho Hne; rewrite KN; [apply SHV; assumption | unfold SB in *; lia | cbv beta; unfold SB in *; lia])
end.
clear SHV; rename SHVn into SHV.
clear KN.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SH14 : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 14) = Some 6) by (let i := s0_idx HS 529%nat in s0_chunk_at HS i AG) end.
upd_aboveW HUP HFr AG. clear HF HFr HG. s0_md.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (s0_drop 529 rs) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(* the 6-turn mac loop 0x82b2c-0x82b60: one checked input byte per turn while bytes remain. *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E10m : ew Ev 10 = Z_to_bv 64 p) by (rewrite (AG 10%nat) by lia; exact E10);
assert (E32m : ew Ev 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (AG 32%nat) by lia; exact E32) end.
clear E10n E32n. rename E10m into E10n. rename E32m into E32n.
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK LVspan 0x300.
all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrFL_with ltac:(idtac; s0_awr_stk HSTK AG) AG fpos F EFA0 end).
s0_win HFr (fun a => (F <= a < F + 16384) \/ (sp1 <= a < sp1 + 120) \/ (spZ regs - 104 <= a < spZ regs)) KN AG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SHVn : forall o, 0 <= o < 1176 -> o <> 14 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + o) = Some (s0_shv o))
by (intros o Ho Hne; rewrite KN; [apply SHV; assumption | unfold SB in *; lia | cbv beta; unfold SB in *; lia])
end.
clear SHV; rename SHVn into SHV.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (SH14n : aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + 14) = Some 6)
by (rewrite KN; [exact SH14 | unfold SB in *; lia | cbv beta; unfold SB in *; lia])
end.
clear SH14; rename SH14n into SH14.
clear KN.
upd_aboveW HUP HFr AG. clear HF HFr HG. s0_md.
rebaseE HS AG HEv. clear HEv.
(* ---- the cut C1 at 0x82b78 ---- *)
set (bs := fun i : Z => nth (Z.to_nat i) [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] 0).
assert (BS0 : bs 0 = 0) by reflexivity.
assert (BS1 : bs 1 = 0) by reflexivity.
assert (BS2 : bs 2 = 0) by reflexivity.
assert (BS3 : bs 3 = 0) by reflexivity.
assert (BS4 : bs 4 = 0) by reflexivity.
assert (BS5 : bs 5 = 0) by reflexivity.
assert (BS6 : bs 6 = 0) by reflexivity.
assert (BS7 : bs 7 = 0) by reflexivity.
assert (BS8 : bs 8 = 0) by reflexivity.
assert (BS9 : bs 9 = 0) by reflexivity.
assert (BS10 : bs 10 = 0) by reflexivity.
destruct (al_flag _ _ LAWS _ _ _ _ _ 8 fpos (proj1 HJ3) Hfin2) as (_ & _ & HFLapp & _).
fold FL in HFLapp. unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (HFLr : 0 <= FL < 2 ^ 64) by (clear - HFLapp C1; lia).
(* the C1 goals need no disjunction and no mod fact of the context: hide them all from lia (rs_hide_all, the kit). *)
rs_hide_all.
pmkst HS.
eapply (s0_c1 WK POST ly S W regs mem md p n T fpos S2 _ _ _ bs E (KONT fpos E) HROD HWKro HJ3
ltac:(rewrite Hfrs2, Hfr0; reflexivity) Eab Hbb2).
{ (s0_c8 HS AG 516%nat; [ (s0_den AG) | (exact HFLr) ]). }
{ intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12) by lia.
  repeat (destruct Hj' as [-> | Hj']); [..| subst j]; [
  (replace (spZ regs - 8 - 8 * 0) with (spZ regs + (-8)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 1%nat 1%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 1%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 1) with (spZ regs + (-16)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 8%nat 8%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 8%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 2) with (spZ regs + (-24)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 9%nat 9%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 9%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 3) with (spZ regs + (-32)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 18%nat 18%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 18%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 4) with (spZ regs + (-40)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 19%nat 19%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 19%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 5) with (spZ regs + (-48)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 20%nat 20%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 20%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 6) with (spZ regs + (-56)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 21%nat 21%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 21%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 7) with (spZ regs + (-64)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 22%nat 22%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 22%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 8) with (spZ regs + (-72)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 23%nat 23%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 23%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 9) with (spZ regs + (-80)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 24%nat 24%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 24%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 10) with (spZ regs + (-88)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 25%nat 25%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 25%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 11) with (spZ regs + (-96)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 26%nat 26%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 26%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ])
| (replace (spZ regs - 8 - 8 * 12) with (spZ regs + (-104)) by ring; s0_c8 HS AG 2%nat; [ (cbn [sv_denot]; rewrite ?Z.add_0_r; try evalE AG; try (rewrite (EE 27%nat 27%bv eq_refl)); try (rewrite !Z_to_bv_bv_unsigned); try reflexivity) | (pose proof (bv_unsigned_in_range 64 (getr regs 27%bv)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu) ]) ]. }
{ (exact SHV). }
{ (exact SH14). }
{ intros i Hi. assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  repeat (destruct Hi' as [-> | Hi']); [..| subst i]; [
  (rewrite BS0; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS1; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS2; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS3; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS4; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS5; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS6; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS7; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS8; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS9; split; [lia | split; [intros; lia | intros; reflexivity]])
| (rewrite BS10; split; [lia | split; [intros; lia | intros; reflexivity]]) ]. }
{ intros j Hj. assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
  repeat (destruct Hj' as [-> | Hj']); [..| subst j]; [
  (replace (frame_addr ly 8 fpos + 112 + 0) with (frame_addr ly 8 fpos + 112) by ring; replace (bs (5 + 0)) with 0 by reflexivity; eapply eq_trans; [s0_cb HS AG 516%nat | (first [reflexivity | cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; reflexivity])])
| (replace (frame_addr ly 8 fpos + 112 + 1) with (frame_addr ly 8 fpos + 113) by ring; replace (bs (5 + 1)) with 0 by reflexivity; eapply eq_trans; [s0_cb HS AG 516%nat | (first [reflexivity | cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; reflexivity])])
| (replace (frame_addr ly 8 fpos + 112 + 2) with (frame_addr ly 8 fpos + 114) by ring; replace (bs (5 + 2)) with 0 by reflexivity; eapply eq_trans; [s0_cb HS AG 516%nat | (first [reflexivity | cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; reflexivity])])
| (replace (frame_addr ly 8 fpos + 112 + 3) with (frame_addr ly 8 fpos + 115) by ring; replace (bs (5 + 3)) with 0 by reflexivity; eapply eq_trans; [s0_cb HS AG 516%nat | (first [reflexivity | cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; reflexivity])])
| (replace (frame_addr ly 8 fpos + 112 + 4) with (frame_addr ly 8 fpos + 116) by ring; replace (bs (5 + 4)) with 0 by reflexivity; eapply eq_trans; [s0_cb HS AG 516%nat | (first [reflexivity | cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; reflexivity])])
| (replace (frame_addr ly 8 fpos + 112 + 5) with (frame_addr ly 8 fpos + 117) by ring; replace (bs (5 + 5)) with 0 by reflexivity; eapply eq_trans; [s0_cb HS AG 516%nat | (first [reflexivity | cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; reflexivity])]) ]. }
{ (s0_c8 HS AG 60%nat; [ (s0_rc AG EE) | (try fold F; unfold SB in *; lia) ]). }
{ (s0_c8 HS AG 60%nat; [ (s0_rc AG EE) | (try fold F; unfold SB in *; lia) ]). }
{ (s0_c8 HS AG 60%nat; [ (s0_rc AG EE) | (try fold F; unfold SB in *; lia) ]). }
{ (s0_c8 HS AG 60%nat; [ (rewrite denot_lit_U; unfold w64; f_equal; s0_Ubytes; rewrite ?BS3, ?BS4; reflexivity) | (apply Z.mod_pos_bound; lia) ]). }
{ (prreg HS (2%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (3%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (4%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (8%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (9%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (23%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (19%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (26%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (25%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (27%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (15%bv : bv 5) R; rewrite R; clear R; s0_rc AG EE). }
{ (prreg HS (16%bv : bv 5) R; rewrite R; clear R; rewrite BS0; s0_rc AG EE). }
{ (s0_preg HS (24%bv : bv 5) R; rewrite R; clear R; rewrite denot_lit_U; unfold w64; f_equal; s0_Ubytes; rewrite ?BS1, ?BS2; reflexivity). }
{ (prreg HS (21%bv : bv 5) R; rewrite R; clear R; rewrite Z.min_l by lia; s0_rc AG EE). }
{ (prreg HS (22%bv : bv 5) R; rewrite R; clear R; rewrite Z.min_l by lia; s0_rc AG EE). }
{ (s0_preg HS (18%bv : bv 5) R; rewrite R; clear R; rewrite denot_lit_U; unfold w64; f_equal; s0_Ubytes; rewrite ?BS4; reflexivity). }
Qed.
End e.
End b.
