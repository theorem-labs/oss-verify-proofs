(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the entry segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0 ..
   0x8a61c), in the form of sup_resp's walk (cgif lib/A/AChf.v, flushFrame): the prologue, the realignment
   `andi sp,sp,-32`, the use-after-return flag (1: `beqz a2` falls through), the class-7 side-stack frame of
   __asan_stack_malloc_7 (not 0: `bnez s2` skips the real-stack fallback), the frame's header and shadow, the two
   shadow fills, up to the BODY cut (answer_s1.v AN_BODY_stmt). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_e.v, with its module paths, module names and numbers changed; 255 of its 346 lines of code are new or changed and 504 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, stage 1: the entry block 0x8a400 .. the call
   of record() at 0x8a534 (listing slots 4020-4097), then record's call and return to M1 (sup_add_s1b.v).

   0x8a400-0x8a43c: the 128-byte frame, the probe, the 13 saves (ra s0 .. s11 at sp0 - 8 .. sp0 - 104) and s0 := sp0;
   0x8a440 the realignment `andi sp,sp,-32` (sp = s1 = sa_s1 sp0); s4, s5, s3 := a3, a2, a1; the frame-mode flag and
   the shadow base through their GOT words (0xa5fa8, 0xa5f50); s6 := a0; `beqz` on the flag (1: not taken);
   __asan_stack_malloc_1 for the class-1 side-stack frame F (aj_stack_malloc_atS); s2 = s10 := F (`bnez` taken: the
   real-stack branch 0x8a490-0x8a4a8 is not run); the spill of F at s1 + 16; s7 := F + 32; the frame header (magic,
   description, pc) at F; s9 := SHADOW_OFF + F / 8; s11 := -8; the 16 shadow bytes (f1 x4, f8 f8, f2 f2, f8 x4,
   f3 x4); a0 := REC_ADD; `jal record`.

   The walk follows the A walk's stage 1 (a working branch 87f17ee4716, lib/A/Prog/sup_add_s1.v): its
   symbolic runs, the realignment step, the side-stack frame's atoms (44 = F, 1028 = its flag pointer, 1029 = its
   shadow) and regions; B differs in the frame size, the saves' offsets, the shadow layout and the register roles,
   and B calls record() where A inlined it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s1a sup_add_s1b.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.

Lemma sa_entry_ok : SA_M1_stmt B MT -> SA_ENTRY_at B MT.
Proof using HB LAWS TL TLF ML SMP MTL MTFL FFL SIGP IMG TRECORD ASTACK_MALLOC1.
intros HM1. unfold SA_ENTRY_at.
intros ly S W regs mem md ch pu id pp pc uri placement client R O CX HFRM0.
pose proof CX as CX'. unfold sa_cx in CX'. cbv zeta in CX'.
destruct CX' as (HPRE & Hfr7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _ & _ & _).
pose proof (s1_O_blocks B ly S (rdW W mem) R O HREP) as HOb.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof alloc_ceiling_value as Ecl.
pose proof (s1_entry B LAWS TL TLF W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_ADD_STK (sa_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_ADD_STK = 16736) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs (s1_extra (as_uar_cell B)))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n0 r Hn0; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
change (A_OBJ 0) with 241%nat in E241 at 1. change (A_OBJ 1) with 242%nat in E242 at 1.
change (A_OBJ 12) with 253%nat in E253 at 1.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold cfg_at. change (w64 (BASE + AF_sup_add)) with (Z_to_bv 64 (BASE + AF_sup_add)).
assert (SHOK : sh_ok SEGS s1_Bx s1_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok, s1_SH; apply Forall_nil).
(* 0x8a400 .. 0x8a440: the frame, the probe, the 13 saves, s0 := sp0, and the realignment *)
paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK s1_Bspan (AF_sup_add + 0x44).
{ awr_ok_tac. all: exact Usp. }
s1_md.
(* the memory below the stack is the entry memory *)
lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ mem) (mrestrict _ ?m1) |- _ =>
assert (KL1 : forall a, 0 <= a < alloc_ceiling -> rdW W m1 a = rdW W mem a)
by (intros a Ha; apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _ (fun a => alloc_ceiling <= a) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
  | lia | lia ]) end.
clear HF HFr HG.
(* the realigned frame base sp1 = sa_s1 sp0: a fresh 32-aligned atom 35 in sp's place; the stack region keeps the
   saves [sp0 - 104, sp0), and atom 35's region [sp1, sp1 + 24) takes the spill of F at sp1 + 16 *)
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (snt_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by lia. clear Hsp1r.
assert (Hs1 : sa_s1 (spZ regs) = sp1).
{ assert (He : sp1 = 32 * ((spZ regs + -128) / 32)) by reflexivity. rewrite He. unfold sa_s1.
  pose proof (Z.div_mod (spZ regs + -128) 32 ltac:(lia)) as D.
  replace (spZ regs - 128) with (spZ regs + -128) by lia. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
s1_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(snt_denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 35 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3; s1_hei_pose Ev 35%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. s1_rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E35 : ew Ev 35 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 35 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 35 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E35, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 35%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (s1_trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; s1_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 35%nat) 0 24 0 24 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E35, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
s1_evalE AG; repeat split; lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
(* 0x8a444 .. 0x8a478: s1 := sp1, s4 := a3, s5 := a2, s3 := a1, the frame-mode flag (1, so `beqz` at 0x8a470 falls
   through) and the shadow base through their GOT words, s6 := a0, then the call of __asan_stack_malloc_1 for 128
   bytes *)
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end.
lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
assert (SHOK : sh_ok sg s1_Bx s1_SH Ex (mrestrict (w_H Wx) (ms_mem msx))) by (unfold sh_ok, s1_SH; apply Forall_nil) end.
paj_run_tok (paj_run B LAWS) HS HJ SHOK s1_Bspan.
{ s1_awr AG ltac:(unfold awr_byte; left; lia). }
s1_md.
lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (KL2 : forall a, 0 <= a < alloc_ceiling -> rdW W m2 a = rdW W mem a)
by (intros a Ha; rewrite <- (KL1 a Ha); apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _ (fun a => alloc_ceiling <= a) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; s1_evalE AG; intros Hrr; lia|]); destruct Hin
  | lia | lia ]) end.
clear HF HFr HG KL1.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (palf_sm B TLF 1 ltac:(cbn [In]; right; left; reflexivity)) as Hsm1. cbn [cs_stack_malloc Z.eqb Pos.eqb] in Hsm1. rewrite Hsm1.
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
assert (Hfs1 : 16 <= fs_frames 1) by (vm_compute; intro Hq; discriminate Hq).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 1 (ASTACK_MALLOC1 fx) ltac:(lia) W rT mT SUP_ADD_STK
    (spZ regs) (sa_FP O) ly S W mem md [] ly S dT 0 (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2, E35, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes. lia.
  - rewrite R3. s1_evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. s1_evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJs & (fS2 & ES2)).
(* the recorder's bytes after the call: g_rec / record.spill are image bytes the record does not own, the
   recorder's blocks are blocks the call keeps *)
assert (TK2 : (forall a, s1_rec a -> rdW W mem2 a = rdW W mem a) /\
  (forall p k i, In (p, k) O -> 0 <= i < req_size k -> rdW W mem2 (p + i) = rdW W mem (p + i))).
{ destruct HK as (K1 & K2 & K3 & _). split.
  - intros a Ha. destruct (CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG a (s1_rec_PG a Ha)) as (Hi & Ho & Herr).
    rewrite (K3 a Hi Ho Herr). apply KL2.
    unfold s1_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia.
  - intros p k i Hin Hi. pose proof (HOb (p, k) Hin) as Hpk.
    destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (_ & Hp4096 & Hpceil & _).
    rewrite (K2 p k i Hpk Hi (fun H => H)). apply KL2. lia. }
clear KL2.
(* back at 0x8a47c: keep atom 35's region and the saves *)
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (U2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (U35 : bv_unsigned (ew Ex 35) = sp1) by (rewrite E35; apply unsigned_lit_small; lia) end.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U2, ?U35; intros a Ha).
  - apply (mbyte_of_aview SEGS). apply K1; [lia | rewrite Hes; lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite FFS. lia.
  - apply (mbyte_of_aview SEGS). apply K1; [lia | rewrite Hes; lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite FFS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 40 ?ws) _ _ =>
  assert (E44 : ew (havoc Eo 40 ws) 44 = Z_to_bv 64 (frame_addr ly 1 fpos)) by (etransitivity; [reflexivity | exact Ha0]) end.
s1_rebaseE HS AG HEv. clear HEv.
(* the side-stack frame F (class 1, 128 bytes), its flag FL and its shadow SB + F / 8 *)
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLapp & HFLrng).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in HFSpres.
fold F in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil, HFhigh. fold FL in HFLpres, HFLown, HFLapp, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1028 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
s1_hei_pose Ev 1028%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. s1_rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E1028 : ew Ev 1028 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 1028 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E1029 : ew Ev 1029 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 1028 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 44 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E44, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1028 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E1028, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1029 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E1029, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 44 32 1029 F SB E44 ltac:(lia) E32 E1029)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 44%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 1028 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E44, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
  [cbn [sv_denot]; rewrite E1028, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
s1_evalE AG; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF4096 HFceil; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz.
  lazymatch goal with |- _ <= _ < ?d => replace d with 16 by (vm_compute; reflexivity) end. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
  (fshadow_region 1029 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E1029, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
  apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
  apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
  apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; s1_evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF4096 HFceil HFhigh HF8lo HF8hi HFq HF8; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
s1_norm_ssp HS.
(* 0x8a47c .. 0x8a534: s2 = s10 := F (`bnez` taken: F >= 4096), the spill of F at s1 + 16, s7 := F + 32, the frame
   header, s9 := SB + F / 8, s11 := -8, the 16 shadow bytes, a0 := REC_ADD, up to `jal record` *)
paj_run_shc (SRr_run_pi_AJ B LAWS) (SRr_run_pi_AJ_call B LAWS) HS HJ2.
{ s1_awr_f AG fpos F. }
s1_md.
(* the recorder's bytes are none of the three writable windows of the frame's block *)
assert (NZr : forall a, s1_rec a -> ~ (alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16)).
{ intros a Ha [Hq | [Hq | Hq]].
  - unfold s1_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. lia.
  - apply (frm_img SEGS B LAWS ly S2 W mem2 md2 1 fpos a HAR2 Hfin2);
    [change (fs_frame_bytes 1) with 128; fold F; lia | exact (CmdRecBase.cif_prog_img _ _ IMG a (s1_rec_PG a Ha))].
  - unfold s1_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha. unfold SB in Hq. lia. }
assert (NZb : forall p k i, In (p, k) O -> 0 <= i < req_size k ->
  ~ (alloc_ceiling <= p + i \/ F <= p + i < F + 128 \/ SB + F / 8 <= p + i < SB + F / 8 + 16)).
{ intros p k i Hin Hi.
  assert (Hpk2 : In (p, k) (ablocks B ly S2)) by (rewrite Eab; exact (HOb _ Hin)).
  destruct (al_blocks _ _ LAWS ly S2 W mem2 md2 p k HAR2 Hpk2) as (Hp16 & Hp4096 & Hpceil & Hpapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p k 1 fpos HAR2 Hpk2 Hfin2) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 1) with 128 in Hdj. fold F in Hdj.
  intros [Hq | [Hq | Hq]]; [lia | lia |].
  exact (fshadow_not_app F 16 p (req_size k) (p + i) ltac:(lia) ltac:(lia) Hpapp ltac:(unfold SB in Hq; lia) ltac:(lia)). }
(* run 3 writes only the stack, the frame and the frame's shadow *)
lazymatch goal with Hfr : frame_of ?Ef ?rs (mrestrict _ mem2) (mrestrict _ ?m3) |- _ =>
assert (KW3 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) ->
  rdW W m3 a = rdW W mem2 a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) Ef rs _ _ _
  (fun a => alloc_ceiling <= a \/ F <= a < F + 128 \/ SB + F / 8 <= a < SB + F / 8 + 16) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; s1_evalE AG; intros Hrr; lia|]); destruct Hin
  | exact Ha | exact Hn ]) end.
assert (KR3 : forall a, s1_rec a -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha. rewrite (KW3 a ltac:(unfold s1_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia) (NZr a Ha)).
  exact (proj1 TK2 a Ha). }
assert (KB3 : forall p k i, In (p, k) O -> 0 <= i < req_size k -> rdW W (ms_mem ms1) (p + i) = rdW W mem (p + i)).
{ intros p k i Hin Hi. pose proof (HOb _ Hin) as Hpk.
  destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (_ & Hp4096 & Hpceil & _).
  rewrite (KW3 (p + i) ltac:(lia) (NZb p k i Hin Hi)). exact (proj2 TK2 p k i Hin Hi). }
clear KW3 TK2.
(* the saves and the frame's flag word at record's entry, from the stack and frame regions *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 1%nat _ HS eq_refl) as HR44;
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 3%nat _ HS eq_refl) as HR2;
cbn [ms_mem restrict mkst] in HR44, HR2;
assert (U2x : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact Usp);
assert (U44x : bv_unsigned (ew Ex 44) = F) by (rewrite E44; apply unsigned_lit_small; lia);
assert (HEREG : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew Ex nn = getr regs rr)
  by (intros nn rr Hnn; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite (AG nn ltac:(lia)); apply EE; exact Hnn) end.
assert (HFRM : sa_frame (rdW W (ms_mem ms1)) (spZ regs) regs) by exact (s1_frame_of_region _ _ _ _ _ _ _ HR2 U2x HEREG).
assert (HFLc : rdword (rdW W (ms_mem ms1)) (F + 120) = Some FL).
{ apply rdword_of_val_mem;
  [ apply (field_of_region _ _ 44%nat _ _ 0 128 0 128 120 8 (SOff 1028 0) _ HR44 U44x);
    [ cbn; tauto
    | cbn [sv_denot]; rewrite E1028, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia
    | cbn; lia ]
  | lia ]. }
(* the registers at record's entry *)
prreg HS (1%bv : bv 5) A1. prreg HS (2%bv : bv 5) A2. prreg HS (3%bv : bv 5) A3. prreg HS (4%bv : bv 5) A4.
prreg HS (8%bv : bv 5) A8. prreg HS (9%bv : bv 5) A9. prreg HS (10%bv : bv 5) A10.
prreg HS (18%bv : bv 5) A18. prreg HS (19%bv : bv 5) A19. prreg HS (20%bv : bv 5) A20. prreg HS (21%bv : bv 5) A21.
prreg HS (22%bv : bv 5) A22. prreg HS (23%bv : bv 5) A23. prreg HS (25%bv : bv 5) A25. prreg HS (26%bv : bv 5) A26.
prreg HS (27%bv : bv 5) A27.
pmkst HS.
exact (s1_call B MT HB LAWS MTL MTFL SIGP IMG TRECORD HM1 ly S W regs mem md ch pu id pp pc uri placement client R O
  S2 (ms_regs ms1) (ms_mem ms1) _ fpos CX HFRM0 HJ2 Eab Hbb2 (ex_intro _ fS2 ES2) KR3 KB3 HFRM HFLc
  ltac:(rewrite A1; reflexivity)
  ltac:(rewrite A2, E35, Hs1; reflexivity)
  ltac:(rewrite A3, (AG 3%nat ltac:(lia)), (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp)
  ltac:(rewrite A4, (AG 4%nat ltac:(lia)), (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp)
  ltac:(rewrite A8, (AG 2%nat ltac:(lia)), (EE 2%nat (2%bv : bv 5) eq_refl); unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned)
  ltac:(rewrite A9, E35, Hs1; reflexivity)
  ltac:(rewrite A10; reflexivity)
  ltac:(rewrite A18, E44; reflexivity)
  ltac:(rewrite A19, (AG 11%nat ltac:(lia)), (EE 11%nat (11%bv : bv 5) eq_refl); reflexivity)
  ltac:(rewrite A20, (AG 13%nat ltac:(lia)), (EE 13%nat (13%bv : bv 5) eq_refl); reflexivity)
  ltac:(rewrite A21, (AG 12%nat ltac:(lia)), (EE 12%nat (12%bv : bv 5) eq_refl); reflexivity)
  ltac:(rewrite A22, (AG 10%nat ltac:(lia)), (EE 10%nat (10%bv : bv 5) eq_refl); reflexivity)
  ltac:(rewrite A23, U44x; reflexivity)
  ltac:(rewrite A25, E1029, <- SB_SHADOW_OFF; reflexivity)
  ltac:(rewrite A26, E44; reflexivity)
  ltac:(rewrite A27; apply bv_eq; vm_compute; reflexivity)).
Qed.
End e.
End f.
End d.

Print Assumptions sa_entry_ok.
