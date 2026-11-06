(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of answer's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8aa10 .. 0x8ab6c), in the form of sup_resp's walk lane (cgif lib/A/AChf.v, flushFrame):
   the prologue, the realignment `andi sp,sp,-32`, the use-after-return flag (the record's const cell 0xb0c40, value
   1: `beqz a2` at 0x8aa7c falls through), the class-7 side-stack frame of __asan_stack_malloc_7 (at least 4096:
   `bnez s2` at 0x8aa9c skips the real-stack fallback 0x8aaa0 .. 0x8aac0), the frame's header and shadow, the two
   shadow fills, up to the BODY cut (answer_s1.v AN_BODY_stmt). The B twin of lib/A/Prog/answer_e.v
   (a working branch d28426fbb96): B's code 0x8aa10 .. 0x8ab6c is A's 0x8a4c0 .. 0x8a61c instruction for
   instruction (function-relative offsets equal; a Theorem Labs lane's gen/dis/answer.s); the runtime entries' contracts are the
   statement's, at every FP state, used at the ambient one (no call in this segment moves it); the allocator facts
   are a Theorem Labs lane's CmdRecRest.v cmd_model_laws / cmd_stack_malloc_progress and, stated there at tfibsegs only, its
   cmd_frame_flag_law at this walk's segments (a Section hypothesis under that lemma's name), the program statics'
   image facts a Theorem Labs lane's CmdRecImg.v cmd_prog_unowned over the image facts cmd_img_facts_tfib at this walk's segments,
   and the realignment's arithmetic CmdSnText.v's snt_sp1_facts / snt_denot_and_m32. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecRest CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
mix_call_c hand_back_c answer_c PaFx answer_s0 answer_s1 answer_e1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's runtime entries (answer_c.v:95, :97, :98), word for word: each at every FP state; this segment
   uses them at the ambient one *)
Hypothesis ASTACK_MALLOC7 : forall fx0 : YK11.FPState, @astack_malloc_sz_realizes fx0 rc SEGS B (SIG CS___asan_stack_malloc_7) 7.
Hypothesis ASET_SHADOW00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Hypothesis ASET_SHADOWF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
(* the walk hypotheses (a Theorem Labs lane's RULING-STMT.md section 1): the per-binary record CmdBSyms, a Theorem Labs lane's CmdRecRest.v
   cmd_palib (stated there at PI := PB_cmd) at this walk's PI, the side-stack walk facts PALibF, the meter's laws,
   a Theorem Labs lane's CmdRecImg.v cmd_img_facts_tfib at this walk's segments, and a Theorem Labs lane's CmdRecRest.v cmd_frame_flag_law
   (stated there at tfibsegs) at this walk's segments *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> PALib (PI := PI) B0.
Hypothesis TLF : PALibF (PI := PI) B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_frame_flag_law : forall B0, frame_flag_lawP SEGS B0.
(* derived: the AR laws (YG0q), the PALib record, the allocator facts (a Theorem Labs lane's CmdRecRest.v), the image facts, and
   the program statics' image fact (a Theorem Labs lane's CmdRecImg.v, by exact) *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let TL : PALib (PI := PI) B := cmd_palib B HB.
Let ML : model_laws (as_universe B) := CmdRecRest.cmd_model_laws B HB.
Let SMP : stack_malloc_progressP B := CmdRecRest.cmd_stack_malloc_progress B.
Let FFL : frame_flag_lawP SEGS B := cmd_frame_flag_law B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_unowned : forall a, inFP cmd_PG a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) :=
  CmdRecImg.cmd_prog_unowned (SK := SK) SEGS B LAWS HB IMG.
Let RUN := paj_run (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let errno_low := pal_env (PI := PI) B TL.

(* the recorder's bytes lie below the allocator's ceiling, outside every frame and its shadow *)
Lemma in_rec_PG : forall a, in_rec a -> inFP cmd_PG a.
Proof.
intros a [Ha | Ha]; unfold cmd_PG;
[exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56)]; cbn [In fst snd];
(split; [tauto | unfold REC_SIZE, SC_SIZE in Ha; lia]).
Qed.
Lemma an_rk_low : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md -> rk_set (ablocks B ly S) a ->
4096 <= a < alloc_ceiling.
Proof.
intros ly S W mem md a HAR [Hr | (p & n & Hin & Ha)].
- pose proof asan_consts as (C1 & _). unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Hr. lia.
- destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma an_rk_frame : forall ly S (W : world SEGS) mem md a cid pos, AR SEGS B ly S W mem md ->
rk_set (ablocks B ly S) a -> In (cid, pos) (frames S) ->
~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8).
Proof.
intros ly S W mem md a cid pos HAR Ha Hin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (HF0 & HFc & HFapp).
pose proof (fs_frame_bytes_nonneg cid) as Hfnn.
assert (Hsh : shadow_addr (frame_addr ly cid pos) = SB + frame_addr ly cid pos / 8)
  by (unfold shadow_addr; rewrite SB_SHADOW_OFF; reflexivity).
rewrite Hsh.
assert (H8 : 8 * (fs_frame_bytes cid / 8) <= fs_frame_bytes cid) by (apply Z.mul_div_le; lia).
assert (H0 : 0 <= frame_addr ly cid pos / 8) by (apply Z.div_pos; lia).
destruct Ha as [Hr | (p & n & Hb & Ha)].
- pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hin) as Hoff. unfold off_img in Hoff.
  unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE, SB in *. lia.
- destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n cid pos HAR Hb Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  split; [lia|]. intros Hs.
  exact (fshadow_not_app (frame_addr ly cid pos) (fs_frame_bytes cid / 8) p (req_size n) a HF0 ltac:(lia) Hpapp
    ltac:(unfold SB in Hs; lia) ltac:(lia)).
Qed.

Lemma an_entry_ok : AN_BODY_stmt B MT ->
forall ly S W regs mem md ch c sh old e x chg R O,
an_pre B MT ly S W regs mem md ch c sh old e x chg R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_answer) regs mem md) (an_post B MT regs ly S W mem md R e x chg old O).
Proof.
intros HBODY ly S W regs mem md ch c sh old e x chg R O HPRE0.
pose proof HPRE0 as (HPRE & Hfr8 & HROD & HRO & H10 & H11 & Hchg & HREP & HOLD & _).
pose proof (@pa_wx _ cmd_listing PI) as Hwx. pose proof (@pa_segs_low _ cmd_listing PI) as Hsegs.
pose proof (@pa_B_ok _ cmd_listing PI) as HBASE.
pose proof (pa_base_lo (L := cmd_listing) (PL := PL_cmd) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : ANSWER_STK = 16592) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 errno_low) as [Herr0 Herr1].
pose proof (an_entry_st B LAWS TL TLF W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B ANSWER_STK (an_FP old O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (PI := PI) (Ereg regs (an_extra (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (apply EE; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EE; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EE; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (an_extra (as_uar_cell B))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (@pa_obj_img _ cmd_listing PI 0 ltac:(lia)) as Hob0. pose proof (@pa_obj_img _ cmd_listing PI 1 ltac:(lia)) as Hob1.
pose proof (@pa_obj_img _ cmd_listing PI 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar.
clear HE.
assert (SHOK : sh_ok SEGS AN_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
unfold cfg_at. change (w64 (BASE + AF_answer)) with (Z_to_bv 64 (BASE + AF_answer)).
(* 0x8aa10 .. 0x8aa50: the 128-byte frame, the saves, s0 := sp0, sp := (sp0 - 128) & -32 *)
paj_run_to_tok RUNTO HS HJ SHOK AN_Bspan 0x4524.
{ awr_ok_tac. exact Usp. }
mdv_name.
(* the recorder's bytes: the run wrote the stack window only *)
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (RK : rkeep (ablocks B ly S) (rdW W m0) (rdW W m1)) end.
{ eapply (rkeep_of_frame SEGS _ _ (w_H W) _ _ (fun a => spZ regs - ANSWER_STK <= a < spZ regs) _ HFr).
  - intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; evalE AG; intros Hrr; rewrite FFS; lia|]); destruct Hin.
  - intros a Ha. pose proof (an_rk_low ly S W mem md a HAR Ha). lia. }
clear_frames.
(* the realigned stack pointer sp1 becomes atom 40; the frame keeps the saves (its top 104 bytes), and sp1's slot
   sp1 + 16 (s9's spill at 0x8aac4) is a region of its own *)
set (sp1 := 32 * ((spZ regs + -128) / 32)).
assert (Hsp1eq : sp1 = 32 * ((spZ regs - 128) / 32))
  by (replace (spZ regs - 128) with (spZ regs + -128) by lia; reflexivity).
destruct (CmdSnText.snt_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by lia. clear Hsp1r.
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
  (CmdSnText.snt_denot_and_m32 E 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2.
pose proof (st_ok_pi_havoc_hi 40 E _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
hei_pose E 40%nat [Z_to_bv 64 sp1].
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E40 : ew Ev 40 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 40 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 40 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E40, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 40%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E40, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
assert (VO : forall Ev n, img_env VAL A_LIM Ev -> (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew Ev n) = VAL n)
  by (intros Ev n HEv Hn; exact (HEv n Hn)).
change (A_OBJ 0) with 241%nat in Hob0. change (A_OBJ 1) with 242%nat in Hob1. change (A_OBJ 12) with 253%nat in Hob12.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HEv := rnHEI Ev in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 40%nat) 16 24 16 24 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E40, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite ?(VO Ev 241%nat HEv), ?(VO Ev 242%nat HEv), ?(VO Ev 253%nat HEv) by (unfold A_TEXT, A_LIM; lia);
    evalE AG; rewrite ?E40, ?unsigned_lit_small by lia;
    repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS. clear HJpres.
(* 0x8aa54 .. 0x8aa88: s1 := sp1, the use-after-return flag and the shadow base through their GOT words, the flag test
   `beqz a2` at 0x8aa7c falls through (the flag word is the record's const cell 0xb0c40, value 1: the seed's chunk
   SLit 1 of uar_cell_regionP, from AR's const law), a0 := 4256, the call of __asan_stack_malloc_7 *)
resh HS.
paj_run_tok RUN HS HJ SHOK AN_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E' ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb E' rs' stk sp0 fp b0 bc fr ly own) end.
  eapply awr_ok_cons_stack_off with (n := 40%nat) (d := sp1 - spZ regs);
    [reflexivity | rewrite E40, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | rewrite (AG 2%nat) by lia; exact Usp | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
mdv_name.
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (RK' : rkeep (ablocks B ly S) (rdW W m0) (rdW W m1)) end.
{ eapply (rkeep_of_frame SEGS _ _ (w_H W) _ _ (fun a => spZ regs - ANSWER_STK <= a < spZ regs) _ HFr).
  - intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; evalE AG; intros Hrr; rewrite FFS; lia|]); destruct Hin.
  - intros a Ha. pose proof (an_rk_low ly S W mem md a HAR Ha). lia. }
pose proof (rkeep_trans _ _ _ _ RK RK') as RK2. clear RK RK'. clear_frames.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10.
(* the call of __asan_stack_malloc_7 (answer_s0.v aj_stack_malloc_sz_atS) *)
pose proof (count_cid_le_length 7 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_sz_atS SEGS B LAWS Hsegs errno_low ML SMP (SIG CS___asan_stack_malloc_7) 7 (ASTACK_MALLOC7 fx) ltac:(lia)
    W (ms_regs msX) (ms_mem msX) ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ 4256 HJ) end.
  - unfold spZ at 1. rewrite R2, E40, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes; lia.
  - rewrite R3, (AG 3%nat), E3 by lia. exact Hgp.
  - rewrite R4, (AG 4%nat), E4 by lia. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R10. reflexivity.
  - change (fs_frame_bytes 7) with 8192. lia.
  - reflexivity.
  - change (fs_frames 7) with 128. lia. }
cbv beta. clear R1 R2 R3 R4 R10.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & (fS2 & ES2)).
rewrite Hes in HK.
(* the call keeps the recorder's bytes (image bytes not owned: a Theorem Labs lane's cmd_prog_unowned) and the blocks *)
assert (RK3 : rkeep (ablocks B ly S) (rdW W mem) (rdW W mem2)).
{ eapply rkeep_trans; [exact RK2|]. pose proof HK as (_ & K2 & K3 & _).
  intros a [Hr | (p & n & Hb & Ha)].
  - destruct (cmd_prog_unowned a (in_rec_PG a Hr)) as (Himg & Hno & Hne).
    apply K3; [exact Himg | exact Hno | exact Hne].
  - destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hq].
    replace a with (p + (a - p)) by lia. apply (K2 p n (a - p)); [exact Hb | lia | intros []]. }
clear RK2.
(* back at 0x8aa8c: sp1's slot and the saves stay (both above sp1) *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  pose proof HK as (K1 & _).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
   rewrite ?E40, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by lia; intros a Ha;
   [ apply (mbyte_of_aview SEGS); apply K1; lia
   | intros _; apply (apresent_writable SEGS); apply Hpres2; rewrite FFS; lia ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
hei_havoc HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E52 : ew Ev 52 = getr regs2 10) by (rewrite HEv; reflexivity) end.
clear HEv.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (7, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 7 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B _ _ _ _ _ 7 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W mem2 md2 7 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 7) with 8192 in *.
set (F := frame_addr ly 7 fpos) in *. set (FL := flag_addr ly 7 fpos) in *.
rewrite Ha0 in E52. unfold w64 in E52.
(* the frame F (atom 52), its flag address FL (atom 64) and its shadow SB + F / 8 (atom 65), as sup_resp's walk
   (cgif's flushFrame, A/AChf.v:241-342) *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (HFsep : F + 8192 <= SB \/ SB + F / 8 + 1024 <= F).
{ clear - HFhigh HF8 HFq HF4096. unfold in_app, kLowShadowBeg, kHighMemBeg in HFhigh. unfold SB. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 64 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 64%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E64 : ew Ev 64 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 64 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E65 : ew Ev 65 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 64 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
pose proof HFLrng as ((HFLapp & HFLni) & HFL4096 & HFLz & HFLceil).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 52 (HPTR 5) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E52, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 65 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E65, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
    split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 52 32 65 F SB E52 ltac:(lia) E32 E65)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
(* the frame's shadow bytes 0 .. 3 (0xf1 at 0x8aafc .. 0x8ab08) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 65%nat) 0 4 0 4 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E65, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
    apply (proj1 (HFSpres o ltac:(change (8192 / 8) with 1024; lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi; unfold SB; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
(* the flag word at F + 8184, which __asan_stack_malloc_7 wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 52%nat) 8184 8192 8184 8184 [YP09.mkChunk 8184 (CVal 8 (SOff 64 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    rewrite E52, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 8184 8 _ FL);
    [cbn [sv_denot]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 8184) with (F + 8192 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite E52, E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFsep; unfold SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
(* the frame header F + 0 .. 24 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 52%nat) 0 24 0 24 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    rewrite E52, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite E52, E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFsep; unfold SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
clear SHOK.
(* 0x8aa8c .. 0x8ab18: s2 = s9 := F, and `bnez s2` at 0x8aa9c is taken (F >= 4096: frames_bounds, the atom fact
   HPTR 5 of atom 52 above), so the real-stack fallback 0x8aaa0 .. 0x8aac0 does not run; sp1's slot := F,
   s5 := buf, the frame header (magic, description, pc: B's PHi 124 / 125, PAddHi A_OBJ 56 / 57), the shadow
   f1 f1 f1 f1, then the call of __asan_set_shadow_f8 on (shadow(F) + 4, 512) *)
paj_run_shc RUNP RUNC HS HJ2.
{ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      first [ exfalso; clear - Hr; lia
            | left; rewrite FFS; lia
            | right; right; right; left; exists 7, fpos; split; [left; reflexivity|];
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; fold F; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024;
                      fold F; unfold SB in *; lia ] ] | ]);
  destruct Hin. }
mdv_name.
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (RK : rkeep (ablocks B ly S) (rdW W m0) (rdW W m1)) end.
{ eapply (rkeep_of_frame SEGS _ _ (w_H W) _ _
    (fun a => (spZ regs - ANSWER_STK <= a < spZ regs) \/ (F <= a < F + 8192) \/ (SB + F / 8 <= a < SB + F / 8 + 1024)) _ HFr).
  - intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; evalE AG;
      rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hrr; unfold SB in *; rewrite FFS; lia|]); destruct Hin.
  - intros a Ha. rewrite <- Eab in Ha. pose proof (an_rk_low ly S2 W mem2 md2 a HAR2 Ha) as HL.
    destruct (an_rk_frame ly S2 W mem2 md2 a 7 fpos HAR2 Ha Hfin2) as [HN1 HN2].
    change (fs_frame_bytes 7) with 8192 in HN1, HN2. fold F in HN1, HN2. unfold shadow_addr in HN2. rewrite <- SB_SHADOW_OFF in HN2.
    change (8192 / 8) with 1024 in HN2.
    split; [lia|]. intros [Hs | [Hs | Hs]]; [lia | exact (HN1 Hs) | exact (HN2 Hs)]. }
pose proof (rkeep_trans _ _ _ _ RK3 RK) as RK4. clear RK3 RK. clear_frames.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
(* 0x8ab18: __asan_set_shadow_f8 marks shadow(F) + 4 .. + 516 (answer_s0.v aj_set_shadow_atS) *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_set_shadow_atS SEGS B LAWS Hsegs (SIG CS___asan_set_shadow_f8) 0xf8 (ASET_SHADOWF8 fx)
    W (ms_regs msX) (ms_mem msX) ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, fpos)] ly S2 _ 0 7 fpos
    (SB + F / 8 + 4) 512 (sp1 - spZ regs) _ HJ2) end.
  - left; reflexivity.
  - rewrite P10, E65, unsigned_lit_small by (unfold SB; lia). reflexivity.
  - rewrite P11. reflexivity.
  - lia.
  - fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. lia.
  - fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 7 / 8) with 1024. lia.
  - unfold spZ at 1. rewrite P2, E40, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes; lia.
  - rewrite P3, (AG 3%nat), E3 by lia. exact Hgp.
  - rewrite P4, (AG 4%nat), E4 by lia. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. clear P1 P2 P3 P4 P10 P11.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HZ3 & HK3 & Hpr3).
assert (RK5 : rkeep (ablocks B ly S) (rdW W mem) (rdW W mem3)).
{ eapply rkeep_trans; [exact RK4|]. intros a Ha.
  pose proof Ha as Ha2. rewrite <- Eab in Ha2.
  pose proof (an_rk_low ly S2 W mem2 md2 a HAR2 Ha2) as HL.
  destruct (an_rk_frame ly S2 W mem2 md2 a 7 fpos HAR2 Ha2 Hfin2) as [_ HN2].
  change (fs_frame_bytes 7) with 8192 in HN2. fold F in HN2. unfold shadow_addr in HN2. rewrite <- SB_SHADOW_OFF in HN2.
  change (8192 / 8) with 1024 in HN2.
  apply HK3; [lia | intros Hq; apply HN2; lia]. }
clear RK4.
(* back at 0x8ab1c: the flag word and the saves stay *)
jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W) mem3) HP3 [1; 4]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
   rewrite ?E52, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by lia; intros a Ha;
   [ apply (mbyte_of_aview SEGS); apply HK3; [lia | unfold SB in *; lia]
   | first [ lia | intros _; apply (apresent_writable SEGS); apply Hpres3; rewrite FFS; lia ] ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
norm_ssp HS.
(* the frame's shadow bytes 516 .. 532 (0xf3 at 0x8ab20 .. 0x8ab5c) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 65%nat) 516 532 516 532 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E65, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS);
    pose proof HJ3 as (HAR3 & _); destruct (al_frames _ _ LAWS _ _ _ _ _ 7 fpos HAR3 Hfin2) as (_ & _ & _ & HFSpres3);
    change (fs_frame_bytes 7) with 8192 in HFSpres3; fold F in HFSpres3;
    unfold shadow_addr in HFSpres3; rewrite <- SB_SHADOW_OFF in HFSpres3;
    apply (proj1 (HFSpres3 o ltac:(change (8192 / 8) with 1024; lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite E65, E52; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFsep; unfold SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
(* 0x8ab1c .. 0x8ab68: the shadow f3 x 16 at shadow(F) + 516 .. + 532, then the call of __asan_set_shadow_00 on
   (shadow(F) + 4, 512) *)
paj_run_shc RUNP RUNC HS HJ3.
{ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      first [ exfalso; clear - Hr; lia
            | left; rewrite FFS; lia
            | right; right; right; left; exists 7, fpos; split; [left; reflexivity|];
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 7) with 8192; fold F; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024;
                      fold F; unfold SB in *; lia ] ] | ]);
  destruct Hin. }
mdv_name.
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (RK : rkeep (ablocks B ly S) (rdW W m0) (rdW W m1)) end.
{ eapply (rkeep_of_frame SEGS _ _ (w_H W) _ _
    (fun a => (spZ regs - ANSWER_STK <= a < spZ regs) \/ (F <= a < F + 8192) \/ (SB + F / 8 <= a < SB + F / 8 + 1024)) _ HFr).
  - intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; revert Hrr; evalE AG;
      rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hrr; unfold SB in *; rewrite FFS; lia|]); destruct Hin.
  - intros a Ha. rewrite <- Eab in Ha. pose proof (an_rk_low ly S2 W mem2 md2 a HAR2 Ha) as HL.
    destruct (an_rk_frame ly S2 W mem2 md2 a 7 fpos HAR2 Ha Hfin2) as [HN1 HN2].
    change (fs_frame_bytes 7) with 8192 in HN1, HN2. fold F in HN1, HN2. unfold shadow_addr in HN2. rewrite <- SB_SHADOW_OFF in HN2.
    change (8192 / 8) with 1024 in HN2.
    split; [lia|]. intros [Hs | [Hs | Hs]]; [lia | exact (HN1 Hs) | exact (HN2 Hs)]. }
pose proof (rkeep_trans _ _ _ _ RK5 RK) as RK6. clear RK5 RK. clear_frames.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
(* the saves and the flag word, read off the symbolic memory at the call *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_region_nth Ex ssx msx 2 _ HS eq_refl) as HRS;
pose proof (st_ok_region_nth Ex ssx msx 1 _ HS eq_refl) as HRF end.
cbn [ms_mem restrict mkst] in HRS, HRF.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (VSg : forall od (rn : nat) r,
  In (YP09.mkChunk od (CVal 8 (SOff rn 0)))
    [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  (rn < 32)%nat -> Z.of_nat rn = bv_unsigned (Z_to_bv 5 r) ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (spZ regs + od) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))));
[ intros od rn r Hin Hrn Hr;
  eapply (field_of_region Ex _ 2%nat (spZ regs) _ (-104) 0 (-104) 0 od 8%N (SOff rn 0) _ HRS);
  [ rewrite (AG 2%nat) by lia; exact Usp
  | exact Hin
  | cbn [sv_denot]; rewrite (AG rn) by lia; rewrite (EE rn (Z_to_bv 5 r) Hr), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hv64;
    change (bv_modulus 64) with (2 ^ 64) in Hv64; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
  | cbn; lia ] | ] end.
assert (VS : forall j r, nth_error an_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (spZ regs + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. pose proof (nth_error_lt _ _ _ Hj) as Hjl. cbn [length an_saved] in Hjl.
  do 13 (destruct j as [|j];
    [ cbn [nth_error an_saved] in Hj; injection Hj as <-;
      match goal with |- val_mem _ _ (_ + ?o) _ _ => let o' := eval vm_compute in o in change o with o' end;
      match goal with |- val_mem _ _ (_ + ?o) _ (bv_unsigned (getr _ (Z_to_bv 5 ?r))) =>
        let rn := eval vm_compute in (Z.to_nat r) in
        exact (VSg o rn r ltac:(cbn [In]; tauto) ltac:(lia) ltac:(vm_compute; reflexivity)) end | ]);
  exfalso; lia. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (VF : val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (F + 8184) 8 FL);
[ eapply (field_of_region Ex _ 52%nat F _ 8184 8192 8184 8184 8184 8%N (SOff 64 0) FL HRF);
  [ rewrite E52; apply unsigned_lit_small; lia
  | cbn [In]; tauto
  | cbn [sv_denot]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
  | cbn; lia ] | ] end.
clear HRS HRF.
(* 0x8ab68: __asan_set_shadow_00 zeroes shadow(F) + 4 .. + 516, the shadow of buf *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_set_shadow_atS SEGS B LAWS Hsegs (SIG CS___asan_set_shadow_00) 0 (ASET_SHADOW00 fx)
    W (ms_regs msX) (ms_mem msX) ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, fpos)] ly S2 _ 0 7 fpos
    (SB + F / 8 + 4) 512 (sp1 - spZ regs) _ HJ3) end.
  - left; reflexivity.
  - rewrite P10, E65, unsigned_lit_small by (unfold SB; lia). reflexivity.
  - rewrite P11. reflexivity.
  - lia.
  - fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. lia.
  - fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 7 / 8) with 1024. lia.
  - unfold spZ at 1. rewrite P2, E40, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes; lia.
  - rewrite P3, (AG 3%nat), E3 by lia. exact Hgp.
  - rewrite P4, (AG 4%nat), E4 by lia. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HZ4 & HK4 & Hpr4).
assert (RK7 : rkeep (ablocks B ly S) (rdW W mem) (rdW W mem4)).
{ eapply rkeep_trans; [exact RK6|]. intros a Ha.
  pose proof Ha as Ha2. rewrite <- Eab in Ha2.
  pose proof (an_rk_low ly S2 W mem2 md2 a HAR2 Ha2) as HL.
  destruct (an_rk_frame ly S2 W mem2 md2 a 7 fpos HAR2 Ha2 Hfin2) as [_ HN2].
  change (fs_frame_bytes 7) with 8192 in HN2. fold F in HN2. unfold shadow_addr in HN2. rewrite <- SB_SHADOW_OFF in HN2.
  change (8192 / 8) with 1024 in HN2.
  apply HK4; [lia | intros Hq; apply HN2; lia]. }
clear RK6.
(* the frame's own numbers, for the shadow of buf and the disjointness of the zeroed window *)
assert (HF64q : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8e : F / 8 = 8 * (F / 64))
  by (rewrite HF64q at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; apply Z.div_mul; lia).
assert (HF32e : (F + 32) / 8 = 8 * (F / 64) + 4)
  by (rewrite HF64q at 1; replace (64 * (F / 64) + 32) with ((8 * (F / 64) + 4) * 8) by lia; apply Z.div_mul; lia).
(* at BODY, 0x8ab6c *)
replace (BASE + 17980) with (BASE + AN_BODY) by (unfold AN_BODY; lia).
assert (Q2 : getr regs4 2 = getr (ms_regs ms2) 2) by (exact (HP4 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr regs4 3 = getr (ms_regs ms2) 3) by (exact (HP4 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr regs4 4 = getr (ms_regs ms2) 4) by (exact (HP4 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr regs4 8 = getr (ms_regs ms2) 8) by (exact (HP4 8 ltac:(unfold acallee_saved; lia))).
assert (Q9 : getr regs4 9 = getr (ms_regs ms2) 9) by (exact (HP4 9 ltac:(unfold acallee_saved; lia))).
assert (Q18 : getr regs4 18 = getr (ms_regs ms2) 18) by (exact (HP4 18 ltac:(unfold acallee_saved; lia))).
assert (Q19 : getr regs4 19 = getr (ms_regs ms2) 19) by (exact (HP4 19 ltac:(unfold acallee_saved; lia))).
assert (Q20 : getr regs4 20 = getr (ms_regs ms2) 20) by (exact (HP4 20 ltac:(unfold acallee_saved; lia))).
assert (Q21 : getr regs4 21 = getr (ms_regs ms2) 21) by (exact (HP4 21 ltac:(unfold acallee_saved; lia))).
assert (Q22 : getr regs4 22 = getr (ms_regs ms2) 22) by (exact (HP4 22 ltac:(unfold acallee_saved; lia))).
assert (Q23 : getr regs4 23 = getr (ms_regs ms2) 23) by (exact (HP4 23 ltac:(unfold acallee_saved; lia))).
assert (Q24 : getr regs4 24 = getr (ms_regs ms2) 24) by (exact (HP4 24 ltac:(unfold acallee_saved; lia))).
assert (Q25 : getr regs4 25 = getr (ms_regs ms2) 25) by (exact (HP4 25 ltac:(unfold acallee_saved; lia))).
assert (Q26 : getr regs4 26 = getr (ms_regs ms2) 26) by (exact (HP4 26 ltac:(unfold acallee_saved; lia))).
apply (HBODY ly S W regs mem md ch c sh old e x chg R O ly S2 W regs4 mem4 md4 fpos sp1 HPRE0).
- (* an_mid: the journal of the walk at BODY *)
  unfold an_mid. fold F. change (fs_frame_bytes 7) with 8192. fold FL.
  split; [exact HJ4|].
  split; [rewrite ES2; apply (mo_le_set_fs_r MT MTFL); exact (mle_start MT S MTL)|].
  split; [rewrite Eab; apply Permutation_refl|].
  split; [exact Hsp1eq|].
  split.
  { intros j r Hj. pose proof (nth_error_lt _ _ _ Hj) as Hjl. cbn [length an_saved] in Hjl.
    replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
    apply aval_mem_of_val_mem.
    eapply (val_mem_moved SEGS (w_H W) (w_H W) (ms_mem ms2) mem4 _ _ 8 _); [|exact (VS j r Hj)].
    intros k Hk. apply HK4; [clear - Hjl Hk Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia|].
    clear - Hjl Hk Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF8hi HF8lo. unfold SB. lia. }
  split.
  { apply (rdword_of_val_mem SEGS (w_H W) mem4 (F + 8192 - 8) FL); [|clear - HFL4096 HFLceil HAC C1; lia].
    replace (F + 8192 - 8) with (F + 8184) by lia.
    eapply (val_mem_moved SEGS (w_H W) (w_H W) (ms_mem ms2) mem4 _ _ 8 _); [|exact VF].
    intros k Hk. apply HK4; [clear - Hk HF4096 HFceil HAC C1; lia|].
    clear - Hk HFsep HF8lo HF8hi HF4096 HFceil. unfold SB in *. lia. }
  split.
  { intros i Hi. change (4096 / 8) with 512 in Hi.
    replace (shadow_of_addr SHADOW_OFF (F + 32) + i) with (SB + F / 8 + 4 + i)
      by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; lia).
    apply HZ4. lia. }
  split; [exact (rec_repA_kept B ly S ly S2 _ _ R O HREP RK7 Eab)|].
  assert (Hinr : forall k, (k < 8)%nat -> in_rec (A_G_REC + OFF_ANSWER + Z.of_nat k))
    by (intros k Hk; unfold in_rec; left; unfold A_G_REC, OFF_ANSWER, REC_SIZE; lia).
  exact (aval_mem_rkeep (ablocks B ly S) (rdW W mem) (rdW W mem4) (A_G_REC + OFF_ANSWER) 8 old RK7 Hinr HOLD).
- (* an_regs_body: the registers of the body *)
  unfold an_regs_body. fold F.
  split; [rewrite Q2, P2, E40; reflexivity|].
  split; [rewrite Q3, P3, (AG 3%nat) by lia; rewrite E3; exact Hgp|].
  split; [rewrite Q4, P4, (AG 4%nat) by lia; rewrite E4; exact Htp|].
  split; [rewrite Q8, P8, (AG 2%nat) by lia; unfold w64; rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity|].
  split; [rewrite Q9, P9, E40; reflexivity|].
  split; [rewrite Q18, P18, E52; reflexivity|].
  split; [rewrite Q25, P25, E52; reflexivity|].
  split; [rewrite Q20, P20, E65; unfold shadow_addr, w64; rewrite <- SB_SHADOW_OFF; reflexivity|].
  split; [rewrite Q21, P21, E52, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite Q22, P22, E65, unsigned_lit_small by (unfold SB; lia);
          unfold shadow_addr, w64; rewrite <- SB_SHADOW_OFF; reflexivity|].
  split; [rewrite Q23, P23, (AG 12%nat) by lia; exact (EE 12%nat 12%bv eq_refl)|].
  split; [rewrite Q24, P24, (AG 10%nat) by lia; exact (EE 10%nat 10%bv eq_refl)|].
  rewrite Q26, P26, E32. reflexivity.
- (* the shape pointer s3 *)
  rewrite Q19, P19, (AG 11%nat) by lia. rewrite (EE 11%nat 11%bv eq_refl). exact H11.
Qed.
End e.
End f.
End d.
