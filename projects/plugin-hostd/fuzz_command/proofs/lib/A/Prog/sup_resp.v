(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and numbers changed; 707 of its 778 lines of code are new or changed and 295 lines of the source are left out. *)
(* sup_resp's ASan walk (plugin-hostd/fuzz_command, 0x89b84, 122 instructions; 102 on the side-stack path walked
   here), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v (flushFrame: a realigned frame, a side-stack frame
   of the stack-malloc entry, released inline) and lib/A/Prog/sup_reply_code.v (a runtime-entry call through PaArt).

   Path: the use-after-return flag is 1 (the allocator record's constant cell, AR_const_law), so `beqz a2` at 0x89bd4
   falls through to __asan_stack_malloc_1; its frame address is not 0, so `bnez s2` at 0x89bf0 skips the real-stack
   fallback (0x89bf4..0x89c0c) and `beqz s2` at 0x89cbc skips the real-stack shadow reset (0x89d10..0x89d3c).

   Pass-4/5 re-fit: the callee and runtime hypotheses hold at every FP state (forall fx0).
   The stack-malloc entry runs at the entry's fx. The snprintf step is the shared contract (RtPFCmd.asnprintf_sh)
   through aj_art_own_atF and srr_art_postF_of_pf; the rest of the walk runs in place at the FP state fx1
   the wrapper returned: srr_apost_baseF_lift, the executor's lemmas taken at fx1, and the
   symbolic state moved to fx1 by the kit's PaFx.st_ok_pi_restrict_xfx. xstrdup keeps the FP state (apost_base, kit rule
   cl_callS). The snprintf destination's 8 slack bytes (amem_range d (w + 8)) lie in sup_resp's own fake
   frame (amem_range_sub_app). Pass 5:
   the chain at the xstrdup call (0x89c98, s0 = sp0, the frame pointer) is achain_push on afn_pre's
   chain with the prologue's saves of ra and s0 at sp0 - 8 and sp0 - 16. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecCells CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c sup_resp_c sup_resp_s0 sup_resp_s1 sup_resp_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a window of the walk's symbolic memory inside the stack window [sp0 - STK, sp0) *)
Ltac sr_awr AG :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
    first [ exfalso; clear - Hr; lia | left; lia | idtac ] | ]);
try destruct Hin.
(* the walk makes no inline check, so its shadow entry list stays empty; restate it over the current env *)
Ltac resh HS :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
assert (SH : sh_ok sg SR_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (unfold sh_ok; apply Forall_nil) end.
(* after each symbolic run the model is left as `with_vm_backing (m_vm_lazy md) mat md`; over a chain of runs the
   term doubles per run (2026-10-29), so make it opaque right after each run *)
Ltac collapse_md :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdl) _ =>
first [ is_var mdl | let mdv := fresh "mdv" in set (mdv := mdl) in *; clearbody mdv ] end.

(* the read-only ranges of the shared snprintf contract lie in the image range 0x10000 .. 0x606000 *)
Lemma sr_cr_img : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) RtPFCmd.cmd_snp_cr_img r Hr) as Hb.
unfold RtPFCmd.in_cmd_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a byte outside a run's write windows keeps its view *)
Lemma sr_frame_kept : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' a Hf Ha Hw. apply aview_eq_of. apply Hf. rewrite unsigned_lit_small by lia. exact Hw. Qed.
(* what the snprintf wrapper leaves in buf (sn_bytes (32 - 1) T, the text T and its terminator: T has at most 16
   bytes, so the cut to 31 keeps all of it) is the C string resp code *)
Lemma sr_buf_str : forall H (m : word -> option byte) d code, -2 ^ 31 <= code < 2 ^ 31 ->
  (forall i, 0 <= i < RtPFShared.sn_len (32 - 1) (RA.RESP_HEAD ++ PF.pf_dec code) ->
     aview SEGS H m (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (32 - 1) (RA.RESP_HEAD ++ PF.pf_dec code)) 0)) ->
  astr_atR (aview SEGS H m) d (resp code).
Proof.
intros H m d code Hc Hb. pose proof (sr_fmt_len code Hc) as HL.
assert (ES : RtPFShared.sn_bytes (32 - 1) (RA.RESP_HEAD ++ PF.pf_dec code) = (RA.RESP_HEAD ++ PF.pf_dec code) ++ [0]).
{ unfold RtPFShared.sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat. rewrite firstn_all2 by lia. reflexivity. }
unfold RtPFShared.sn_len in Hb. rewrite ES in Hb. rewrite length_app in Hb. cbn [length] in Hb.
assert (E : PF.pf_bytes ((RA.RESP_HEAD ++ PF.pf_dec code) ++ [0]) = resp code ++ [Z_to_bv 8 0]).
{ rewrite <- (sr_fmt_bytes code Hc). unfold PF.pf_bytes. rewrite map_app. reflexivity. }
split; [|exact (resp_no0 code)].
rewrite <- E. intros i Hi. unfold PF.pf_bytes in Hi |- *. rewrite length_map, length_app in Hi. cbn [length] in Hi.
pose proof (Hb (Z.of_nat i) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv. rewrite Hv. f_equal.
rewrite map_nth.
set (v := nth i ((RA.RESP_HEAD ++ PF.pf_dec code) ++ [0]) 0) in *. clearbody v.
unfold aview in Hv. cbv beta in Hv.
destruct (mbyte SEGS (mrestrict H m) (d + Z.of_nat i)) as [b|]; cbn [option_map] in Hv; [|discriminate].
injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_resp_c.v:64-67), word for word: at every FP state *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
(* IMG: the image facts of the record (CmdRecBase.v). The record facts the walk
   uses are the kit's lemmas, applied by exact: RRO and cmd_ro_ok_of_aro (CmdRecRo.v), cmd_rec_cells
   (CmdRecCells.v), cmd_hull_vis_chk (CmdRecBase.v), and IMG's field cif_prog_img. *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let errno_low := pal_env B TL.

(* the shadow word over the format "resp %d" (0x21d00) is visible: its first byte is the literal's zero shadow, the
   other seven the record's constant shadow cells (the literal's redzone and the literal "resp " at 0x21d20); the
   record's checker decides it *)
Lemma sr_lit_hull : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> shadow_hull_vis (rdW W mem) 0x21d00 8.
Proof. intros ly S W mem md HAR. exact (cmd_hull_vis_chk SEGS B LAWS HB ly S W mem md 0x21d00 8 HAR ltac:(vm_compute; reflexivity)). Qed.
(* the listing's call target for xstrdup is its entry in the statement's form *)
Lemma sr_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof.
rewrite (SIGP CS_xstrdup ltac:(unfold cmd_prog_syms; cbn [In]; repeat (try (now left); right))).
try (f_equal; vm_compute; reflexivity).
Qed.

Theorem tsup_resp_spec_holds : tsup_resp_spec B MT.
Proof.
unfold tsup_resp_spec.
intros ly S W regs mem md ch code HPRE HFRM Hfr8 HROD HRO H10 Hcode Hev Hlive MOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : SUP_RESP_STK = 16528) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 errno_low) as [Herr0 Herr1].
pose proof (sr_entry B LAWS TL TLF W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_RESP_STK [] ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (sr_extra (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (apply EE; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EE; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EE; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 code) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (sr_extra (as_uar_cell B))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar.
clear HE.
assert (SHOK : sh_ok SEGS SR_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (AD : ed E = ed E) by reflexivity.
unfold cfg_at. change (w64 (BASE + AF_sup_resp)) with (Z_to_bv 64 (BASE + AF_sup_resp)).
(* 0x89b84 .. 0x89bb0: the 96-byte frame, the saves, s0 := sp0, sp := (sp0 - 96) & -32 *)
paj_run_to_tok RUNTO HS HJ SHOK SR_Bspan 0x36d0.
{ awr_ok_tac. exact Usp. }
clear_frames. collapse_md.
(* the realigned stack pointer sp1 becomes atom 40; the frame keeps its top 64 bytes (the saves), and sp1's own
   slot sp1 + 24 (s6's spill at 0x89c10) is a region of its own *)
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (sp1_facts (spZ regs + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia. clear Hsp1r.
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
  (denot_and_m32 E 2 (spZ regs) (-96) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2.
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
let rs' := eval vm_compute in (trim_stack rs (-64) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
assert (VO : forall Ev n, img_env VAL A_LIM Ev -> (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew Ev n) = VAL n)
  by (intros Ev n HEv Hn; exact (HEv n Hn)).
change (A_OBJ 0) with 241%nat in Hob0. change (A_OBJ 1) with 242%nat in Hob1. change (A_OBJ 12) with 253%nat in Hob12.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HEv := rnHEI Ev in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 40%nat) 24 32 24 32 []) HS eq_refl
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
(* 0x89bb4 .. 0x89bdc: s1 := sp1, the shadow base and the use-after-return flag (1, the record's constant cell),
   the flag test falls through, a0 := 96, the call of __asan_stack_malloc_1 *)
resh HS.
paj_run_tok RUN HS HJ SHOK SR_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E' ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb E' rs' stk sp0 fp b0 bc fr ly own) end.
  eapply awr_ok_cons_stack_off with (n := 40%nat) (d := sp1 - spZ regs);
    [reflexivity | rewrite E40, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | rewrite (AG 2%nat) by lia; exact Usp | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
pmkst HS. collapse_md.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* the call of __asan_stack_malloc_1 (cgif's flushFrame, A/AChf.v:205-219) *)
pose proof (palf_sm B TLF 1 ltac:(cbn; tauto)) as HSM1. change (cs_stack_malloc 1) with CS___asan_stack_malloc_1 in HSM1.
rewrite HSM1.
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 (ASTACK_MALLOC1 fx) ltac:(lia) W (ms_regs msX) (ms_mem msX)
    SUP_RESP_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2, E40, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes; lia.
  - rewrite R3, (AG 3%nat), E3 by lia. exact Hgp.
  - rewrite R4, (AG 4%nat), E4 by lia. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - change (fs_frames 1) with 8192. lia. }
cbv beta. clear R1 R2 R3 R4.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
rewrite Hes in HK.
(* back at 0x89be0: the frame region keeps the slot sp1 + 24 and the saves (both above sp1) *)
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
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
rewrite Ha0 in E52. unfold w64 in E52.
(* the frame F (atom 52), its flag address FL (atom 64) and its shadow SB + F / 8 (atom 65), as cgif's flushFrame
   (A/AChf.v:241-342): the 24 header bytes, the flag word at F + 120, and the 16 shadow bytes, all zero *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 64 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 64%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E64 : ew Ev 64 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 64 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E65 : ew Ev 65 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 64 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (128 / 8) with 16. lia. }
pose proof HFLrng as ((HFLapp & HFLni) & HFL4096 & HFLz & HFLceil).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 52 (HPTR 5) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E52, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 64 (HPTR 0) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E64, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 65 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E65, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
    split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 52 32 65 F SB E52 ltac:(lia) E32 E65)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
  (fshadow_region 65 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    change (fs_frame_bytes 1 / 8) with 16; rewrite E65, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
      apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
    | apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
      apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
      apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 1 / 8) with 16; rewrite E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi; unfold SB; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 52%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 64 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    rewrite E52, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
    [cbn [sv_denot]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite E52, E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFhigh HFq HF8; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 52%nat) 0 24 0 24 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    rewrite E52, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite E52, E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFhigh HFq HF8; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
clear SHOK.
(* 0x89be0 .. 0x89c90: s2 = s6 := F (not 0: `bnez s2` skips the real-stack fallback), sp1's slot := F, s4 := buf,
   the frame header (magic, description, pc), the shadow f1 f1 f1 f1 00 00 00 00 f3 f3 f3 f3, then the call of the
   snprintf wrapper on (buf, 32, "resp %d", code) *)
paj_run_shc RUNP RUNC HS HJ2.
{ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      first [ exfalso; clear - Hr; lia
            | left; rewrite FFS; lia
            | right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16;
                      fold F; unfold SB in *; lia ] ] | ]);
  destruct Hin. }
pmkst HS. collapse_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
(* the state at the call: the record's view, the read-only bytes (cmd_ro_ok again, from arodata_okP), the frame *)
pose proof (proj1 HJ2) as HAR3.
pose proof (aro_journal0 SEGS B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RRO SEGS B LAWS HB IMG) HJ2 HROD) as HROD3.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HAR3 HROD3) as HRO3.
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR3) as (_ & HGUARD3 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin2) as (_ & _ & HFpres3 & HFSpres3).
change (fs_frame_bytes 1) with 128 in HFpres3, HFSpres3. fold F in HFpres3, HFSpres3.
assert (HLIT : abytes_atR (rdW W (ms_mem ms1)) 0x21d00 RO_lit_21d00).
{ clear - HRO3. destruct HRO3 as [HRO3 _]. unfold cmd_ro_bytes in HRO3.
  repeat match type of HRO3 with
  | abytes_atR _ 0x21d00 _ /\ _ => exact (proj1 HRO3)
  | _ /\ _ => apply proj2 in HRO3
  end. }
assert (HspT : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite P2, E40, unsigned_lit_small by lia; lia).
assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (AG 3%nat), E3 by lia; exact Hgp).
assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (AG 4%nat), E4 by lia; exact Htp).
assert (P10' : getr (ms_regs ms1) 10 = w64 (F + 32)) by (rewrite P10, E52, unsigned_lit_small by lia; reflexivity).
assert (P12' : getr (ms_regs ms1) 12 = w64 0x21d00).
{ rewrite P12. lazymatch goal with |- ew ?Ev _ = _ => let HEv := rnHEI Ev in
  pose proof (HEv 288%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H288 end.
  change (VAL 288%nat) with (VAL (A_OBJ 47)) in H288. rewrite (VOBJS 47%nat ltac:(vm_compute; lia)) in H288.
  apply bv_eq. rewrite H288. unfold w64. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (P13' : getr (ms_regs ms1) 13 = w64 code) by (rewrite P13, (AG 10%nat), E10 by lia; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hal1 : (sp1 - spZ regs) mod 16 = 0) by (rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity).
(* the buffer's shadow (bytes 4..7 of the frame's shadow, written 00 at 0x89c6c..0x89c78) *)
assert (ZB : forall i, 4 <= i < 8 -> aview SEGS (w_H W) (ms_mem ms1) (SB + F / 8 + i) = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_region_nth Ex ssx msx 2 _ HS eq_refl) as HR end.
  cbn [ms_mem restrict] in HR.
  intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]]; (apply aview_of_val_mem1; [|lia]);
  (eapply field_of_region with (w := 1%N) (e := SLit 0) (v := 0); [exact HR | rewrite E65, unsigned_lit_small by (unfold SB; lia); reflexivity
    | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia ]). }
(* 0x89c90: the snprintf wrapper writes "resp <code>" and its terminator into buf: the shared contract
   RtPFCmd.asnprintf_sh at the entry's FP state, in art form (srr_art_postF_of_pf), through
   the journal step for a destination in sup_resp's own side-stack frame (aj_art_own_atF). The text T has at most 16
   bytes, so the wrapper writes w = |T| + 1 <= 17 bytes of buf [F + 32, F + 64). *)
pose proof (sr_fmt_len code Hcode) as HLT0.
assert (HW : RtPFShared.sn_len (32 - 1) (RA.RESP_HEAD ++ PF.pf_dec code) = Z.of_nat (length (RA.RESP_HEAD ++ PF.pf_dec code)) + 1).
{ unfold RtPFShared.sn_len, RtPFShared.sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat.
  rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. lia. }
assert (HKS : RtPFCmd.CMD_SNP_K = 8192) by (unfold RtPFCmd.CMD_SNP_K; rewrite Hes; reflexivity).
(* the frame is off the image range 0x10000 .. 0x606000 *)
pose proof (frm_off_imgP B ly S2 W (ms_mem ms1) _ 1 fpos HAR3 Hfin2) as HFoff.
change (fs_frame_bytes 1) with 128 in HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (ecall_pre_stk_at SEGS B RtPFCmd.CMD_SNP_K SUP_RESP_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly S2 W (ms_mem ms1) _ 0
  (ms_regs ms1) (sp1 - spZ regs) HJ2 HspT Hal1 ltac:(lia) ltac:(rewrite HKS, Hes; lia) ltac:(rewrite HKS, FFS; lia) HraT P3' P4')
  as (HEP & HKlo & HKpres).
destruct HGUARD3 as [HG1 [cval HG2]].
assert (A3 : argZ (ms_regs ms1) 3 = bv_unsigned (w64 code)).
{ assert (I13 : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
  unfold argZ. rewrite I13, P13'. reflexivity. }
assert (HL8 : length RO_lit_21d00 = 8%nat) by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (aj_art_own_atF SEGS B LAWS Hsegs RtPFCmd.CMD_SNP_K
    (fun a => F + 32 <= a < F + 32 + RtPFShared.sn_len (32 - 1) (RA.RESP_HEAD ++ PF.pf_dec code))
    (SIG CS___interceptor_trampoline_snprintf)
    W (ms_regs ms1) (ms_mem ms1) SUP_RESP_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly S2 _ 0 (sp1 - spZ regs) _ _ HJ2 HspT
    Hal1 ltac:(lia) ltac:(rewrite HKS; lia) ltac:(rewrite HKS, FFS; lia) P1).
  - intros a Ha. cbv beta in Ha. rewrite HW in Ha. right; right; right; left. exists 1, fpos. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
  - eapply srr_art_postF_of_pf; [exact HKpres|].
    apply (ASNPRINTF fx ly S2 W (ms_regs ms1) (ms_mem ms1) _ (F + 32) 32 0x21d00 []
      (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) (RA.RESP_HEAD ++ PF.pf_dec code) cval).
    + exact HEP.
    + exact HKlo.
    + exact HKpres.
    + exact P10'.
    + exact P11.
    + exact P12'.
    + exact (CmdRecImg.cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI W (ms_mem ms1) HROD3).
    + apply Forall_forall. intros r Hr. cbv beta. destruct (sr_cr_img r Hr) as (Hr1 & Hr2 & Hr3). lia.
    + apply Forall_forall. intros r Hr. cbv beta. destruct (sr_cr_img r Hr) as (Hr1 & Hr2 & Hr3).
      unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint; cbn [fst snd]; rewrite ?HW, ?HKS; lia.
    + exact HG1.
    + exact HG2.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint; cbn [fst snd]; rewrite ?HW, ?HKS; lia.
    + unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint; cbn [fst snd]; rewrite ?HW, ?HKS; lia.
    + split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
    + cbn [length]. rewrite HspT. lia.
    + unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint; cbn [fst snd length]; rewrite ?HW, ?HKS; lia.
    + apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ RA.RESP_FMT RA.RESP_PS [PF.AInt code]).
      * unfold RtPFShared.fmt_at.
        change (Z.of_nat (length RA.RESP_FMT) + 1) with 8. change (Z.of_nat (length RA.RESP_FMT)) with 7.
        split; [lia|]. split.
        { intros i Hi. replace (0x21d00 + i) with (0x21d00 + Z.of_nat (Z.to_nat i)) by lia.
          rewrite (HLIT (Z.to_nat i)) by (rewrite HL8; lia). f_equal.
          assert (Hk : (Z.to_nat i < 8)%nat) by lia. revert Hk. generalize (Z.to_nat i). clear.
          intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
        split.
        { unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
          unfold zdisjoint; cbn [fst snd]; rewrite ?HW, ?HKS; lia. }
        split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
        split.
        { apply (cmd_addressable_in SEGS B LAWS HB _ _ W _ _ (0x21d00, 0x21d08 - 0x21d00) 0x21d00 8 HAR3);
            [apply (nth_error_In _ 42); reflexivity | reflexivity | reflexivity | cbn; lia | cbn; lia]. }
        exact (sr_lit_hull _ _ W _ _ HAR3).
      * exact sr_fmt_parse.
      * cbn [RtPFShared.pf_args_asan RtPFShared.pf_arg_asan map app RtPFCmd.arg_of].
        split; [|exact I]. split; [exact Hcode|]. rewrite A3. unfold w64. apply RA.lit_mod32.
      * exact (sr_fmt_text code).
      * cbn [RtPFShared.pf_prec_pos map RtPFCmd.piece_of RtPFCmd.arg_of RA.RESP_PS]. exact I.
      * vm_compute; reflexivity.
    + lia.
    + lia.
    + lia.
    + rewrite HW. lia.
    + unfold RtPFShared.snp_out. cbn [YG0f.pairwise].
      split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rewrite ?HW, ?HKS; lia | apply Forall_nil]|].
      split; [apply Forall_nil | exact I].
    + intros a Ha. rewrite HW in Ha. destruct (HFpres3 a ltac:(lia)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite HspT. lia.
    + (* the destination with the 8 slack bytes the contract reads past it, F + 32 .. F + 32 + w + 8 <= F + 57, lies in
         sup_resp's own 128-byte fake frame *)
      apply (amem_range_sub_app F 128); [exact HFhigh | exact HFceil | lia | rewrite HW; lia | rewrite HW; lia].
    + intros x Hx. exists 0. split; [|left; reflexivity].
      unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
      assert (Hi : 4 <= x / 8 - F / 8 < 8) by (rewrite HW in Hx; clear - Hx HF64 HLT0; Z.div_mod_to_equations; lia).
      replace (SB + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by lia. apply ZB. exact Hi.
    + eapply (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W (ms_mem ms1) _ 1 fpos);
        [exact HAR3 | exact Hfin2 | fold F; lia | change (fs_frame_bytes 1) with 128; fold F; rewrite HW; lia | rewrite HW; lia].
    + unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. rewrite HW. lia.
    + exact HFRM. }
cbv beta. intros W3 c3 _ (-> & fx1 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HP3 & (HQa & HQb) & HK3).
(* the rest of the walk runs in place at the FP state fx1 the wrapper returned: the post at
   fx1 is the post at fx, and the executor's lemmas are taken again at fx1 *)
apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
pose proof (SRr_run_pi_AJ (fx := fx1) B LAWS) as RUNP1. pose proof (SRr_run_pi_AJ_call (fx := fx1) B LAWS) as RUNC1.
pose proof (aj_flag_store_pi (fx := fx1) B LAWS ML ASF FFL) as RUNF1.
pose proof (paj_ret_at (fx := fx1) (PL := PL_cmd) (PI := PI)) as RET1.
cbv beta in HK3. rewrite ?HW, ?HKS in HK3.
(* back at 0x89c94: the wrapper wrote only buf [F + 32, F + 64) and its scratch below sp1, so the five regions (the
   frame header, the flag word, the frame's shadow, sp1's slot, the saves) are kept *)
pose proof HJ3 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin2) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
unfold shadow_addr in HFSpres4. rewrite <- SB_SHADOW_OFF in HFSpres4. change (128 / 8) with 16 in HFSpres4.
assert (HFz : F + 128 <= SB \/ 0x10007fff8000 <= F)
  by (clear - HFhigh; unfold in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SB in *; lia).
jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
   rewrite ?E40, ?E52, ?E65, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by (unfold SB; lia); intros a Ha;
   [ apply (mbyte_of_aview SEGS); apply HK3; unfold ESTACK in *; unfold SB in *; lia
   | intros _; apply (apresent_writable SEGS);
     first [ apply Hpres4; rewrite FFS; lia
           | apply (proj1 (HFpres4 a ltac:(lia)))
           | let Hp := fresh "Hp" in
             pose proof (proj1 (HFSpres4 (a - (SB + F / 8)) ltac:(lia))) as Hp;
             replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
           | lia ] ]). }
(* the state after the call is a state at fx1 (the kit's PaFx.st_ok_pi_restrict_xfx) *)
clear HS. rewrite <- (restrict_mkst_fx (fx := fx)) in HS2.
pose proof (st_ok_pi_restrict_xfx fx fx1 _ _ _ _ _ _ _ _ _ HS2) as HS. clear HS2.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
(* 0x89c94 .. 0x89c98: a0 := buf, the call of xstrdup *)
paj_run_shc RUNP1 RUNC1 HS HJ3.
{ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      first [ exfalso; clear - Hr; lia
            | left; rewrite FFS; lia
            | right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16;
                      fold F; unfold SB in *; lia ] ] | ]);
  destruct Hin. }
(* the bytes outside the run's write windows are kept: buf is in no window *)
lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem3) (mrestrict _ _) |- _ => rename HFx into HFrT end.
pmkst HS. collapse_md.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ => rename msX into msT end.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
assert (HbufT : forall a, F + 32 <= a < F + 64 -> rdW W (ms_mem msT) a = rdW W mem3 a).
{ intros a Ha. apply sr_frame_kept with (1 := HFrT); [lia|].
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      unfold SB in *; lia | ]);
  destruct Hin. }
pose proof HJ3 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
assert (HspX : spZ (ms_regs msT) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite T2, E40, unsigned_lit_small by lia; lia).
assert (T3' : getr (ms_regs msT) 3 = w64 (as_gp B)) by (rewrite T3, (AG 3%nat), E3 by lia; exact Hgp).
assert (T4' : getr (ms_regs msT) 4 = w64 (as_tp B)) by (rewrite T4, (AG 4%nat), E4 by lia; exact Htp).
assert (T10' : getr (ms_regs msT) 10 = w64 (F + 32)) by (rewrite T10, E52, unsigned_lit_small by lia; reflexivity).
assert (Hs0X : s0Z (ms_regs msT) = spZ regs) by (unfold s0Z; rewrite T8, (AG 2%nat) by lia; exact Usp).
assert (HraX : YK0s.ret_ok (getr (ms_regs msT) 1)) by (rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4X : 4096 <= bv_unsigned (getr (ms_regs msT) 1)) by (rewrite T1, unsigned_lit_small by lia; lia).
(* xstrdup's pre at the call. Its frame chain (pass 5): s0 = sp0 (the prologue's `addi s0,sp,96`), so the chain is
   afn_pre's chain pushed by the frame record the prologue saved, ra at sp0 - 8 and the entry s0 at sp0 - 16 (the
   saves region of the symbolic state); the bytes from sp0 up are the entry's (the journal, footprint []) *)
assert (HCH_T : exists ch1, achain ly (rdW W (ms_mem msT)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs msT)) ch1).
{ rewrite Hs0X.
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (ss_mem ssx) in
    let i := idx_of_base rs 2%nat in
    pose proof (st_ok_region_nth Ex ssx msx i _ HS eq_refl) as HRst end.
  cbn [ms_mem restrict mkst] in HRst.
  destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    assert (Hal8 : spZ regs mod 8 = 0) by (clear - Hal16; Z.div_mod_to_equations; lia).
    eapply (achain_push ly (rdW W mem) (rdW W (ms_mem msT)) (spZ regs) (s0Z regs) (raZ regs) ch);
      [exact Hch | lia | | | | exact Hra4 | lia | exact Hal8 | exact Hlt | lia].
    + intros a Ha. exact (aview_above_of_journal B _ _ _ ly S W mem md _ _ _ _ _ _ _ HJ3 a Ha (inFP_nil a)).
    + apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
      replace (spZ regs - 8) with (spZ regs + -8) by lia.
      refine (field_of_region _ _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-8) 8%N (SOff 1 0) (raZ regs) HRst _ _ _ _ _);
        [ rewrite (AG 2%nat) by lia; exact Usp | cbn [In]; tauto
        | rewrite sv_denot_SOff0, (AG 1%nat), E1 by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
        | unfold raZ; apply bv_unsigned_in_range | lia ].
    + apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
      replace (spZ regs - 16) with (spZ regs + -16) by lia.
      refine (field_of_region _ _ 2 (spZ regs) _ (-64) 0 (-64) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HRst _ _ _ _ _);
        [ rewrite (AG 2%nat) by lia; exact Usp | cbn [In]; tauto
        | rewrite sv_denot_SOff0, (AG 8%nat), (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
        | unfold s0Z; apply bv_unsigned_in_range | lia ].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH_T as (ch1 & Hch1).
assert (HROD_T : arodata_okP SEGS RLO RHI B (rdW W (ms_mem msT)))
  by exact (aro_journal0 SEGS B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RRO SEGS B LAWS HB IMG) HJ3 HROD).
assert (HSTR_T : astr_atR (rdW W (ms_mem msT)) (F + 32) (resp code)).
{ pose proof (resp_length code Hcode) as HL2.
  pose proof (sr_buf_str (w_H W) mem3 (F + 32) code Hcode HQb) as Hb3.
  destruct Hb3 as [Hb Hnz]. split; [|exact Hnz]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  rewrite HbufT by lia. exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
(* buf's shadow: bytes 4..7 of the frame's shadow are 00 (the region's chunks) *)
assert (ZBT : forall i, 4 <= i < 8 -> aview SEGS (w_H W) (ms_mem msT) (SB + F / 8 + i) = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_region_nth Ex ssx msx 2 _ HS eq_refl) as HR end.
  cbn [ms_mem restrict] in HR.
  intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]]; (apply aview_of_val_mem1; [|lia]);
  (eapply field_of_region with (w := 1%N) (e := SLit 0) (v := 0); [exact HR | rewrite E65, unsigned_lit_small by (unfold SB; lia); reflexivity
    | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia ]). }
pose proof (sr_fmt_len code Hcode) as HLT. pose proof (resp_length code Hcode) as HLR.
assert (HARG_T : astr_argA B ly S2 (rdW W (ms_mem msT)) (in_roP SEGS RLO RHI) [] (F + 32) (Some (resp code)) \/
  (astr_atR (rdW W (ms_mem msT)) (F + 32) (resp code) /\ Z.of_nat (length (resp code)) + 1 <= LMAX + 1 /\
   afobj SEGS B ly S2 W (ms_mem msT) (F + 32) (Z.of_nat (length (resp code)) + 1))).
{ right. split; [exact HSTR_T|]. split; [unfold LMAX; lia|].
  assert (HF8m : F mod 8 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
  split; [exists 1, fpos; split; [exact Hfin2|]; fold F; split; [lia|]; split; [exact HF8m|];
          change (fs_frame_bytes 1) with 128; split; lia|].
  split; [clear - HF64; Z.div_mod_to_equations; lia|].
  intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  assert (Hi : 4 <= x / 8 - F / 8 < 8) by (clear - Hx HF64 HLR; Z.div_mod_to_equations; lia).
  replace (SB + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by lia. apply ZBT. exact Hi. }
assert (HTAIL_T : atail_vis SEGS W (ms_mem msT) (F + 32 + Z.of_nat (length (resp code)))).
{ destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin2) as (_ & _ & HFpres5 & _).
  change (fs_frame_bytes 1) with 128 in HFpres5. fold F in HFpres5.
  intros a Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HFpres5 a ltac:(clear - Ha HF64 HLR; Z.div_mod_to_equations; lia))). }
assert (HEV_T : st_nev S2 + EV_XSTRDUP <= EV_MAX) by (unfold EV_SUP_RESP in Hev; lia).
assert (HLIVE_T : blocks_bytes S2 + LIVE_XSTRDUP (resp code) <= LIVE_MAX) by (unfold LIVE_SUP_RESP in Hlive; lia).
assert (HMOK_T : mo_ok MT S2 (XM_XSTRDUP MT (resp code))) by (rewrite ES2; apply (mo_ok_set_fs MT MTFL); exact MOK).
assert (HXS : XSTRDUP_STK = 16416) by reflexivity.
(* 0x89c98: xstrdup(buf), through the kit's call rule (xstrdup's footprint is empty; it keeps the FP state, so the
   rule is cl_callS at fx1 and xstrdup's contract is taken at fx1) *)
rewrite sr_sig_xstrdup.
eapply SRr_bind.
{ eapply (cl_callS (fx := fx1) B LAWS W (ms_regs msT) (ms_mem msT) (Z_to_bv 64 (BASE + AF_xstrdup)) SUP_RESP_STK (spZ regs) []
    ly S W mem md [(1, fpos)] ly S2 _ 0 XSTRDUP_STK [] EV_XSTRDUP (sp1 - spZ regs) (getr (ms_regs msT) 1) ch1
    (fun ly4 S4 W4 regs4 mem4 md4 => exists p : Z,
       getr regs4 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly4 S4) ((p, LIVE_XSTRDUP (resp code)) :: ablocks B ly S2) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP (resp code)) (fst qk) (snd qk)) (ablocks B ly S2) /\
       in_blockA (ablocks B ly4 S4) p (LIVE_XSTRDUP (resp code)) /\
       astr_atR (rdW W4 mem4) p (resp code) /\ astr_atR (rdW W4 mem4) (F + 32) (resp code) /\
       blocks_bytes S4 <= blocks_bytes S2 + LIVE_XSTRDUP (resp code) /\
       mo_le MT S2 S4 (XM_XSTRDUP MT (resp code)))
    HJ3 HspX Hal1 ltac:(lia) ltac:(rewrite HXS; lia) ltac:(rewrite FFS, HXS; lia)
    T3' T4' eq_refl HraX Hra4X Hch1).
  - intros HPREc. eapply SRr_mono.
    { exact (TXSTRDUP fx1 ly S2 W (ms_regs msT) (ms_mem msT) _ ch1 (F + 32) (resp code) HPREc HROD_T T10' HARG_T
        HTAIL_T HEV_T HLIVE_T HMOK_T). }
    cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJx & HPx & HQx).
    exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJx|]. split; [exact HPx | exact HQx].
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta.
intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJ4c & HP4 & p & Hp10 & Hp4096 & Hpperm & Hpapart & Hpblk & Hpstr
  & Hbufstr & Hbb4 & MLE4).
(* back at 0x89c9c: the frame (header, flag word, shadow) and the saves are kept *)
pose proof HJ4 as (HAR6 & Hly6 & _ & _ & _ & Hfrs6 & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _).
pose proof HJ4c as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _ & _ & F4c & _).
assert (Hfin6 : In (1, fpos) (frames S4)) by (rewrite Hfrs6; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR Hly6) as (_ & Efa6 & _).
assert (EF6 : frame_addr ly4 1 fpos = F) by exact (Efa6 1 fpos).
assert (EFL6 : flag_addr ly4 1 fpos = FL).
{ change FL with (flag_addr ly 1 fpos). pose proof (Efa6 1 fpos) as Ee. unfold frame_addr, flag_addr in *. lia. }
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6).
rewrite EF6 in HFpres6, HFSpres6. change (fs_frame_bytes 1) with 128 in HFpres6, HFSpres6.
unfold shadow_addr in HFSpres6. rewrite <- SB_SHADOW_OFF in HFSpres6. change (128 / 8) with 16 in HFSpres6.
destruct (FFL ly4 S4 W4 mem4 md4 1 fpos HAR6 Hfin6) as (HFLpres6 & HFLown6 & _).
rewrite EFL6 in HFLpres6, HFLown6.
jafter_call_keep_pi HS 82%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 4]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
   rewrite ?E40, ?E52, ?E65, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by (unfold SB; lia); intros a Ha;
   [ apply (mbyte_of_aview SEGS);
     first [ apply F1c; [unfold SB in *; lia | rewrite HXS; lia | exact (inFP_nil a)]
           | apply (F4c 1 fpos a Hfin2); [|exact (inFP_nil a)];
             first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia
                   | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16;
                     fold F; unfold SB in *; lia ] ]
   | intros _; apply (apresent_writable SEGS);
     first [ apply Hpres6; rewrite FFS; lia
           | apply (proj1 (HFpres6 a ltac:(lia)))
           | let Hp := fresh "Hp" in
             pose proof (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(lia))) as Hp;
             replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
           | lia ] ]). }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS.
hei_havoc HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E86 : ew Ev 86 = getr regs4 10) by (rewrite HEv; reflexivity) end.
clear HEv.
(* the flag byte FL (atom 64) is a region of its own: present, owned by the allocator, so outside the frame and its
   shadow, and below the stack *)
assert (HnoF : FL < F \/ F + 128 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_ge_dec FL (F + 128)) as [Hh|Hh]; [exfalso | right; lia].
  exact (proj2 (HFpres6 FL ltac:(lia)) HFLown6). }
assert (HnoS : FL < SB + F / 8 \/ SB + F / 8 + 16 <= FL).
{ destruct (Z_lt_ge_dec FL (SB + F / 8)) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_ge_dec FL (SB + F / 8 + 16)) as [Hh|Hh]; [exfalso | right; lia].
  pose proof (proj2 (HFSpres6 (FL - (SB + F / 8)) ltac:(lia))) as Hn.
  replace (SB + F / 8 + (FL - (SB + F / 8))) with FL in Hn by lia. exact (Hn HFLown6). }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 64%nat) 0 1 0 1 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E64, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLpres6)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite ?E64, ?E52, ?E65, ?E40; evalE AG;
    clear - HnoF HnoS HFLceil HFL4096 Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil; unfold SB in *;
    repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
(* 0x89c9c .. 0x89d68: buf's shadow f8 (use after scope), the frame's magic := retired, `beqz s2` falls through
   (F <> 0), the frame's shadow f5 (16 bytes), the flag byte := 0 (the frame is released), `j`, the epilogue, up to
   `ret` *)
rewrite T1.
paj_run_flag_sh RUNF1 HS HJ4.
- lia.
- let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E64, ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      first [ exfalso; clear - Hr; lia
            | right; rewrite EFL6; lia
            | left; left; rewrite FFS; lia
            | left; right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; rewrite EF6;
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16;
                      unfold SB in *; lia ] ] | ]);
  destruct Hin.
- let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
  intros msr HSr; rewrite EFL6;
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
    ltac:(rewrite E64; apply unsigned_lit_small; lia)
    ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
  rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.
- collapse_md.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX _) _ => rename msX into msF end.
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msF)) |- _ => rename HFx into HFrF end.
  cbn [ms_mem mkst] in HFrF.
  (* the copy's bytes are in no write window of the run: a live block is apart from the frame, owned by no one
     (the flag byte is the allocator's), an application address (not shadow) and below the stack *)
  assert (Hin6 : In (p, LIVE_XSTRDUP (resp code)) (ablocks B ly4 S4))
    by (eapply Permutation_in; [apply Permutation_sym; exact Hpperm | left; reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR6 Hin6) as (_ & Hp4k & Hpceil & Hpapp & Hpown & _ & Hn0).
  pose proof (req_size_pos _ (proj1 Hn0)) as [_ Hrq].
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 1 fpos HAR6 Hin6 Hfin6) as Hsep.
  rewrite EF6 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 1) with 128 in Hsep.
  assert (Happ : p + req_size (LIVE_XSTRDUP (resp code)) <= SB \/ 0x10007fff8000 <= p)
    by (clear - Hpapp; unfold in_app in Hpapp; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SB in *; lia).
  assert (HpF : forall a, p <= a < p + LIVE_XSTRDUP (resp code) -> rdW W4 (ms_mem msF) a = rdW W4 mem4 a).
  { intros a Ha.
    assert (HaFL : a <> FL) by (intros Heq; rewrite Heq in Ha; exact (proj2 (Hpown FL ltac:(lia)) HFLown6)).
    apply sr_frame_kept with (1 := HFrF); [lia|].
    let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG;
        rewrite ?E64, ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
        unfold SB in *; lia | ]);
    destruct Hin. }
  (* 0x89d68: ret *)
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  eapply (RET1 W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  (* no printf-reaching code after the wrapper: the post at fx1 is apost_base's (fx' := fx1) *)
  intros mat'. apply (apost_baseF_of_base (fx := fx1) SEGS). unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly4, (stack_free_state 1 fpos S4), r, m, d end.
  split; [rewrite F1, (AG 1%nat), E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ4|].
  split.
  { eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sr_extra (as_uar_cell B)) HS).
    - split; [intros n Hn; rewrite (AG n Hn); exact (proj1 HAE n Hn) | rewrite AD; exact (proj2 HAE)].
    - vm_compute; reflexivity. }
  (* the post *)
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2f & F3f & _).
  assert (EabF : ablocks B ly4 (stack_free_state 1 fpos S4) = ablocks B ly4 S4)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  assert (HSYMS : asyms_ok B) by exact (am_syms _ _ _ _ (proj1 HAR)).
  assert (FSP : forall a, fp_spares [] a) by (intros a; apply fp_spares_closed; [apply sink_closed_pos; apply Forall_nil | apply inFP_nil]).
  rewrite Eab in Hpperm, Hpapart.
  exists p. cbv zeta.
  split; [rewrite F10, E86; exact Hp10|].
  split; [exact Hp4096|].
  split; [rewrite EabF; exact Hpperm|].
  split; [exact Hpapart|].
  split; [rewrite EabF; exact (Permutation_in _ (Permutation_sym Hpperm) (or_introl eq_refl))|].
  split.
  { destruct Hpstr as [Hb Hnz]. split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite HpF by (unfold LIVE_XSTRDUP; lia). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
  split.
  { intros R O HR. cbn [fst sup_resp_m].
    apply (rec_repA_kept B ly S ly4 (stack_free_state 1 fpos S4) _ _ R O HR).
    - intros pn Hpn. rewrite EabF. eapply Permutation_in; [apply Permutation_sym; exact Hpperm | right; exact Hpn].
    - intros a Ha.
      assert (HPG : inFP cmd_PG a) by (apply (proj2 (inFP_cons _ _ _ a)); left; cbn [fst snd]; unfold REC_SIZE in Ha; lia).
      assert (HPS : Exists (in_zr a) (as_prog_static B))
        by (rewrite (ts_prog B HB); apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC, REC_SIZE in Ha; lia).
      destruct (prog_static_sep B a HSYMS HPS) as (Hno & Hne & _).
      exact (F3f a (cif_prog_img _ _ IMG a HPG) Hno Hne (FSP a)).
    - intros a Ha.
      assert (HPG : inFP cmd_PG a)
        by (apply (proj2 (inFP_cons _ _ _ a)); right; apply (proj2 (inFP_cons _ _ _ a)); left; cbn [fst snd]; unfold SC_SIZE in Ha; lia).
      assert (HPS : Exists (in_zr a) (as_prog_static B))
        by (rewrite (ts_prog B HB); apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_REC_SPILL, SC_SIZE in Ha; lia).
      destruct (prog_static_sep B a HSYMS HPS) as (Hno & Hne & _).
      exact (F3f a (cif_prog_img _ _ IMG a HPG) Hno Hne (FSP a)).
    - intros q n a Hq Ha.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hq) as (_ & _ & _ & _ & _ & _ & Hn0q).
      pose proof (req_size_pos _ (proj1 Hn0q)) as [_ Hrqq].
      replace a with (q + (a - q)) by lia.
      apply (F2f q n (a - q)); [exact Hq | rewrite EabF; eapply Permutation_in; [apply Permutation_sym; exact Hpperm | right; exact Hq] | lia | exact (inFP_nil _)]. }
  split; [change (blocks_bytes (stack_free_state 1 fpos S4)) with (blocks_bytes S4); unfold LIVE_SUP_RESP, LIVE_XSTRDUP in *; lia|].
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). rewrite ES2 in MLE4. exact (mo_le_set_fs_l MT MTFL _ _ _ _ MLE4).
Qed.
End e.
End f.
End d.
Print Assumptions tsup_resp_spec_holds.
