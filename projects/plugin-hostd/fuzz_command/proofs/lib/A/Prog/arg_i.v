(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and numbers changed; 821 of its 908 lines of code are new or changed and 279 lines of the source are left out. *)
(* arg_i's walk on the ASan build of plugin-hostd/fuzz_command: targ_i_spec (lib/A/Prog/arg_i_c.v).

   Pass-4/5 re-fit: the callee and runtime hypotheses hold at every FP state (forall fx0).
   The stack-malloc entry runs at the entry's fx. The snprintf step is the shared contract (RtPFCmd.asnprintf_sh)
   through aj_art_own_atF and srr_art_postF_of_pf; the rest of the walk runs in place at the FP state fx1
   the wrapper returned: srr_apost_baseF_lift, the executor's lemmas taken at fx1, and the
   symbolic state moved to fx1 by YL05.st_ok_xfx. xstrdup keeps the FP state (apost_base, kit rule cl_callS). Pass 5:
   the chain at the xstrdup call (0x8a36c, s0 = sp0) is achain_push on afn_pre's
   chain with the prologue's saves of ra and s0 at sp0 - 8 and sp0 - 16. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00 YI0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecCells CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YL05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c arg_i_c arg_i_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.
(* the read-only ranges of the shared snprintf contract lie in the image range 0x10000 .. 0x606000 *)
Lemma ai_cr_img : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) RtPFCmd.cmd_snp_cr_img r Hr) as Hb.
unfold RtPFCmd.in_cmd_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the symbolic state sees the FP state only through ms_fregs / ms_fcsr: a state built by mkst at one FP state is one
   at another (YL05.st_ok_xfx) *)
Lemma ai_xfx : forall (fx1 fx2 : YK11.FPState) E ss regs pc mem,
  st_ok_pi (fx := fx1) SEGS VAL E ss (@mkst fx1 regs pc mem (seg_rom SEGS)) ->
  st_ok_pi (fx := fx2) SEGS VAL E ss (@mkst fx2 regs pc mem (seg_rom SEGS)).
Proof. intros fx1 fx2 E ss regs pc mem H. exact (YL05.st_ok_xfx fx1 fx2 SEGS E (abs_ss VAL ss) regs pc mem H). Qed.
(* what the snprintf wrapper leaves in b (sn_bytes (16 - 1) T for the text T = pf_dec v: T has at most 11 bytes, so
   the cut to 15 keeps all of it, and its terminator) is the C string dec v *)
Lemma ai_buf_str : forall H (m : word -> option byte) d v, -2 ^ 31 <= v < 2 ^ 31 ->
  (forall i, 0 <= i < RtPFShared.sn_len (16 - 1) (PF.pf_dec v) ->
     aview SEGS H m (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (16 - 1) (PF.pf_dec v)) 0)) ->
  astr_atR (aview SEGS H m) d (dec v).
Proof.
intros H m d v Hv Hb. pose proof (dec_length v Hv) as HL. pose proof (ai_dec_len v Hv) as HL2.
assert (ES : RtPFShared.sn_bytes (16 - 1) (PF.pf_dec v) = PF.pf_dec v ++ [0]).
{ unfold RtPFShared.sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia. reflexivity. }
unfold RtPFShared.sn_len in Hb. rewrite ES in Hb. rewrite length_app in Hb. cbn [length] in Hb.
assert (E : PF.pf_bytes (PF.pf_dec v ++ [0]) = dec v ++ [Z_to_bv 8 0]).
{ rewrite <- (ai_dec_text v Hv). change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia. reflexivity. }
split; [|apply dec_no0].
rewrite <- E. intros i Hi. unfold PF.pf_bytes in Hi |- *. rewrite length_map, length_app in Hi. cbn [length] in Hi.
pose proof (Hb (Z.of_nat i) ltac:(lia)) as Hv'. rewrite Nat2Z.id in Hv'. rewrite Hv'. f_equal.
rewrite map_nth.
set (x := nth i (PF.pf_dec v ++ [0]) 0) in *. clearbody x.
unfold aview in Hv'. cbv beta in Hv'.
destruct (mbyte SEGS (mrestrict H m) (d + Z.of_nat i)) as [b|]; cbn [option_map] in Hv'; [|discriminate].
injection Hv' as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
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
Hypothesis PRW : prog_rw SEGS B.
(* IMG, a walk hypothesis: the image facts of the record (CmdRecBase.v). The record facts the walk
   uses are the kit's lemmas, applied by exact: RRO, RPG and cmd_ro_ok_of_aro (CmdRecRo.v), cmd_rec_cells
   (CmdRecCells.v), cmd_aread_ok_chk (CmdRecBase.v), cmd_consts_view_snp (CmdRecImg.v), and IMG's field
   cif_prog_img. *)
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's Section hypotheses (arg_i_c.v:67-70), word for word: at every FP state *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_cmd PI.
Theorem targ_i_spec_holds : targ_i_spec B MT.
Proof.
unfold targ_i_spec.
intros ly S W regs mem md ch c v m HPRE HFRM Hfr8 HROD HRO H10 H11 Hv Hc Hm Hm6 Hev Hlive MOK.
set (FP := if m <? REC_ARGS_MAX then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)] else []).
assert (HFPns : ~ YI16.sink_open_fp FP).
{ pose proof (ai_slot_range c Hc) as (_ & Hc0' & _). intros (r & Hr & H0). unfold FP in Hr.
  destruct (m <? REC_ARGS_MAX); cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in H0; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in H0; lia|]); destruct Hr. }
assert (HFPPG : forall a, inFP FP a -> inFP cmd_PG a).
{ intros a (r & Hr & H0). unfold FP in Hr. apply (ai_slot_PG c a Hc).
  destruct (Z.ltb_spec m REC_ARGS_MAX); cbn [In] in Hr; unfold REC_ARGS_MAX in *;
  repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in H0; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in H0; lia|]); destruct Hr. }
assert (HFPro : forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a)
  by (intros a Hro Hf; exact (RPG SEGS B LAWS HB IMG a (HFPPG a Hf) Hro)).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ai_entry B LAWS TL TLF HB W ly S regs mem md ch c m HPRE H10 Hc Hm Hm6) as HS.
pose proof (ajournal_init SEGS B ARG_I_STK FP ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : ARG_I_STK = 16528) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (ai_slot_range c Hc) as (Hc8 & Hc0 & Hc1).
remember (Eimg (Ereg regs (ai_extra (as_uar_cell B) m))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 m) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_arg_i)) with (Z_to_bv 64 (BASE + AF_arg_i)).
pose proof (ai_zc B LAWS HB ly S W mem md c HAR Hc) as HZc.
ai_reshok HS AG HZc.
paj_run_to_tok RUNTO HS HJ SHOK AI_Bspan (AF_arg_i + 0x3c).
{ awr_ok_tac. all: exact Usp. }
upd_aboveW_init HFr AG HUP. clear_frames.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply (img_env_atomP E _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
change (A_OBJ 0) with 241%nat in E241 at 1. change (A_OBJ 1) with 242%nat in E242 at 1. change (A_OBJ 12) with 253%nat in E253 at 1.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (sp1_facts (spZ regs + -96) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-96) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(clear - Hshi H47; lia) ltac:(clear - Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)) R2 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 35 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 35%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E35 : ew Ev 35 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 35 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 35 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E35, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 35%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); change (2 ^ 5) with 32;
clear - Hsp1 Hsp1al Hslo Hstk0 Hshi H47 Hceil FFS C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-88) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 35%nat) 0 8 0 8 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E35, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; clear - Ho Hsp1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 Hob0 Hob1 Hob12 Huar Hc0 Hc1; repeat split; lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ssp HS.
(* 0x8a274 .. 0x8a2a0: s1 := sp1, the shadow base and the use-after-return flag (1) through their GOT words, then
   the call of __asan_stack_malloc_0 for the 64-byte frame *)
clear HZc. pose proof (ai_zc B LAWS HB _ _ _ _ _ c (proj1 HJ) Hc) as HZc.
ai_reshok HS AG HZc.
paj_run_tok RUN HS HJ SHOK AI_Bspan.
{ ai_awr AG ltac:(unfold awr_byte; left; clear - Ha Hsp1 FFS Hceil Hslo Hstk0 C1; lia). }
upd_aboveW HUP HFr AG. clear_frames.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (palf_sm B TLF 0 ltac:(cbn [In]; left; reflexivity)) as Hsm0. cbn [cs_stack_malloc Z.eqb] in Hsm0. rewrite Hsm0.
pose proof (count_cid_le_length 0 (frames S)) as Hcnt.
assert (Hfs0 : 16 <= fs_frames 0) by (vm_compute; intro Hq; discriminate Hq).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 0 (ASTACK_MALLOC0 fx) ltac:(lia) W rT mT ARG_I_STK (spZ regs) FP
    ly S W mem md [] ly S dT 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 15808)) HJ) end.
  - unfold spZ at 1. rewrite R2, E35, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia). lia.
  - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes. lia.
  - rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJs & (fS2 & ES2)).
(* back at 0x8a2a4: keep sp1's slot, the saved registers and c->nargs *)
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (U2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (U10 : bv_unsigned (ew Ex 10) = c) by (rewrite (AG 10%nat), E10 by lia; apply unsigned_lit_small; lia);
assert (U35 : bv_unsigned (ew Ex 35) = sp1) by (rewrite E35; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia) end.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 6]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U2, ?U10, ?U35; intros a Ha).
  - apply (mbyte_of_aview SEGS). apply K1; [clear - Ha Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia | rewrite Hes; lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite FFS. lia.
  - apply (mbyte_of_aview SEGS). apply K1; [clear - Ha Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia | rewrite Hes; lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite FFS. lia.
  - pose proof (ai_slot_apart B HB ly S W mem md c HAR Hc a ltac:(lia)) as (_ & Ho & Herr).
    apply (mbyte_of_aview SEGS). apply K3; [exact (cif_prog_img _ _ IMG a (ai_slot_PG c a Hc ltac:(lia))) | exact Ho | exact Herr].
  - lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 40 ?ws) _ _ =>
  assert (E44 : ew (havoc Eo 40 ws) 44 = Z_to_bv 64 (frame_addr ly 0 fpos)) by (etransitivity; [reflexivity | exact Ha0]) end.
rebaseE HS AG HEv. clear HEv.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (FFL ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLapp & HFLrng).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in HFSpres.
fold F in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil, HFhigh. fold FL in HFLpres, HFLown, HFLapp, HFLrng.
assert (DFS : F + 64 <= c + 4 \/ c + 8 <= F).
{ apply or_comm. apply zr_apart; [lia | lia |]. intros a Ha Hb.
  pose proof (al_client_img _ _ LAWS ly S2 W mem2 md2 a HAR2
    ltac:(right; left; exists 0, fpos; split; [exact Hfin2 | fold F; change (fs_frame_bytes 0) with 64; lia])) as [_ Hni].
  exact (Hni (cif_prog_img _ _ IMG a (ai_slot_PG c a Hc ltac:(lia)))). }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1028 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 1028%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
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
norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 44%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 1028 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E44, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 56 8 _ FL);
  [cbn [sv_denot]; rewrite E1028, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF4096 HFceil Hc0 Hc1 DFS; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
assert (ZS : val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8) 8 0).
{ apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz. apply Hz. change (64 / 8) with 8. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 1029 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0 / 8) with 8; rewrite E1029, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
  apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; exact ZS]|]; apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF4096 HFceil HFhigh HF8lo HF8hi HFq HF8 Hc0 Hc1; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
(* 0x8a2a4 .. 0x8a344: s2 = s7 := the frame, its header and shadow, then the call of the snprintf wrapper on
   (b = frame + 32, 16, "%d", v) *)
paj_run_shc RUNP RUNC HS HJ2.
{ ai_awr AG ltac:(unfold awr_byte; first
  [ left; clear - Ha Hsp1 FFS Hceil Hslo Hstk0 C1; lia
  | right; right; right; left; exists 0, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia]
  | right; right; right; left; exists 0, fpos; split; [left; reflexivity | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; unfold SB in *; lia] ]). }
(* at 0x8a344: the frame's flag word and b's shadow bytes, then the frame region cut to its header and its flag
   word, so that the snprintf call keeps both (it writes b = frame + 32 .. + 48) *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r0 := eval vm_compute in (nth 0 rs got_regionP) in
let r1 := eval vm_compute in (nth 1 rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRsh;
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HRfr;
pose proof (field_of_region Ex _ 44 F _ 0 64 0 64 56 8%N (SOff 1028 0) FL HRfr
  ltac:(evalE AG) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; evalE AG; rewrite Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VFL;
pose proof (field_of_region Ex _ 1029 (SB + F / 8) _ 0 8 0 8 4 1%N (SLit 0) 0 HRsh
  ltac:(evalE AG) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V4;
pose proof (field_of_region Ex _ 1029 (SB + F / 8) _ 0 8 0 8 5 1%N (SLit 0) 0 HRsh
  ltac:(evalE AG) ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V5;
clear HRsh HRfr;
let rs' := eval vm_compute in (list_upd rs 1 (trim_region r1 0 24)) in
pose proof (st_ok_submem SEGS Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
pose proof HJ2 as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc Hfin2) as (_ & _ & HFpresc & HFSpresc).
change (fs_frame_bytes 0) with 64 in HFpresc, HFSpresc. change (64 / 8) with 8 in HFSpresc. fold F in HFpresc, HFSpresc.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_add_region' SEGS Ev ssv msv (YP09.mkRegion (Some 44%nat) 56 64 56 64 [YP09.mkChunk 56 (CVal 8 (SOff 1028 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  evalE AG; split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpresc (F + o) ltac:(lia)))
  | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 56 8 _ FL);
    [cbn [sv_denot]; evalE AG; rewrite Z.add_0_r; reflexivity | zside | zside | exact VFL] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; unfold SB; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HF4096 HFceil HFhigh HF8lo HF8hi HFq HF8 Hc0 Hc1 DFS;
  repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
cbn [ms_mem restrict] in VFL, V4, V5.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
assert (V297 : VAL 297%nat = 0x21f00).
{ change 297%nat with (A_OBJ 56). rewrite (VOBJS 56%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)). vm_compute. reflexivity. }
lazymatch type of HS with st_ok _ ?Ex _ _ => lazymatch goal with HEIx : img_env _ _ Ex |- _ =>
  assert (E297 : ew Ex 297 = Z_to_bv 64 0x21f00) by (rewrite <- V297; apply (img_env_atomP Ex _ HEIx); unfold A_TEXT, A_LIM; lia) end end.
(* the state at the call: the record's view, the read-only bytes (cmd_ro_ok again, from arodata_okP: the literal "%d"
   at 0x21f00), the guard, and the record's shadow checks over the literal *)
pose proof (ai_aro_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HFPns (RRO SEGS B LAWS HB IMG) HFPro HROD) as HRODc.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HARc HRODc) as HROc.
pose proof (ai_ro_lit _ HROc) as HLIT.
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HARc) as (_ & HGUc & _).
destruct HGUc as [HG1 [cval HG2]].
destruct (cmd_aread_ok_chk SEGS B LAWS HB _ _ _ _ _ 0x21f00 3 HARc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  as (ZL1 & ZL2).
pose proof (dec_length v Hv) as Hdl.
assert (HspT : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite Q2; evalE AG).
assert (Hal1 : (sp1 - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Q3' : getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (rewrite Q3; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (Q4' : getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (rewrite Q4; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (Q10' : getr (ms_regs ms1) 10 = w64 (F + 32)) by (rewrite Q10; evalE AG).
assert (Q11' : getr (ms_regs ms1) 11 = w64 16) by (rewrite Q11; reflexivity).
assert (Q12' : getr (ms_regs ms1) 12 = w64 0x21f00) by (rewrite Q12, E297; reflexivity).
assert (A3 : argZ (ms_regs ms1) 3 mod 2 ^ 32 = v mod 2 ^ 32).
{ assert (I13 : Z_to_bv 5 (10 + 3) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
  unfold argZ. rewrite I13.
  rewrite Q13, (AG 11%nat) by lia. rewrite (EE 11%nat 11%bv eq_refl), H11. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]. }
(* 0x8a344: the snprintf wrapper writes dec v and its terminator into b: the shared contract RtPFCmd.asnprintf_sh at
   the entry's FP state, in art form (srr_art_postF_of_pf), through the journal step for a
   destination in arg_i's own side-stack frame (aj_art_own_atF). The text T = pf_dec v has at most 11 bytes, so the
   wrapper writes w = |T| + 1 <= 12 bytes of b [F + 32, F + 48). *)
assert (HW : RtPFShared.sn_len (16 - 1) (PF.pf_dec v) = Z.of_nat (length (dec v)) + 1).
{ unfold RtPFShared.sn_len, RtPFShared.sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat.
  rewrite firstn_all2 by (rewrite (ai_dec_len v Hv); lia). rewrite length_app, (ai_dec_len v Hv). cbn [length]. lia. }
assert (HKS : RtPFCmd.CMD_SNP_K = 8192) by (unfold RtPFCmd.CMD_SNP_K; rewrite Hes; reflexivity).
assert (HL3 : length RO_lit_21f00 = 3%nat) by (vm_compute; reflexivity).
(* the frame is off the image range 0x10000 .. 0x606000 *)
pose proof (frm_off_imgP B ly S2 W (ms_mem ms1) _ 0 fpos HARc Hfin2) as HFoff.
change (fs_frame_bytes 0) with 64 in HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (ecall_pre_stk_at SEGS B RtPFCmd.CMD_SNP_K ARG_I_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms1) _ 0
  (ms_regs ms1) (sp1 - spZ regs) HJ2 HspT Hal1 ltac:(lia) ltac:(rewrite HKS, Hes; lia) ltac:(rewrite HKS, FFS; lia) HraT Q3' Q4')
  as (HEP & HKlo & HKpres).
eapply SRr_bind.
{ eapply (aj_art_own_atF SEGS B LAWS Hsegs RtPFCmd.CMD_SNP_K
    (fun a => F + 32 <= a < F + 32 + RtPFShared.sn_len (16 - 1) (PF.pf_dec v))
    (SIGMA CS___interceptor_trampoline_snprintf)
    W (ms_regs ms1) (ms_mem ms1) ARG_I_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly S2 _ 0 (sp1 - spZ regs) _ _ HJ2 HspT
    Hal1 ltac:(lia) ltac:(rewrite HKS; lia) ltac:(rewrite HKS, FFS; lia) Q1).
  - intros a Ha. cbv beta in Ha. rewrite HW in Ha.
    unfold awr_byte. right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia.
  - eapply srr_art_postF_of_pf; [exact HKpres|].
    apply (ASNPRINTF fx ly S2 W (ms_regs ms1) (ms_mem ms1) _ (F + 32) 16 0x21f00 []
      (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) (PF.pf_dec v) cval).
    + exact HEP.
    + exact HKlo.
    + exact HKpres.
    + exact Q10'.
    + exact Q11'.
    + exact Q12'.
    + exact (CmdRecImg.cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI W (ms_mem ms1) HRODc).
    + apply Forall_forall. intros r Hr. cbv beta. destruct (ai_cr_img r Hr) as (Hr1 & Hr2 & Hr3). lia.
    + apply Forall_forall. intros r Hr. cbv beta. destruct (ai_cr_img r Hr) as (Hr1 & Hr2 & Hr3).
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
    + apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ PAI.AI_FMT PAI.AI_PS [PF.AInt v]).
      * unfold RtPFShared.fmt_at.
        change (Z.of_nat (length PAI.AI_FMT) + 1) with 3. change (Z.of_nat (length PAI.AI_FMT)) with 2.
        split; [lia|]. split.
        { intros i Hi. replace (0x21f00 + i) with (0x21f00 + Z.of_nat (Z.to_nat i)) by lia.
          rewrite (HLIT (Z.to_nat i)) by (rewrite HL3; lia). f_equal.
          assert (Hk : (Z.to_nat i < 3)%nat) by lia. revert Hk. generalize (Z.to_nat i). clear.
          intros k Hk. do 3 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. }
        split.
        { unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
          unfold zdisjoint; cbn [fst snd]; rewrite ?HW, ?HKS; lia. }
        split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
        split; [exact ZL1 | exact ZL2].
      * exact PAI.ai_parse.
      * cbn [RtPFShared.pf_args_asan RtPFShared.pf_arg_asan map app RtPFCmd.arg_of].
        split; [|exact I]. split; [exact Hv | exact A3].
      * exact (PAI.ai_text v).
      * cbn [RtPFShared.pf_prec_pos map RtPFCmd.piece_of RtPFCmd.arg_of PAI.AI_PS]. exact I.
      * vm_compute; reflexivity.
    + lia.
    + rewrite (ai_dec_len v Hv). lia.
    + lia.
    + rewrite HW. lia.
    + unfold RtPFShared.snp_out. cbn [YG0f.pairwise].
      split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rewrite ?HW, ?HKS; lia | apply Forall_nil]|].
      split; [apply Forall_nil | exact I].
    + intros a Ha. rewrite HW in Ha. destruct (HFpresc a ltac:(lia)) as [Hp Hno].
      split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite HspT. lia.
    + rewrite HW. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
    + intros x Hx. rewrite HW in Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
      assert (Hx8 : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5).
      { pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). rewrite HF8. lia. }
      destruct Hx8 as [-> | ->]; rewrite Z.add_assoc;
      [exact (aview_of_val_mem1 SEGS _ _ _ 0 V4 ltac:(lia)) | exact (aview_of_val_mem1 SEGS _ _ _ 0 V5 ltac:(lia))].
    + rewrite HW. eapply shadow_hull_vis_of_frame with (cid := 0) (pos := fpos);
      first [exact LAWS | exact HARc | exact Hfin2 | (fold F; lia) | (change (fs_frame_bytes 0) with 64; fold F; lia) | lia].
    + unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. rewrite HW. lia.
    + exact HFRM. }
cbv beta. intros W3 c3 _ (-> & fx1 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HP3 & (HQa & HQb) & HK3).
(* the rest of the walk runs in place at the FP state fx1 the wrapper returned: the post at
   fx1 is the post at fx, and the executor's lemmas are taken again at fx1 *)
apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
pose proof (paj_run (fx := fx1) B LAWS) as RUN1. pose proof (paj_run_to (fx := fx1) B LAWS) as RUNTO1.
pose proof (paj_branch (fx := fx1) (PI := PI)) as BR1.
pose proof (SRr_run_pi_AJ (fx := fx1) B LAWS) as RUNP1. pose proof (SRr_run_pi_AJ_call (fx := fx1) B LAWS) as RUNC1.
pose proof (aj_flag_store_pi (fx := fx1) B LAWS ML ASF FFL) as RUNF1.
pose proof (paj_ret_at (fx := fx1) (PL := PL_cmd) (PI := PI)) as RET1.
cbv beta in HK3. rewrite ?HW, ?HKS in HK3.
pose proof (ai_buf_str (w_H W) mem3 (F + 32) v Hv HQb) as Hb3.
(* the facts only the call step used (HFoff is a disjunction: keep it out of the later lia contexts) *)
clear HQb HQa HFoff HEP HKlo HKpres HLIT A3 ZL1 ZL2 HG1 HG2 Q3' Q4' Q10' Q11' Q12' HraT HROc HRODc.
(* back at 0x8a348: b holds dec v; keep the frame's header and flag word, its shadow, the saved registers, sp1's
   slot and c->nargs: the wrapper wrote only b [F + 32, F + 32 + w) and its scratch below sp1 *)
clear U2 U10 U35.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (U44 : bv_unsigned (ew Ex 44) = F) by (evalE AG);
assert (U1029 : bv_unsigned (ew Ex 1029) = SB + F / 8) by (evalE AG);
assert (U35 : bv_unsigned (ew Ex 35) = sp1) by (evalE AG);
assert (U2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (U10 : bv_unsigned (ew Ex 10) = c) by (rewrite (AG 10%nat), E10 by lia; apply unsigned_lit_small; lia) end.
jafter_call_keep_pi HS 100%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4; 5]%nat HS2.
pose proof HJ3 as (HAR3p & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres3 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3p Hfin2) as (_ & _ & HFpres3p & HFSpres3p).
change (fs_frame_bytes 0) with 64 in HFpres3p, HFSpres3p. change (64 / 8) with 8 in HFSpres3p. fold F in HFpres3p, HFSpres3p.
assert (HSHp3 : forall a, SB + F / 8 <= a < SB + F / 8 + 8 -> apresent (w_H W) mem3 a).
{ intros a Ha. pose proof (proj1 (HFSpres3p (a - (SB + F / 8)) ltac:(lia))) as Hq. unfold shadow_addr in Hq.
  rewrite <- SB_SHADOW_OFF in Hq. replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hq by lia. exact Hq. }
assert (HFsmall : F + 8 * 8 <= 2 ^ 47) by (pose proof alloc_ceiling_val as HAC; lia).
assert (HSHb : forall a, SB + F / 8 <= a < SB + F / 8 + 8 -> ~ (F + 32 <= a < F + 32 + (Z.of_nat (length (dec v)) + 1))).
{ intros a Ha Hb. exact (fshadow_not_app F 8 F 64 a ltac:(lia) HFsmall HFhigh ltac:(unfold SB in Ha; lia) ltac:(lia)). }
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil;
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U44, ?U1029, ?U2, ?U10, ?U35; intros a Ha).
  all: first
  [ lia
  | apply (mbyte_of_aview SEGS); apply HK3;
    first [ lia
          | apply HSHb; lia
          | (intros Hb; first [lia | exact (HSHb a ltac:(lia) Hb)])
          | (unfold SB in *; try unfold alloc_ceiling in *; lia)
          | match goal with |- ?g => idtac "SCFAIL" g end; fail ]
  | intros _; apply (apresent_writable SEGS);
    first [ apply HJpres3; lia | apply (proj1 (HFpres3p a ltac:(lia))) | apply HSHp3; lia ]
  | match goal with |- ?g => idtac "RKFAIL" g end; fail ]. }
(* DFS (a disjunction) has no later user: keep it out of the later lia contexts *)
clear DFS.
(* the state after the call is a state at fx1 (ai_xfx) *)
clear HS. pose proof (ai_xfx _ fx1 _ _ _ _ _ HS2) as HS. clear HS2.
rewrite <- (restrict_mkst_fx (fx := fx1)) in HS. mdclr.
rebaseE HS AG HEv. clear HEv.
(* 0x8a348 .. 0x8a364: the slot's shadow byte, c->nargs, and the branch on 5 < nargs *)
clear HZc. pose proof (ai_zc B LAWS HB _ _ _ _ _ c (proj1 HJ3) Hc) as HZc.
(* the frame's shadow region is in the shadow band: narrow its writable window while sh_ok is rebuilt *)
ai_fs_ro HS 1029%nat.
ai_reshok HS AG HZc.
paj_run_tok RUN1 HS HJ3 SHOK AI_Bspan.
{ ai_awr AG ltac:(unfold awr_byte; first
  [ left; clear - Ha Hsp1 FFS Hceil Hslo Hstk0 C1; lia
  | right; right; right; left; exists 0, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia]
  | right; right; right; left; exists 0, fpos; split; [left; reflexivity | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; unfold SB in *; lia] ]). }
(* b's bytes, which snprintf wrote, are outside every write window of the run *)
match goal with HFx : frame_of ?Ef ?rsf (mrestrict (w_H W) ?m0) (mrestrict (w_H W) ?m1) |- _ =>
  assert (HKB : forall a, F + 32 <= a < F + 48 -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha;
        rewrite (ai_aview_kept SEGS Ef rsf (w_H W) m0 m1 a HFx ltac:(clear - Ha HF4096 HFceil Hceil C1; lia)
          ltac:(ai_nowrange AG)); reflexivity) end.
clear_frames.
psrr_branch_tok RUN1 BR1 HS SHOK AI_Bspan.
- (* 5 < c->nargs: m = REC_ARGS_MAX, the argument is dropped; 0x8a3a4 on, the frame's release *)
  assert (Hc5 : (5 <? m) = true)
    by (rewrite <- (ai_lt_rev _ 34 m 5 E34 ltac:(unfold REC_ARGS_MAX in *; lia) ltac:(lia));
        match goal with H : branch_taken _ _ _ = true |- _ => exact H end).
  assert (Em6 : m = REC_ARGS_MAX) by (apply Z.ltb_lt in Hc5; unfold REC_ARGS_MAX in *; lia).
  pose proof (proj1 HJ3) as HAR3.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 Hfin2) as (_ & _ & HFpres3 & HFSpres3).
  change (fs_frame_bytes 0) with 64 in HFpres3, HFSpres3. change (64 / 8) with 8 in HFSpres3.
  fold F in HFpres3, HFSpres3.
  destruct (FFL _ _ _ _ _ 0 fpos HAR3 Hfin2) as (HFLpres3 & HFLown3 & HFLapp3 & HFLrng3).
  fold FL in HFLpres3, HFLown3, HFLapp3, HFLrng3.
  assert (HnoF3 : forall a, F <= a < F + 64 -> ~ aowned B ly S2 a) by (intros a Ha; exact (proj2 (HFpres3 a Ha))).
  ai_fs_rw HS 1029%nat E1029 HFSpres3.
  ai_flag_region HS AG E1028 HFLpres3 HFLrng3 HFLown3 HnoF3.
  paj_run_flag_sh RUNF1 HS HJ3.
  + lia.
  + ai_wrange AG fpos F FL.
  + ai_flag0 E1028.
  + (* at the return: the post *)
    prreg HS (1%bv : bv 5) Z1.
    lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET1 Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
    (* no printf-reaching code after the wrapper: the post at fx1 is apost_base's (fx' := fx1) *)
    intros mat'. apply (apost_baseF_of_base (fx := fx1) SEGS). unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
      exists ly, (stack_free_state 0 fpos S2), rg, mm, mdx end.
    split; [rewrite Z1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
            rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
    split; [cbn [ms_mem]; eapply (ajournal_mono_k SEGS B);
            [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 | unfold EV_ARG_I, EV_XSTRDUP; lia]|].
    split; [apply aregs_preserved_eqs; ai_creg HS AG EE|].
    (* the functional post: no block changed, the meter is spent on nothing *)
    split.
    { change (blocks_bytes (stack_free_state 0 fpos S2)) with (blocks_bytes S2). rewrite Hbb2.
      unfold LIVE_ARG_I, LIVE_XSTRDUP. lia. }
    split.
    { unfold XM_ARG_I, XM_XSTRDUP.
      pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec v)) + 1) ltac:(lia)) as Hmn.
      apply (mle_weaken MT S _ 0 _ MTL); [|exact Hmn].
      unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). rewrite ES2.
      apply (mo_le_set_fs_r MT MTFL). exact (mle_start MT S MTL). }
    left. split; [exact Em6|].
    change (ablocks B ly (stack_free_state 0 fpos S2)) with (ablocks B ly S2). rewrite Eab. apply Permutation_refl.
- (* c->nargs <= 5: the xstrdup call, the two stores, then the same release *)
  assert (Hc5 : (5 <? m) = false)
    by (rewrite <- (ai_lt_rev _ 34 m 5 E34 ltac:(unfold REC_ARGS_MAX in *; lia) ltac:(lia));
        match goal with H : branch_taken _ _ _ = false |- _ => exact H end).
  assert (Em5 : m < REC_ARGS_MAX) by (apply Z.ltb_ge in Hc5; unfold REC_ARGS_MAX in *; lia).
  (* 0x8a368: a0 := b, then the call of xstrdup *)
  paj_run_shc RUNP1 RUNC1 HS HJ3.
  { ai_awr AG ltac:(unfold awr_byte; first
    [ left; clear - Ha Hsp1 FFS Hceil Hslo Hstk0 C1; lia
    | right; right; right; left; exists 0, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia]
    | right; right; right; left; exists 0, fpos; split; [left; reflexivity | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; unfold SB in *; lia] ]). }
  mdclr.
  match goal with HFx : frame_of ?Ef ?rsf (mrestrict (w_H W) ?m0) (mrestrict (w_H W) ?m1) |- _ =>
    assert (HKB2 : forall a, F + 32 <= a < F + 48 -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem3 a)
      by (intros a Ha;
          rewrite (ai_aview_kept SEGS Ef rsf (w_H W) m0 m1 a HFx ltac:(clear - Ha HF4096 HFceil Hceil C1; lia)
            ltac:(ai_nowrange AG)); exact (HKB a Ha)) end.
  clear_frames.
  pmkst HS.
  prreg HS (1%bv : bv 5) X1. prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
  prreg HS (8%bv : bv 5) X8. prreg HS (10%bv : bv 5) X10.
  pose proof (proj1 HJ3) as HARc2.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc2 Hfin2) as (_ & _ & HFpresc2 & HFSpresc2).
  change (fs_frame_bytes 0) with 64 in HFpresc2, HFSpresc2. change (64 / 8) with 8 in HFSpresc2.
  fold F in HFpresc2, HFSpresc2.
  (* xstrdup's frame chain at the call (pass 5): s0 = sp0 (the prologue's `addi s0,sp,96`, 0x8a26c), so the chain is
     afn_pre's chain pushed by the frame record the prologue saved, ra at sp0 - 8 and the entry s0 at sp0 - 16 (the
     saved registers' region of the symbolic state); the bytes from sp0 up are the entry's (the journal: FP lies in
     the image, below the stack) *)
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (Hsprt : spZ rT = sp1) by (unfold spZ at 1; rewrite X2; evalE AG);
  assert (Hs0rt : s0Z rT = spZ regs) by (unfold s0Z at 1; rewrite X8; evalE AG);
  assert (HCH : exists ch1, achain ly (rdW W mT) (spZ rT) (s0Z rT) ch1) end.
  { rewrite Hs0rt.
    lazymatch type of HS with
    | st_ok _ ?Ex ?ssx ?msx =>
      let rs := eval vm_compute in (ss_mem ssx) in
      let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
      let r := eval vm_compute in (nth i rs got_regionP) in
      pose proof (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HRst
    | st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let rs := eval vm_compute in (ss_mem ssx) in
      let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
      let r := eval vm_compute in (nth i rs got_regionP) in
      pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HRst end.
    cbn [ms_mem restrict mkst] in HRst.
    destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
    - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
      assert (Hal8 : spZ regs mod 8 = 0) by (clear - Hal16; Z.div_mod_to_equations; lia).
      eapply (achain_push ly (rdW W mem) _ (spZ regs) (s0Z regs) (raZ regs) ch);
        [exact Hch | lia | | | | exact Hra4 | lia | exact Hal8 | exact Hlt | rewrite Hsprt; lia].
      + intros a Ha. apply (aview_above_of_journal B _ _ _ ly S W mem md _ _ _ _ _ _ _ HJ3 a Ha).
        intros Hf. pose proof (HFPPG a Hf) as (r & Hr & H0). unfold cmd_PG in Hr. cbn [In] in Hr.
        repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in H0; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in H0; lia|]);
        destruct Hr.
      + apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
        replace (spZ regs - 8) with (spZ regs + -8) by lia.
        refine (field_of_region _ _ 2 (spZ regs) _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HRst _ _ _ _ _);
          [ rewrite (AG 2%nat) by lia; exact Usp | cbn [In]; tauto
          | rewrite sv_denot_SOff0, (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl); unfold raZ; symmetry;
            apply Z_to_bv_bv_unsigned
          | unfold raZ; apply bv_unsigned_in_range | lia ].
      + apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
        replace (spZ regs - 16) with (spZ regs + -16) by lia.
        refine (field_of_region _ _ 2 (spZ regs) _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HRst _ _ _ _ _);
          [ rewrite (AG 2%nat) by lia; exact Usp | cbn [In]; tauto
          | rewrite sv_denot_SOff0, (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl); unfold s0Z; symmetry;
            apply Z_to_bv_bv_unsigned
          | unfold s0Z; apply bv_unsigned_in_range | lia ].
    - exists []. left. split; [right; left; lia | reflexivity]. }
  destruct HCH as (ch1 & Hch1).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT ?pcT ?mT _) ?dT) _ =>
  assert (HRODc2 : arodata_okP SEGS RLO RHI B (rdW W mT))
    by exact (ai_aro_journal B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HFPns (RRO SEGS B LAWS HB IMG) HFPro HROD);
  assert (HX10 : getr rT 10 = w64 (F + 32)) by (rewrite X10; evalE AG);
  ai_sh_byte HS E1029 4 V4c; ai_sh_byte HS E1029 5 V5c;
  assert (Hstr : astr_atR (rdW W mT) (F + 32) (dec v));
  [ destruct Hb3 as [Hb3b _]; unfold astr_atR, abytes_atR; split; [| apply dec_no0];
    intros i Hi; rewrite length_app in Hi; cbn [length] in Hi;
    rewrite (HKB2 (F + 32 + Z.of_nat i) ltac:(clear - Hi Hdl; lia));
    exact (Hb3b i ltac:(rewrite length_app; cbn [length]; clear - Hi Hdl; lia))
  | ];
  assert (Hobj : afobj SEGS B ly S2 W mT (F + 32) (Z.of_nat (length (dec v)) + 1));
  [ split;
    [ exists 0, fpos; split; [exact Hfin2|]; split; [lia|];
      split; [fold F; rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; apply Z_mod_mult|];
      split; [fold F; lia|];
      fold F; change (fs_frame_bytes 0) with 64; clear - Hdl; lia
    | split;
      [ rewrite HFq at 1; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult
      | intros x Hx; exists 0; split; [|left; reflexivity];
        unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
        assert (Hx8 : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5)
          by (pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm; pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb;
              rewrite HF8; clear - Hx Hdl HF8 HFq Hdm Hmb; lia);
        destruct Hx8 as [-> | ->]; rewrite Z.add_assoc;
        [exact (aview_of_val_mem1 SEGS _ _ _ 0 V4c ltac:(lia)) | exact (aview_of_val_mem1 SEGS _ _ _ 0 V5c ltac:(lia))] ] ]
  | ];
  assert (Htail : atail_vis SEGS W mT (F + 32 + Z.of_nat (length (dec v))));
  [ intros a Ha; apply (aview_some_of_apresent SEGS);
    apply (proj1 (HFpresc2 a ltac:(pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length (dec v))) 8 ltac:(lia)) as Hmb;
                                   clear - Ha Hdl Hmb; lia)))
  | ] end.
  assert (Hev2 : st_nev S2 + EV_XSTRDUP <= EV_MAX) by (rewrite Hnev2; exact Hev).
  assert (Hlive2 : blocks_bytes S2 + LIVE_XSTRDUP (dec v) <= LIVE_MAX) by (rewrite Hbb2; exact Hlive).
  assert (MOK2 : mo_ok MT S2 (XM_XSTRDUP MT (dec v)))
    by (rewrite ES2; apply (mo_ok_set_fs MT MTFL); exact MOK).
  assert (Hsig : SIGMA CS_xstrdup = BASE + AF_xstrdup)
    by (rewrite (SIGP CS_xstrdup ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
        f_equal; vm_compute; reflexivity).
  (* 0x8a36c: xstrdup(b), through the kit's call rule (xstrdup's footprint is empty; it keeps the FP state, so the
     rule is cl_callS at fx1 and xstrdup's contract is taken at fx1) *)
  eapply SRr_bind.
  { rewrite Hsig.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT ?pcT ?mT _) ?dT) _ =>
    eapply (cl_callS (fx := fx1) B LAWS W rT mT pcT ARG_I_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly S2 dT 0
      XSTRDUP_STK [] EV_XSTRDUP (sp1 - spZ regs) (Z_to_bv 64 (BASE + 16012)) ch1 _ HJ3) end.
    - rewrite Hsprt. lia.
    - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
    - clear - Hsp1; lia.
    - unfold XSTRDUP_STK, ASTACK; lia.
    - unfold XSTRDUP_STK, ASTACK in *; clear - Hsp1 FFS; lia.
    - rewrite X3, (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite X4, (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact X1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBASE; lia.
    - replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia. rewrite <- Hsprt. exact Hch1.
    - intros HPREx. eapply SRr_mono.
      { assert (HLM : Z.of_nat (length (dec v)) + 1 <= LMAX + 1) by (unfold LMAX; clear - Hdl; lia).
        exact (TXSTRDUP fx1 _ _ _ _ _ _ _ (F + 32) (dec v) HPREx HRODc2 HX10
                 (or_intror (conj Hstr (conj HLM Hobj))) Htail Hev2 Hlive2 MOK2). }
      cbv beta. unfold apost_base. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HK5).
      exists ly5, S5, regs5, mem5, md5. split; [rewrite X1; reflexivity|]. split; [exact HJ5|]. split; [exact HP5 | exact HK5].
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJ6c & HP6 & HK6). mdclr.
  destruct HK6 as (p & Hp10 & Hp & HPerm6 & Hapart6 & Hblk6 & Hpstr & Hbstr & Hbb6 & Hmo6).
  (* back at 0x8a370: keep the frame's flag word, its shadow, its header, the saved registers and c->nargs; the
     callee's journal keeps their bytes (stack above its window, our frame, an unowned image byte) *)
  pose proof HJ6c as (_ & _ & _ & _ & _ & Kfrs & _ & _ & K1 & _ & K3 & K4 & _ & _ & _ & _ & _).
  pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & Hfrs6 & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _ & _ & _).
  destruct Hly6 as (_ & _ & _ & _ & _ & HlyF6 & _ & _ & Hlytop6 & _).
  assert (EF6 : frame_addr ly6 0 fpos = F) by (unfold F, frame_addr; rewrite HlyF6; reflexivity).
  assert (EFL6 : flag_addr ly6 0 fpos = FL) by (unfold FL, flag_addr; rewrite HlyF6; reflexivity).
  assert (Hfin6 : In (0, fpos) (frames S6)) by (rewrite Kfrs; exact Hfin2).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6).
  change (fs_frame_bytes 0) with 64 in HFpres6, HFSpres6. change (64 / 8) with 8 in HFSpres6.
  rewrite EF6 in HFpres6, HFSpres6.
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (Y44 : bv_unsigned (ew Ex 44) = F) by (evalE AG);
  assert (Y1029 : bv_unsigned (ew Ex 1029) = SB + F / 8) by (evalE AG);
  assert (Y2 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
  assert (Y10 : bv_unsigned (ew Ex 10) = c) by (rewrite (AG 10%nat), E10 by lia; apply unsigned_lit_small; lia) end.
  jafter_call_keep_pi HS 200%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0; 1; 2; 4; 5]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Y44, ?Y1029, ?Y2, ?Y10; intros a Ha).
    all: first
    [ lia
    | apply (mbyte_of_aview SEGS); first
        [ apply (K4 0 fpos a Hfin2);
          [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia | exact (inFP_nil a)]
        | apply (K4 0 fpos a Hfin2);
          [right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; unfold shadow_addr; fold F;
           rewrite <- SB_SHADOW_OFF; unfold SB in *; lia | exact (inFP_nil a)]
        | apply K1; [lia | unfold XSTRDUP_STK, ASTACK in *; lia | exact (inFP_nil a)]
        | pose proof (ai_slot_apart B HB ly S W mem md c HAR Hc a ltac:(lia)) as (_ & Ho & Herr);
          apply K3; [exact (cif_prog_img _ _ IMG a (ai_slot_PG c a Hc ltac:(lia))) | exact Ho | exact Herr
                    | apply fp_spares_closed; [intros (rr & Hrr & _); destruct Hrr | exact (inFP_nil a)]] ]
    | intros _; apply (apresent_writable SEGS); first
        [ apply Hpres6; lia
        | apply (proj1 (HFpres6 a ltac:(lia))) ]
    | match goal with |- ?g => idtac "RK6FAIL:" g end; fail 1 "rk6" ]. }
  clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2. rename HS2 into HS. mdclr.
  rebaseE HS AG HEv.
  (* a0 after the call is p, the copy (havoc's fifth word, CLOB's a0) *)
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (E204 : ew Ev 204 = Z_to_bv 64 p)
    by (rewrite HEv; change 204%nat with (200 + 4)%nat;
        rewrite (ew_havoc_new _ 200 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia); exact Hp10) end.
  clear HEv.
  (* the copy's block: in the allocator's blocks, apart from the frame, the image, the stack and the shadow *)
  unfold LIVE_XSTRDUP in HPerm6, Hapart6, Hblk6, Hbb6.
  assert (Hpin : In (p, Z.of_nat (length (dec v)) + 1) (ablocks B ly6 S6))
    by (apply (Permutation_in _ (Permutation_sym HPerm6)); left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p _ HAR6 Hpin) as (_ & _ & Hpceil & Hpapp & Hpbpres & _ & _).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p _ 0 fpos HAR6 Hpin Hfin6) as HpF.
  pose proof (blk_off_imgP B _ _ _ _ _ p _ HAR6 Hpin) as Hpoff.
  assert (Hrq : req_size (Z.of_nat (length (dec v)) + 1) = Z.of_nat (length (dec v)) + 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (dec v)) + 1) 0); lia).
  rewrite Hrq in Hpceil, Hpapp, Hpbpres, HpF, Hpoff.
  unfold zdisjoint in HpF. cbn [fst snd] in HpF. rewrite EF6 in HpF. change (fs_frame_bytes 0) with 64 in HpF.
  unfold off_img in Hpoff. unfold in_app, kLowShadowBeg in Hpapp.
  assert (HpFL : ~ (p <= FL < p + (Z.of_nat (length (dec v)) + 1))).
  { intros HH. destruct (FFL _ _ _ _ _ 0 fpos HAR6 Hfin6) as (_ & HFLown6 & _ & _). rewrite EFL6 in HFLown6.
    exact (proj2 (Hpbpres FL HH) HFLown6). }
  (* each byte of the copy is apart from every write window the rest of the walk opens: the frame and its flag word,
     the stack, the frame's shadow, g_rec's slot, the flag byte *)
  assert (HPA : forall a, p <= a < p + (Z.of_nat (length (dec v)) + 1) ->
    (a < F \/ F + 64 <= a) /\ a < spZ regs - 112 /\ (a < 2147450880 \/ 2147450880 + F / 8 + 8 <= a) /\
    (a < c \/ c + 56 <= a) /\ a <> FL /\ 0 <= m <= 5 /\ 4096 <= F).
  { intros a Ha. split; [lia|]. split; [lia|].
    split; [|split; [lia|]; split; [intros ->; exact (HpFL Ha) | split; [unfold REC_ARGS_MAX in *; lia | lia]]].
    destruct Hpapp as (_ & [Hl | (Hh & _)]); [left; lia | right; rewrite C3 in Hh; lia]. }
  (* c->nargs becomes writable: a byte of g_rec in the footprint (prog_rw) *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  assert (Z10 : bv_unsigned (ew Ex 10) = c) by (rewrite (AG 10%nat), E10 by lia; apply unsigned_lit_small; lia);
  let rs := eval vm_compute in (ss_mem ssx) in
  let r := eval vm_compute in (nth 4 rs got_regionP) in
  pose proof (ast_ok_pi_set_region Ex ssx msx 4 r (set_window r 4 8) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 4 8 (st_ok_pi_region_nth Ex ssx msx 4 r HS ltac:(vm_compute; reflexivity))
       ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite Z10; intros o Ho; apply PRW; apply (HPROG B HB);
             apply (ai_slot_PG c _ Hc); lia))) as HS3 end.
  clear HS; rename HS3 into HS; norm_ssp HS.
  pose proof (ai_zc B LAWS HB _ _ _ _ _ c HAR6 Hc) as HZc6.
  ai_reshok HS AG HZc6.
  (* 0x8a370 .. 0x8a38c: the slot's shadow byte, c->nargs, the store c->nargs := m + 1, and the address
     c + 8 + 8 m *)
  paj_run_to_tok RUNTO1 HS HJ6 SHOK AI_Bspan (AF_arg_i + 0x158).
  { ai_awr AG ltac:(unfold awr_byte; rewrite ?EF6; first
    [ left; clear - Ha Hsp1 FFS Hceil Hslo Hstk0 C1; lia
    | right; right; right; left; exists 0, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite ?EF6; fold F; clear - Ha; lia]
    | right; right; right; left; exists 0, fpos; split; [left; reflexivity | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; unfold shadow_addr; rewrite ?EF6; fold F; rewrite <- SB_SHADOW_OFF; unfold SB in *; clear - Ha; lia]
    | right; right; right; right; left; split;
      [ unfold FP; rewrite (proj2 (Z.ltb_lt m REC_ARGS_MAX) Em5); exists (c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
        split; [left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS; clear - Ha; lia]
      | split; [apply (HPROG B HB); apply (ai_slot_PG c _ Hc); clear - Ha; lia | apply (cif_prog_img _ _ IMG); apply (ai_slot_PG c _ Hc); clear - Ha; lia] ] ]). }
  (* the copy's bytes are outside every write window of the run *)
  match goal with HFx : frame_of ?Ef ?rsf (mrestrict (w_H W6) ?m0) (mrestrict (w_H W6) ?m1) |- _ =>
    assert (HKP : forall a, p <= a < p + (Z.of_nat (length (dec v)) + 1) ->
              aview SEGS (w_H W6) m1 a = aview SEGS (w_H W6) mem6 a)
      by (intros a Ha; rewrite (ai_aview_kept SEGS Ef rsf (w_H W6) m0 m1 a HFx ltac:(clear - Ha Hp Hpceil C1; lia) ltac:(ai_nowrange2 AG HPA a Ha));
          reflexivity) end.
  clear_frames.
  (* at 0x8a390: a1 = c + 8 + 8 m, the address of c->args[m]; a fresh atom 1030 for it, and its 8 bytes
     writable (a byte of g_rec in the footprint) *)
  assert (DFS56 : F + 64 <= c \/ c + 56 <= F).
  { apply or_comm. apply zr_apart; [lia | lia |]. intros a Ha Hb.
    pose proof (al_client_img _ _ LAWS ly S2 W mem2 md2 a HAR2
      ltac:(right; left; exists 0, fpos; split; [exact Hfin2 | fold F; change (fs_frame_bytes 0) with 64; lia])) as [_ Hni].
    exact (Hni (cif_prog_img _ _ IMG a (ai_slot_PG c a Hc ltac:(lia)))). }
  assert (Hm8 : (c + 8 + 8 * m) mod 8 = 0)
    by (replace (c + 8 + 8 * m) with (c + (1 + m) * 8) by lia; rewrite Z_mod_plus_full; exact Hc8).
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 1030 Ev ssv msv [Z_to_bv 64 (c + 8 + 8 * m)] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 1030%nat [Z_to_bv 64 (c + 8 + 8 * m)] end.
  clear HS. rename HS3 into HS. rebaseE HS AG HEv.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (E1030 : ew Ev 1030 = Z_to_bv 64 (c + 8 + 8 * m))
    by (rewrite HEv; exact (ew_havoc_new _ 1030 [Z_to_bv 64 (c + 8 + 8 * m)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
  assert (E10c : ew Ev 10 = Z_to_bv 64 c) by (rewrite (AG 10%nat) by lia; exact E10) end.
  clear HEv.
  assert (Hc62 : 0 <= c < 2 ^ 62) by lia.
  assert (Hm06 : 0 <= m <= 6) by (unfold REC_ARGS_MAX in *; lia).
  rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (c + 8 + 8 * m))
    (eq_trans (denot_lit_U _ _) (f_equal (Z_to_bv 64) (ai_args_U _ c m E10c E34 Hc62 Hm06))) R11.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (11%bv : bv 5) (SOff 1030 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E1030, Z.add_0_r, R11;
          rewrite unsigned_lit_small by (unfold REC_ARGS_MAX in *; lia); reflexivity)) as HS3 end.
  clear HS; rename HS3 into HS. norm_ssp HS. clear R11.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 1030 (mkAF 0x5e3740 0x5e3c18 3) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E1030, unsigned_lit_small by (unfold REC_ARGS_MAX in *; lia);
          change (2 ^ 3) with 8; unfold REC_ARGS_MAX in *; repeat split; lia)) as HS3 end.
  clear HS; rename HS3 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 1030%nat) 0 8 0 8 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E1030, unsigned_lit_small by (unfold REC_ARGS_MAX in *; lia); split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply PRW; apply (HPROG B HB); apply (ai_slot_PG c _ Hc); unfold REC_ARGS_MAX in *; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalEq AG; unfold REC_ARGS_MAX in *; repeat split; clear - DFS56 Hm6 Em5 Hc0 Hc1 HF4096 HFceil Hceil Hslo Hstk0 FFS C1; lia)) as HS3 end.
  clear HS; rename HS3 into HS. norm_ssp HS.
  (* the copy's placement facts went into HPA and the slot's apartness from the frame into region 1030: their
     disjunctions have no later user, so they stay out of the later lia contexts *)
  clear DFS56 Hpapp Hpoff HpF HpFL.
  pose proof (ai_zc B LAWS HB _ _ _ _ _ c (proj1 HJ6) Hc) as HZc7.
  lazymatch type of HZc7 with range_addressable ?rd ?o _ _ =>
    assert (HZa : range_addressable rd o (c + 8 + 8 * m) 8)
      by (eapply range_addressable_sub; [exact HZc7 | unfold REC_ARGS_MAX in *; lia | lia]) end.
  ai_reshok2 HS AG HZc7 HZa.
  (* 0x8a390 .. 0x8a3a0: c->args[m]'s shadow byte, then c->args[m] := p; on to the frame's release at 0x8a3a4 *)
  paj_run_to_tok RUNTO1 HS HJ6 SHOK AI_Bspan (AF_arg_i + 0x16c).
  { ai_awr AG ltac:(unfold awr_byte; rewrite ?EF6; first
    [ left; clear - Ha Hsp1 FFS Hceil Hslo Hstk0 C1; lia
    | right; right; right; left; exists 0, fpos; split; [left; reflexivity | left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite ?EF6; fold F; clear - Ha; lia]
    | right; right; right; left; exists 0, fpos; split; [left; reflexivity | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; unfold shadow_addr; rewrite ?EF6; fold F; rewrite <- SB_SHADOW_OFF; unfold SB in *; clear - Ha; lia]
    | right; right; right; right; left; split;
      [ unfold FP; rewrite (proj2 (Z.ltb_lt m REC_ARGS_MAX) Em5);
        first [ exists (c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); split; [left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS; clear - Ha; lia]
              | exists (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8);
                split; [right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_ARGS; clear - Ha; lia] ]
      | split; [apply (HPROG B HB); apply (ai_slot_PG c _ Hc); clear - Ha Em5 Hm6; unfold REC_ARGS_MAX in *; lia
               | apply (cif_prog_img _ _ IMG); apply (ai_slot_PG c _ Hc); clear - Ha Em5 Hm6; unfold REC_ARGS_MAX in *; lia] ] ]). }
  match goal with HFx : frame_of ?Ef ?rsf (mrestrict (w_H W6) ?m0) (mrestrict (w_H W6) ?m1) |- _ =>
    assert (HKP2 : forall a, p <= a < p + (Z.of_nat (length (dec v)) + 1) ->
              aview SEGS (w_H W6) m1 a = aview SEGS (w_H W6) mem6 a)
      by (intros a Ha; rewrite (ai_aview_kept SEGS Ef rsf (w_H W6) m0 m1 a HFx ltac:(clear - Ha Hp Hpceil C1; lia) ltac:(ai_nowrange2 AG HPA a Ha));
          exact (HKP a Ha)) end.
  clear_frames. clear HKP. rename HKP2 into HKP.
  (* 0x8a3a4 on: the frame's release, as in the other branch, on the call's later layout *)
  pose proof (proj1 HJ6) as HAR7.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR7 Hfin6) as (_ & _ & HFpres7 & HFSpres7).
  change (fs_frame_bytes 0) with 64 in HFpres7, HFSpres7. change (64 / 8) with 8 in HFSpres7.
  rewrite EF6 in HFpres7, HFSpres7.
  destruct (FFL _ _ _ _ _ 0 fpos HAR7 Hfin6) as (HFLpres7 & HFLown7 & HFLapp7 & HFLrng7).
  rewrite EFL6 in HFLpres7, HFLown7, HFLapp7, HFLrng7.
  assert (HnoF7 : forall a, F <= a < F + 64 -> ~ aowned B ly6 S6 a) by (intros a Ha; exact (proj2 (HFpres7 a Ha))).
  ai_fs_rw HS 1029%nat E1029 HFSpres7.
  (* the flag byte FL (below alloc_ceiling, outside the image, below or above the shadow band: HFLrng7) is apart from
     the saved registers (above alloc_ceiling), from c->nargs and c->args[m] (image statics) and from the frame's
     shadow (SB + F / 8 with F + 64 <= alloc_ceiling, F = 32 * (F / 32)): one small lia over those facts each *)
  ai_flag_region_q HS AG E1028 HFLpres7 HFLrng7 HFLown7 HnoF7
    ltac:(clear - HFLrng7 Hc0 Hc1 Hm6 Em5 HFceil HF4096 Hceil Hslo FFS C1 HFq HF8 HF8lo HF8hi Hsp1;
          unfold zone2, off_img in HFLrng7; unfold REC_ARGS_MAX in *; lia).
  paj_run_flag_sh RUNF1 HS HJ6.
  + lia.
  + ai_wrange_x AG fpos F FL EF6 EFL6 ltac:(fun Hr => right; right; right; right; left; split;
      [ unfold FP; rewrite (proj2 (Z.ltb_lt m REC_ARGS_MAX) Em5);
        first [ exists (c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); split; [left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS; clear - Hr; lia]
              | exists (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8);
                split; [right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_ARGS; clear - Hr; lia] ]
      | split; [apply (HPROG B HB); apply (ai_slot_PG c _ Hc); clear - Hr Em5 Hm6; unfold REC_ARGS_MAX in *; lia
               | apply (cif_prog_img _ _ IMG); apply (ai_slot_PG c _ Hc); clear - Hr Em5 Hm6; unfold REC_ARGS_MAX in *; lia] ]).
  + rewrite EFL6. ai_flag0 E1028.
  + (* at the return: the two stores' values, the copy still in its block, then the post *)
    match goal with HFx : frame_of ?Ef ?rsf (mrestrict (w_H W6) ?m0) (mrestrict (w_H W6) ?m1) |- _ =>
      assert (HKP3 : forall a, p <= a < p + (Z.of_nat (length (dec v)) + 1) ->
                aview SEGS (w_H W6) m1 a = aview SEGS (w_H W6) mem6 a)
        by (intros a Ha; rewrite (ai_aview_kept SEGS Ef rsf (w_H W6) m0 m1 a HFx ltac:(clear - Ha Hp Hpceil C1; lia) ltac:(ai_nowrange2 AG HPA a Ha));
            exact (HKP a Ha)) end.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let rs := eval vm_compute in (ss_mem ssx) in
      let i10 := idx_of_base rs 10%nat in let i10 := eval vm_compute in i10 in
      let r10 := eval vm_compute in (nth i10 rs got_regionP) in
      let i30 := idx_of_base rs 1030%nat in let i30 := eval vm_compute in i30 in
      let r30 := eval vm_compute in (nth i30 rs got_regionP) in
      pose proof (st_ok_pi_region_nth Ex ssx msx i10 r10 HS ltac:(vm_compute; reflexivity)) as HR10;
      pose proof (st_ok_pi_region_nth Ex ssx msx i30 r30 HS ltac:(vm_compute; reflexivity)) as HR30 end.
    pose proof (field_of_region _ _ _ c _ _ _ _ _ 4 4%N (SOff 34 1) (m + 1) HR10 ltac:(evalE AG)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot]; rewrite E34, unsigned_lit_small by (unfold REC_ARGS_MAX in *; lia); reflexivity)
      ltac:(cbn; unfold REC_ARGS_MAX in *; lia) ltac:(cbn; lia)) as VN.
    pose proof (field_of_region _ _ _ (c + 8 + 8 * m) _ _ _ _ _ 0 8%N (SOff 204 0) p HR30
      ltac:(evalE AG; rewrite E1030; apply unsigned_lit_small; unfold REC_ARGS_MAX in *; lia)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot]; rewrite E204, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as VA.
    cbn [ms_mem restrict] in VN, VA. clear HR10 HR30.
    prreg HS (1%bv : bv 5) Z1.
    lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET1 Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
    intros mat'. apply (apost_baseF_of_base (fx := fx1) SEGS). unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
      exists ly6, (stack_free_state 0 fpos S6), rg, mm, mdx end.
    split; [rewrite Z1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
            rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
    split; [cbn [ms_mem]; eapply (ajournal_mono_k SEGS B);
            [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ6 | unfold EV_ARG_I, EV_XSTRDUP; lia]|].
    split; [apply aregs_preserved_eqs; ai_creg HS AG EE|].
    split.
    { change (blocks_bytes (stack_free_state 0 fpos S6)) with (blocks_bytes S6). rewrite <- Hbb2.
      unfold LIVE_ARG_I, LIVE_XSTRDUP. lia. }
    split.
    { unfold XM_ARG_I.
      apply (mle_weaken MT S _ (0 + XM_XSTRDUP MT (dec v)) _ MTL); [|lia].
      unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL).
      apply (mle_station MT S S2 S6 0 _ MTL); [|exact Hmo6].
      rewrite ES2. apply (mo_le_set_fs_r MT MTFL). exact (mle_start MT S MTL). }
    right. split; [exact Em5|]. exists p. cbv zeta.
    split; [exact Hp|].
    split; [change (ablocks B ly6 (stack_free_state 0 fpos S6)) with (ablocks B ly6 S6); rewrite <- Eab; exact HPerm6|].
    split; [rewrite <- Eab; exact Hapart6|].
    split; [unfold CALL_OFF_NARGS; exact (ai_aval_of_val _ _ _ _ _ _ VN)|].
    split; [unfold CALL_OFF_ARGS; rewrite Z.add_0_r in VA; exact (ai_aval_of_val _ _ _ _ _ _ VA)|].
    destruct Hpstr as (Hpb & Hp0). split; [|exact Hp0].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (HKP3 (p + Z.of_nat i) ltac:(lia)). exact (Hpb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
End c.
End b.
End a.
