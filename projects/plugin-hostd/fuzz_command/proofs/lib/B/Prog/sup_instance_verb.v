(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_instance_verb (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_instance_verb = 0x8b8f8, 141 instructions): it proves
   `tsup_instance_verb_spec` (lib/B/Prog/sup_instance_verb_c.v, the frozen statement of a working branch 707acd856cb,
   byte-identical on the B base fc8bcbd8b42 this walk builds on) in the form of
   cgif_file_fuzzer's per-function walks, after lib/A/Prog/answer_code.v (a working branch 2ba4488ce71: a
   class-N side-stack frame taken by __asan_stack_malloc_N, its header and shadow, and its release by the flag
   store) and lib/B/Prog/socket_send.v (a working branch a470f91dbfb: the B kit's runs, calls and
   return). It is the B re-walk of the ASan walk lib/A/Prog/sup_instance_verb.v (a working branch
   2beecf4cd76), at B's addresses and B's shape: B calls record() and arg_s() where A inlined record(), and
   inlines arg_i (the snprintf of the ledger into the class-0 side-stack frame), and it calls answer and releases
   its frame instead of A's tail jump. The function has no ASan report call; its two UBSan trap branches (0x8ba50
   `bltu s4,s3` and 0x8ba60 `beqz a0`, both of `line += strspn(line, " \t")`, both to the unimp at 0x8bb28) are
   refuted where the walk meets them, by sivb_br_8ba50 and sivb_br_8ba60 (sup_instance_verb_aux.v) from the line's
   block premise and strspn's count <= |line|. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI0s YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0d_tail YG0q YG05 YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecCells CmdRecRo CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_canonical_c hand_back_c record_c arg_line_c arg_s_c rec_shape_of_c answer_c sup_instance_verb_c
sup_instance_verb_aux sup_instance_verb_kit sup_instance_verb_snp sup_instance_verb_rec sup_instance_verb_post.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
(* CmdRecAns / CmdSnText (a Theorem Labs lane) change zify's division setting; this file's lia calls were written with it on
   (a Theorem Labs lane 14:17Z, SETTINGS TRAP) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a disjunction kept out of lia's sight: every lia call case-splits on each disjunction in its context, so the
   walk's lasting disjunctive facts are held under this name and opened only where they are used *)
Definition sivb_hold (P : Prop) : Prop := P.
Definition sivb_unhold {P : Prop} (h : sivb_hold P) : P := h.

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
(* the statement's Section hypotheses (lib/B/Prog/sup_instance_verb_c.v on a working branch 357b1f0783f), verbatim *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the facts a Theorem Labs lane states only at its pinned instance (PI := PB_cmd), under the lemma's own name (a Theorem Labs lane's
   naming rule of 09:4xZ); every other record fact comes from lib/B/Prog/CmdRec*.v by `exact`, since those are
   stated for any segs and B given AR_laws, CmdBSyms and cmd_img_facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_palib : PALib B.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the use-after-return GOT word and flag cell, the class-0 side-stack entry's pc and the four cells' separation
   (lib/B/Prog/PaLibF.v Record PALibF): CmdRecRest.cmd_palibf at PB_cmd *)
Hypothesis TLF : PALibF B.
(* the side-stack frames' flag cells (CmdRecRest.cmd_frame_flag_law at tfibsegs) *)
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.

Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let ML : model_laws (as_universe B) := CmdRecRest.cmd_model_laws B HB.
Let SMP : stack_malloc_progressP B := CmdRecRest.cmd_stack_malloc_progress B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.

(* the write windows of the five regions the walk carries from the frame setup on: the frame's shadow, its flag
   word (no window), its header, the realigned stack slot and the own stack frame *)
Ltac sivb_awr5 fpos sp1 regs FS Vs Vf V2 V34 EFA :=
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1041%nat); [reflexivity | exact Vs |
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
  right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |];
apply (awr_ok_cons_ro _ _); [cbn; lia|];
eapply (YCbq.awr_ok_cons_gen _ _) with (k := 1028%nat); [reflexivity | exact Vf |
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
  left; unfold in_zr; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes 0) with 64; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 34%nat) (d := sp1 - spZ regs);
  [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off _ _) with (n := 2%nat) (d := 0);
  [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |];
apply (awr_ok_nil _ _).

(* the regions of the class-0 side-stack frame F = frame_addr ly 0 fpos (64 bytes): its header [F, F + 24) (the
   magic, the descriptor and this function's address), the flag word at F + 56 = F + fs_frame_bytes 0 - 8 that
   the release reads (0x8bac4), its 8 shadow bytes, and the realigned stack slot [sp1, sp1 + 8) the frame
   pointer goes to. The 16 bytes of b = F + 32 that the snprintf writes are in NO region: the walk takes that
   write from the entry's contract, not from the executor. *)
Definition sivb_fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 24 0 24 [].
Definition sivb_fr_flg : YP09.region := YP09.mkRegion (Some 1028%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))].
Definition sivb_fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 8 [].
Definition sivb_fr_sp1 : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 8 [].
Definition sivb_shx_F : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).

Theorem tsup_instance_verb_holds : tsup_instance_verb_spec B MT.
Proof.
unfold tsup_instance_verb_spec.
intros ly S W regs mem md ch pl ledger line R O HPRE HRM0 HROD HRO H10 Hpl64 H11 Hled HLB HLSTR HLL HLAP HREP HFR HEV HLIVE HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SUP_INSTANCE_VERB_STK = 16704) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (HRS : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HLS : ARG_LINE_STK = 16480) by (vm_compute; reflexivity).
assert (HAS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HSS : REC_SHAPE_OF_STK = 8288) by (vm_compute; reflexivity).
assert (HNS : ANSWER_STK = 16592) by (vm_compute; reflexivity).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sivk_O_in B ly S _ R O HREP).
assert (HOpos : forall pn, In pn O -> 0 < fst pn).
{ intros [b n] Hpn. destruct (sivk_blk_bounds B ly S W mem md b n HAR (HOin _ Hpn)) as (Hb & _). cbn. lia. }
assert (HFPpos : Forall (fun r => 0 < fst r) (sivk_FP O)) by exact (sivk_FP_pos O HOpos).
assert (HFPlow : forall a, inFP (sivk_FP O) a -> 0 <= a < alloc_ceiling)
  by (intros a Ha; exact (sivk_FP_low B HB cmd_img_facts_tfib ly S W mem md O a HAR HOin Ha)).
pose proof HREP as (Q0 & HQ0 & HOQ0).
pose proof HQ0 as (_ & _ & _ & (HC1 & _) & _).
set (sp1 := 32 * ((spZ regs - 96) / 32)).
assert (Hm16 : (spZ regs - 96) mod 16 = 0)
  by (replace (spZ regs - 96) with (spZ regs + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
destruct (snt_sp1_facts (spZ regs - 96) ltac:(lia) Hm16) as (Hsp1 & Hsp1a & Hsp1b).
fold sp1 in Hsp1, Hsp1a, Hsp1b.
change ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O) with (sivk_FP O).
set (FP := sivk_FP O).
pose proof (ajournal_init SEGS B SUP_INSTANCE_VERB_STK FP ly S W regs mem md ch HPRE) as HJ.
pose proof (sivb_entry B LAWS cmd_palib TLF SUP_INSTANCE_VERB_STK W ly S regs mem md ch sp1
  ltac:(rewrite FS; lia) HPRE ltac:(lia) Hsp1a) as HS.
unfold cfg_at. change (w64 (BASE + AF_sup_instance_verb)) with (Z_to_bv 64 (BASE + AF_sup_instance_verb)).
remember (Eimg (Ereg regs (sivb_extra0 (as_uar_cell B) sp1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
(* run 1: the prologue (96 bytes, ra and s0 .. s9 saved), the realignment `andi sp,sp,-32`, the shadow base and
   the use-after-return flag through their GOT words, the flag's branch at 0x8b958 (the flag is the record's const
   cell 0xb0c40 = 1, so only the side-stack arm runs) and the call of __asan_stack_malloc_0 at 0x8b960 *)
paj_run_shc RUNP RUNC HS HJ.
{ eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
  repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
sivb_preg HS (1%bv : bv 5) R1. sivb_preg HS (2%bv : bv 5) R2. sivb_preg HS (3%bv : bv 5) R3.
sivb_preg HS (4%bv : bv 5) R4. sivb_preg HS (9%bv : bv 5) R9. sivb_preg HS (10%bv : bv 5) R10.
rewrite (snt_denot_and_m32 E 2 (spZ regs) (-96) Esp ltac:(lia) ltac:(lia) ltac:(lia)) in R2.
change (spZ regs + -96) with (spZ regs - 96) in R2. fold sp1 in R2.
rewrite sivb_denot_add0, (snt_denot_and_m32 E 2 (spZ regs) (-96) Esp ltac:(lia) ltac:(lia) ltac:(lia)) in R9.
change (spZ regs + -96) with (spZ regs - 96) in R9. fold sp1 in R9.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E HEI 21556) in R1.
rewrite sivb_denot_off0, (EE 3%nat 3%bv eq_refl) in R3. rewrite sivb_denot_off0, (EE 4%nat 4%bv eq_refl) in R4.
(* the realigned stack pointer, and s1 beside it, become the atom 34 the walk seats its slot on *)
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl
  ltac:(rewrite sivb_denot_off0, E34; cbn [ms_regs restrict]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok _ _ ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS E ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl
  ltac:(rewrite sivb_denot_off0, E34; cbn [ms_regs restrict]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. sivb_norm_ssp HS.
pose proof (palf_sm B TLF 0 ltac:(cbn; tauto)) as SM0. change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in SM0.
rewrite SM0.
assert (Qsp : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
(* __asan_stack_malloc_0 (0x8b960): the class-0 side-stack frame, 64 bytes *)
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B cmd_palib) ML SMP 0 (ASTACK_MALLOC0 fx) ltac:(lia) W (ms_regs ms1) (ms_mem ms1)
  SUP_INSTANCE_VERB_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 21556)) HJ);
  [ exact Qsp | rewrite Zminus_mod, Hsp1b, Hal16; reflexivity | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
  | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | pose proof (count_cid_le_length 0 (frames S)); change (fs_frames 0) with 16384; lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJS & (fS2 & ES2)).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & _ & HK3 & _ & _ & _).
(* the zero slot's region goes: when the entry sp is 32-aligned it IS the realigned slot, which the walk now
   seats on the atom 34 (the slot is never read) *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply sivb_region_kept_hi; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 R9 R10 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HAE1 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E1)
  by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
destruct (FFL _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
replace (F + 64 - 8) with (F + 56) in Hflag by lia.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HFin : in_app F 64) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HAE2 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E2)
  by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1040 : ew E2 1040 = Z_to_bv 64 FL)
  by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2028 : ew E2 1028 = Z_to_bv 64 F) by (rewrite HE2, ew_havoc_old by lia; exact E1028).
clear HE2.
assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (V2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (V34 : bv_unsigned (ew E2 34) = sp1) by (rewrite OLD2 by lia; exact U34).
assert (V1028 : bv_unsigned (ew E2 1028) = F) by (rewrite E2028; apply unsigned_lit_small; lia).
assert (V1040 : bv_unsigned (ew E2 1040) = FL) by (rewrite E1040; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HF8b : F / 8 <= 17592185978880) by (apply Z.div_le_upper_bound; lia).
assert (V1041 : bv_unsigned (ew E2 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 1028 (HPTR 5) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite V1028; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_alias Ev _ msv sivb_shx_F (SOff 1041 0) HS
  (shadow_decl_ok Ev 1028 32 1041 F SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. sivb_norm_ssp HS.
(* the realigned slot [sp1, sp1 + 8) the frame pointer goes to (`sd s8,0(s1)`, 0x8b994) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sivb_fr_sp1 HS eq_refl
  ltac:(unfold region_ok, sivb_fr_sp1; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite V34; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply HJ2pres; rewrite FS; lia)
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sivb_fr_sp1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite V34, V2; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sivb_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sivb_fr_hdr HS eq_refl
  ltac:(unfold region_ok, sivb_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sivb_fr_hdr, sivb_fr_sp1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sivb_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sivb_fr_flg HS eq_refl
  ltac:(unfold region_ok, sivb_fr_flg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite V1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val SEGS Ev _ F 56 8 (SOff 1040 0) FL); [rewrite sivb_denot_off0; exact E1040 | lia | lia |];
        exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sivb_fr_flg, sivb_fr_hdr, sivb_fr_sp1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite V1028, V2, V34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sivb_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sivb_fr_shd HS eq_refl
  ltac:(unfold region_ok, sivb_fr_shd; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite V1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS);
        replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
        apply (proj1 (HFSpres o ltac:(lia))))
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sivb_fr_shd, sivb_fr_flg, sivb_fr_hdr, sivb_fr_sp1;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite V1041, V1028, V2, V34; unfold SB;
        pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
        repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sivb_norm_ssp HS.
(* run 2: the frame pointer into the realigned slot, the frame header (magic 0x41b58ab3, the descriptor
   "1 32 16 7 b.i:237" at 0x15923, this function's own address 0x8b8f8) and the frame's shadow
   (f1 f1 f1 f1 f8 f8 f3 f3), up to the call of record() at 0x8b9f8 *)
paj_run_shc RUNP RUNC HS HJ2.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact V1041 |
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
  right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; rewrite <- SB_SHADOW_OFF;
  change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact V1028 |
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
  left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs);
  [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0);
  [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
(* the frame and its shadow are apart (low band: the frame below the shadow; high band: above it) *)
assert (HFSd : sivb_hold (F + 64 <= SB + F / 8 \/ SB + F / 8 + 8 <= F)).
{ unfold sivb_hold, SB. pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia. }
clear HFin. change (sivb_hold (F + 64 <= 0x10000 \/ 0x606000 <= F)) in HFoff.
pmkst HS.
sivb_preg HS (1%bv : bv 5) Q1. sivb_preg HS (2%bv : bv 5) Q2. sivb_preg HS (3%bv : bv 5) Q3.
sivb_preg HS (4%bv : bv 5) Q4. sivb_preg HS (8%bv : bv 5) Q8. sivb_preg HS (10%bv : bv 5) Q10.
sivb_preg HS (19%bv : bv 5) Q19. sivb_preg HS (20%bv : bv 5) Q20. sivb_preg HS (22%bv : bv 5) Q22.
cbn [sv_denot] in Q10, Q1. rewrite (img_env_codeptr E2 HEI2 21708) in Q1.
rewrite sivb_denot_off0, OLD2, E34 in Q2 by lia.
rewrite sivb_denot_off0, OLD2, (EE 3%nat 3%bv eq_refl) in Q3 by lia. rewrite sivb_denot_off0, OLD2, (EE 4%nat 4%bv eq_refl) in Q4 by lia.
rewrite sivb_denot_off0, OLD2, Esp in Q8 by lia.
rewrite sivb_denot_off0, OLD2, (EE 10%nat 10%bv eq_refl), H10 in Q19 by lia.
rewrite sivb_denot_off0, OLD2, (EE 11%nat 11%bv eq_refl), H11 in Q20 by lia.
pose proof (proj1 HJ2) as HAR3.
assert (Qsp3 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite Q2, unsigned_lit_small by lia; lia).
(* where the recorder's state and the live blocks lie: none of them in the frame, its shadow, its flag or the
   stack *)
set (KA := fun a : Z => (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
  (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n)).
assert (KIMG : forall a, KA a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
  (in_img SEGS a /\ 0x10000 <= a < 0x606000 /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))).
{ intros a Ha. rewrite (YF0m.ts_owned B HB), (YF0m.ts_errno B HB). unfold YF0m.TFIB_ERRNO.
  destruct Ha as [Ha | [Ha | Ha]]; [right | right | left; exact Ha].
  - split; [apply cmd_prog_img; exact (sivk_grec_in a Ha)|]. unfold A_G_REC, REC_SIZE in Ha. split; [lia|].
    split; [apply (sivb_not_in_ranges _ 0x5e32c0 0x5e3680); [vm_compute; reflexivity | lia] | lia].
  - split; [apply cmd_prog_img; exact (sivk_spill_in a Ha)|]. unfold A_REC_SPILL, SC_SIZE in Ha. split; [lia|].
    split; [apply (sivb_not_in_ranges _ 0x5e3760 0x5e3798); [vm_compute; reflexivity | lia] | lia]. }
assert (KLOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & Hr & _ & _)].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & _ & _).
    assert (Hpn2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hpn).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hpn2) as (_ & _ & _ & _ & Hpres2 & _).
    pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p n 0 fpos HAR2 Hpn2 Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
    intros ->. exact (proj2 (Hpres2 FL ltac:(lia)) HFLo).
  - pose proof (sivb_unhold HFoff) as HFo.
    split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (HFLimg Hi). }
assert (K01 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & _). apply (sivb_aview_frame_pt E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
  sivb_nwin_tac ltac:(fun H => rewrite ?Usp, ?U34 in H; lia). }
assert (K12 : forall a, KA a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms1) a).
{ pose proof HK as (_ & HK2 & _ & _ & _ & _).
  intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & _ & Ho & He)].
  - replace a with (p + (a - p)) by lia. apply (HK2 p n (a - p) Hpn); [lia | intros []].
  - exact (HK3 a Hi Ho He). }
assert (K23 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (sivb_aview_frame_pt E2 _ (w_H W) mem2 (ms_mem ms3) a HFr3); [lia|].
  sivb_nwin_tac ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; lia). }
assert (K03 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; rewrite (K23 a Ha), (K12 a Ha), (K01 a Ha); reflexivity).
assert (HFPKA : forall a, inFP FP a -> KA a).
{ intros a (r & Hr & Hrq). unfold FP, sivk_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hrq.
  - left. exact Hrq.
  - right. left. exact Hrq.
  - right. right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p q] & <- & Hpq). cbn [fst snd] in Hrq.
    exists p, q. split; [exact (HOin _ Hpq) | exact Hrq]. }
assert (HNFP : forall a, spZ regs <= a < 2 ^ 64 -> ~ inFP FP a).
{ intros a Ha Hf. pose proof (HFPlow a Hf). lia. }
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms3)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly S2 W (ms_mem ms3) _ _ _ _ _ HAR HOin HJ2 HROD).
assert (HREP3 : rec_repA B ly S2 (rdW W (ms_mem ms3)) R O).
{ apply (sivk_rec_repA_ext B ly S (rdW W mem) ly S2 _ R O HREP).
  - intros pn Hpn. rewrite Eab. exact (HOin pn Hpn).
  - intros a Ha. apply K03. destruct Ha as [Ha | [Ha | ([b n] & Hpn & Ha)]]; [left; exact Ha | right; left; exact Ha|].
    right. right. exists b, n. split; [exact (HOin _ Hpn)|]. cbn [fst snd] in Ha.
    destruct (sivk_blk_bounds B ly S W mem md b n HAR (HOin _ Hpn)) as (_ & _ & _ & Hnr & _). lia. }
assert (HCH3 : exists ch3, achain ly (rdW W (ms_mem ms3)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms3)) ch3).
{ unfold s0Z. rewrite Q8, unsigned_lit_small by lia.
  pose proof (st_ok_region_nth E2 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
  destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    eapply (achain_push ly (rdW W mem) (rdW W (ms_mem ms3)) (spZ regs) (s0Z regs) (raZ regs) ch);
    [exact Hch | lia | | | | exact Hra4 | lia | exact (sivb_Z_mod_16_8 _ Hal16) | exact Hlt | lia].
    + intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ2 a Ha (HNFP a Ha)).
    + apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
      replace (spZ regs - 8) with (spZ regs + -8) by lia.
      refine (field_of_region E2 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 V2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
      | unfold raZ; apply bv_unsigned_in_range | lia].
    + apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
      replace (spZ regs - 16) with (spZ regs + -16) by lia.
      refine (field_of_region E2 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 V2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
      | unfold s0Z; apply bv_unsigned_in_range | lia].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH3 as (ch3 & HCH3).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & HNEV3 & _).
(* the meter's parts are nonnegative *)
assert (XR0 : 0 <= XM_RECORD MT R).
{ unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL). destruct (Nat.ltb _ _); lia. }
assert (XL0 : 0 <= XM_ARG_LINE MT line).
{ unfold XM_ARG_LINE, XM_REC_CANONICAL, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
assert (XA0 : 0 <= XM_ARG_S MT (Some (dec ledger))).
{ unfold XM_ARG_S, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
(* record's footprint is the recorder's: g_rec's ncalls, the slot (in g_rec's table or record.spill), the spill's
   argument blocks *)
assert (HRFKA : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> KA a).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
  { left. unfold OFF_NCALLS, REC_SIZE in *. lia. }
  apply inFP_cons in Ha as [Ha | Ha].
  { destruct (sivk_slot_bounds R HC1) as [Hs | Hs]; [left; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    right. left. rewrite Hs in Ha. unfold A_REC_SPILL, SC_SIZE in *. lia. }
  destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
  destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
  right. right. exists b, n. split; [exact (HOin _ Hbn) | exact Hba]. }
(* ---- the call of record(REC_INSTANCE_VERB) (0x8b9f8) ---- *)
rewrite (rca_sig_record cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms3) (ms_mem ms3) (Z_to_bv 64 (BASE + AF_record)) SUP_INSTANCE_VERB_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly S2 _ _ RECORD_STK _ (EV_RECORD R) (sp1 - spZ regs) (getr (ms_regs ms3) 1) ch3 _ HJ2 Qsp3
    ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity));
  [ lia | rewrite HRS; lia | rewrite HRS, FS; lia | rewrite Q3; exact Hgp | rewrite Q4; exact Htp | reflexivity
  | rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite Q1, unsigned_lit_small by lia; lia
  | exact HCH3
  | | | ].
  - intros HPRE3. pose proof (TRECORD fx ly S2 W (ms_regs ms3) (ms_mem ms3) _ ch3 REC_INSTANCE_VERB R O HPRE3) as T.
    unfold apost_base in T. apply T.
    + exact HROD3.
    + rewrite Q10. reflexivity.
    + exact sivb_fn_range.
    + exact HREP3.
    + unfold EV_SUP_INSTANCE_VERB, EV_ARG_LINE, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL, EV_XMALLOC in HEV. lia.
    + rewrite ES2. apply (mo_ok_set_fs MT MTLF). apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_INSTANCE_VERB.
      pose proof (XN0 (snd (sup_instance_verb_m R line ledger))). lia.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { apply (sivk_awr_grec B HB cmd_img_facts_tfib). unfold OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (sivk_awr_slot B HB cmd_img_facts_tfib _ _ _ _ _ _ _ _ R a HC1). unfold CALL_SIZE. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
    apply (sivk_awr_blk B _ _ _ _ _ _ _ _ b n a Hbn); [rewrite Eab; exact (HOin _ Hbn) | exact Hba].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    destruct (KLOC a (HRFKA a Ha)) as (Hb & _). rewrite FS in Hw. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HKR).
destruct HKR as (Fr & O1 & R10 & HPermF & HFlen & HFO & HREP1 & HO1 & HBB1 & MLE1).
rewrite Q1.
pose proof (proj1 HJ3) as HAR4.
pose proof HJc3 as (_ & Hly3 & _ & _ & _ & Hfrs3 & _). cbn [app] in Hfrs3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR3 Hly3) as (Eab3 & Efa3 & _).
assert (EFA3 : frame_addr ly3 0 fpos = F) by (rewrite Efa3; reflexivity).
assert (Hfin3 : In (0, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR4 Hfin3) as (_ & _ & HFpres3 & HFSpres3). rewrite EFA3 in HFpres3, HFSpres3.
change (fs_frame_bytes 0) with 64 in HFpres3, HFSpres3. change (64 / 8) with 8 in HFSpres3.
jafter_call_keep_hi HS 1042%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0;1;2;3;4]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly3 S3 W3 mem3 md3 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc3 V1041 Hfin);
    [ unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (KLOC a (HRFKA a HFa)) as (_ & _ & HnS & _); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres3 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly3 S3 W3 mem3 md3 _ 1028 F _ _ _ _ _ 0 fpos HJc3 V1028 Hfin);
    [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC a (HRFKA a HFa)) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly S2 W (ms_mem ms3) _ ly3 S3 W3 mem3 md3 _ 1028 F _ _ _ _ _ 0 fpos HJc3 V1028 Hfin);
    [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (KLOC a (HRFKA a HFa)) as (_ & HnF & _); lia
    | intros a Ha; exact (proj1 (HFpres3 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc3 HJ3 V34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HRFKA a HFa)); lia].
  - eapply (region_kept_stack_sub SEGS B E2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc3 HJ3 V2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (KLOC a (HRFKA a HFa)); lia]. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
remember (havoc E2 1042 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HAE3 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E3)
  by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (OLD3 : forall n, (n < 1042)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (E1046 : ew E3 1046 = getr regs3 10).
{ rewrite HE3. change 1046%nat with (1042 + 4)%nat. rewrite (ew_havoc_new E2 1042 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE3.
assert (W2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact V2).
assert (W34 : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3 by lia; exact V34).
assert (W1028 : bv_unsigned (ew E3 1028) = F) by (rewrite OLD3 by lia; exact V1028).
assert (W1040 : bv_unsigned (ew E3 1040) = FL) by (rewrite OLD3 by lia; exact V1040).
assert (W1041 : bv_unsigned (ew E3 1041) = SB + F / 8) by (rewrite OLD3 by lia; exact V1041).
clear Q1 Q2 Q3 Q4 Q8 Q10.
(* run 3: s5 := the slot, a1 := the line, the call of arg_line (0x8ba04) *)
paj_run_shc RUNP RUNC HS HJ3.
{ sivb_awr5 fpos sp1 regs FS W1041 W1028 W2 W34 EFA3. }
rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md5 := m) in *; clearbody md5 end.
sivb_preg HS (1%bv : bv 5) P1. sivb_preg HS (2%bv : bv 5) P2. sivb_preg HS (3%bv : bv 5) P3.
sivb_preg HS (4%bv : bv 5) P4. sivb_preg HS (8%bv : bv 5) P8. sivb_preg HS (10%bv : bv 5) P10.
sivb_preg HS (11%bv : bv 5) P11.
cbn [sv_denot] in P1. rewrite (img_env_codeptr E3 HEI3 21720) in P1.
rewrite sivb_denot_off0, E1046, R10 in P10.
rewrite sivb_denot_off0, OLD3, OLD2, (EE 10%nat 10%bv eq_refl), H10 in P11 by lia.
rewrite sivb_denot_off0, OLD3, OLD2, E34 in P2 by lia.
rewrite sivb_denot_off0, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in P3 by lia.
rewrite sivb_denot_off0, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in P4 by lia.
rewrite sivb_denot_off0, OLD3, OLD2, Esp in P8 by lia.
pose proof (proj1 HJ3) as HAR5.
assert (Qsp5 : spZ (ms_regs ms5) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite P2, unsigned_lit_small by lia; lia).
assert (HSL : sivb_hold ((A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL))
  by exact (sivk_slot_bounds R HC1).
assert (HSLKA : forall a, rec_slot R <= a < rec_slot R + CALL_SIZE -> KA a).
{ intros a Ha. destruct (sivb_unhold HSL) as [Hs | Hs]; [left; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
  right. left. rewrite Hs in Ha. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
(* run 3 wrote only the frame's regions *)
assert (K35 : forall a, KA a -> aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (sivb_aview_frame_pt E3 _ (w_H W3) mem3 (ms_mem ms5) a HFr5); [lia|].
  sivb_nwin_tac ltac:(fun H => rewrite ?W2, ?W34, ?W1028, ?W1041 in H; lia). }
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms5)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly3 S3 W3 (ms_mem ms5) _ _ _ _ _ HAR HOin HJ3 HROD).
assert (HO1in : forall pn, In pn O1 -> In pn (ablocks B ly3 S3)) by exact (sivk_O_in B ly3 S3 _ _ O1 HREP1).
(* the line's block is none of the recorder's, so record() did not free it and kept its bytes *)
destruct HLB as (pb & kb & Hpbk & Hpb1 & Hpb2).
assert (HnOb : ~ In (pb, kb) O).
{ intros HO'. rewrite Forall_forall in HLAP. specialize (HLAP (pb, kb) HO'). unfold iv_apart in HLAP. cbn [fst snd] in HLAP. lia. }
assert (Hpbk3 : In (pb, kb) (ablocks B ly3 S3)).
{ rewrite <- Eab in Hpbk. apply (Permutation_in _ HPermF) in Hpbk. apply in_app_or in Hpbk as [H | H]; [exact H|].
  exfalso. exact (HnOb (HFO _ H)). }
destruct (sivk_blk_bounds B ly S W mem md pb kb HAR Hpbk) as (Hpb4096 & Hpbc & Hkb0 & Hkbr & _).
assert (HLB3 : in_blockA (ablocks B ly3 S3) pl (Z.of_nat (length line) + 1)) by (exists pb, kb; split; [exact Hpbk3 | lia]).
assert (HLKA : forall a, pl <= a < pl + Z.of_nat (length line) + 1 -> KA a)
  by (intros a Ha; right; right; exists pb, kb; split; [exact Hpbk | lia]).
assert (HLRF : forall a, pl <= a < pl + Z.of_nat (length line) + 1 ->
  ~ inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a).
{ intros a Ha HFa. apply inFP_cons in HFa as [HFa | HFa].
  { apply (sivk_blk_noimg B ly S W mem md pb kb a HAR Hpbk ltac:(lia)). apply cmd_prog_img.
    apply sivk_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
  apply inFP_cons in HFa as [HFa | HFa].
  { apply (sivk_blk_noimg B ly S W mem md pb kb a HAR Hpbk ltac:(lia)). apply cmd_prog_img.
    destruct (sivb_unhold HSL) as [Hs | Hs]; [apply sivk_grec_in; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    apply sivk_spill_in. rewrite Hs in HFa. unfold A_REC_SPILL, SC_SIZE in *. lia. }
  destruct (Nat.ltb (length (r_calls R)) 16); [exact (inFP_nil _ HFa)|].
  destruct (inFP_ablocks_fp_inv O _ HFa) as (b' & n' & Hbn & Hba).
  destruct (sivk_pair_dec (pb, kb) (b', n')) as [Eq | Hne]; [apply HnOb; rewrite Eq; exact Hbn|].
  destruct (sivk_blk_apart B ly S W mem md pb kb b' n' HAR Hpbk (HOin _ Hbn) Hne); lia. }
assert (HLSTR5 : astr_atR (rdW W3 (ms_mem ms5)) pl line).
{ apply (sivk_str_keep (rdW W mem)); [exact HLSTR|]. intros a Ha.
  rewrite (K35 a (HLKA a ltac:(lia))).
  replace a with (pb + (a - pb)) by lia.
  rewrite (sivk_keep_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pb kb (a - pb) HJc3 ltac:(rewrite Eab; exact Hpbk) Hpbk3
    ltac:(lia) ltac:(replace (pb + (a - pb)) with a by lia; exact (HLRF a ltac:(lia)))).
  replace (pb + (a - pb)) with a by lia. exact (K03 a (HLKA a ltac:(lia))). }
(* the slot's argument count: 0 after record() *)
assert (HN0 : aval_mem (rdW W3 (ms_mem ms5)) (rec_slot R + CALL_OFF_NARGS) 4 0).
{ pose proof (rec_repA_slot_nargs B ly3 S3 _ R REC_INSTANCE_VERB [] O1 HREP1 HC1) as N. cbn [length Z.of_nat] in N.
  apply (sivk_aval_keep (rdW W3 mem3)); [exact N|]. intros k Hk. apply K35. apply HSLKA.
  change (rec_slotA R) with (rec_slot R) in *. unfold CALL_OFF_NARGS, CALL_SIZE in *. lia. }
assert (HCH5 : exists ch5, achain ly3 (rdW W3 (ms_mem ms5)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms5)) ch5).
{ unfold s0Z. rewrite P8, unsigned_lit_small by lia.
  pose proof (st_ok_region_nth E3 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
  pose proof HJ3 as (_ & Hly5 & _). pose proof Hly5 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop5 & _).
  destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    eapply (achain_push ly3 (rdW W mem) (rdW W3 (ms_mem ms5)) (spZ regs) (s0Z regs) (raZ regs) ch);
    [apply (achain_ly_top ly ly3); [exact Etop5 | exact Hch] | rewrite Etop5; lia | | | | exact Hra4 | lia
    | exact (sivb_Z_mod_16_8 _ Hal16) | rewrite Etop5; exact Hlt | lia].
    + intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ3 a Ha (HNFP a Ha)).
    + apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
      replace (spZ regs - 8) with (spZ regs + -8) by lia.
      refine (field_of_region E3 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 W2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
      | unfold raZ; apply bv_unsigned_in_range | lia].
    + apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
      replace (spZ regs - 16) with (spZ regs + -16) by lia.
      refine (field_of_region E3 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 W2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
      | unfold s0Z; apply bv_unsigned_in_range | lia].
  - exists []. left. split; [right; left; rewrite Etop5; lia | reflexivity]. }
destruct HCH5 as (ch5 & HCH5).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & HNEV5 & _).
assert (LA0 : 0 <= LIVE_ARG_S (Some (dec ledger))) by (unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
assert (LN0 : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (HMOK2 : mo_ok MT S2 (XM_SUP_INSTANCE_VERB MT R line ledger)) by (rewrite ES2; apply (mo_ok_set_fs MT MTLF); exact HMOK).
(* ---- the call of arg_line(slot, line) (0x8ba04) ---- *)
rewrite (sivb_sig_arg_line cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W3 (ms_regs ms5) (ms_mem ms5) (Z_to_bv 64 (BASE + AF_arg_line)) SUP_INSTANCE_VERB_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly3 S3 _ _ ARG_LINE_STK _ EV_ARG_LINE (sp1 - spZ regs) (getr (ms_regs ms5) 1) ch5 _ HJ3 Qsp5
    ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity));
  [ lia | rewrite HLS; lia | rewrite HLS, FS; lia | rewrite P3; exact Hgp | rewrite P4; exact Htp | reflexivity
  | rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | exact HCH5
  | | | ].
  - intros HPRE5. pose proof (TARG_LINE fx ly3 S3 W3 (ms_regs ms5) (ms_mem ms5) _ ch5 (rec_slot R) pl 0 line HPRE5) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROD5.
    + exact P10.
    + exact P11.
    + exact Hpl64.
    + exact (proj1 (rec_slotA_home R HC1)).
    + exact HN0.
    + unfold REC_ARGS_MAX. lia.
    + exact HLB3.
    + exact HLSTR5.
    + exact HLL.
    + unfold EV_SUP_INSTANCE_VERB, EV_ARG_LINE, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL, EV_XMALLOC in *.
      rewrite Hnev2 in HNEV3. lia.
    + pose proof (LN0 (snd (sup_instance_verb_m R line ledger))). unfold LIVE_SUP_INSTANCE_VERB in HLIVE. lia.
    + apply (mok_station MT S2 S3 (XM_SUP_INSTANCE_VERB MT R line ledger) (XM_RECORD MT R) _ MTL HMOK2 MLE1 XL0).
      unfold XM_SUP_INSTANCE_VERB. pose proof (XN0 (snd (sup_instance_verb_m R line ledger))). lia.
  - intros a Ha. unfold REC_ARGS_MAX in Ha. cbn [Z.ltb Z.compare] in Ha.
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (sivk_awr_slot B HB cmd_img_facts_tfib _ _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_NARGS, CALL_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    apply (sivk_awr_slot B HB cmd_img_facts_tfib _ _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    unfold REC_ARGS_MAX in Ha. cbn [Z.ltb Z.compare] in Ha.
    assert (HaK : KA a).
    { apply HSLKA. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
      apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exact (False_ind _ (inFP_nil a Ha))]. }
    destruct (KLOC a HaK) as (Hb & _). rewrite FS in Hw. lia. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJc6 & HP6 & HKL).
cbv zeta in HKL. destruct HKL as (HBB6 & MLE6 & [(Hm6 & _) | (_ & p1 & Hp1 & Hperm6 & Hfresh6 & HN6 & HA6 & HSTR6)]).
{ exfalso. unfold REC_ARGS_MAX in Hm6. lia. }
rewrite P1.
pose proof (proj1 HJ6) as HAR6.
pose proof HJc6 as (_ & Hly6 & _ & _ & _ & Hfrs6 & _). cbn [app] in Hfrs6.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR5 Hly6) as (Eab6 & Efa6 & _).
assert (EFA6 : frame_addr ly6 0 fpos = F) by (rewrite Efa6; exact EFA3).
assert (Hfin6 : In (0, fpos) (frames S6)) by (rewrite Hfrs6; exact Hfin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6). rewrite EFA6 in HFpres6, HFSpres6.
change (fs_frame_bytes 0) with 64 in HFpres6, HFSpres6. change (64 / 8) with 8 in HFSpres6.
assert (HLFKA : forall a, inFP [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
  (rec_slot R + CALL_OFF_ARGS + 8 * 0, rec_slot R + CALL_OFF_ARGS + 8 * 0 + 8)] a -> KA a).
{ intros a Ha. apply HSLKA. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exact (False_ind _ (inFP_nil a Ha))]. }
jafter_call_keep_hi HS 1058%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0;1;2;3;4]%nat HS6.
match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E3 _ _ _ ly3 S3 W3 (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc6 W1041 Hfin3);
    [ unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; apply HLFKA in HFa; destruct (KLOC a HFa) as (_ & _ & HnS & _); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E3 _ _ _ ly3 S3 W3 (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1028 F _ _ _ _ _ 0 fpos HJc6 W1028 Hfin3);
    [ rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; apply HLFKA in HFa; destruct (KLOC a HFa) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E3 _ _ _ ly3 S3 W3 (ms_mem ms5) _ ly6 S6 W6 mem6 md6 _ 1028 F _ _ _ _ _ 0 fpos HJc6 W1028 Hfin3);
    [ rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; apply HLFKA in HFa; destruct (KLOC a HFa) as (_ & HnF & _); lia
    | intros a Ha; exact (proj1 (HFpres6 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc6 HJ6 W34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; apply HLFKA in HFa; destruct (KLOC a HFa); lia].
  - eapply (region_kept_stack_sub SEGS B E3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc6 HJ6 W2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; apply HLFKA in HFa; destruct (KLOC a HFa); lia]. }
rewrite <- restrict_mkst_fx in HS6. clear HS. rename HS6 into HS.
remember (havoc E3 1058 (map (getr regs6) CLOB)) as E4 eqn:HE4 in HS.
assert (HAE4 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E4)
  by (rewrite HE4; apply env_agree_havoc_ge; [lia | exact HAE3]).
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (OLD4 : forall n, (n < 1058)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
clear HE4.
assert (X2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact W2).
assert (X34 : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact W34).
assert (X1028 : bv_unsigned (ew E4 1028) = F) by (rewrite OLD4 by lia; exact W1028).
assert (X1040 : bv_unsigned (ew E4 1040) = FL) by (rewrite OLD4 by lia; exact W1040).
assert (X1041 : bv_unsigned (ew E4 1041) = SB + F / 8) by (rewrite OLD4 by lia; exact W1041).
clear P1 P2 P3 P4 P8 P10 P11.
(* run 4: b's shadow := 00 00 (0x8ba08, 0x8ba0c), a2 := "%d", a1 := 16, a0 := b, a3 := ledger, the call of the
   snprintf wrapper (0x8ba24) *)
paj_run_shc RUNP RUNC HS HJ6.
{ sivb_awr5 fpos sp1 regs FS X1041 X1028 X2 X34 EFA6. }
rename ms into ms7, mat into mat7, HF into HF7, HFr into HFr7, HG into HG7.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md7 := m) in *; clearbody md7 end.
sivb_preg HS (1%bv : bv 5) T1. sivb_preg HS (2%bv : bv 5) T2. sivb_preg HS (3%bv : bv 5) T3.
sivb_preg HS (4%bv : bv 5) T4. sivb_preg HS (10%bv : bv 5) T10. sivb_preg HS (11%bv : bv 5) T11.
sivb_preg HS (12%bv : bv 5) T12. sivb_preg HS (13%bv : bv 5) T13.
cbn [sv_denot] in T1, T11, T10. rewrite (img_env_codeptr E4 HEI4 21752) in T1. rewrite X1028 in T10.
rewrite sivb_denot_off0, (img_env_atomP E4 292 HEI4 ltac:(unfold A_TEXT, A_LIM; lia)) in T12.
change (VAL 292) with (VAL (A_OBJ 51)) in T12. rewrite (sivb_obj51 VOBJS) in T12.
rewrite sivb_denot_off0, OLD4, OLD3, OLD2, (EE 11%nat 11%bv eq_refl), H11 in T13 by lia.
rewrite sivb_denot_off0, OLD4, OLD3, OLD2, E34 in T2 by lia.
rewrite sivb_denot_off0, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in T3 by lia.
rewrite sivb_denot_off0, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in T4 by lia.
assert (Qsp7 : spZ (ms_regs ms7) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite T2, unsigned_lit_small by lia; lia).
assert (HF8m : F mod 8 = 0) by (rewrite HFq, Z.mul_comm; replace 64 with (8 * 8) by reflexivity; rewrite Z.mul_assoc; apply Z_mod_mult).
(* b's two shadow bytes are 00 (run 4's stores) *)
assert (ZS7 : forall j, 4 <= j < 6 -> rdW W6 (ms_mem ms7) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E4 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
  assert (Hj2 : j = 4 \/ j = 5) by lia.
  destruct Hj2 as [-> | ->]; (apply (aview_of_val_mem1 SEGS); [|lia]);
  (lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
     refine (field_of_region E4 _ 1041 (SB + F / 8) _ 0 8 0 8 od 1%N (SLit 0) 0 HR0 X1041 _ _ _ _) end;
   [cbn [In]; tauto | reflexivity | lia | lia]). }
assert (ESH : SHADOW_OFF + (F + 32) / 8 = SB + F / 8 + 4).
{ rewrite <- SB_SHADOW_OFF. pose proof (Z.div_mod F 8 ltac:(lia)). replace (F + 32) with ((F / 8 + 4) * 8) by lia.
  rewrite Z.div_mul by lia. lia. }
assert (HROD7 : arodata_okP SEGS RLO RHI B (rdW W6 (ms_mem ms7)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly6 S6 W6 (ms_mem ms7) _ _ _ _ _ HAR HOin HJ6 HROD).
(* ---- the call of the snprintf wrapper: snprintf(b, 16, "%d", ledger) (0x8ba24), the inlined arg_i ---- *)
eapply SRr_bind.
{ eapply (sivb_snprintf_atS (fx := fx) B HB cmd_img_facts_tfib
    (SIG CS___interceptor_trampoline_snprintf) ASNPRINTF W6 (ms_regs ms7) (ms_mem ms7) SUP_INSTANCE_VERB_STK (spZ regs) FP
    ly S W mem md [(0, fpos)] ly6 S6 _ _ (sp1 - spZ regs) (getr (ms_regs ms7) 1) F fpos ledger HJ6 Qsp7
    ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity) ltac:(lia) ltac:(unfold RtPFCmd.CMD_SNP_K; rewrite FS, Hes; lia)
    ltac:(rewrite T3; exact Hgp) ltac:(rewrite T4; exact Htp) eq_refl ltac:(rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity])
    T10 T11 T12 T13 Hled ltac:(left; reflexivity) (eq_sym EFA6)
    ltac:(rewrite ESH; exact (ZS7 4 ltac:(lia))) ltac:(rewrite ESH, <- Z.add_assoc; exact (ZS7 5 ltac:(lia))) HROD7 HRM0). }
cbv beta. intros W7 c7 _ (-> & fx1 & regs8 & mem8 & md8 & -> & HFR8 & HRM8 & HJ8 & HP8 & H108 & HBUF8 & HK8 & HPR8 & HSM8).
jafter_call_keep_hi HS 1074%nat regs8 (mrestrict (w_H W6) mem8) HP8 [0;1;2;3;4]%nat HS8.
match type of HS8 with ?tq -> _ => assert (HRK : tq); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply (region_kept_aview E4 (w_H W6) (ms_mem ms7) mem8); [first [exact X1041 | exact X1028 | exact X2 | exact X34] | | exact HPR8]);
  (intros a Ha; apply HK8; [unfold SB in *; lia | unfold SB in *; lia | unfold RtPFCmd.CMD_SNP_K; rewrite Hes; unfold SB in *; lia]). }
rewrite <- restrict_mkst_fx in HS8. clear HS. rename HS8 into HS.
remember (havoc E4 1074 (map (getr regs8) CLOB)) as E5 eqn:HE5 in HS.
assert (HAE5 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E5)
  by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact HAE4]).
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI4 | unfold A_LIM; lia]).
assert (OLD5 : forall n, (n < 1074)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
clear HE5.
assert (Y2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact X2).
assert (Y34 : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact X34).
assert (Y1028 : bv_unsigned (ew E5 1028) = F) by (rewrite OLD5 by lia; exact X1028).
assert (Y1040 : bv_unsigned (ew E5 1040) = FL) by (rewrite OLD5 by lia; exact X1040).
assert (Y1041 : bv_unsigned (ew E5 1041) = SB + F / 8) by (rewrite OLD5 by lia; exact X1041).
rewrite T1.
clear T1 T2 T3 T4 T10 T11 T12 T13.
(* from here on the machine runs at the FP state the snprintf wrapper returned *)
sivb_move_fx HS fx fx1.
pose proof (SRr_run_pi_AJ (fx := fx1) (L := cmd_listing) B LAWS) as RUNP1.
pose proof (SRr_run_pi_AJ_call (fx := fx1) (L := cmd_listing) B LAWS) as RUNC1.
(* run 5: a1 := b, a0 := the slot, the call of arg_s (0x8ba30) *)
paj_run_shc RUNP1 RUNC1 HS HJ8.
{ sivb_awr5 fpos sp1 regs FS Y1041 Y1028 Y2 Y34 EFA6. }
rename ms into ms9, mat into mat9, HF into HF9, HFr into HFr9, HG into HG9.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md9 := m) in *; clearbody md9 end.
sivb_preg HS (1%bv : bv 5) U1. sivb_preg HS (2%bv : bv 5) U2. sivb_preg HS (3%bv : bv 5) U3.
sivb_preg HS (4%bv : bv 5) U4. sivb_preg HS (10%bv : bv 5) U10. sivb_preg HS (11%bv : bv 5) U11.
cbn [sv_denot] in U1, U11. rewrite (img_env_codeptr E5 HEI5 21764) in U1.
rewrite sivb_denot_off0, OLD5, OLD4, E1046, R10 in U10 by lia. rewrite Y1028 in U11.
rewrite sivb_denot_off0, OLD5, OLD4, OLD3, OLD2, E34 in U2 by lia.
rewrite sivb_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in U3 by lia.
rewrite sivb_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in U4 by lia.
assert (Qsp9 : spZ (ms_regs ms9) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite U2, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ8) as HAR9.
(* the blocks and statics the recorder reads, kept from the record call's state to here *)
assert (HO1KA : forall a, (exists p n, In (p, n) O1 /\ p <= a < p + req_size n) -> KA a).
{ intros a (p & n & Hpn & Hpa). right. right. exists p, n. split; [|exact Hpa].
  rewrite <- Eab. apply (Permutation_in _ (Permutation_sym HPermF)). apply in_or_app. left. exact (HO1in _ Hpn). }
assert (K67 : forall a, KA a -> aview SEGS (w_H W6) (ms_mem ms7) a = aview SEGS (w_H W6) mem6 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (sivb_aview_frame_pt E4 _ (w_H W6) mem6 (ms_mem ms7) a HFr7); [lia|].
  sivb_nwin_tac ltac:(fun H => rewrite ?X2, ?X34, ?X1028, ?X1041 in H; lia). }
assert (K78 : forall a, KA a -> aview SEGS (w_H W6) mem8 a = aview SEGS (w_H W6) (ms_mem ms7) a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & _). apply HK8; [lia | lia | unfold RtPFCmd.CMD_SNP_K; rewrite Hes; lia]. }
assert (K89 : forall a, KA a -> aview SEGS (w_H W6) (ms_mem ms9) a = aview SEGS (w_H W6) mem8 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _). apply (sivb_aview_frame_pt E5 _ (w_H W6) mem8 (ms_mem ms9) a HFr9); [lia|].
  sivb_nwin_tac ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in H; lia). }
assert (K69 : forall a, KA a -> aview SEGS (w_H W6) (ms_mem ms9) a = aview SEGS (w_H W6) mem6 a)
  by (intros a Ha; rewrite (K89 a Ha), (K78 a Ha); exact (K67 a Ha)).
(* arg_line's own footprint: the slot's nargs and args[0] *)
assert (HLFP : forall a, inFP [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
   (rec_slot R + CALL_OFF_ARGS + 8 * 0, rec_slot R + CALL_OFF_ARGS + 8 * 0 + 8)] a ->
   (rec_slot R + CALL_OFF_NARGS <= a < rec_slot R + CALL_OFF_NARGS + 4) \/
   (rec_slot R + CALL_OFF_ARGS <= a < rec_slot R + CALL_OFF_ARGS + 8)).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [left; exact Ha|].
  apply inFP_cons in Ha as [Ha | Ha]; [right; rewrite Z.mul_0_r in Ha; lia | exact (False_ind _ (inFP_nil a Ha))]. }
assert (HLFPpos : Forall (fun r : Z * Z => 0 < fst r)
  [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
   (rec_slot R + CALL_OFF_ARGS + 8 * 0, rec_slot R + CALL_OFF_ARGS + 8 * 0 + 8)]).
{ destruct (sivb_unhold HSL) as [Hs | Hs]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst];
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_OFF_NARGS, CALL_OFF_ARGS in *; rewrite ?Hs; lia. }
assert (KG : forall a, in_recA a -> ~ (rec_slot R + CALL_OFF_NARGS <= a < rec_slot R + CALL_OFF_NARGS + 4) ->
   ~ (rec_slot R + CALL_OFF_ARGS + 8 * 0 <= a < rec_slot R + CALL_OFF_ARGS + 8 * 0 + 8) ->
   rdW W6 (ms_mem ms9) a = rdW W3 mem3 a).
{ intros a Ha Hn1 Hn2. rewrite Z.mul_0_r in Hn2.
  assert (HaKA : KA a) by (destruct Ha as [Ha | Ha]; [left; exact Ha | right; left; exact Ha]).
  rewrite (K69 a HaKA).
  rewrite (sivk_keep_prog B HB cmd_img_facts_tfib _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc6 HLFPpos
    ltac:(intros HFa; destruct (HLFP a HFa) as [H | H]; [exact (Hn1 H) | apply Hn2; lia])
    ltac:(destruct Ha as [Ha | Ha]; [exact (sivk_grec_in a Ha) | exact (sivk_spill_in a Ha)])).
  exact (K35 a HaKA). }
assert (KO : rd_keepsO (rdW W3 mem3) (rdW W6 (ms_mem ms9)) (ablocks B ly6 S6) O1).
{ intros [p n] Hpn. cbn [fst snd].
  assert (Hp6 : In (p, n) (ablocks B ly6 S6)) by (apply (Permutation_in _ (Permutation_sym Hperm6)); right; exact (HO1in _ Hpn)).
  split; [exact Hp6|]. intros i Hi.
  destruct (sivk_blk_bounds B ly3 S3 W3 mem3 _ p n HAR4 (HO1in _ Hpn)) as (Hb4096 & Hbc & Hn0 & Hnr & _).
  assert (HaKA : KA (p + i)) by (apply HO1KA; exists p, n; split; [exact Hpn | lia]).
  rewrite (K69 _ HaKA).
  rewrite (sivk_keep_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n i HJc6 (HO1in _ Hpn) Hp6 ltac:(lia)
    ltac:(intros HFa; destruct (HLFP _ HFa) as [H | H];
          [ apply (sivk_blk_noimg B ly3 S3 W3 mem3 _ p n (p + i) HAR4 (HO1in _ Hpn) ltac:(lia)); apply cmd_prog_img;
            destruct (sivb_unhold HSL) as [Hs | Hs]; [apply sivk_grec_in; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, CALL_OFF_NARGS in *; lia|];
            apply sivk_spill_in; rewrite Hs in H; unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *; lia
          | apply (sivk_blk_noimg B ly3 S3 W3 mem3 _ p n (p + i) HAR4 (HO1in _ Hpn) ltac:(lia)); apply cmd_prog_img;
            destruct (sivb_unhold HSL) as [Hs | Hs]; [apply sivk_grec_in; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, CALL_OFF_ARGS in *; lia|];
            apply sivk_spill_in; rewrite Hs in H; unfold A_REC_SPILL, SC_SIZE, CALL_OFF_ARGS in *; lia ])).
  exact (K35 _ HaKA). }
(* the blocks live after arg_line (the new one included) are kept from mem6 to the arg_s call *)
set (n1 := Z.of_nat (length line) + 1) in *.
assert (EFL6 : flag_addr ly6 0 fpos = FL).
{ pose proof EFA6 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
destruct (FFL _ _ _ _ _ 0 fpos HAR6 Hfin6) as (HFLp6 & HFLo6 & _ & _). rewrite EFL6 in HFLp6, HFLo6.
assert (KNLOC : forall p n a, In (p, n) (ablocks B ly6 S6) -> p <= a < p + req_size n ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros p n a Hpn Hpa.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR6 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres6 & _).
  pose proof (sep_block_frame SEGS B LAWS ly6 S6 W6 mem6 md6 p n 0 fpos HAR6 Hpn Hfin6) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA6 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
  intros ->. exact (proj2 (Hpres6 FL ltac:(lia)) HFLo6). }
assert (K69N : forall p n a, In (p, n) (ablocks B ly6 S6) -> p <= a < p + req_size n ->
  aview SEGS (w_H W6) (ms_mem ms9) a = aview SEGS (w_H W6) mem6 a).
{ intros p n a Hpn Hpa. destruct (KNLOC p n a Hpn Hpa) as (Hb & HnF & HnS & _).
  rewrite (sivb_aview_frame_pt E5 _ (w_H W6) mem8 (ms_mem ms9) a HFr9);
  [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in H; lia)].
  rewrite (HK8 a ltac:(lia) ltac:(lia) ltac:(unfold RtPFCmd.CMD_SNP_K; rewrite Hes; lia)).
  apply (sivb_aview_frame_pt E4 _ (w_H W6) mem6 (ms_mem ms7) a HFr7); [lia|].
  sivb_nwin_tac ltac:(fun H => rewrite ?X2, ?X34, ?X1028, ?X1041 in H; lia). }
assert (Hp1in : In (p1, n1) (ablocks B ly6 S6)) by (apply (Permutation_in _ (Permutation_sym Hperm6)); left; reflexivity).
pose proof (canon_length line) as HCL.
(* the recorder after arg_line: the call (REC_INSTANCE_VERB, [canon line]) with the new block *)
assert (HREPS : rec_repA B ly6 S6 (rdW W6 (ms_mem ms9)) (rec_record R REC_INSTANCE_VERB ([] ++ [canon line])) (O1 ++ [(p1, n1)])).
{ apply (rec_repA_arg B ly3 S3 (rdW W3 mem3) ly6 S6 _ R REC_INSTANCE_VERB [] O1 (canon line) p1 n1 HREP1 ltac:(cbn [length]; lia)).
  - cbn [length Z.of_nat]. change (rec_slotA R) with (rec_slot R).
    apply (sivk_aval_keep (rdW W6 mem6)); [exact HN6|]. intros x Hx. apply K69. apply HSLKA.
    unfold CALL_OFF_NARGS, CALL_SIZE in *. lia.
  - cbn [length Z.of_nat]. change (rec_slotA R) with (rec_slot R). rewrite Z.mul_0_r.
    apply (sivk_aval_keep (rdW W6 mem6)); [rewrite Z.mul_0_r in HA6; exact HA6|]. intros x Hx. apply K69. apply HSLKA.
    unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
  - cbn [length Z.of_nat]. change (rec_slotA R) with (rec_slot R). exact KG.
  - exact KO.
  - intros Hq. apply in_map_iff in Hq as ([q0 k0] & Eq & Hin). cbn [fst] in Eq.
    rewrite Forall_forall in Hfresh6. pose proof (Hfresh6 (q0, k0) (HO1in _ Hin)) as Hap.
    unfold iv_apart in Hap. cbn [fst snd] in Hap.
    pose proof (rec_repA_sizes B ly3 S3 _ _ _ HREP1 (q0, k0) Hin) as Hk0. cbn [snd] in Hk0. unfold n1 in *. lia.
  - lia.
  - exact Hp1in.
  - unfold LMAX in *. lia.
  - unfold n1, LMAX in *. lia.
  - apply (sivk_str_keep (rdW W6 mem6)); [exact HSTR6|]. intros x Hx.
    apply (K69N p1 n1 x Hp1in). pose proof (req_size_pos n1 ltac:(unfold n1; lia)) as [_ Hrq]. unfold n1 in *. lia.
  - unfold iv_apart. pose proof (req_size_pos n1 ltac:(unfold n1; lia)) as [_ Hrq].
    destruct (Z_le_gt_dec (p1 + n1) A_G_REC) as [Hd|Hd]; [left; exact Hd|].
    destruct (Z_le_gt_dec (A_G_REC + REC_SIZE) p1) as [Hd2|Hd2]; [right; exact Hd2|].
    exfalso. apply (sivk_blk_noimg B ly6 S6 W6 mem6 md6 p1 n1 (Z.max p1 A_G_REC) HAR6 Hp1in
      ltac:(unfold A_G_REC, REC_SIZE in *; lia)).
    apply cmd_prog_img. apply sivk_grec_in. unfold A_G_REC, REC_SIZE in *. lia.
  - unfold iv_apart. pose proof (req_size_pos n1 ltac:(unfold n1; lia)) as [_ Hrq].
    destruct (Z_le_gt_dec (p1 + n1) A_REC_SPILL) as [Hd|Hd]; [left; exact Hd|].
    destruct (Z_le_gt_dec (A_REC_SPILL + SC_SIZE) p1) as [Hd2|Hd2]; [right; exact Hd2|].
    exfalso. apply (sivk_blk_noimg B ly6 S6 W6 mem6 md6 p1 n1 (Z.max p1 A_REC_SPILL) HAR6 Hp1in
      ltac:(unfold A_REC_SPILL, SC_SIZE in *; lia)).
    apply cmd_prog_img. apply sivk_spill_in. unfold A_REC_SPILL, SC_SIZE in *. lia. }
(* b holds dec ledger, in the frame, with its tail word *)
assert (HBUF9 : astr_atR (rdW W6 (ms_mem ms9)) (F + 32) (dec ledger)).
{ split; [|exact (sivb_dec_no0 ledger)]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (sivb_aview_frame_pt E5 _ (w_H W6) mem8 (ms_mem ms9) (F + 32 + Z.of_nat i) HFr9);
  [ exact (HBUF8 i ltac:(rewrite length_app; cbn [length]; lia))
  | pose proof (dec_length ledger Hled); lia
  | pose proof (sivb_unhold HFSd) as HFSd';
    sivb_nwin_tac ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in H; pose proof (dec_length ledger Hled); unfold SB in *; lia) ]. }
assert (ZS9 : forall j, 4 <= j < 6 -> rdW W6 (ms_mem ms9) (SB + F / 8 + j) = Some 0).
{ intros j Hj. pose proof (st_ok_region_nth E5 _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
  assert (Hj2 : j = 4 \/ j = 5) by lia.
  destruct Hj2 as [-> | ->]; (apply (aview_of_val_mem1 SEGS); [|lia]);
  (lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
     refine (field_of_region E5 _ 1041 (SB + F / 8) _ 0 8 0 8 od 1%N (SLit 0) 0 HR0 Y1041 _ _ _ _) end;
   [cbn [In]; tauto | reflexivity | lia | lia]). }
assert (HAFO9 : afobj SEGS B ly6 S6 W6 (ms_mem ms9) (F + 32) (Z.of_nat (length (dec ledger)) + 1)).
{ pose proof (dec_length ledger Hled) as HDL.
  split; [exists 0, fpos; split; [exact Hfin6|]; split; [lia|]; rewrite EFA6; split; [exact HF8m|];
          split; [lia | change (fs_frame_bytes 0) with 64; lia]|].
  split; [rewrite Zplus_mod, HF8m; reflexivity|].
  intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  pose proof (Z.div_mod F 8 ltac:(lia)).
  assert (Hx8 : x / 8 = F / 8 + (x / 8 - F / 8)) by lia. rewrite Hx8, Z.add_assoc. apply ZS9.
  split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.lt_sub_lt_add_l; apply Z.div_lt_upper_bound; lia]. }
(* the bytes after the ledger's terminator up to the end of its word are in the frame, present at the call's state *)
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR9 Hfin6) as (_ & _ & HFpres9 & _). rewrite EFA6 in HFpres9.
change (fs_frame_bytes 0) with 64 in HFpres9.
assert (HTAIL9 : atail_vis SEGS W6 (ms_mem ms9) (F + 32 + Z.of_nat (length (dec ledger)))).
{ pose proof (dec_length ledger Hled) as HDL. intros a Ha.
  assert (HaF : F <= a < F + 64).
  { pose proof (Z.div_mod (F + 32 + Z.of_nat (length (dec ledger))) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length (dec ledger))) 8 ltac:(lia)) as M. lia. }
  apply (aview_some_of_apresent SEGS). exact (proj1 (HFpres9 a ltac:(lia))). }
assert (HROD9 : arodata_okP SEGS RLO RHI B (rdW W6 (ms_mem ms9)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly6 S6 W6 (ms_mem ms9) _ _ _ _ _ HAR HOin HJ8 HROD).
assert (HROK9 : cmd_ro_ok (rdW W6 (ms_mem ms9)))
  by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HAR9 HROD9).
assert (HCH9 : exists ch9, achain ly6 (rdW W6 (ms_mem ms9)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms9)) ch9).
{ sivb_preg HS (8%bv : bv 5) U8. rewrite sivb_denot_off0, OLD5, OLD4, OLD3, OLD2, Esp in U8 by lia.
  unfold s0Z. rewrite U8, unsigned_lit_small by lia.
  pose proof (st_ok_region_nth E5 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
  pose proof HJ8 as (_ & Hly9 & _). pose proof Hly9 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop9 & _).
  destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    eapply (achain_push ly6 (rdW W mem) (rdW W6 (ms_mem ms9)) (spZ regs) (s0Z regs) (raZ regs) ch);
    [apply (achain_ly_top ly ly6); [exact Etop9 | exact Hch] | rewrite Etop9; lia | | | | exact Hra4 | lia
    | exact (sivb_Z_mod_16_8 _ Hal16) | rewrite Etop9; exact Hlt | lia].
    + intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ8 a Ha (HNFP a Ha)).
    + apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
      replace (spZ regs - 8) with (spZ regs + -8) by lia.
      refine (field_of_region E5 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 Y2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
      | unfold raZ; apply bv_unsigned_in_range | lia].
    + apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
      replace (spZ regs - 16) with (spZ regs + -16) by lia.
      refine (field_of_region E5 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 Y2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD5, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia; unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
      | unfold s0Z; apply bv_unsigned_in_range | lia].
  - exists []. left. split; [right; left; rewrite Etop9; lia | reflexivity]. }
destruct HCH9 as (ch9 & HCH9).
pose proof HJ8 as (_ & _ & _ & _ & _ & _ & HNEV9 & _).
(* ---- the call of arg_s(slot, b) (0x8ba30) ---- *)
rewrite (sivb_sig_arg_s cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx1) B LAWS W6 (ms_regs ms9) (ms_mem ms9) (Z_to_bv 64 (BASE + AF_arg_s)) SUP_INSTANCE_VERB_STK (spZ regs) FP
    ly S W mem md [(0, fpos)] ly6 S6 _ _ ARG_S_STK _ EV_ARG_S (sp1 - spZ regs) (getr (ms_regs ms9) 1) ch9 _ HJ8 Qsp9
    ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity));
  [ lia | rewrite HAS; lia | rewrite HAS, FS; lia | rewrite U3; exact Hgp | rewrite U4; exact Htp | reflexivity
  | rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite U1, unsigned_lit_small by lia; lia
  | exact HCH9
  | | | ].
  - intros HPRE9. pose proof (TARG_S fx1 ly6 S6 W6 (ms_regs ms9) (ms_mem ms9) _ ch9 (rec_slot R) (F + 32)
      REC_INSTANCE_VERB [canon line] (Some (dec ledger)) R (O1 ++ [(p1, n1)]) HPRE9) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROD9.
    + exact HROK9.
    + exact U10.
    + exact U11.
    + reflexivity.
    + cbn [app] in HREPS. exact HREPS.
    + right. exists (dec ledger). split; [reflexivity|]. split; [exact HBUF9|].
      split; [pose proof (dec_length ledger Hled); unfold LMAX; lia | exact HAFO9].
    + intros x Hx. injection Hx as <-. exact HTAIL9.
    + unfold EV_SUP_INSTANCE_VERB, EV_ARG_LINE, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL, EV_XMALLOC in *.
      lia.
    + pose proof (LN0 (snd (sup_instance_verb_m R line ledger))). unfold LIVE_SUP_INSTANCE_VERB in HLIVE.
      unfold LIVE_ARG_LINE, LIVE_REC_CANONICAL in *. lia.
    + apply (mok_station MT S2 S6 (XM_SUP_INSTANCE_VERB MT R line ledger) (XM_RECORD MT R + XM_ARG_LINE MT line) _ MTL HMOK2
        ltac:(apply (mo_le_trans MT MTL S2 S3 S6); [exact MLE1 | exact MLE6]) XA0).
      unfold XM_SUP_INSTANCE_VERB. pose proof (XN0 (snd (sup_instance_verb_m R line ledger))). lia.
  - intros a Ha. cbn [length Z.of_nat] in Ha. unfold REC_ARGS_MAX in Ha. cbn [Z.ltb Z.compare] in Ha.
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (sivk_awr_slot B HB cmd_img_facts_tfib _ _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_NARGS, CALL_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
    apply (sivk_awr_slot B HB cmd_img_facts_tfib _ _ _ _ _ _ _ _ R a HC1). unfold CALL_OFF_ARGS, CALL_SIZE in *. lia.
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    cbn [length Z.of_nat] in Ha. unfold REC_ARGS_MAX in Ha. cbn [Z.ltb Z.compare] in Ha.
    assert (HaK : KA a).
    { apply HSLKA. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
      apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exact (False_ind _ (inFP_nil a Ha))]. }
    destruct (KLOC a HaK) as (Hb & _). rewrite FS in Hw. lia. }
cbv beta. intros W10 c10 Hwle10 (ly10 & S10 & regs10 & mem10 & md10 & -> & HJ10 & HJc10 & HP10 & HKS).
cbv zeta in HKS. destruct HKS as (HBB10 & MLE10 & [(Hm10 & _ & _) | (_ & p2 & Hp2 & Hperm10 & Hfresh10 & HREP10)]).
{ exfalso. cbn [length Z.of_nat] in Hm10. unfold REC_ARGS_MAX in Hm10. lia. }
rewrite U1.
pose proof (proj1 HJ10) as HAR10.
pose proof HJc10 as (_ & Hly10 & _ & _ & _ & Hfrs10 & _). cbn [app] in Hfrs10.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly10 HAR9 Hly10) as (Eab10 & Efa10 & _).
assert (EFA10 : frame_addr ly10 0 fpos = F) by (rewrite Efa10; exact EFA6).
assert (Hfin10 : In (0, fpos) (frames S10)) by (rewrite Hfrs10; exact Hfin6).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR10 Hfin10) as (_ & _ & HFpres10 & HFSpres10). rewrite EFA10 in HFpres10, HFSpres10.
change (fs_frame_bytes 0) with 64 in HFpres10, HFSpres10. change (64 / 8) with 8 in HFSpres10.
assert (HSFKA : forall a, inFP [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
  (rec_slot R + CALL_OFF_ARGS + 8 * 1, rec_slot R + CALL_OFF_ARGS + 8 * 1 + 8)] a -> KA a).
{ intros a Ha. apply HSLKA. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exact (False_ind _ (inFP_nil a Ha))]. }
jafter_call_keep_hi HS 1090%nat regs10 (mrestrict (w_H W10) mem10) HP10 [0;1;2;3;4]%nat HS10.
match type of HS10 with ?tq -> _ => assert (HRK : tq); [|specialize (HS10 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E5 _ _ _ ly6 S6 W6 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc10 Y1041 Hfin6);
    [ unfold shadow_addr; rewrite EFA6, <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA6, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; apply HSFKA in HFa; destruct (KLOC a HFa) as (_ & _ & HnS & _); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres10 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E5 _ _ _ ly6 S6 W6 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _ 1028 F _ _ _ _ _ 0 fpos HJc10 Y1028 Hfin6);
    [ rewrite EFA6; lia | rewrite EFA6; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; apply HSFKA in HFa; destruct (KLOC a HFa) as (_ & HnF & _); lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E5 _ _ _ ly6 S6 W6 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _ 1028 F _ _ _ _ _ 0 fpos HJc10 Y1028 Hfin6);
    [ rewrite EFA6; lia | rewrite EFA6; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; apply HSFKA in HFa; destruct (KLOC a HFa) as (_ & HnF & _); lia
    | intros a Ha; exact (proj1 (HFpres10 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc10 HJ10 Y34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; apply HSFKA in HFa; destruct (KLOC a HFa); lia].
  - eapply (region_kept_stack_sub SEGS B E5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc10 HJ10 Y2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; apply HSFKA in HFa; destruct (KLOC a HFa); lia]. }
rewrite <- restrict_mkst_fx in HS10. clear HS. rename HS10 into HS.
remember (havoc E5 1090 (map (getr regs10) CLOB)) as E6 eqn:HE6 in HS.
assert (HAE6 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E6)
  by (rewrite HE6; apply env_agree_havoc_ge; [lia | exact HAE5]).
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc_hi; [exact HEI5 | unfold A_LIM; lia]).
assert (OLD6 : forall n, (n < 1090)%nat -> ew E6 n = ew E5 n) by (intros n Hn; rewrite HE6; apply ew_havoc_old; exact Hn).
clear HE6.
assert (Z2 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Y2).
assert (Z34 : bv_unsigned (ew E6 34) = sp1) by (rewrite OLD6 by lia; exact Y34).
assert (Z1028 : bv_unsigned (ew E6 1028) = F) by (rewrite OLD6 by lia; exact Y1028).
assert (Z1040 : bv_unsigned (ew E6 1040) = FL) by (rewrite OLD6 by lia; exact Y1040).
assert (Z1041 : bv_unsigned (ew E6 1041) = SB + F / 8) by (rewrite OLD6 by lia; exact Y1041).
clear U1 U2 U3 U4 U10 U11.
(* run 6: b's shadow := f8 f8 again (0x8ba34, 0x8ba38), a1 := " \t", a0 := the line, the call of the strspn wrapper
   (0x8ba48) *)
paj_run_shc RUNP1 RUNC1 HS HJ10.
{ sivb_awr5 fpos sp1 regs FS Z1041 Z1028 Z2 Z34 EFA10. }
rename ms into ms11, mat into mat11, HF into HF11, HFr into HFr11, HG into HG11.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md11 := m) in *; clearbody md11 end.
sivb_preg HS (1%bv : bv 5) Wr1. sivb_preg HS (2%bv : bv 5) Wr2. sivb_preg HS (3%bv : bv 5) Wr3.
sivb_preg HS (4%bv : bv 5) Wr4. sivb_preg HS (10%bv : bv 5) Wr10. sivb_preg HS (11%bv : bv 5) Wr11.
cbn [sv_denot] in Wr1. rewrite (img_env_codeptr E6 HEI6 21788) in Wr1.
rewrite sivb_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 10%nat 10%bv eq_refl), H10 in Wr10 by lia.
rewrite sivb_denot_off0, (img_env_atomP E6 306 HEI6 ltac:(unfold A_TEXT, A_LIM; lia)) in Wr11.
change (VAL 306) with (VAL (A_OBJ 65)) in Wr11. rewrite (sivb_obj65 VOBJS) in Wr11.
rewrite sivb_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, E34 in Wr2 by lia.
rewrite sivb_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in Wr3 by lia.
rewrite sivb_denot_off0, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in Wr4 by lia.
assert (Qsp11 : spZ (ms_regs ms11) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite Wr2, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ10) as HAR11.
(* the line's block is live at the strspn call, its bytes the entry's *)
assert (Hpbk6 : In (pb, kb) (ablocks B ly6 S6)) by (apply (Permutation_in _ (Permutation_sym Hperm6)); right; exact Hpbk3).
assert (Hpbk10 : In (pb, kb) (ablocks B ly10 S10)) by (apply (Permutation_in _ (Permutation_sym Hperm10)); right; exact Hpbk6).
assert (HLB10 : in_blockA (ablocks B ly10 S10) pl (Z.of_nat (length line) + 1)) by (exists pb, kb; split; [exact Hpbk10 | lia]).
(* a byte of a live block is none of a slot footprint's (the slot is a static, a block byte is no image byte) *)
assert (HnSlot : forall p n a off w, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  0 <= off -> off + w <= CALL_SIZE -> ~ (rec_slot R + off <= a < rec_slot R + off + w)).
{ intros p n a off w Hpn Hpa Hoff Hw Hs.
  apply (sivk_blk_noimg B ly S W mem md p n a HAR Hpn Hpa). apply cmd_prog_img.
  destruct (sivb_unhold HSL) as [HsR | HsR]; [apply sivk_grec_in; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
  apply sivk_spill_in. rewrite HsR in Hs. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
assert (HLKEEP : forall a, pl <= a < pl + Z.of_nat (length line) + 1 -> rdW W10 (ms_mem ms11) a = rdW W3 (ms_mem ms5) a).
{ intros a Ha.
  destruct (KNLOC pb kb a Hpbk6 ltac:(lia)) as (Hb & HnF & HnS & _).
  rewrite (sivb_aview_frame_pt E6 _ (w_H W10) mem10 (ms_mem ms11) a HFr11);
  [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Z2, ?Z34, ?Z1028, ?Z1041 in H; lia)].
  replace a with (pb + (a - pb)) by lia.
  rewrite (sivk_keep_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pb kb (a - pb) HJc10 Hpbk6 Hpbk10 ltac:(lia)
    ltac:(intros HFa; apply inFP_cons in HFa as [HFa | HFa];
          [ exact (HnSlot pb kb (pb + (a - pb)) CALL_OFF_NARGS 4 Hpbk ltac:(lia) ltac:(unfold CALL_OFF_NARGS; lia)
                     ltac:(unfold CALL_OFF_NARGS, CALL_SIZE; lia) HFa)
          | apply inFP_cons in HFa as [HFa | HFa]; [|exact (inFP_nil _ HFa)];
            exact (HnSlot pb kb (pb + (a - pb)) (CALL_OFF_ARGS + 8 * 1) 8 Hpbk ltac:(lia) ltac:(unfold CALL_OFF_ARGS; lia)
                     ltac:(unfold CALL_OFF_ARGS, CALL_SIZE; lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat] in HFa; lia)) ])).
  replace (pb + (a - pb)) with a by lia. rewrite (K69N pb kb a Hpbk6 ltac:(lia)).
  replace a with (pb + (a - pb)) by lia.
  rewrite (sivk_keep_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pb kb (a - pb) HJc6 Hpbk3 Hpbk6 ltac:(lia)
    ltac:(intros HFa; apply inFP_cons in HFa as [HFa | HFa];
          [ exact (HnSlot pb kb (pb + (a - pb)) CALL_OFF_NARGS 4 Hpbk ltac:(lia) ltac:(unfold CALL_OFF_NARGS; lia)
                     ltac:(unfold CALL_OFF_NARGS, CALL_SIZE; lia) HFa)
          | apply inFP_cons in HFa as [HFa | HFa]; [|exact (inFP_nil _ HFa)];
            exact (HnSlot pb kb (pb + (a - pb)) (CALL_OFF_ARGS + 8 * 0) 8 Hpbk ltac:(lia) ltac:(unfold CALL_OFF_ARGS; lia)
                     ltac:(unfold CALL_OFF_ARGS, CALL_SIZE; lia) ltac:(lia)) ])).
  replace (pb + (a - pb)) with a by lia. reflexivity. }
assert (HLSTR11 : astr_atR (rdW W10 (ms_mem ms11)) pl line)
  by (apply (sivk_str_keep (rdW W3 (ms_mem ms5))); [exact HLSTR5 | exact HLKEEP]).
assert (HROD11 : arodata_okP SEGS RLO RHI B (rdW W10 (ms_mem ms11)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly10 S10 W10 (ms_mem ms11) _ _ _ _ _ HAR HOin HJ10 HROD).
assert (HROK11 : cmd_ro_ok (rdW W10 (ms_mem ms11)))
  by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HAR11 HROD11).
assert (Hra11 : YK0s.ret_ok (getr (ms_regs ms11) 1)) by (rewrite Wr1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* ---- the call of the strspn wrapper: strspn(line, " \t") (0x8ba48) ---- *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B cmd_palib) (2 * ESTACK) (fun _ => False)
    (SIG CS___interceptor_trampoline_strspn) W10 (ms_regs ms11) (ms_mem ms11) SUP_INSTANCE_VERB_STK (spZ regs) FP
    ly S W mem md [(0, fpos)] ly10 S10 _ _ (sp1 - spZ regs) (Z_to_bv 64 (BASE + 21788)) _ HJ10 Qsp11
    ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity) ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite FS, Hes; lia) Wr1
    (fun a (H : False) => False_ind _ H)).
  apply (ASTRSPN fx1 ly10 S10 W10 (ms_regs ms11) (ms_mem ms11) _ pl 0x21da0 line sivb_set).
  - exact (proj1 (proj2 (CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR11))).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_INSTANCE_VERB_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly10 S10 W10
      (ms_mem ms11) _ _ (ms_regs ms11) (sp1 - spZ regs) HJ10 Qsp11 ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity)
      ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite FS, Hes; lia) Hra11 ltac:(rewrite Wr3; exact Hgp) ltac:(rewrite Wr4; exact Htp)).
  - exact Wr10.
  - exact Wr11.
  - lia.
  - lia.
  - apply (astr_atR_view SEGS). exact HLSTR11.
  - exact (sivb_set_str W10 (ms_mem ms11) HROK11).
  - pose proof (sivb_line_rd B ly10 S10 W10 (ms_mem ms11) _ (ms_regs ms11) pl line 0%nat (2 * ESTACK) HAR11 HLB10
      ltac:(lia) ltac:(rewrite Qsp11, Hes; lia)) as HRD.
    rewrite Z.add_0_r in HRD. exact HRD.
  (* the `+ 8` band premise of the string (PASS4-REFIT.md E.0.1): the line is in a live heap block *)
  - pose proof (req_size_pos kb ltac:(lia)) as [_ Hrq].
    exact (amem8_of_block SEGS B LAWS ly10 S10 W10 (ms_mem ms11) _ pb kb pl (astr_len line) HAR11 Hpbk10 ltac:(lia)
      ltac:(unfold astr_len; lia) ltac:(unfold astr_len; lia)).
  - exact (sivb_set_read B HB ly10 S10 W10 (ms_mem ms11) _ (ms_regs ms11) (2 * ESTACK) HAR11 HROK11 VOBJS ltac:(lia)
      ltac:(rewrite Qsp11, Hes; lia)).
  (* the set's: " \t" is a .rodata literal in the low band *)
  - exact (amem8_of_low 0x21da0 (astr_len sivb_set) ltac:(lia) ltac:(unfold astr_len; rewrite sivb_set_len; unfold kLowMemEnd; lia)).
  - unfold astr_len. exact (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB ly10 S10 W10 (ms_mem ms11) _ pb kb
      (pl + Z.of_nat (length line)) HAR11 Hpbk10 ltac:(pose proof (req_size_pos kb ltac:(lia)) as [_ Hrq]; lia)).
  - change (0x21da0 + astr_len sivb_set) with 0x21da2. exact (sivb_tail_set W10 (ms_mem ms11) HROK11).
  - exact (CmdRecImg.cmd_rom_view_on SEGS B LAWS HB IMG _ _ W10 (ms_mem ms11) HROD11). }
cbv beta. intros W12 c12 _ (-> & regs12 & mem12 & md12 & -> & HJ12 & HP12 & HQ12 & HK12).
jafter_call_keep_hi HS 1106%nat regs12 (mrestrict (w_H W10) mem12) HP12 [0;1;2;3;4]%nat HS12.
match type of HS12 with ?tq -> _ => assert (HRK : tq); [|specialize (HS12 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst].
  pose proof HJ12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ12pres & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ12) Hfin10) as (_ & _ & HFpres12 & HFSpres12).
  rewrite EFA10 in HFpres12, HFSpres12.
  change (fs_frame_bytes 0) with 64 in HFpres12, HFSpres12. change (64 / 8) with 8 in HFSpres12.
  repeat apply Forall_cons; try apply Forall_nil.
  - eapply sivb_region_kept_hi;
    [exact Z1041 | intros a Ha; apply HK12; [unfold SB in *; lia | rewrite Hes; unfold SB in *; lia | intros []] |].
    intros a Ha. replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
    apply (proj1 (HFSpres12 (a - (SB + F / 8)) ltac:(lia))).
  - eapply sivb_region_kept_hi; [exact Z1028 | intros a Ha; apply HK12; [lia | rewrite Hes; lia | intros []] | intros a Ha; lia].
  - eapply sivb_region_kept_hi;
    [exact Z1028 | intros a Ha; apply HK12; [lia | rewrite Hes; lia | intros []] | intros a Ha; exact (proj1 (HFpres12 a ltac:(lia)))].
  - eapply sivb_region_kept_hi;
    [exact Z34 | intros a Ha; apply HK12; [lia | rewrite Hes; lia | intros []] | intros a Ha; apply HJ12pres; rewrite FS; lia].
  - eapply sivb_region_kept_hi;
    [exact Z2 | intros a Ha; apply HK12; [lia | rewrite Hes; lia | intros []] | intros a Ha; apply HJ12pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS12. clear HS. rename HS12 into HS.
remember (havoc E6 1106 (map (getr regs12) CLOB)) as E7 eqn:HE7 in HS.
assert (HAE7 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E7)
  by (rewrite HE7; apply env_agree_havoc_ge; [lia | exact HAE6]).
assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc_hi; [exact HEI6 | unfold A_LIM; lia]).
assert (OLD7 : forall n, (n < 1106)%nat -> ew E7 n = ew E6 n) by (intros n Hn; rewrite HE7; apply ew_havoc_old; exact Hn).
assert (E1110 : ew E7 1110 = getr regs12 10).
{ rewrite HE7. change 1110%nat with (1106 + 4)%nat. rewrite (ew_havoc_new E6 1106 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE7.
assert (Vv2 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact Z2).
assert (Vv34 : bv_unsigned (ew E7 34) = sp1) by (rewrite OLD7 by lia; exact Z34).
assert (Vv1028 : bv_unsigned (ew E7 1028) = F) by (rewrite OLD7 by lia; exact Z1028).
assert (Vv1040 : bv_unsigned (ew E7 1040) = FL) by (rewrite OLD7 by lia; exact Z1040).
assert (Vv1041 : bv_unsigned (ew E7 1041) = SB + F / 8) by (rewrite OLD7 by lia; exact Z1041).
(* run 7: s4 := line + strspn(...) (0x8ba4c), up to the UBSan check `bltu s4,s3` (0x8ba50) *)
paj_run_sh RUNP1 HS HJ12.
{ sivb_awr5 fpos sp1 regs FS Vv1041 Vv1028 Vv2 Vv34 EFA10. }
rename ms into ms13, mat into mat13, HF into HF13, HFr into HFr13, HG into HG13.
pose proof (paj_branch (fx := fx1) (PI := PI)) as BR1.
(* the line address and strspn's count as atoms, and the bound that keeps their sum below 2 ^ 64 *)
assert (Epl7 : ew E7 10 = Z_to_bv 64 pl).
{ rewrite OLD7, OLD6, OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 10%nat 10%bv eq_refl), H10. reflexivity. }
assert (Ek7 : ew E7 1110 = Z_to_bv 64 (Z.of_nat (sivb_spn line))) by (rewrite E1110, HQ12; reflexivity).
pose proof (sivb_spn_le line) as Hspn.
destruct (sivb_traps_not_taken B ly10 S10 W10 (ms_mem ms11) _ pl line (Z.of_nat (sivb_spn line)) HAR11 HLB10
  ltac:(lia)) as (Hpl0 & Hplk).
(* ---- the UBSan check 0x8ba50 `bltu s4,s3`: refuted by sivb_br_8ba50 (sivb_ubsan_8ba50) from the line's block
   premise and strspn's count <= |line| ---- *)
psrr_branch_pi RUNP1 BR1 HS.
{ exfalso. rewrite (sivb_br_8ba50 E7 10 1110 pl (Z.of_nat (sivb_spn line)) Epl7 Ek7 ltac:(lia) ltac:(lia) Hplk) in Hc.
  discriminate Hc. }
(* run 7': the operands of the second check (0x8ba54 .. 0x8ba5c), up to `beqz a0` (0x8ba60) *)
paj_run_sh RUNP1 HS HJ12.
{ sivb_awr5 fpos sp1 regs FS Vv1041 Vv1028 Vv2 Vv34 EFA10. }
rename ms into ms14, mat into mat14, HF into HF14, HFr into HFr14, HG into HG14.
(* ---- the UBSan check 0x8ba60 `beqz a0`: refuted by sivb_br_8ba60 (sivb_ubsan_8ba60), same premises ---- *)
psrr_branch_pi RUNP1 BR1 HS.
{ exfalso. lazymatch goal with Hc2 : branch_taken _ _ _ = true |- _ =>
    rewrite (sivb_br_8ba60 E7 10 1110 pl (Z.of_nat (sivb_spn line)) Epl7 Ek7 ltac:(lia) ltac:(lia) Hplk) in Hc2;
    discriminate Hc2 end. }
(* run 7'': a1 := " \t", a0 := s4 = line + strspn's count, the call of the strcspn wrapper (0x8ba70) *)
paj_run_shc RUNP1 RUNC1 HS HJ12.
{ sivb_awr5 fpos sp1 regs FS Vv1041 Vv1028 Vv2 Vv34 EFA10. }
rename ms into ms15, mat into mat15, HF into HF15, HFr into HFr15, HG into HG15.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md15 := m) in *; clearbody md15 end.
sivb_preg HS (1%bv : bv 5) Xr1. sivb_preg HS (2%bv : bv 5) Xr2. sivb_preg HS (3%bv : bv 5) Xr3.
sivb_preg HS (4%bv : bv 5) Xr4. sivb_preg HS (10%bv : bv 5) Xr10. sivb_preg HS (11%bv : bv 5) Xr11.
cbn [sv_denot] in Xr1. rewrite (img_env_codeptr E7 HEI7 21828) in Xr1.
rewrite (sivb_denot_add_atoms E7 10 1110 pl (Z.of_nat (sivb_spn line)) Epl7 Ek7 ltac:(lia) ltac:(lia) Hplk) in Xr10.
rewrite sivb_denot_off0, (img_env_atomP E7 306 HEI7 ltac:(unfold A_TEXT, A_LIM; lia)) in Xr11.
change (VAL 306) with (VAL (A_OBJ 65)) in Xr11. rewrite (sivb_obj65 VOBJS) in Xr11.
rewrite sivb_denot_off0, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, E34 in Xr2 by lia.
rewrite sivb_denot_off0, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in Xr3 by lia.
rewrite sivb_denot_off0, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in Xr4 by lia.
assert (Qsp15 : spZ (ms_regs ms15) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite Xr2, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ12) as HAR15.
(* the line, kept from the strspn call to here: the strspn wrapper wrote only its scratch window, run 7 only the
   frame's regions *)
assert (HLSTR15 : astr_atR (rdW W10 (ms_mem ms15)) pl line).
{ apply (sivk_str_keep (rdW W10 (ms_mem ms11))); [exact HLSTR11|]. intros a Ha.
  destruct (KNLOC pb kb a Hpbk6 ltac:(lia)) as (Hb & HnF & HnS & _).
  rewrite (sivb_aview_frame_pt E7 _ (w_H W10) (ms_mem ms14) (ms_mem ms15) a HFr15);
  [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Vv2, ?Vv34, ?Vv1028, ?Vv1041 in H; lia)].
  rewrite (sivb_aview_frame_pt E7 _ (w_H W10) (ms_mem ms13) (ms_mem ms14) a HFr14);
  [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Vv2, ?Vv34, ?Vv1028, ?Vv1041 in H; lia)].
  rewrite (sivb_aview_frame_pt E7 _ (w_H W10) mem12 (ms_mem ms13) a HFr13);
  [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Vv2, ?Vv34, ?Vv1028, ?Vv1041 in H; lia)].
  apply HK12; [lia | rewrite Hes; lia | intros []]. }
assert (HROD15 : arodata_okP SEGS RLO RHI B (rdW W10 (ms_mem ms15)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly10 S10 W10 (ms_mem ms15) _ _ _ _ _ HAR HOin HJ12 HROD).
assert (HROK15 : cmd_ro_ok (rdW W10 (ms_mem ms15)))
  by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HAR15 HROD15).
assert (Hra15 : YK0s.ret_ok (getr (ms_regs ms15) 1)) by (rewrite Xr1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* ---- the call of the strcspn wrapper: strcspn(line + spn, " \t") (0x8ba70) ---- *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B cmd_palib) (2 * ESTACK) (fun _ => False)
    (SIG CS___interceptor_trampoline_strcspn) W10 (ms_regs ms15) (ms_mem ms15) SUP_INSTANCE_VERB_STK (spZ regs) FP
    ly S W mem md [(0, fpos)] ly10 S10 _ _ (sp1 - spZ regs) (Z_to_bv 64 (BASE + 21828)) _ HJ12 Qsp15
    ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity) ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite FS, Hes; lia) Xr1
    (fun a (H : False) => False_ind _ H)).
  apply (ASTRCSPN fx1 ly10 S10 W10 (ms_regs ms15) (ms_mem ms15) _ (pl + Z.of_nat (sivb_spn line)) 0x21da0
    (skipn (sivb_spn line) line) sivb_set).
  - exact (proj1 (proj2 (CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR15))).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_INSTANCE_VERB_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly10 S10 W10
      (ms_mem ms15) _ _ (ms_regs ms15) (sp1 - spZ regs) HJ12 Qsp15 ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity)
      ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite FS, Hes; lia) Hra15 ltac:(rewrite Xr3; exact Hgp) ltac:(rewrite Xr4; exact Htp)).
  - exact Xr10.
  - exact Xr11.
  - lia.
  - lia.
  - apply (astr_atR_view SEGS). exact (sivb_str_skipn _ pl line (sivb_spn line) HLSTR15 Hspn).
  - exact (sivb_set_str W10 (ms_mem ms15) HROK15).
  - exact (sivb_line_rd B ly10 S10 W10 (ms_mem ms15) _ (ms_regs ms15) pl line (sivb_spn line) (2 * ESTACK) HAR15 HLB10
      Hspn ltac:(rewrite Qsp15, Hes; lia)).
  (* the `+ 8` band premise of the string: line + spn's tail is in the line's live heap block *)
  - pose proof (req_size_pos kb ltac:(lia)) as [_ Hrq].
    exact (amem8_of_block SEGS B LAWS ly10 S10 W10 (ms_mem ms15) _ pb kb (pl + Z.of_nat (sivb_spn line))
      (astr_len (skipn (sivb_spn line) line)) HAR15 Hpbk10 ltac:(lia)
      ltac:(unfold astr_len; rewrite length_skipn; lia) ltac:(unfold astr_len; lia)).
  - exact (sivb_set_read B HB ly10 S10 W10 (ms_mem ms15) _ (ms_regs ms15) (2 * ESTACK) HAR15 HROK15 VOBJS ltac:(lia)
      ltac:(rewrite Qsp15, Hes; lia)).
  (* the set's: the .rodata literal " \t" *)
  - exact (amem8_of_low 0x21da0 (astr_len sivb_set) ltac:(lia) ltac:(unfold astr_len; rewrite sivb_set_len; unfold kLowMemEnd; lia)).
  - unfold astr_len. rewrite length_skipn.
    exact (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB ly10 S10 W10 (ms_mem ms15) _ pb kb
      (pl + Z.of_nat (sivb_spn line) + Z.of_nat (length line - sivb_spn line)) HAR15 Hpbk10
      ltac:(pose proof (req_size_pos kb ltac:(lia)) as [_ Hrq]; lia)).
  - change (0x21da0 + astr_len sivb_set) with 0x21da2. exact (sivb_tail_set W10 (ms_mem ms15) HROK15).
  - exact (CmdRecImg.cmd_rom_view_on SEGS B LAWS HB IMG _ _ W10 (ms_mem ms15) HROD15). }
cbv beta. intros W16 c16 _ (-> & regs16 & mem16 & md16 & -> & HJ16 & HP16 & HQ16 & HK16).
jafter_call_keep_hi HS 1122%nat regs16 (mrestrict (w_H W10) mem16) HP16 [0;1;2;3;4]%nat HS16.
match type of HS16 with ?tq -> _ => assert (HRK : tq); [|specialize (HS16 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst].
  pose proof HJ16 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ16pres & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ16) Hfin10) as (_ & _ & HFpres16 & HFSpres16).
  rewrite EFA10 in HFpres16, HFSpres16.
  change (fs_frame_bytes 0) with 64 in HFpres16, HFSpres16. change (64 / 8) with 8 in HFSpres16.
  repeat apply Forall_cons; try apply Forall_nil.
  - eapply sivb_region_kept_hi;
    [exact Vv1041 | intros a Ha; apply HK16; [unfold SB in *; lia | rewrite Hes; unfold SB in *; lia | intros []] |].
    intros a Ha. replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
    apply (proj1 (HFSpres16 (a - (SB + F / 8)) ltac:(lia))).
  - eapply sivb_region_kept_hi; [exact Vv1028 | intros a Ha; apply HK16; [lia | rewrite Hes; lia | intros []] | intros a Ha; lia].
  - eapply sivb_region_kept_hi;
    [exact Vv1028 | intros a Ha; apply HK16; [lia | rewrite Hes; lia | intros []] | intros a Ha; exact (proj1 (HFpres16 a ltac:(lia)))].
  - eapply sivb_region_kept_hi;
    [exact Vv34 | intros a Ha; apply HK16; [lia | rewrite Hes; lia | intros []] | intros a Ha; apply HJ16pres; rewrite FS; lia].
  - eapply sivb_region_kept_hi;
    [exact Vv2 | intros a Ha; apply HK16; [lia | rewrite Hes; lia | intros []] | intros a Ha; apply HJ16pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS16. clear HS. rename HS16 into HS.
remember (havoc E7 1122 (map (getr regs16) CLOB)) as E8 eqn:HE8 in HS.
assert (HAE8 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E8)
  by (rewrite HE8; apply env_agree_havoc_ge; [lia | exact HAE7]).
assert (HEI8 : img_env VAL A_LIM E8) by (rewrite HE8; apply img_env_havoc_hi; [exact HEI7 | unfold A_LIM; lia]).
assert (OLD8 : forall n, (n < 1122)%nat -> ew E8 n = ew E7 n) by (intros n Hn; rewrite HE8; apply ew_havoc_old; exact Hn).
assert (E1126 : ew E8 1126 = getr regs16 10).
{ rewrite HE8. change 1126%nat with (1122 + 4)%nat. rewrite (ew_havoc_new E7 1122 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE8.
assert (Ww2 : bv_unsigned (ew E8 2) = spZ regs) by (rewrite OLD8 by lia; exact Vv2).
assert (Ww34 : bv_unsigned (ew E8 34) = sp1) by (rewrite OLD8 by lia; exact Vv34).
assert (Ww1028 : bv_unsigned (ew E8 1028) = F) by (rewrite OLD8 by lia; exact Vv1028).
assert (Ww1040 : bv_unsigned (ew E8 1040) = FL) by (rewrite OLD8 by lia; exact Vv1040).
assert (Ww1041 : bv_unsigned (ew E8 1041) = SB + F / 8) by (rewrite OLD8 by lia; exact Vv1041).
assert (Epl8 : ew E8 10 = Z_to_bv 64 pl) by (rewrite OLD8 by lia; exact Epl7).
assert (Ek8 : ew E8 1110 = Z_to_bv 64 (Z.of_nat (sivb_spn line))) by (rewrite OLD8 by lia; exact Ek7).
assert (Ec8 : ew E8 1126 = Z_to_bv 64 (Z.of_nat (sivb_cspn line))) by (rewrite E1126, HQ16; reflexivity).
clear Xr1 Xr2 Xr3 Xr4 Xr10 Xr11.
(* run 8: a1 := strcspn's count, a0 := s4, the call of rec_shape_of (0x8ba7c) *)
paj_run_shc RUNP1 RUNC1 HS HJ16.
{ sivb_awr5 fpos sp1 regs FS Ww1041 Ww1028 Ww2 Ww34 EFA10. }
rename ms into ms17, mat into mat17, HF into HF17, HFr into HFr17, HG into HG17.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md17 := m) in *; clearbody md17 end.
sivb_preg HS (1%bv : bv 5) Yr1. sivb_preg HS (2%bv : bv 5) Yr2. sivb_preg HS (3%bv : bv 5) Yr3.
sivb_preg HS (4%bv : bv 5) Yr4. sivb_preg HS (10%bv : bv 5) Yr10. sivb_preg HS (11%bv : bv 5) Yr11.
cbn [sv_denot] in Yr1. rewrite (img_env_codeptr E8 HEI8 21840) in Yr1.
rewrite (sivb_denot_add_atoms E8 10 1110 pl (Z.of_nat (sivb_spn line)) Epl8 Ek8 ltac:(lia) ltac:(lia) Hplk) in Yr10.
rewrite sivb_denot_off0, Ec8 in Yr11.
rewrite sivb_denot_off0, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, E34 in Yr2 by lia.
rewrite sivb_denot_off0, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in Yr3 by lia.
rewrite sivb_denot_off0, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in Yr4 by lia.
assert (Qsp17 : spZ (ms_regs ms17) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite Yr2, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ16) as HAR17.
(* the line, kept from the strcspn call to here (the wrapper wrote its scratch window, run 8 nothing else) *)
assert (HLSTR17 : astr_atR (rdW W10 (ms_mem ms17)) pl line).
{ apply (sivk_str_keep (rdW W10 (ms_mem ms15))); [exact HLSTR15|]. intros a Ha.
  destruct (KNLOC pb kb a Hpbk6 ltac:(lia)) as (Hb & HnF & HnS & _).
  rewrite (sivb_aview_frame_pt E8 _ (w_H W10) mem16 (ms_mem ms17) a HFr17);
  [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Ww2, ?Ww34, ?Ww1028, ?Ww1041 in H; lia)].
  apply HK16; [lia | rewrite Hes; lia | intros []]. }
assert (HROD17 : arodata_okP SEGS RLO RHI B (rdW W10 (ms_mem ms17)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly10 S10 W10 (ms_mem ms17) _ _ _ _ _ HAR HOin HJ16 HROD).
assert (HROK17 : cmd_ro_ok (rdW W10 (ms_mem ms17)))
  by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HAR17 HROD17).
pose proof (sivb_cspn_le line) as Hcspn. rewrite length_skipn in Hcspn.
assert (HFWL : length (first_word line) = sivb_cspn line).
{ rewrite <- sivb_verb_first_word, length_firstn, length_skipn. lia. }
assert (HVB17 : Z.of_nat (length (first_word line)) <= 16 ->
  abytes_atR (rdW W10 (ms_mem ms17)) (pl + Z.of_nat (sivb_spn line)) (first_word line) /\
  (in_blockA (ablocks B ly10 S10) (pl + Z.of_nat (sivb_spn line)) (Z.of_nat (length (first_word line))) \/
   astr_argA B ly10 S10 (rdW W10 (ms_mem ms17)) (in_roP SEGS RLO RHI) [] (pl + Z.of_nat (sivb_spn line)) (Some (first_word line)))).
{ intros _. split.
  - rewrite <- sivb_verb_first_word. apply (sivb_slice_bytes _ pl line (sivb_spn line) (sivb_cspn line) HLSTR17). lia.
  - left. exists pb, kb. split; [exact Hpbk10|]. rewrite HFWL. lia. }
(* ---- the call of rec_shape_of(line + spn, cspn) (0x8ba7c) ---- *)
rewrite (sivb_sig_rec_shape_of cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_na (fx := fx1) B LAWS W10 (ms_regs ms17) (ms_mem ms17) (Z_to_bv 64 (BASE + AF_rec_shape_of)) SUP_INSTANCE_VERB_STK
    (spZ regs) FP ly S W mem md [(0, fpos)] ly10 S10 _ _ REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (sp1 - spZ regs)
    (getr (ms_regs ms17) 1) _ HJ16 Qsp17 ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity) ltac:(lia)
    ltac:(rewrite HSS; lia) ltac:(rewrite HSS, FS; lia) ltac:(rewrite Yr3; exact Hgp) ltac:(rewrite Yr4; exact Htp) eq_refl
    ltac:(rewrite Yr1; apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite Yr1, unsigned_lit_small by lia; lia)).
  - intros HPRE17. pose proof (TREC_SHAPE_OF fx1 ly10 S10 W10 (ms_regs ms17) (ms_mem ms17) _ (pl + Z.of_nat (sivb_spn line))
      (first_word line) HPRE17 HROD17 Yr10 ltac:(lia) ltac:(rewrite Yr11, HFWL; reflexivity) ltac:(rewrite HFWL; lia)
      HROK17 VOBJS HVB17) as T.
    unfold apost_base in T. apply T.
    pose proof HJ16 as (_ & _ & _ & _ & _ & _ & HNEV17 & _).
    unfold EV_SUP_INSTANCE_VERB, EV_REC_SHAPE_OF, EV_ARG_LINE, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL, EV_XMALLOC in *. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W18 c18 Hwle18 (ly18 & S18 & regs18 & mem18 & md18 & -> & HJ18 & HJc18 & HP18 &
  ((q & Hq10 & Hq64 & HqA) & Hperm18 & Ely18 & ES18)).
subst ly18 S18. rewrite Yr1.
pose proof (proj1 HJ18) as HAR18.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ18) Hfin10) as (_ & _ & HFpres18 & HFSpres18).
rewrite EFA10 in HFpres18, HFSpres18.
change (fs_frame_bytes 0) with 64 in HFpres18, HFSpres18. change (64 / 8) with 8 in HFSpres18.
jafter_call_keep_hi HS 1138%nat regs18 (mrestrict (w_H W18) mem18) HP18 [0;1;2;3;4]%nat HS18.
match type of HS18 with ?tq -> _ => assert (HRK : tq); [|specialize (HS18 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E8 _ _ _ ly10 S10 W10 (ms_mem ms17) _ ly10 S10 W18 mem18 md18 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc18 Ww1041 Hfin10);
    [ unfold shadow_addr; rewrite EFA10, <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA10, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; exact (False_ind _ (inFP_nil a HFa))
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres18 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E8 _ _ _ ly10 S10 W10 (ms_mem ms17) _ ly10 S10 W18 mem18 md18 _ 1028 F _ _ _ _ _ 0 fpos HJc18 Ww1028 Hfin10);
    [ rewrite EFA10; lia | rewrite EFA10; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; exact (False_ind _ (inFP_nil a HFa)) | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E8 _ _ _ ly10 S10 W10 (ms_mem ms17) _ ly10 S10 W18 mem18 md18 _ 1028 F _ _ _ _ _ 0 fpos HJc18 Ww1028 Hfin10);
    [ rewrite EFA10; lia | rewrite EFA10; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; exact (False_ind _ (inFP_nil a HFa)) | intros a Ha; exact (proj1 (HFpres18 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc18 HJ18 Ww34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; exact (False_ind _ (inFP_nil a HFa))].
  - eapply (region_kept_stack_sub SEGS B E8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc18 HJ18 Ww2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; exact (False_ind _ (inFP_nil a HFa))]. }
rewrite <- restrict_mkst_fx in HS18. clear HS. rename HS18 into HS.
remember (havoc E8 1138 (map (getr regs18) CLOB)) as E9 eqn:HE9 in HS.
assert (HAE9 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E9)
  by (rewrite HE9; apply env_agree_havoc_ge; [lia | exact HAE8]).
assert (HEI9 : img_env VAL A_LIM E9) by (rewrite HE9; apply img_env_havoc_hi; [exact HEI8 | unfold A_LIM; lia]).
assert (OLD9 : forall n, (n < 1138)%nat -> ew E9 n = ew E8 n) by (intros n Hn; rewrite HE9; apply ew_havoc_old; exact Hn).
assert (E1142 : ew E9 1142 = getr regs18 10).
{ rewrite HE9. change 1142%nat with (1138 + 4)%nat. rewrite (ew_havoc_new E8 1138 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE9.
assert (Xx2 : bv_unsigned (ew E9 2) = spZ regs) by (rewrite OLD9 by lia; exact Ww2).
assert (Xx34 : bv_unsigned (ew E9 34) = sp1) by (rewrite OLD9 by lia; exact Ww34).
assert (Xx1028 : bv_unsigned (ew E9 1028) = F) by (rewrite OLD9 by lia; exact Ww1028).
assert (Xx1040 : bv_unsigned (ew E9 1040) = FL) by (rewrite OLD9 by lia; exact Ww1040).
assert (Xx1041 : bv_unsigned (ew E9 1041) = SB + F / 8) by (rewrite OLD9 by lia; exact Ww1041).
clear Yr1 Yr2 Yr3 Yr4 Yr10 Yr11.
(* run 9: a1 := the shape, a0 := the slot, a2 := 1, the call of answer (0x8ba8c) *)
paj_run_shc RUNP1 RUNC1 HS HJ18.
{ sivb_awr5 fpos sp1 regs FS Xx1041 Xx1028 Xx2 Xx34 EFA10. }
rename ms into ms19, mat into mat19, HF into HF19, HFr into HFr19, HG into HG19.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => set (md19 := m) in *; clearbody md19 end.
sivb_preg HS (1%bv : bv 5) Zr1. sivb_preg HS (2%bv : bv 5) Zr2. sivb_preg HS (3%bv : bv 5) Zr3.
sivb_preg HS (4%bv : bv 5) Zr4. sivb_preg HS (8%bv : bv 5) Zr8. sivb_preg HS (10%bv : bv 5) Zr10.
sivb_preg HS (11%bv : bv 5) Zr11. sivb_preg HS (12%bv : bv 5) Zr12.
cbn [sv_denot] in Zr1, Zr12. rewrite (img_env_codeptr E9 HEI9 21856) in Zr1.
rewrite sivb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, E1046, R10 in Zr10 by lia.
rewrite sivb_denot_off0, E1142, Hq10 in Zr11.
rewrite sivb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, E34 in Zr2 by lia.
rewrite sivb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 3%nat 3%bv eq_refl) in Zr3 by lia.
rewrite sivb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 4%nat 4%bv eq_refl) in Zr4 by lia.
rewrite sivb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, Esp in Zr8 by lia.
assert (Qsp19 : spZ (ms_regs ms19) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite Zr2, unsigned_lit_small by lia; lia).
pose proof (proj1 HJ18) as HAR19.
cbn [sarg app] in HREP10, Hperm10, Hfresh10.
set (n2 := Z.of_nat (length (dec ledger)) + 1) in *.
set (R' := rec_record R REC_INSTANCE_VERB [canon line; dec ledger]) in *.
set (O' := (p2, n2) :: O1 ++ [(p1, n1)]) in *.
(* bytes below alloc_ceiling outside the frame and its shadow, kept from arg_s's return to answer's call *)
assert (KX : forall a, 0 <= a < alloc_ceiling -> ~ (F <= a < F + 64) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
  aview SEGS (w_H W18) (ms_mem ms19) a = aview SEGS (w_H W18) mem18 a /\
  aview SEGS (w_H W10) (ms_mem ms17) a = aview SEGS (w_H W10) mem10 a).
{ intros a Ha HnF HnS. split.
  - apply (sivb_aview_frame_pt E9 _ (w_H W18) mem18 (ms_mem ms19) a HFr19); [lia|].
    sivb_nwin_tac ltac:(fun H => rewrite ?Xx2, ?Xx34, ?Xx1028, ?Xx1041 in H; lia).
  - rewrite (sivb_aview_frame_pt E8 _ (w_H W10) mem16 (ms_mem ms17) a HFr17);
    [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Ww2, ?Ww34, ?Ww1028, ?Ww1041 in H; lia)].
    rewrite (HK16 a ltac:(lia) ltac:(rewrite Hes; lia) ltac:(intros [])).
    rewrite (sivb_aview_frame_pt E7 _ (w_H W10) (ms_mem ms14) (ms_mem ms15) a HFr15);
    [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Vv2, ?Vv34, ?Vv1028, ?Vv1041 in H; lia)].
    rewrite (sivb_aview_frame_pt E7 _ (w_H W10) (ms_mem ms13) (ms_mem ms14) a HFr14);
    [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Vv2, ?Vv34, ?Vv1028, ?Vv1041 in H; lia)].
    rewrite (sivb_aview_frame_pt E7 _ (w_H W10) mem12 (ms_mem ms13) a HFr13);
    [| lia | sivb_nwin_tac ltac:(fun H => rewrite ?Vv2, ?Vv34, ?Vv1028, ?Vv1041 in H; lia)].
    rewrite (HK12 a ltac:(lia) ltac:(rewrite Hes; lia) ltac:(intros [])).
    apply (sivb_aview_frame_pt E6 _ (w_H W10) mem10 (ms_mem ms11) a HFr11); [lia|].
    sivb_nwin_tac ltac:(fun H => rewrite ?Z2, ?Z34, ?Z1028, ?Z1041 in H; lia). }
assert (EFL10 : flag_addr ly10 0 fpos = FL).
{ pose proof EFA10 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
destruct (FFL _ _ _ _ _ 0 fpos HAR10 Hfin10) as (HFLp10 & HFLo10 & _ & _). rewrite EFL10 in HFLp10, HFLo10.
assert (KN10LOC : forall p n a, In (p, n) (ablocks B ly10 S10) -> p <= a < p + req_size n ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros p n a Hpn Hpa.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR10 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres10 & _).
  pose proof (sep_block_frame SEGS B LAWS ly10 S10 W10 mem10 md10 p n 0 fpos HAR10 Hpn Hfin10) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA10 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
  intros ->. exact (proj2 (Hpres10 FL ltac:(lia)) HFLo10). }
assert (HOS10 : forall pn, In pn O' -> In pn (ablocks B ly10 S10)) by exact (sivk_O_in B ly10 S10 _ _ O' HREP10).
(* the recorder at answer's call *)
assert (HREP19 : rec_repA B ly10 S10 (rdW W18 (ms_mem ms19)) R' O').
{ apply (sivk_rec_repA_ext B ly10 S10 (rdW W10 mem10) ly10 S10 _ R' O' HREP10 HOS10).
  intros a Ha.
  assert (HaL : (0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8)) /\
    ((A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
     exists p n, In (p, n) (ablocks B ly10 S10) /\ p <= a < p + req_size n)).
  { destruct Ha as [Ha | [Ha | ([p n] & Hpn & Ha)]].
    - destruct (KLOC a (or_introl Ha)) as (Hb & HnF & HnS & _). split; [lia | left; left; exact Ha].
    - destruct (KLOC a (or_intror (or_introl Ha))) as (Hb & HnF & HnS & _). split; [lia | left; right; exact Ha].
    - cbn [fst snd] in Ha. pose proof (req_size_pos n ltac:(destruct (sivk_blk_bounds B ly10 S10 W10 mem10 md10 p n HAR10 (HOS10 _ Hpn)) as (_ & _ & Hn0 & _); lia)) as [_ Hrq].
      destruct (KN10LOC p n a (HOS10 _ Hpn) ltac:(lia)) as (Hb & HnF & HnS & _).
      split; [lia | right; exists p, n; split; [exact (HOS10 _ Hpn) | lia]]. }
  destruct HaL as ((Hb & HnF & HnS) & [Hst | (p & n & Hpn & Hpa)]).
  - destruct (KX a Hb HnF HnS) as [K1 K2]. rewrite K1.
    rewrite (sivk_keep_prog B HB cmd_img_facts_tfib _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc18 (Forall_nil _) (inFP_nil a)
      ltac:(destruct Hst as [Hs | Hs]; [exact (sivk_grec_in a Hs) | exact (sivk_spill_in a Hs)])).
    exact K2.
  - destruct (KX a Hb HnF HnS) as [K1 K2]. rewrite K1.
    replace a with (p + (a - p)) by lia.
    rewrite (sivk_keep_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) HJc18 Hpn Hpn ltac:(lia) (inFP_nil _)).
    replace (p + (a - p)) with a by lia. exact K2. }
destruct (rec_repA_answer B ly10 S10 _ _ _ HREP19) as (old & Hold & Hold0).
change (sivb_hold (old = 0 \/ exists pn, In pn O' /\ fst pn = old)) in Hold0.
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct (sivb_unhold Hold0) as [-> | ([b m] & Hbm & Hbo)]; [lia|]. cbn [fst] in Hbo. subst old.
  destruct (sivk_blk_bounds B ly10 S10 W10 mem10 md10 b m HAR10 (HOS10 _ Hbm)) as (Hb4096 & Hbc & _ & _ & Hrq1).
  lia. }
set (t := snd (rec_answer R' (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true)) in *.
assert (Et : t = snd (sup_instance_verb_m R line ledger)) by (rewrite sivb_model; reflexivity).
(* the shape's text, kept from rec_shape_of's return to answer's call (read-only or a block: neither the frame nor
   its shadow) *)
assert (HQA19 : astr_argA B ly10 S10 (rdW W18 (ms_mem ms19)) (in_roP SEGS RLO RHI) O' q (Some (shape_of (first_word line)))).
{ pose proof (HqA O') as HqO. apply (sivk_argA_kept B _ _ (rdW W18 mem18) _ _ _ _ _ HqO). intros i Hi.
  pose proof (sivk_argA_low B HB cmd_img_facts_tfib ly10 S10 W18 mem18 md18 O' q _ HAR18 HqO i Hi) as Hlow.
  assert (HnFS : ~ (F <= q + i < F + 64) /\ ~ (SB + F / 8 <= q + i < SB + F / 8 + 8)).
  { pose proof HqO as (_ & _ & _ & [((b & m & Hbm & Hb1 & Hb2) & _) | (Hro & _)]).
    - pose proof (req_size_pos m ltac:(destruct (sivk_blk_bounds B ly10 S10 W10 mem10 md10 b m HAR10 Hbm) as (_ & _ & Hm0 & _); lia)) as [_ Hrq].
      destruct (KN10LOC b m (q + i) Hbm ltac:(lia)) as (_ & HnF & HnS & _). split; assumption.
    - destruct (Hro i Hi) as (Hr & _ & _). destruct (cmd_ro_prog_apart (q + i) Hr) as (Himg & _).
      pose proof (pa_segs_low (q + i) Himg) as Hl. pose proof asan_consts as (_ & _ & _ & _ & C5').
      pose proof (pa_img_range (q + i) Himg) as Hir. pose proof (sivb_unhold HFoff) as HFo.
      split; [lia | unfold SB; lia]. }
  destruct (KX (q + i) Hlow (proj1 HnFS) (proj2 HnFS)) as [K1 _]. exact K1. }
assert (HNEWB : forall x, In x O' -> ~ In x O -> ~ In x (ablocks B ly S)).
{ intros x Hx HnO HxS. rewrite <- Eab in HxS.
  apply (Permutation_in _ HPermF) in HxS. apply in_app_or in HxS as [Hx3 | HxF]; [|exact (HnO (HFO _ HxF))].
  unfold O' in Hx. destruct Hx as [<- | Hx]; [|apply in_app_or in Hx as [Hx | [<- | []]]].
  - apply (sivk_dup_false B ly10 S10 W10 mem10 md10 [(p2, n2)] (ablocks B ly6 S6) (p2, n2) HAR10 Hperm10 (or_introl eq_refl)).
    apply (Permutation_in _ (Permutation_sym Hperm6)). right. exact Hx3.
  - exact (HnO (proj1 (proj1 (HO1 x) Hx))).
  - exact (sivk_dup_false B ly6 S6 W6 mem6 md6 [(p1, n1)] (ablocks B ly3 S3) (p1, n1) HAR6 Hperm6 (or_introl eq_refl) Hx3). }
assert (HROD19 : arodata_okP SEGS RLO RHI B (rdW W18 (ms_mem ms19)))
  by exact (sivk_aro B HB cmd_img_facts_tfib ly S W mem md O ly10 S10 W18 (ms_mem ms19) _ _ _ _ _ HAR HOin HJ18 HROD).
assert (HROK19 : cmd_ro_ok (rdW W18 (ms_mem ms19)))
  by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HAR19 HROD19).
assert (HCH19 : exists ch19, achain ly10 (rdW W18 (ms_mem ms19)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms19)) ch19).
{ unfold s0Z. rewrite Zr8, unsigned_lit_small by lia.
  pose proof (st_ok_region_nth E9 _ _ 4 _ HS eq_refl) as HR4. cbn [ms_mem restrict mkst] in HR4.
  pose proof HJ18 as (_ & Hly19 & _). pose proof Hly19 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop19 & _).
  destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    eapply (achain_push ly10 (rdW W mem) (rdW W18 (ms_mem ms19)) (spZ regs) (s0Z regs) (raZ regs) ch);
    [apply (achain_ly_top ly ly10); [exact Etop19 | exact Hch] | rewrite Etop19; lia | | | | exact Hra4 | lia
    | exact (sivb_Z_mod_16_8 _ Hal16) | rewrite Etop19; exact Hlt | lia].
    + intros a Ha. exact (aview_above_of_journal B _ _ FP ly S W mem md _ _ _ _ _ _ _ HJ18 a Ha (HNFP a Ha)).
    + apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
      replace (spZ regs - 8) with (spZ regs + -8) by lia.
      refine (field_of_region E9 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-8) 8%N (SOff 1 0) (raZ regs) HR4 Xx2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) by lia;
        unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
      | unfold raZ; apply bv_unsigned_in_range | lia].
    + apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
      replace (spZ regs - 16) with (spZ regs + -16) by lia.
      refine (field_of_region E9 _ 2 (spZ regs) _ (-88) 0 (-88) 0 (-16) 8%N (SOff 8 0) (s0Z regs) HR4 Xx2 _ _ _ _);
      [cbn [In]; tauto | rewrite sivb_denot_off0, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 8%nat 8%bv eq_refl) by lia;
        unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
      | unfold s0Z; apply bv_unsigned_in_range | lia].
  - exists []. left. split; [right; left; rewrite Etop19; lia | reflexivity]. }
destruct HCH19 as (ch19 & HCH19).
pose proof HJ18 as (_ & _ & _ & _ & _ & _ & HNEV19 & _).
(* ---- the call of answer(slot, shape, 1) (0x8ba8c) ---- *)
rewrite (sivb_sig_answer cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wideF (fx := fx1) B LAWS W18 (ms_regs ms19) (ms_mem ms19) (Z_to_bv 64 (BASE + AF_answer)) SUP_INSTANCE_VERB_STK
    (spZ regs) FP ly S W mem md [(0, fpos)] ly10 S10 _ _ ANSWER_STK _ EV_ANSWER (sp1 - spZ regs) (getr (ms_regs ms19) 1) ch19 _
    HJ18 Qsp19 ltac:(rewrite Zminus_mod, Hsp1b, Hal16; reflexivity) ltac:(lia) ltac:(rewrite HNS; lia)
    ltac:(rewrite HNS, FS; lia) ltac:(rewrite Zr3; exact Hgp) ltac:(rewrite Zr4; exact Htp) eq_refl
    ltac:(rewrite Zr1; apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite Zr1, unsigned_lit_small by lia; lia) HCH19).
  - intros HPRE19. pose proof (TANSWER fx1 ly10 S10 W18 (ms_regs ms19) (ms_mem ms19) _ ch19 (rec_slot R) q old
      (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true R' O' HPRE19) as T.
    cbv zeta in T. apply T.
    + exact HRM8.
    + rewrite Hfrs10, Hfrs6, Hfrs3, Hfrs2. cbn [length]. lia.
    + exact HROD19.
    + exact HROK19.
    + exact Zr10.
    + pose proof (rec_slotA_home R HC1) as (_ & Hs1 & Hs2 & _).
      change (rec_slotA R) with (rec_slot R) in Hs1, Hs2. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in Hs1, Hs2. lia.
    + exact Zr11.
    + exact Hq64.
    + rewrite Zr12. vm_compute. reflexivity.
    + exact HREP19.
    + exact Hold.
    + exact Hold64.
    + intros _. split; [exact HQA19 | exact (proj1 (shape_of_facts (first_word line)))].
    + intros _ _. exact (rec_slotA_entry R REC_INSTANCE_VERB [canon line; dec ledger] HC1).
    + unfold EV_SUP_INSTANCE_VERB, EV_ARG_LINE, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL, EV_XMALLOC,
        EV_REC_SHAPE_OF in *. lia.
    + fold t. pose proof (LN0 t). pose proof HLIVE as HLV. unfold LIVE_SUP_INSTANCE_VERB in HLV. rewrite <- Et in HLV.
      lia.
    + apply (mok_station MT S2 S10 (XM_SUP_INSTANCE_VERB MT R line ledger)
        (XM_RECORD MT R + XM_ARG_LINE MT line + XM_ARG_S MT (Some (dec ledger))) _ MTL HMOK2
        ltac:(apply (mo_le_trans MT MTL S2 S6 S10); [apply (mo_le_trans MT MTL S2 S3 S6); [exact MLE1 | exact MLE6] | exact MLE10])
        (XN0 t)).
      unfold XM_SUP_INSTANCE_VERB. rewrite <- Et. lia.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { apply (sivk_awr_grec B HB cmd_img_facts_tfib). unfold OFF_ANSWER, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (sivk_awr_grec B HB cmd_img_facts_tfib). unfold OFF_STATE, REC_SIZE in *. lia. }
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & n & Hbn & Hba). apply sivk_in_filter in Hbn as [Hbn _].
    destruct (in_dec sivk_pair_dec (b, n) O) as [HbO | HbO].
    + exact (sivk_awr_blk B _ _ _ _ _ _ _ _ b n a HbO (HOS10 _ Hbn) Hba).
    + right. right. left. exists b, n. split; [exact (HOS10 _ Hbn)|]. split; [exact (HNEWB _ Hbn HbO) | exact Hba].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    apply inFP_cons in Ha as [Ha | Ha]; [unfold OFF_ANSWER, REC_SIZE, A_G_REC in *; rewrite FS in Hw; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [unfold OFF_STATE, REC_SIZE, A_G_REC in *; rewrite FS in Hw; lia|].
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & n & Hbn & Hba). apply sivk_in_filter in Hbn as [Hbn _].
    destruct (KN10LOC b n a (HOS10 _ Hbn) Hba) as (Hb & _). rewrite FS in Hw. lia. }
cbv beta. intros W20 c20 Hwle20 (fx2 & ly20 & S20 & regs20 & mem20 & md20 & Hfx2 & -> & HJ20 & HJc20 & HP20 & HKA).
cbv zeta in HKA.
destruct HKA as (pa & q2 & O5 & Hq2 & Hq2r & Hpaq & Hnew5 & Hbl5 & HREP20 & HO5 & HT20 & HBB20 & MLE20).
rewrite Zr1.
(* from here on the machine runs at the FP state answer returned; the post is lifted to it *)
assert (Hfx02 : fxrel fx fx2) by exact (fxrel_trans fx fx1 fx2 (fxrel_of_frm0 fx fx1 HFR8 HRM8) Hfx2).
apply (srr_apost_base_liftF (fx := fx) SEGS fx2); [exact Hfx02|].
pose proof (proj1 HJ20) as HAR20.
pose proof HJc20 as (_ & Hly20 & _ & _ & _ & Hfrs20 & _). cbn [app] in Hfrs20.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly20 HAR19 Hly20) as (Eab20 & Efa20 & _).
assert (EFA20 : frame_addr ly20 0 fpos = F) by (rewrite Efa20; exact EFA10).
assert (Hfin20 : In (0, fpos) (frames S20)) by (rewrite Hfrs20; exact Hfin10).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR20 Hfin20) as (_ & _ & HFpres20 & HFSpres20). rewrite EFA20 in HFpres20, HFSpres20.
change (fs_frame_bytes 0) with 64 in HFpres20, HFSpres20. change (64 / 8) with 8 in HFSpres20.
(* answer's footprint: g_rec's answer and state words and the old answer's block, none of the frame's bytes *)
assert (HANKA : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
    ablocks_fp (filter (fun pn => fst pn =? old) O')) a ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
  { apply KLOC. left. unfold OFF_ANSWER, REC_SIZE in *. lia. }
  apply inFP_cons in Ha as [Ha | Ha].
  { apply KLOC. left. unfold OFF_STATE, REC_SIZE in *. lia. }
  destruct (inFP_ablocks_fp_inv _ a Ha) as (b & n & Hbn & Hba). apply sivk_in_filter in Hbn as [Hbn _].
  exact (KN10LOC b n a (HOS10 _ Hbn) Hba). }
jafter_call_keep_hi HS 1154%nat regs20 (mrestrict (w_H W20) mem20) HP20 [0;1;2;3;4]%nat HS20.
match type of HS20 with ?tq -> _ => assert (HRK : tq); [|specialize (HS20 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub (segs := SEGS) B E9 _ _ _ ly10 S10 W18 (ms_mem ms19) _ ly20 S20 W20 mem20 md20 _ 1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJc20 Xx1041 Hfin10);
    [ unfold shadow_addr; rewrite EFA10, <- SB_SHADOW_OFF; lia
    | unfold shadow_addr; rewrite EFA10, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (HANKA a HFa) as (_ & _ & HnS & _); lia
    | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres20 (a - (SB + F / 8)) ltac:(lia))) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E9 _ _ _ ly10 S10 W18 (ms_mem ms19) _ ly20 S20 W20 mem20 md20 _ 1028 F _ _ _ _ _ 0 fpos HJc20 Xx1028 Hfin10);
    [ rewrite EFA10; lia | rewrite EFA10; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (HANKA a HFa) as (_ & HnF & _); lia | intros a Ha; lia ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E9 _ _ _ ly10 S10 W18 (ms_mem ms19) _ ly20 S20 W20 mem20 md20 _ 1028 F _ _ _ _ _ 0 fpos HJc20 Xx1028 Hfin10);
    [ rewrite EFA10; lia | rewrite EFA10; change (fs_frame_bytes 0) with 64; lia
    | intros a Ha HFa; destruct (HANKA a HFa) as (_ & HnF & _); lia | intros a Ha; exact (proj1 (HFpres20 a ltac:(lia))) ].
  - eapply (region_kept_stack_sub SEGS B E9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 34 _ _ _ _ _ sp1 _ _ _ _ _ _ _ _ _ _ HJc20 HJ20 Xx34);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HANKA a HFa); lia].
  - eapply (region_kept_stack_sub SEGS B E9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2 _ _ _ _ _ (spZ regs) _ _ _ _ _ _ _ _ _ _ HJc20 HJ20 Xx2);
    [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HANKA a HFa); lia]. }
rewrite <- restrict_mkst_fx in HS20. clear HS. rename HS20 into HS.
sivb_move_fx HS fx1 fx2.
remember (havoc E9 1154 (map (getr regs20) CLOB)) as E10 eqn:HE10 in HS.
assert (HAE10 : env_agree 32 (Ereg regs (sivb_extra0 (as_uar_cell B) sp1)) E10)
  by (rewrite HE10; apply env_agree_havoc_ge; [lia | exact HAE9]).
assert (HEI10 : img_env VAL A_LIM E10) by (rewrite HE10; apply img_env_havoc_hi; [exact HEI9 | unfold A_LIM; lia]).
assert (OLD10 : forall n, (n < 1154)%nat -> ew E10 n = ew E9 n) by (intros n Hn; rewrite HE10; apply ew_havoc_old; exact Hn).
assert (E1158 : ew E10 1158 = getr regs20 10).
{ rewrite HE10. change 1158%nat with (1154 + 4)%nat. rewrite (ew_havoc_new E9 1154 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE10.
assert (Yy2 : bv_unsigned (ew E10 2) = spZ regs) by (rewrite OLD10 by lia; exact Xx2).
assert (Yy34 : bv_unsigned (ew E10 34) = sp1) by (rewrite OLD10 by lia; exact Xx34).
assert (Yy1028 : bv_unsigned (ew E10 1028) = F) by (rewrite OLD10 by lia; exact Xx1028).
assert (Yy1040 : bv_unsigned (ew E10 1040) = FL) by (rewrite OLD10 by lia; exact Xx1040).
assert (Yy1041 : bv_unsigned (ew E10 1041) = SB + F / 8) by (rewrite OLD10 by lia; exact Xx1041).
clear Zr1 Zr2 Zr3 Zr4 Zr8 Zr10 Zr11 Zr12.
(* the flag cell: a one-byte region on the atom 1040 (FL), apart from the frame and its shadow *)
assert (EFL20 : flag_addr ly20 0 fpos = FL).
{ pose proof EFA20 as Hx. unfold F, frame_addr in Hx. unfold FL, flag_addr. lia. }
destruct (FFL _ _ _ _ _ 0 fpos HAR20 Hfin20) as (HFLp20 & HFLo20 & _ & _). rewrite EFL20 in HFLp20, HFLo20.
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 8)).
{ intros Hx. apply (proj2 (HFSpres20 (FL - (SB + F / 8)) ltac:(lia))).
  replace (shadow_addr F + (FL - (SB + F / 8))) with FL by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia). exact HFLo20. }
assert (HFLnF : ~ (F <= FL < F + 64)) by (intros Hx; exact (proj2 (HFpres20 FL Hx) HFLo20)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 1040%nat) 0 1 0 1 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite Yy1040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp20)
  ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite Yy1040, Yy1041, Yy1028, Yy2, Yy34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sivb_norm_ssp HS.
(* run 10, the release: the frame's magic retired (0x8ba98), s2 <> 0 at 0x8ba9c, the frame's shadow := f5, its
   flag byte := 0 through frame + 56 (0x8bac4, 0x8bac8: the release), the saved registers back, return *)
pose (RUNF := aj_flag_store_pi (fx := fx2) (PL := PL_cmd) (PI := PI) B LAWS ML AFREE_LAW FFL).
paj_run_flag_sh RUNF HS HJ20.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  destruct Hin as [<- | Hin]; [right; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Yy1040 in Hr; rewrite EFL20; lia|]. left.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Yy1041, ?Yy1028, ?Yy2, ?Yy34 in Hr;
    first [ exfalso; lia | left; rewrite FS; lia
    | right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
      first [ left; unfold in_zr; cbn [fst snd]; rewrite EFA20; change (fs_frame_bytes 0) with 64; lia
            | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA20, <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia ] ] |]).
  destruct Hin.
- intros msr HSr. rewrite EFL20.
  pose proof (st_ok_pi_region_nth E10 _ _ 0 _ HSr eq_refl) as HR0.
  pose proof (field_of_region E10 _ 1040 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR0 Yy1040 ltac:(cbn [In]; tauto) eq_refl ltac:(lia) ltac:(lia)) as HV.
  specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
-
rename ms into ms21, mat into mat21, HF into HF21, HFr into HFr21, HG into HG21.
sivb_preg HS (1%bv : bv 5) Rf1. sivb_preg HS (10%bv : bv 5) Rf10.
rewrite sivb_denot_off0, OLD10, OLD9, OLD8, OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, (EE 1%nat 1%bv eq_refl) in Rf1 by lia.
rewrite sivb_denot_off0, E1158, Hq2 in Rf10.
(* the blocks live at the release, located: none of the frame, its shadow or its flag cell *)
assert (KN20LOC : forall p n a, In (p, n) (ablocks B ly20 S20) -> p <= a < p + req_size n ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros p n a Hpn Hpa.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR20 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres20 & _).
  pose proof (sep_block_frame SEGS B LAWS ly20 S20 W20 mem20 md20 p n 0 fpos HAR20 Hpn Hfin20) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA20 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
  intros ->. exact (proj2 (Hpres20 FL ltac:(lia)) HFLo20). }
(* the release wrote only the frame's regions and the flag cell *)
assert (K2021 : forall a, 0 <= a < alloc_ceiling -> ~ (F <= a < F + 64) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) -> a <> FL ->
  aview SEGS (w_H W20) (ms_mem ms21) a = aview SEGS (w_H W20) mem20 a).
{ intros a Hb HnF HnS HnFL. apply (sivb_aview_frame_pt E10 _ (w_H W20) mem20 (ms_mem ms21) a HFr21); [lia|].
  sivb_nwin_tac ltac:(fun H => rewrite ?Yy2, ?Yy34, ?Yy1028, ?Yy1040, ?Yy1041 in H; lia). }
assert (EAB21 : ablocks B ly20 (stack_free_state 0 fpos S20) = ablocks B ly20 S20)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (HO5in : forall pn, In pn O5 -> In pn (ablocks B ly20 S20)) by exact (sivk_O_in B ly20 S20 _ _ O5 HREP20).
eapply (paj_ret_at (fx := fx2) (PL := PL_cmd) (PI := PI) W20 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
eexists ly20, (stack_free_state 0 fpos S20), (ms_regs ms21), (ms_mem ms21), _.
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
split; [rewrite Rf1, Hra'; reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ20 |
  unfold EV_SUP_INSTANCE_VERB, EV_REC_SHAPE_OF in *; lia]|].
split; [eapply (aregs_preserved_of_st_ok SEGS (w_H W20) E10 _ ms21 regs (sivb_extra0 (as_uar_cell B) sp1) HS HAE10); vm_compute; reflexivity|].
exists (fst (rec_answer R' (REC_INSTANCE_VERB, [canon line; dec ledger]) (shape_of (first_word line)) true)), t, q2, O5.
split; [rewrite sivb_model; apply surjective_pairing|].
split; [exact Rf10|].
split; [exact Hq2r|].
split.
{ rewrite <- EAB21 in HO5in.
  apply (sivk_rec_repA_ext B ly20 S20 (rdW W20 mem20) ly20 (stack_free_state 0 fpos S20) _ _ O5 HREP20 HO5in).
  intros a Ha. destruct Ha as [Ha | [Ha | ([b n] & Hpn & Ha)]].
  - destruct (KLOC a (or_introl Ha)) as (Hb & HnF & HnS & HnFL). exact (K2021 a Hb HnF HnS HnFL).
  - destruct (KLOC a (or_intror (or_introl Ha))) as (Hb & HnF & HnS & HnFL). exact (K2021 a Hb HnF HnS HnFL).
  - cbn [fst snd] in Ha. rewrite EAB21 in HO5in.
    destruct (sivk_blk_bounds B ly20 S20 W20 mem20 md20 b n HAR20 (HO5in _ Hpn)) as (_ & _ & _ & Hnr & _).
    destruct (KN20LOC b n a (HO5in _ Hpn) ltac:(lia)) as (Hb & HnF & HnS & HnFL). exact (K2021 a Hb HnF HnS HnFL). }
(* the block-set clauses of the post (sup_instance_verb_post.v) *)
pose proof HPermF as HPF0. rewrite Eab in HPF0.
destruct (sivb_blocks_post (ablocks B ly S) (ablocks B ly3 S3) (ablocks B ly6 S6) (ablocks B ly10 S10) (ablocks B ly20 S20)
  O Fr O1 O' O5 p1 n1 p2 n2 pa q2 (Z.of_nat (length t) + 1) old
  (RecBLemmas.recb_ablocks_nodup_m B ly S W mem md HAR) HOin HPF0 HFO HO1 Hperm6 Hfresh6 ltac:(unfold n1; lia)
  Hperm10 Hfresh10 ltac:(unfold n2; lia)
  ltac:(intros x; unfold O'; split;
        [ intros Hx; destruct Hx as [<- | Hx]; [right; right; reflexivity|];
          apply in_app_or in Hx as [Hx | [<- | []]]; [left; exact Hx | right; left; reflexivity]
        | intros [Hx | [-> | ->]]; [right; apply in_or_app; left; exact Hx | right; apply in_or_app; right; left; reflexivity
                                   | left; reflexivity] ])
  (fun x y Hx Hy Hf => sivk_same_start B ly10 S10 W10 mem10 md10 x y HAR10 Hx Hy Hf)
  (sivb_unhold Hold0)
  ltac:(intros [b m] Hbm; cbn [fst]; destruct (sivk_blk_bounds B ly S W mem md b m HAR Hbm) as (Hb & _); lia)
  Hnew5 Hbl5 HO5 Hpaq
  (fun x y Hx Hy Hf => sivk_same_start B ly20 S20 W20 mem20 md20 x y HAR20 Hx Hy Hf)
  ltac:(intros [b m] [b' m'] Hx Hy Hne; cbn [fst snd];
        destruct (sivk_blk_bounds B ly20 S20 W20 mem20 md20 b m HAR20 Hx) as (_ & _ & _ & Hm & _);
        destruct (sivk_blk_bounds B ly20 S20 W20 mem20 md20 b' m' HAR20 Hy) as (_ & _ & _ & Hm' & _);
        destruct (sivk_blk_apart B ly20 S20 W20 mem20 md20 b m b' m' HAR20 Hx Hy Hne); unfold iv_apart; lia))
  as (PB1 & PB2 & PB3 & PB4 & PB5 & PB6).
rewrite EAB21.
split; [exact PB1|]. split; [exact PB2|]. split; [exact PB3|]. split; [exact PB4|].
split.
{ apply (sivk_str_keep (rdW W20 mem20)); [exact HT20|]. intros a Ha.
  assert (Hq2in : In (q2, Z.of_nat (length t) + 1) (ablocks B ly20 S20)) by exact PB2.
  destruct (sivk_blk_bounds B ly20 S20 W20 mem20 md20 _ _ HAR20 Hq2in) as (_ & _ & _ & Hnr & _).
  destruct (KN20LOC q2 _ a Hq2in ltac:(lia)) as (Hb & HnF & HnS & HnFL).
  exact (K2021 a Hb HnF HnS HnFL). }
split; [exact PB5|]. split; [exact PB6|].
split.
{ assert (B21 : blocks_bytes (stack_free_state 0 fpos S20) = blocks_bytes S20).
  { reflexivity. }
  pose proof (LN0 t). fold t in HBB20. unfold LIVE_SUP_INSTANCE_VERB. rewrite <- Et.
  rewrite B21. lia. }
unfold XM_SUP_INSTANCE_VERB, stack_free_state. rewrite <- Et. apply (mo_le_set_fs_r MT MTLF).
apply (mo_le_trans MT MTL S S10 S20); [| exact MLE20].
apply (mo_le_trans MT MTL S S6 S10); [| exact MLE10].
apply (mo_le_trans MT MTL S S3 S6); [| exact MLE6].
apply (mo_le_set_fs_l MT MTLF S S3 fS2). rewrite <- ES2. exact MLE1.
Qed.
End e.
End f.
End d.
