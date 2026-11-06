(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and numbers changed; 918 of its 990 lines of code are new or changed and 294 lines of the source are left out. *)
(* sup_resp's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (image fuzz_command.asan-ubsan, entry
   0x8a188, 132 instructions; the side-stack path walked here), the B twin of the A walk (a working branch
   3b9b122549f, lib/A/Prog/sup_resp.v) in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v (flushFrame: a realigned
   frame, a side-stack frame of the stack-malloc entry, released inline).

   B's code is A's up to registers (the shadow address in s6, the frame in s7, s7 saved, sp1's slot at sp1 + 16) and
   one real difference: B inlines xstrdup, so after the snprintf wrapper the walk calls the strlen wrapper, the program
   function xmalloc (its contract, TXMALLOC, through the kit's cl_callS) and __asan_memcpy (aj_intrin_atS) itself.
   No UBSan trap site (a Theorem Labs lane's scan of the B-only code, file bonly.txt: 0 trap instructions, 0 guard branches).

   Path: the use-after-return flag is 1 (the allocator record's constant cell, AR_const_law), so `beqz a2` at 0x8a1dc
   falls through to __asan_stack_malloc_1; its frame address is not 0, so `bnez s2` at 0x8a1f8 skips the real-stack
   fallback (0x8a1fc..0x8a214) and `beqz s2` at 0x8a2e0 skips the real-stack shadow reset (0x8a334..0x8a360).

   FP state: the snprintf wrapper returns at some FP state fx1 (RtPFShared.v sh_asnprintf_realizes). The rest of the
   walk (strlen, xmalloc, memcpy, the release, ret) keeps it, so it runs at fx1 with the runtime and callee contracts
   taken at fx1 (the statement's forall fx0 hypotheses) and the symbolic state moved to fx1 by the kit's
   PaFx.st_ok_pi_restrict_xfx; its apost_baseF at fx1 is the function's apost_baseF at the entry's fx. The snprintf
   destination's 8 slack bytes (amem_range d (w + 8)) lie in sup_resp's own fake frame (PaLibH.amem_range_sub_app). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaArt PaArtOwn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdRecRo CmdRecImg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtAPI RtString RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c sup_resp_c sup_resp_s0 sup_resp_s1 sup_resp_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas CmdSnText.
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
   term doubles per run (a Theorem Labs lane, 2026-10-29), so make it opaque right after each run *)
Ltac collapse_md :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdl) _ =>
first [ is_var mdl | let mdv := fresh "mdv" in set (mdv := mdl) in *; clearbody mdv ] end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the text "resp <code>" is bytes: every element of "resp " and of the decimal digits (and '-') is below 256 *)
Lemma sr_digits_rng : forall f x acc, 0 <= x -> Forall (fun c => 0 <= c < 256) acc ->
  Forall (fun c => 0 <= c < 256) (PF.pf_digits f x acc).
Proof.
induction f as [|f IH]; intros x acc Hx Hacc; cbn [PF.pf_digits]; [exact Hacc|].
destruct (Z.ltb_spec x 10) as [Hl|Hl].
- constructor; [lia | exact Hacc].
- apply IH; [apply Z.div_pos; lia|]. constructor; [pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia | exact Hacc].
Qed.
Lemma sr_T_rng : forall code, Forall (fun c => 0 <= c < 256) (RA.RESP_HEAD ++ PF.pf_dec code).
Proof.
intros code. apply Forall_app. split; [unfold RA.RESP_HEAD; repeat apply Forall_cons; try apply Forall_nil; lia|].
unfold PF.pf_dec. destruct (Z.ltb_spec code 0) as [Hc|Hc].
- constructor; [lia|]. apply sr_digits_rng; [lia | constructor].
- apply sr_digits_rng; [lia | constructor].
Qed.
(* the bytes the snprintf wrapper leaves at d (the shared post's sn_bytes, a list of Z) as the byte list of the
   string *)
Lemma sr_buf_strZ : forall (rd : reader) d (T : list Z), Forall (fun c => 0 <= c < 256) T ->
  (forall i, 0 <= i < Z.of_nat (length T) + 1 -> rd (d + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)) ->
  abytes_atR rd d (PF.pf_bytes T ++ [Z_to_bv 8 0]).
Proof.
intros rd d T HT H i Hi. unfold PF.pf_bytes in *. rewrite length_app, length_map in Hi. cbn [length] in Hi.
rewrite (H (Z.of_nat i)) by lia. rewrite Nat2Z.id. f_equal.
destruct (Nat.lt_ge_cases i (length T)) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. rewrite app_nth1 by (rewrite length_map; exact Hl).
  rewrite map_nth. rewrite Z_to_bv_unsigned, bv_wrap8_mod.
  pose proof (proj1 (Forall_forall _ T) HT (nth i T 0) (nth_In T 0 Hl)) as Hr. cbv beta in Hr.
  rewrite Z.mod_small by lia. reflexivity.
- assert (i = length T) as -> by lia.
  rewrite app_nth2 by lia. rewrite app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Nat.sub_diag. reflexivity.
Qed.
(* a literal of the image as the format's Z bytes *)
Lemma sr_lit_bytes : forall (rd : reader) f (l : list Z), Forall (fun c => 0 <= c < 256) l ->
  abytes_atR rd f (map (Z_to_bv 8) l) -> forall i, 0 <= i < Z.of_nat (length l) -> rd (f + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros rd f l Hl H i Hi. pose proof (H (Z.to_nat i) ltac:(rewrite length_map; lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal. rewrite map_nth. rewrite Z_to_bv_unsigned, bv_wrap8_mod.
assert (Hn : (Z.to_nat i < length l)%nat) by lia.
pose proof (proj1 (Forall_forall _ l) Hl (nth (Z.to_nat i) l 0) (nth_In l 0 Hn)) as Hr. cbv beta in Hr.
apply Z.mod_small. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_resp_c.v:77-82), word for word *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, a Theorem Labs lane's names (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
(* IMG (a Theorem Labs lane's RULING-STMT.md section 1): the image facts of the record (lib/B/Prog/CmdRecBase.v). The record facts the walk
   uses are the kit's lemmas, applied by exact: RRO and cmd_ro_ok_of_aro (CmdRecRo.v), cmd_rec_cells
   (CmdRecCells.v), cmd_hull_vis_chk (CmdRecBase.v), and IMG's field cif_prog_img. *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let errno_low := pal_env B TL.

(* the shadow word over the format "resp %d" (0x21d40) is visible and its 8 bytes addressable; the record's
   checkers decide both *)
Lemma sr_lit_hull : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> shadow_hull_vis (rdW W mem) 0x21d40 8.
Proof. intros ly S W mem md HAR. exact (cmd_hull_vis_chk SEGS B LAWS HB ly S W mem md 0x21d40 8 HAR ltac:(vm_compute; reflexivity)). Qed.
Lemma sr_lit_addr : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (rdW W mem) SHADOW_OFF 0x21d40 8.
Proof. intros ly S W mem md HAR. exact (cmd_addressable_chk SEGS B LAWS HB ly S W mem md 0x21d40 8 HAR ltac:(vm_compute; reflexivity)). Qed.
(* the listing's call target for xmalloc is its entry in the statement's form *)
Lemma sr_sig_xmalloc : SIG CS_xmalloc = BASE + AF_xmalloc.
Proof.
rewrite (SIGP CS_xmalloc ltac:(unfold cmd_prog_syms; cbn [In]; repeat (try (now left); right))).
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
assert (FFS : SUP_RESP_STK = 16512) by reflexivity.
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
(* 0x8a188 .. 0x8a1b8: the 96-byte frame, the saves (ra, s0 .. s7), s0 := sp0, sp := (sp0 - 96) & -32 *)
paj_run_to_tok RUNTO HS HJ SHOK SR_Bspan 0x3c8c.
{ awr_ok_tac. exact Usp. }
clear_frames. collapse_md.
(* the realigned stack pointer sp1 becomes atom 40; the frame keeps its top 72 bytes (the saves), and sp1's own
   slot sp1 + 16 (s7's spill at 0x8a218) is a region of its own *)
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (CmdSnText.snt_sp1_facts (spZ regs + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia. clear Hsp1r.
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
  (CmdSnText.snt_denot_and_m32 E 2 (spZ regs) (-96) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2.
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
let rs' := eval vm_compute in (trim_stack rs (-72) 0) in
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
(* 0x8a1bc .. 0x8a1e4: s1 := sp1, the shadow base and the use-after-return flag (1, the record's constant cell),
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
(* back at 0x8a1e8: the frame region keeps the slot sp1 + 16 and the saves (both above sp1) *)
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
(* 0x8a1e8 .. 0x8a298: s2 = s7 := F (not 0: `bnez s2` skips the real-stack fallback), sp1's slot := F, s4 := buf,
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
assert (HLIT : abytes_atR (rdW W (ms_mem ms1)) 0x21d40 RO_lit_21d40).
{ clear - HRO3. destruct HRO3 as [HRO3 _]. unfold cmd_ro_bytes in HRO3.
  repeat match type of HRO3 with
  | abytes_atR _ 0x21d40 _ /\ _ => exact (proj1 HRO3)
  | _ /\ _ => apply proj2 in HRO3
  end. }
assert (HspT : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite P2, E40, unsigned_lit_small by lia; lia).
assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (AG 3%nat), E3 by lia; exact Hgp).
assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (AG 4%nat), E4 by lia; exact Htp).
assert (P10' : getr (ms_regs ms1) 10 = w64 (F + 32)) by (rewrite P10, E52, unsigned_lit_small by lia; reflexivity).
assert (P12' : getr (ms_regs ms1) 12 = w64 0x21d40).
{ rewrite P12. lazymatch goal with |- ew ?Ev _ = _ => let HEv := rnHEI Ev in
  pose proof (HEv 288%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H288 end.
  change (VAL 288%nat) with (VAL (A_OBJ 47)) in H288. rewrite (VOBJS 47%nat ltac:(vm_compute; lia)) in H288.
  apply bv_eq. rewrite H288. unfold w64. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (P13' : getr (ms_regs ms1) 13 = w64 code) by (rewrite P13, (AG 10%nat), E10 by lia; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hal1 : (sp1 - spZ regs) mod 16 = 0) by (rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity).
(* the buffer's shadow (bytes 4..7 of the frame's shadow, written 00 at 0x8a274..0x8a280) *)
assert (ZB : forall i, 4 <= i < 8 -> aview SEGS (w_H W) (ms_mem ms1) (SB + F / 8 + i) = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_region_nth Ex ssx msx 2 _ HS eq_refl) as HR end.
  cbn [ms_mem restrict] in HR.
  intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]]; (apply aview_of_val_mem1; [|lia]);
  (eapply field_of_region with (w := 1%N) (e := SLit 0) (v := 0); [exact HR | rewrite E65, unsigned_lit_small by (unfold SB; lia); reflexivity
    | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia ]). }
(* the text the snprintf wrapper writes: T = "resp " ++ the decimal of code (6 .. 16 bytes), then its terminator *)
set (T := RA.RESP_HEAD ++ PF.pf_dec code).
pose proof (sr_fmt_len code Hcode) as HLT. fold T in HLT.
pose proof (sr_T_rng code) as HTR. fold T in HTR.
assert (HTB : PF.pf_bytes T = resp code) by exact (sr_fmt_bytes code Hcode).
assert (HLR : length (resp code) = length T) by (rewrite <- HTB; unfold PF.pf_bytes; apply length_map).
assert (HSNW : sn_len (32 - 1) T = Z.of_nat (length T) + 1).
{ unfold sn_len, sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat. rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. lia. }
assert (HSNB : sn_bytes (32 - 1) T = T ++ [0]).
{ unfold sn_bytes. change (Z.to_nat (32 - 1)) with 31%nat. rewrite firstn_all2 by lia. reflexivity. }
assert (HFz : F + 128 <= SB \/ 0x10007fff8000 <= F)
  by (clear - HFhigh; unfold in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SB in *; lia).
  assert (HF8m : F mod 8 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
  (* the buffer's facts every entry's read premise asks, for a length n <= 32 *)
  assert (HBUF : forall (rd : reader) n, 0 < n <= 32 -> (forall i, 4 <= i < 8 -> rd (SB + F / 8 + i) = Some 0) ->
    amem_range (F + 32) n /\ range_addressable rd SHADOW_OFF (F + 32) n).
  { intros rd n Hn HZ. split.
    - unfold amem_range; unfold in_app in HFhigh; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *; lia.
    - intros x Hx. exists 0. split; [|left; reflexivity].
      unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
      assert (Hi : 4 <= x / 8 - F / 8 < 8) by (clear - Hx HF64 Hn; Z.div_mod_to_equations; lia).
      replace (SB + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by lia. apply HZ. exact Hi. }
lazymatch goal with |- SRr _ _ _ (apost_baseF _ _ _ _ _ _ _ _ _ _ _ ?Q) => set (QP := Q) end.
(* the walk after the snprintf wrapper (0x8a29c .. 0x8a394), at the FP state fx1 the wrapper returns at *)
assert (CONT : forall (fx1 : YK11.FPState) regs3 mem3 md3,
  ajournal SEGS B SUP_RESP_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly S2 W mem3 md3 0 ->
  aregs_preserved (ms_regs ms1) regs3 ->
  (forall i, 0 <= i < sn_len (32 - 1) T ->
     aview SEGS (w_H W) mem3 (F + 32 + i) = Some (nth (Z.to_nat i) (sn_bytes (32 - 1) T) 0)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - CMD_SNP_K <= a < sp1) -> ~ (F + 32 <= a < F + 32 + sn_len (32 - 1) T) ->
     aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) (ms_mem ms1) a) ->
  SRr SEGS W (mkCfg (mkst (fx := fx1) regs3 (getr (ms_regs ms1) 1) mem3 (seg_rom SEGS)) md3)
    (apost_baseF (fx := fx1) SEGS B SUP_RESP_STK [] regs ly S W mem md EV_SUP_RESP QP)).
{ intros fx1 regs3 mem3 md3 HJ3 HP3 HQb HK3.
  rewrite HSNW in HQb, HK3. rewrite HSNB in HQb.
  assert (HCK : CMD_SNP_K = 8192) by reflexivity. rewrite HCK in HK3.
  pose proof HJ3 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin2) as (_ & _ & HFpres4 & HFSpres4).
  change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
  unfold shadow_addr in HFSpres4. rewrite <- SB_SHADOW_OFF in HFSpres4. change (128 / 8) with 16 in HFSpres4.
  (* back at 0x8a29c: the wrapper wrote only buf [F + 32, F + 32 + |T| + 1) and its window below sp1, so the five
     regions (the frame header, the flag word, the frame's shadow, sp1's slot, the saves) are kept *)
  jafter_call_keep_pi HS 66%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3; 4]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
     rewrite ?E40, ?E52, ?E65, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by (unfold SB; lia); intros a Ha;
     [ apply (mbyte_of_aview SEGS); apply HK3; unfold SB in *; lia
     | intros _; apply (apresent_writable SEGS);
       first [ apply Hpres4; rewrite FFS; lia
             | apply (proj1 (HFpres4 a ltac:(lia)))
             | let Hp := fresh "Hp" in
               pose proof (proj1 (HFSpres4 (a - (SB + F / 8)) ltac:(lia))) as Hp;
               replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
             | lia ] ]). }
  clear HS. rewrite <- restrict_mkst_fx in HS2.
  apply (st_ok_pi_restrict_xfx fx fx1) in HS2. rename HS2 into HS.
  hei_havoc HS. rebaseE HS AG HEv. clear HEv.
  rewrite P1.
  (* the walk's steps at fx1 *)
  pose (RUNP1 := SRr_run_pi_AJ (fx := fx1) B LAWS). pose (RUNC1 := SRr_run_pi_AJ_call (fx := fx1) B LAWS).
  pose (RUNF1 := aj_flag_store_pi (fx := fx1) B LAWS ML ASF FFL).
  pose (RET1 := paj_ret_at (fx := fx1) (PL := PL_cmd) (PI := PI)).
  (* 0x8a29c .. 0x8a2a0: a0 := buf, the call of the strlen wrapper *)
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
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem3) (mrestrict _ _) |- _ => rename HFx into HFrT end.
  pmkst HS. collapse_md.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ => rename msX into msT end.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10.
  (* buf is in no write window of the run *)
  assert (HbufT : forall a, F + 32 <= a < F + 64 -> rdW W (ms_mem msT) a = rdW W mem3 a).
  { intros a Ha. apply RecBLemmas.recb_run_keeps_m with (1 := HFrT); [lia|].
    let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
        unfold SB in *; lia | ]);
    destruct Hin. }
  pose proof HJ3 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin2) as (_ & _ & HFpres5 & _).
  change (fs_frame_bytes 1) with 128 in HFpres5. fold F in HFpres5.
  assert (HspX : spZ (ms_regs msT) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite T2, E40, unsigned_lit_small by lia; lia).
  assert (T3' : getr (ms_regs msT) 3 = w64 (as_gp B)) by (rewrite T3, (AG 3%nat), E3 by lia; exact Hgp).
  assert (T4' : getr (ms_regs msT) 4 = w64 (as_tp B)) by (rewrite T4, (AG 4%nat), E4 by lia; exact Htp).
  assert (T10' : getr (ms_regs msT) 10 = w64 (F + 32)) by (rewrite T10, E52, unsigned_lit_small by lia; reflexivity).
  assert (HraX : YK0s.ret_ok (getr (ms_regs msT) 1)) by (rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (HROD_T : arodata_okP SEGS RLO RHI B (rdW W (ms_mem msT)))
    by exact (aro_journal0 SEGS B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RRO SEGS B LAWS HB IMG) HJ3 HROD).
  assert (HSTR_T : astr_atR (rdW W (ms_mem msT)) (F + 32) (resp code)).
  { split; [|exact (resp_no0 code)]. rewrite <- HTB. apply sr_buf_strZ; [exact HTR|].
    intros i Hi. rewrite HbufT by lia. exact (HQb i Hi). }
  (* buf's shadow: bytes 4..7 of the frame's shadow are 00 (the region's chunks) *)
  assert (ZBT : forall i, 4 <= i < 8 -> aview SEGS (w_H W) (ms_mem msT) (SB + F / 8 + i) = Some 0).
  { lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_region_nth Ex ssx msx 2 _ HS eq_refl) as HR end.
    cbn [ms_mem restrict] in HR.
    intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]]; (apply aview_of_val_mem1; [|lia]);
    (eapply field_of_region with (w := 1%N) (e := SLit 0) (v := 0); [exact HR | rewrite E65, unsigned_lit_small by (unfold SB; lia); reflexivity
      | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia ]). }
  (* 0x8a2a0: strlen(buf) = |resp code| (a Theorem Labs lane's astrlen_realizes, at fx1) *)
  eapply SRr_bind.
  { eapply (aj_art_at (fx := fx1) SEGS B LAWS Hsegs errno_low ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen)
      W (ms_regs msT) (ms_mem msT) SUP_RESP_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly S2 _ 0 (sp1 - spZ regs) _ _
      HJ3 HspX Hal1 ltac:(lia) ltac:(lia) ltac:(rewrite FFS, Hes; lia) T1 (fun a (H : False) => False_ind _ H)).
    apply (ASTRLEN fx1 ly S2 W (ms_regs msT) (ms_mem msT) _ (F + 32) (resp code)).
    - exact (ecall_pre_stk_at SEGS B ESTACK SUP_RESP_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly S2 W (ms_mem msT) _ 0
        (ms_regs msT) (sp1 - spZ regs) HJ3 HspX Hal1 ltac:(lia) ltac:(lia) ltac:(rewrite FFS, Hes; lia) HraX T3' T4').
    - exact T10'.
    - lia.
    - apply (astr_atR_view SEGS). exact HSTR_T.
    - unfold astr_len. rewrite HLR.
      destruct (HBUF (rdW W (ms_mem msT)) (Z.of_nat (length T) + 1) ltac:(lia) ZBT) as [Hamr Hra1].
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [apply (aview_some_of_apresent SEGS); exact (proj1 (HFpres5 a ltac:(lia))) | unfold ascratch_stk; rewrite HspX; lia]. }
      split; [exact Hamr|]. split; [exact Hra1|]. intros _.
      exact (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W (ms_mem msT) _ 1 fpos (F + 32) (Z.of_nat (length T) + 1) HAR5 Hfin2
        ltac:(fold F; lia) ltac:(change (fs_frame_bytes 1) with 128; fold F; lia) ltac:(lia)).
    - unfold astr_len. rewrite HLR. intros a Ha. apply (aview_some_of_apresent SEGS).
      exact (proj1 (HFpres5 a ltac:(clear - Ha HF64 HLT; Z.div_mod_to_equations; lia))).
    - intros a (sg & Hsg & Hw & Hr) Ho He.
      exact (HROD_T a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & HK4).
  (* back at 0x8a2a4: the wrapper wrote only its window below sp1 *)
  pose proof HJ4 as (HAR6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin2) as (_ & _ & HFpres6 & HFSpres6).
  change (fs_frame_bytes 1) with 128 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
  unfold shadow_addr in HFSpres6. rewrite <- SB_SHADOW_OFF in HFSpres6. change (128 / 8) with 16 in HFSpres6.
  jafter_call_keep_pi HS 82%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2; 3; 4]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
     rewrite ?E40, ?E52, ?E65, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by (unfold SB; lia); intros a Ha;
     [ apply (mbyte_of_aview SEGS); apply HK4; first [tauto | unfold ESTACK, SB in *; lia]
     | intros _; apply (apresent_writable SEGS);
       first [ apply Hpres6; rewrite FFS; lia
             | apply (proj1 (HFpres6 a ltac:(lia)))
             | let Hp := fresh "Hp" in
               pose proof (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(lia))) as Hp;
               replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
             | lia ] ]). }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  hei_havoc HS. rebaseE HS AG HEv.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E86 : ew Ev 86 = getr regs4 10) by (rewrite HEv; reflexivity) end.
  clear HEv.
  assert (Hbuf4 : forall a, F + 32 <= a < F + 64 -> rdW W mem4 a = rdW W (ms_mem msT) a)
    by (intros a Ha; apply HK4; [lia | unfold ESTACK in *; lia | tauto]).
  (* 0x8a2a4 .. 0x8a2ac: s5 := |resp code| + 1, a0 := s5, the call of xmalloc *)
  paj_run_shc RUNP1 RUNC1 HS HJ4.
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
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem4) (mrestrict _ _) |- _ => rename HFx into HFrU end.
  pmkst HS. collapse_md.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ => rename msX into msU end.
  prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
  prreg HS (8%bv : bv 5) U8. prreg HS (10%bv : bv 5) U10.
  assert (HbufU : forall a, F + 32 <= a < F + 64 -> rdW W (ms_mem msU) a = rdW W mem4 a).
  { intros a Ha. apply RecBLemmas.recb_run_keeps_m with (1 := HFrU); [lia|].
    let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
        unfold SB in *; lia | ]);
    destruct Hin. }
  set (n := Z.of_nat (length (resp code)) + 1).
  assert (Hn : 2 <= n <= 17) by (unfold n; rewrite HLR; lia).
  assert (HspU : spZ (ms_regs msU) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite U2, E40, unsigned_lit_small by lia; lia).
  assert (U3' : getr (ms_regs msU) 3 = w64 (as_gp B)) by (rewrite U3, (AG 3%nat), E3 by lia; exact Hgp).
  assert (U4' : getr (ms_regs msU) 4 = w64 (as_tp B)) by (rewrite U4, (AG 4%nat), E4 by lia; exact Htp).
  assert (U10' : getr (ms_regs msU) 10 = w64 n).
  { rewrite U10, E86, Ha04. unfold w64. rewrite unsigned_lit_small by (unfold astr_len; lia). unfold astr_len. reflexivity. }
  assert (Hs0U : s0Z (ms_regs msU) = spZ regs) by (unfold s0Z; rewrite U8, (AG 2%nat) by lia; exact Usp).
  assert (HraU : YK0s.ret_ok (getr (ms_regs msU) 1)) by (rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hra4U : 4096 <= bv_unsigned (getr (ms_regs msU) 1)) by (rewrite U1, unsigned_lit_small by lia; lia).
  (* xmalloc's frame chain at the call (pass 5; S0-SITES.md class B: s0 is this call's frame pointer sp0): afn_pre's
     chain pushed by the frame record the prologue stored, ra at sp0 - 8 and the entry s0 at sp0 - 16 (achain_push,
     YCbq.v:413), or the empty chain when sp0 is within 16 bytes of the stack top *)
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 4 _ HS eq_refl) as HR4 end.
  cbn [ms_mem restrict] in HR4.
  assert (HRA8 : rdword (rdW W (ms_mem msU)) (spZ regs + -8) = Some (raZ regs)).
  { apply rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
    apply (field_of_region _ _ 2 _ _ _ _ _ _ (-8) 8%N (SOff 1 0) (raZ regs) HR4).
    - rewrite (AG 2%nat) by lia. exact Usp.
    - cbn [In]; tauto.
    - cbn [sv_denot]. rewrite (AG 1%nat), E1 by lia. rewrite Z.add_0_r. reflexivity.
    - unfold raZ. apply bv_unsigned_in_range.
    - lia. }
  assert (HS016 : rdword (rdW W (ms_mem msU)) (spZ regs + -16) = Some (s0Z regs)).
  { apply rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
    apply (field_of_region _ _ 2 _ _ _ _ _ _ (-16) 8%N (SOff 8 0) (s0Z regs) HR4).
    - rewrite (AG 2%nat) by lia. exact Usp.
    - cbn [In]; tauto.
    - cbn [sv_denot]. rewrite (AG 8%nat), (EE 8%nat 8%bv eq_refl) by lia. rewrite Z.add_0_r. reflexivity.
    - unfold s0Z. apply bv_unsigned_in_range.
    - lia. }
  assert (HCH_U : exists ch1, achain ly (rdW W (ms_mem msU)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs msU)) ch1).
  { rewrite Hs0U. destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
    - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
      pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1j & _).
      apply (achain_push ly (rdW W mem) (rdW W (ms_mem msU)) (spZ regs) (s0Z regs) (raZ regs) ch _ Hch).
      + lia.
      + intros a Ha. apply F1j; [lia | lia | exact (inFP_nil a)].
      + replace (spZ regs - 8) with (spZ regs + -8) by lia. exact HRA8.
      + replace (spZ regs - 16) with (spZ regs + -16) by lia. exact HS016.
      + exact Hra4.
      + lia.
      + clear - Hal16. Z.div_mod_to_equations. lia.
      + exact Hlt.
      + lia.
    - exists []. left. split; [right; left; exact Hge | reflexivity]. }
  destruct HCH_U as (ch1 & Hch1).
  assert (HEV_U : st_nev S2 + EV_XMALLOC <= EV_MAX) by (unfold EV_SUP_RESP in Hev; lia).
  assert (HLIVE_U : blocks_bytes S2 + LIVE_XMALLOC n <= LIVE_MAX) by (unfold LIVE_SUP_RESP in Hlive; fold n in Hlive; lia).
  assert (HMOK_U : mo_ok MT S2 (XM_XMALLOC MT n)) by (rewrite ES2; apply (mo_ok_set_fs MT MTFL); exact MOK).
  assert (HnM : 0 <= n < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
  assert (HXM : XMALLOC_STK = 16400) by reflexivity.
  assert (HLX : LIVE_XMALLOC n = n) by (unfold LIVE_XMALLOC; lia).
  (* 0x8a2ac: xmalloc(|resp code| + 1), through the kit's call rule (xmalloc's footprint is empty) *)
  rewrite sr_sig_xmalloc.
  eapply SRr_bind.
  { eapply (cl_callS (fx := fx1) B LAWS W (ms_regs msU) (ms_mem msU) (Z_to_bv 64 (BASE + AF_xmalloc)) SUP_RESP_STK (spZ regs) []
      ly S W mem md [(1, fpos)] ly S2 _ 0 XMALLOC_STK [] EV_XMALLOC (sp1 - spZ regs) (getr (ms_regs msU) 1) ch1
      (fun ly5 S5 W5 regs5 mem5 md5 => exists p : Z,
         getr regs5 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
         Permutation (ablocks B ly5 S5) ((p, LIVE_XMALLOC n) :: ablocks B ly S2) /\
         Forall (fun qk => iv_apart p (LIVE_XMALLOC n) (fst qk) (snd qk)) (ablocks B ly S2) /\
         in_blockA (ablocks B ly5 S5) p (LIVE_XMALLOC n) /\
         blocks_bytes S5 <= blocks_bytes S2 + LIVE_XMALLOC n /\
         mo_le MT S2 S5 (XM_XMALLOC MT n))
      HJ4 HspU Hal1 ltac:(lia) ltac:(rewrite HXM; lia) ltac:(rewrite FFS, HXM; lia)
      U3' U4' eq_refl HraU Hra4U Hch1).
    - intros HPREc. eapply SRr_mono.
      { exact (TXMALLOC fx1 ly S2 W (ms_regs msU) (ms_mem msU) _ ch1 n HPREc U10' HnM HEV_U HLIVE_U HMOK_U). }
      cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJx & HPx & HQx).
      exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJx|]. split; [exact HPx | exact HQx].
    - intros a Ha. destruct (inFP_nil a Ha). }
  cbv beta.
  intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJ5c & HP5 & p & Hp10 & Hp4096 & Hpperm & Hpapart & Hpblk & Hbb5 & MLE5).
  rewrite HLX in Hpperm, Hpapart, Hpblk, Hbb5.
  (* back at 0x8a2b0: the frame (header, flag word, shadow) and the saves are kept *)
  pose proof HJ5 as (HAR7 & Hly7 & _ & _ & _ & Hfrs7 & _ & _ & _ & _ & _ & _ & _ & Hpres7 & _).
  pose proof HJ5c as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _ & _ & F4c & _).
  assert (Hfin7 : In (1, fpos) (frames S5)) by (rewrite Hfrs7; left; reflexivity).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR Hly7) as (_ & Efa7 & _).
  assert (EF7 : frame_addr ly5 1 fpos = F) by exact (Efa7 1 fpos).
  assert (EFL7 : flag_addr ly5 1 fpos = FL).
  { change FL with (flag_addr ly 1 fpos). pose proof (Efa7 1 fpos) as Ee. unfold frame_addr, flag_addr in *. lia. }
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & HFSpres7).
  rewrite EF7 in HFpres7, HFSpres7. change (fs_frame_bytes 1) with 128 in HFpres7, HFSpres7.
  unfold shadow_addr in HFSpres7. rewrite <- SB_SHADOW_OFF in HFSpres7. change (128 / 8) with 16 in HFSpres7.
  jafter_call_keep_pi HS 98%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0; 1; 2; 3; 4]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
     rewrite ?E40, ?E52, ?E65, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by (unfold SB; lia); intros a Ha;
     [ apply (mbyte_of_aview SEGS);
       first [ apply F1c; [unfold SB in *; lia | rewrite HXM; lia | exact (inFP_nil a)]
             | apply (F4c 1 fpos a Hfin2); [|exact (inFP_nil a)];
               first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia
                     | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16;
                       fold F; unfold SB in *; lia ] ]
     | intros _; apply (apresent_writable SEGS);
       first [ apply Hpres7; rewrite FFS; lia
             | apply (proj1 (HFpres7 a ltac:(lia)))
             | let Hp := fresh "Hp" in
               pose proof (proj1 (HFSpres7 (a - (SB + F / 8)) ltac:(lia))) as Hp;
               replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
             | lia ] ]). }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  hei_havoc HS. rebaseE HS AG HEv.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E102 : ew Ev 102 = getr regs5 10) by (rewrite HEv; reflexivity) end.
  clear HEv.
  assert (Hbuf5 : forall a, F + 32 <= a < F + 64 -> rdW W5 mem5 a = rdW W (ms_mem msU) a).
  { intros a Ha. apply (F4c 1 fpos a Hfin2); [|exact (inFP_nil a)].
    left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia. }
  (* 0x8a2b0 .. 0x8a2bc: s3 := the block, a1 := buf, a2 := s5, the call of __asan_memcpy *)
  rewrite U1.
  paj_run_shc RUNP1 RUNC1 HS HJ5.
  { let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros a (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
        first [ exfalso; clear - Hr; lia
              | left; rewrite FFS; lia
              | right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; rewrite EF7;
                first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
                      | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16;
                        unfold SB in *; lia ] ] | ]);
    destruct Hin. }
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem5) (mrestrict _ _) |- _ => rename HFx into HFrV end.
  pmkst HS. collapse_md.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ => rename msX into msV end.
  prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3. prreg HS (4%bv : bv 5) V4.
  prreg HS (10%bv : bv 5) V10. prreg HS (11%bv : bv 5) V11. prreg HS (12%bv : bv 5) V12.
  assert (HbufV : forall a, F + 32 <= a < F + 64 -> rdW W5 (ms_mem msV) a = rdW W5 mem5 a).
  { intros a Ha. apply RecBLemmas.recb_run_keeps_m with (1 := HFrV); [lia|].
    let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
        unfold SB in *; lia | ]);
    destruct Hin. }
  (* buf still holds resp code: kept by the strlen wrapper, xmalloc (a frame of S2, footprint []) and the runs *)
  assert (HSTR_V : astr_atR (rdW W5 (ms_mem msV)) (F + 32) (resp code)).
  { apply (s3_str (rdW W (ms_mem msT))); [|exact HSTR_T].
    intros x Hx. rewrite HLR in Hx.
    rewrite HbufV by lia. rewrite Hbuf5 by lia. rewrite HbufU by lia. apply Hbuf4. lia. }
  pose proof HJ5 as (HAR8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres8 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR8 Hfin7) as (_ & _ & HFpres8 & _).
  rewrite EF7 in HFpres8. change (fs_frame_bytes 1) with 128 in HFpres8.
  assert (HspV : spZ (ms_regs msV) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite V2, E40, unsigned_lit_small by lia; lia).
  assert (V3' : getr (ms_regs msV) 3 = w64 (as_gp B)) by (rewrite V3, (AG 3%nat), E3 by lia; exact Hgp).
  assert (V4' : getr (ms_regs msV) 4 = w64 (as_tp B)) by (rewrite V4, (AG 4%nat), E4 by lia; exact Htp).
  assert (HraV : YK0s.ret_ok (getr (ms_regs msV) 1)) by (rewrite V1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Va0 : getr (ms_regs msV) 10 = w64 p) by (rewrite V10, E102; exact Hp10).
  assert (Va1 : getr (ms_regs msV) 11 = w64 (F + 32)) by (rewrite V11, E52, unsigned_lit_small by lia; reflexivity).
  assert (Va2 : getr (ms_regs msV) 12 = w64 n).
  { rewrite V12, E86, Ha04. unfold w64. rewrite unsigned_lit_small by (unfold astr_len; lia). unfold astr_len. reflexivity. }
  assert (ZBV : forall i, 4 <= i < 8 -> aview SEGS (w_H W5) (ms_mem msV) (SB + F / 8 + i) = Some 0).
  { lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_region_nth Ex ssx msx 2 _ HS eq_refl) as HR end.
    cbn [ms_mem restrict] in HR.
    intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]]; (apply aview_of_val_mem1; [|lia]);
    (eapply field_of_region with (w := 1%N) (e := SLit 0) (v := 0); [exact HR | rewrite E65, unsigned_lit_small by (unfold SB; lia); reflexivity
      | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia ]). }
  (* the block: live in S5, made in this call (apart from every block of S), below the stack and apart from the frame *)
  assert (Hin5 : In (p, n) (ablocks B ly5 S5)) by (eapply Permutation_in; [apply Permutation_sym; exact Hpperm | left; reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR8 Hin5) as (_ & Hp4k & Hpceil & Hpapp & Hpown & _ & Hn0).
  pose proof (req_size_pos _ (proj1 Hn0)) as [_ Hrq].
  assert (Hnot0 : ~ In (p, n) (ablocks B ly S)).
  { intros Hq. rewrite <- Eab in Hq. pose proof (proj1 (Forall_forall _ _) Hpapart _ Hq) as Hap.
    unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 1 fpos HAR8 Hin5 Hfin7) as Hsep.
  rewrite EF7 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 1) with 128 in Hsep.
  assert (Happ : p + req_size n <= SB \/ 0x10007fff8000 <= p)
    by (clear - Hpapp; unfold in_app in Hpapp; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SB in *; lia).
  (* 0x8a2bc: memcpy(block, buf, |resp code| + 1) (cgif's aintrin_realizes, at fx1) *)
  eapply SRr_bind.
  { eapply (aj_intrin_atS (fx := fx1) SEGS B LAWS Hsegs OCpy (SIG CS___asan_memcpy) (AMEMCPY fx1) _ (ms_regs msV) (ms_mem msV)
      SUP_RESP_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly5 S5 _ _ p (F + 32) n (sp1 - spZ regs) (getr (ms_regs msV) 1) HJ5).
    - exact Va0.
    - exact Va1.
    - exact Va2.
    - lia.
    - lia.
    - lia.
    - exact HspV.
    - exact Hal1.
    - lia.
    - rewrite Hes, FFS. lia.
    - exact V3'.
    - exact V4'.
    - reflexivity.
    - exact HraV.
    - intros a Ha. split; [|lia].
      right; right; left. exists p, n. split; [exact Hin5|]. split; [exact Hnot0 | lia].
    - intros a _ Hf. exfalso. exact (inFP_nil a Hf).
    - exact (amem_range_of_block SEGS B LAWS ly5 S5 W5 (ms_mem msV) _ p n p n HAR8 Hin5 ltac:(lia) ltac:(lia)).
    - exact (range_addressable_of_block SEGS B LAWS ly5 S5 W5 (ms_mem msV) _ p n p n HAR8 Hin5 ltac:(lia) ltac:(lia)).
    - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly5 S5 W5 (ms_mem msV) _ p n p n HAR8 Hin5 ltac:(lia) ltac:(lia) ltac:(lia)).
    - destruct (HBUF (rdW W5 (ms_mem msV)) n ltac:(lia) ZBV) as [Hamr Hra1].
      split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [|rewrite HspV; lia].
        destruct HSTR_V as [Hb _]. replace a with (F + 32 + Z.of_nat (Z.to_nat (a - (F + 32)))) by lia.
        rewrite Hb; [discriminate|]. rewrite length_app; cbn [length]. unfold n in Ha. lia. }
      split; [lia|]. split; [exact Hamr|]. split; [exact Hra1|]. intros _.
      exact (shadow_hull_vis_of_frame SEGS B LAWS ly5 S5 W5 (ms_mem msV) _ 1 fpos (F + 32) n HAR8 Hfin7
        ltac:(rewrite EF7; lia) ltac:(rewrite EF7; change (fs_frame_bytes 1) with 128; lia) ltac:(lia)). }
  cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Ha06 & Heff & Hfr6 & Hpres6' & HSM6).
  cbv iota in Heff.
  (* back at 0x8a2c0: memcpy wrote only the block and its window below sp1 *)
  pose proof HJ6 as (HAR9 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres9 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR9 Hfin7) as (_ & _ & HFpres9 & HFSpres9).
  rewrite EF7 in HFpres9, HFSpres9. change (fs_frame_bytes 1) with 128 in HFpres9, HFSpres9.
  unfold shadow_addr in HFSpres9. rewrite <- SB_SHADOW_OFF in HFSpres9. change (128 / 8) with 16 in HFSpres9.
  jafter_call_keep_pi HS 114%nat regs6 (mrestrict (w_H W5) mem6) HP6 [0; 1; 2; 3; 4]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
     rewrite ?E40, ?E52, ?E65, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by (unfold SB; lia); intros a Ha;
     [ apply (mbyte_of_aview SEGS); apply Hfr6; unfold ESTACK, SB in *; lia
     | intros _; apply (apresent_writable SEGS);
       first [ apply Hpres9; rewrite FFS; lia
             | apply (proj1 (HFpres9 a ltac:(lia)))
             | let Hp := fresh "Hp" in
               pose proof (proj1 (HFSpres9 (a - (SB + F / 8)) ltac:(lia))) as Hp;
               replace (SB + F / 8 + (a - (SB + F / 8))) with a in Hp by lia; exact Hp
             | lia ] ]). }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  hei_havoc HS. rebaseE HS AG HEv. clear HEv.
  (* the flag byte FL (atom 64) is a region of its own: present, owned by the allocator, so outside the frame and its
     shadow, and below the stack *)
  destruct (FFL ly5 S5 W5 mem6 md6 1 fpos HAR9 Hfin7) as (HFLpres9 & HFLown9 & _).
  rewrite EFL7 in HFLpres9, HFLown9.
  assert (HnoF : FL < F \/ F + 128 <= FL).
  { destruct (Z_lt_ge_dec FL F) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_lt_ge_dec FL (F + 128)) as [Hh|Hh]; [exfalso | right; lia].
    exact (proj2 (HFpres9 FL ltac:(lia)) HFLown9). }
  assert (HnoS : FL < SB + F / 8 \/ SB + F / 8 + 16 <= FL).
  { destruct (Z_lt_ge_dec FL (SB + F / 8)) as [Hl|Hl]; [left; exact Hl|].
    destruct (Z_lt_ge_dec FL (SB + F / 8 + 16)) as [Hh|Hh]; [exfalso | right; lia].
    pose proof (proj2 (HFSpres9 (FL - (SB + F / 8)) ltac:(lia))) as Hn'.
    replace (SB + F / 8 + (FL - (SB + F / 8))) with FL in Hn' by lia. exact (Hn' HFLown9). }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 64%nat) 0 1 0 1 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite E64, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLpres9)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?E64, ?E52, ?E65, ?E40; evalE AG;
      clear - HnoF HnoS HFLceil HFL4096 Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil; unfold SB in *;
      repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  norm_ssp HS.
  (* 0x8a2c0 .. 0x8a394: buf's shadow f8 (use after scope), the frame's magic := retired, `beqz s2` falls through
     (F <> 0), the frame's shadow f5 (16 bytes), the flag byte := 0 (the frame is released), `j`, a0 := the block,
     the epilogue, up to `ret` *)
  rewrite V1.
  paj_run_flag_sh RUNF1 HS HJ6.
  - lia.
  - let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros a (r & Hin & Hr);
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E64, ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
        first [ exfalso; clear - Hr; lia
              | right; rewrite EFL7; lia
              | left; left; rewrite FFS; lia
              | left; right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; rewrite EF7;
                first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
                      | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16;
                        unfold SB in *; lia ] ] | ]);
    destruct Hin.
  - let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
    intros msr HSr; rewrite EFL7;
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
    (* the copy's bytes are in no write window of the run: the block is apart from the frame, owned by no one (the
       flag byte is the allocator's), an application address (not shadow) and below the stack *)
    assert (HpF : forall a, p <= a < p + n -> rdW W5 (ms_mem msF) a = rdW W5 mem6 a).
    { intros a Ha.
      assert (HaFL : a <> FL) by (intros Heq; rewrite Heq in Ha; exact (proj2 (Hpown FL ltac:(lia)) HFLown9)).
      apply RecBLemmas.recb_run_keeps_m with (1 := HFrF); [lia|].
      let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros (r & Hin & Hr);
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG;
          rewrite ?E64, ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
          unfold SB in *; lia | ]);
      destruct Hin. }
    (* 0x8a394: ret *)
    prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
    eapply (RET1 W5 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_baseF.
    lazymatch goal with |- exists _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists fx1, ly5, (stack_free_state 1 fpos S5), r, m, d end.
    split; [rewrite F1, (AG 1%nat), E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [intros k _; reflexivity|].
    split; [left; reflexivity|].
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ6|].
    split.
    { eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sr_extra (as_uar_cell B)) HS).
      - split; [intros n0 Hn0'; rewrite (AG n0 Hn0'); exact (proj1 HAE n0 Hn0') | rewrite AD; exact (proj2 HAE)].
      - vm_compute; reflexivity. }
    (* the post *)
    pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2f & F3f & _).
    assert (EabF : ablocks B ly5 (stack_free_state 1 fpos S5) = ablocks B ly5 S5)
      by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
    assert (HSYMS : asyms_ok B) by exact (am_syms _ _ _ _ (proj1 HAR)).
    assert (FSP : forall a, fp_spares [] a) by (intros a; apply fp_spares_closed; [apply sink_closed_pos; apply Forall_nil | apply inFP_nil]).
    rewrite Eab in Hpperm, Hpapart.
    unfold QP. exists p. cbv zeta. fold n.
    split; [rewrite F10, E102; exact Hp10|].
    split; [exact Hp4096|].
    split; [rewrite EabF; exact Hpperm|].
    split; [exact Hpapart|].
    split; [rewrite EabF; exact Hin5|].
    split.
    { destruct HSTR_V as [Hb Hnz]. split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      rewrite HpF by (unfold n; lia). rewrite (Heff (Z.of_nat i) ltac:(unfold n; lia)).
      exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)). }
    split.
    { intros R O HR. cbn [fst sup_resp_m].
      apply (rec_repA_kept B ly S ly5 (stack_free_state 1 fpos S5) _ _ R O HR).
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
      - intros q k a Hq Ha.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hq) as (_ & _ & _ & _ & _ & _ & Hn0q).
        pose proof (req_size_pos _ (proj1 Hn0q)) as [_ Hrqq].
        replace a with (q + (a - q)) by lia.
        apply (F2f q k (a - q)); [exact Hq | rewrite EabF; eapply Permutation_in; [apply Permutation_sym; exact Hpperm | right; exact Hq] | lia | exact (inFP_nil _)]. }
    split; [change (blocks_bytes (stack_free_state 1 fpos S5)) with (blocks_bytes S5); unfold LIVE_SUP_RESP; fold n; rewrite HLX; lia|].
    unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). rewrite ES2 in MLE5. exact (mo_le_set_fs_l MT MTFL _ _ _ _ MLE5). }
(* 0x8a298: the snprintf wrapper writes "resp <code>" and its terminator into buf (RtPFCmd.v's asnprintf_sh at FR_cmd)
   and returns at some FP state fx1 *)
destruct HGUARD3 as [HG1 [cval HG2]].
pose proof (ecall_pre_stk_at SEGS B CMD_SNP_K SUP_RESP_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly S2 W (ms_mem ms1) _ 0
  (ms_regs ms1) (sp1 - spZ regs) HJ2 HspT Hal1 ltac:(lia) ltac:(unfold CMD_SNP_K; lia) ltac:(rewrite FFS; unfold CMD_SNP_K; lia) HraT P3' P4')
  as (HPS1 & HPS2 & HPS3).
pose proof (frm_off_imgP B ly S2 W (ms_mem ms1) _ 1 fpos HAR3 Hfin2) as HOI.
unfold off_img in HOI. change (fs_frame_bytes 1) with 128 in HOI. fold F in HOI.
assert (HCK : CMD_SNP_K = 8192) by reflexivity.
(* where the destination, the window and the read-only words lie: the frame below the stack, off the image *)
assert (HLOC : (F + 128 <= 0x10000 \/ 0x606000 <= F) /\ F + 128 <= sp1 - 8192 /\ 0x606000 <= sp1 - 8192 /\ sp1 + 8 <= 2 ^ 47)
  by (split; [exact HOI|]; lia).
change (RO_lit_21d40) with (map (Z_to_bv 8) (RA.RESP_FMT ++ [0])) in HLIT.
(* the kit's printf step (PASS4-REFIT.md section E): the shared post as art_postF (srr_art_postF_of_pf), the journal
   step for a destination in sup_resp's own side-stack frame (aj_art_own_atF), and the rest of the walk at the FP
   state fx1 the wrapper returns at (srr_after_artF, CONT) *)
eapply (srr_after_artF (fx := fx) SEGS W _ (getr (ms_regs ms1) 1)).
{ eapply (aj_art_own_atF (fx := fx) SEGS B LAWS Hsegs CMD_SNP_K (fun a => F + 32 <= a < F + 32 + sn_len (32 - 1) T)
    (SIG CS___interceptor_trampoline_snprintf) W (ms_regs ms1) (ms_mem ms1) SUP_RESP_STK (spZ regs) [] ly S W mem md
    [(1, fpos)] ly S2 _ 0 (sp1 - spZ regs) (getr (ms_regs ms1) 1) _ HJ2 HspT Hal1 ltac:(lia) ltac:(unfold CMD_SNP_K; lia)
    ltac:(rewrite FFS; unfold CMD_SNP_K; lia) eq_refl).
  { intros a Ha. right; right; right; left. exists 1, fpos. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. rewrite HSNW in Ha. lia. }
  apply (srr_art_postF_of_pf (fx := fx) SEGS B CMD_SNP_K ly S2 W (ms_regs ms1) (ms_mem ms1) _ _ (F + 32)
    (sn_len (32 - 1) T) (sn_bytes (32 - 1) T) (Z.of_nat (length T))).
  { intros a Ha. apply HPS3. unfold ascratch_stk. exact Ha. }
  apply (ASNPRINTF fx ly S2 W (ms_regs ms1) (ms_mem ms1) _ (F + 32) 32 0x21d40 [] (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) T cval).
  - exact HPS1.
  - exact HPS2.
  - intros a Ha. apply HPS3. unfold ascratch_stk. exact Ha.
  - exact P10'.
  - exact P11.
  - exact P12'.
  - exact (cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI W (ms_mem ms1) HROD3).
  - unfold CMD_SNP_CR. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
  - rewrite HSNW, HCK, HspT. unfold CMD_SNP_CR, snp_out.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; clear - HLOC HLT; lia.
  - exact HG1.
  - exact HG2.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite HSNW, HCK, HspT. unfold snp_out. repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; clear - HLOC HLT; lia.
  - rewrite HSNW, HCK, HspT. unfold snp_out. repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; clear - HLOC HLT; lia.
  - split; [reflexivity | intros i Hi; cbn in Hi; lia].
  - cbn [length]. rewrite HspT. clear - HLOC HLT; lia.
  - rewrite HSNW, HCK, HspT. cbn [length]. unfold snp_out.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; clear - HLOC HLT; lia.
  - apply (FR_cmd_intro _ _ _ _ _ RA.RESP_FMT RA.RESP_PS [PF.AInt code]).
    + split; [lia|]. split.
      { intros i Hi. apply (sr_lit_bytes _ _ (RA.RESP_FMT ++ [0]));
          [unfold RA.RESP_FMT; repeat apply Forall_cons; try apply Forall_nil; lia | exact HLIT | cbn in Hi |- *; lia]. }
      split; [change (Z.of_nat (length RA.RESP_FMT) + 1) with 8; rewrite HSNW, HCK, HspT; unfold snp_out;
        repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; clear - HLOC HLT; lia|].
      split; [unfold amem_range; left; unfold kLowMemEnd; cbn; lia|].
      split; [exact (sr_lit_addr _ _ W _ _ HAR3) | exact (sr_lit_hull _ _ W _ _ HAR3)].
    + exact sr_fmt_parse.
    + cbn [map arg_of pf_args_asan app]. split; [|exact I]. cbn [pf_arg_asan]. split; [exact Hcode|].
      unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite P13'. unfold w64. apply RA.lit_mod32.
    + exact (sr_fmt_text code).
    + exact I.
    + vm_compute; reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite HSNW. lia.
  - rewrite HSNW, HCK, HspT. unfold snp_out. cbn [pairwise].
    split; [repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; clear - HLOC HLT; lia|].
    split; [apply Forall_nil | exact I].
  - rewrite HSNW. intros a Ha. destruct (HFpres3 a ltac:(lia)) as [Hp Hno].
    split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite HspT. lia.
  - exact (amem_range_sub_app F 128 (F + 32) (sn_len (32 - 1) T + 8) HFhigh HFceil ltac:(lia)
      ltac:(rewrite HSNW; lia) ltac:(rewrite HSNW; lia)).
  - rewrite HSNW. exact (proj2 (HBUF _ (Z.of_nat (length T) + 1) ltac:(lia) ZB)).
  - rewrite HSNW. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W (ms_mem ms1) _ 1 fpos (F + 32) (Z.of_nat (length T) + 1) HAR3 Hfin2
      ltac:(fold F; lia) ltac:(change (fs_frame_bytes 1) with 128; fold F; lia) ltac:(lia)).
  - rewrite HSNW. unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. clear - HLOC HLT; lia.
  - exact HFRM. }
cbv beta. intros fx1 regs3 mem3 md3 Hfx (HJ3 & HP3 & (HQa & HQb) & HK3).
apply (CONT fx1 regs3 mem3 md3 HJ3 HP3 HQb).
intros a Ha Hw Hb. apply HK3; [exact Ha | lia | exact Hb].
Qed.
End e.
End f.
End d.
About tsup_resp_spec_holds.
Print Assumptions tsup_resp_spec_holds.
