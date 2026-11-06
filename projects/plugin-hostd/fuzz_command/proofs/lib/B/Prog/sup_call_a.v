(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the entry segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0 ..
   0x8a61c), in the form of sup_resp's walk (cgif lib/A/AChf.v, flushFrame): the prologue, the realignment
   `andi sp,sp,-32`, the use-after-return flag (1: `beqz a2` falls through), the class-7 side-stack frame of
   __asan_stack_malloc_7 (not 0: `bnez s2` skips the real-stack fallback), the frame's header and shadow, the two
   shadow fills, up to the BODY cut (answer_s1.v AN_BODY_stmt). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_e.v, with its module paths, module names and numbers changed; 171 of its 370 lines of code are new or changed and 396 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan, entry 0x8af34),
   part a, 0x8af34 .. 0x8b030 (sup_call_s3.v): the 96-byte frame (the probe store, the 11 saves, s0 := sp0, the
   realignment sp1 := (sp0 - 96) & -32), the use-after-return flag (1, the allocator record's constant cell), so
   `beqz a2` at 0x8af94 falls through to frame_alloc_0 (class 0, 64 bytes, 0x8af9c); its frame F is not 0, so
   `bnez s2` at 0x8afb0 skips the real-stack fallback; sp1's slot := F, the frame header (magic, description, pc) and
   its 8 shadow bytes (f1 f1 f1 f1 f8 f8 f3 f3). The walk ends in sup_call_s3.v's `sc_at_a` and the statement of the
   rest (SC_A_stmt) takes over.

   The form is A's sup_resp walk (an earlier version of lib/A/Prog/sup_resp.v, lines 128-445) over
   B's kit (pass 5: aj_stack_malloc_atS keeps the layout and the world). The walk carries its journal with the empty
   footprint, so that the journal itself shows that g_rec, record.spill, the recorder's blocks and the line keep
   their bytes, and widens it to sup_call's footprint (PaCallPg.v ajournal_fp_widen) at 0x8b030. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRest CmdRecImg RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_call_s3 sup_call_s0 sup_call_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the walk makes no inline check, so its shadow entry list stays empty; restate it over the current env *)
Ltac sca_resh HS :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
assert (SH : sh_ok sg SC_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (unfold sh_ok; apply Forall_nil) end.
(* after each symbolic run the model is left as `with_vm_backing (m_vm_lazy md) mat md`; make it opaque at once *)
Ltac collapse_md :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdl) _ =>
first [ is_var mdl | let mdv := fresh "mdv" in set (mdv := mdl) in *; clearbody mdv ] end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a saved register read back out of the walk's frame region (base s0's entry value sp0) *)
Lemma sca_saved : forall E m n0 cs lo hi wlo whi sp0 od k (regs0 : bvmap 5 word) (r : bv 5) a,
  region_ok SEGS E m (YP09.mkRegion (Some n0) lo hi wlo whi cs) ->
  bv_unsigned (ew E n0) = sp0 -> In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs ->
  ew E k = getr regs0 r -> a = sp0 + od ->
  val_mem SEGS m a 8 (bv_unsigned (getr regs0 r)).
Proof.
intros E m n0 cs lo hi wlo whi sp0 od k regs0 r a HR Hn Hin Hk ->.
exact (field_of_region E m n0 sp0 cs lo hi wlo whi od 8%N (SOff k 0) (bv_unsigned (getr regs0 r)) HR Hn Hin
  ltac:(cbn [sv_denot]; rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as HX; change (bv_modulus 64) with (2 ^ 64) in HX; cbn; lia)
  ltac:(cbn; lia)).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypothesis this part uses (sup_call_c.v:87-93), word for word *)
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run (PL := PL_cmd) (PI := PI) B LAWS. Let RUNTO := paj_run_to (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (PL := PL_cmd) (PI := PI) B LAWS.
Let errno_low := pal_env B TL.

Lemma sc_stage_a : @SC_A_stmt fx rc SK PI B MT -> @SC_main_stmt fx rc SK PI B MT.
Proof.
intros HAS. unfold SC_main_stmt.
intros ly S W regs mem md ch id pl line R O HFRM HPRE0.
pose proof HPRE0 as (HPRE & Hfr7 & HROD & HRO & H10 & Hid & H11 & Hpl & HLINE & HREP & Hev & Hlive & HMOK).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : SUP_CALL_STK = ltac:(let v := eval vm_compute in SUP_CALL_STK in exact v)) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (sc_entry B LAWS TL TLF W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_CALL_STK [] ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (sc_extra (as_uar_cell B)))) as E eqn:HE.
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
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar.
clear HE.
assert (SHOK : sh_ok SEGS SC_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (AD : ed E = ed E) by reflexivity.
unfold cfg_at. change (w64 (BASE + AF_sup_call)) with (Z_to_bv 64 (BASE + AF_sup_call)).
(* 0x8af34 .. 0x8af6c: the 96-byte frame (the probe store at sp0 - 96), the saves, s0 := sp0, sp := (sp0 - 96) & -32 *)
paj_run_to_tok RUNTO HS HJ SHOK SC_Bspan (AF_sup_call + 0x3c).
{ awr_ok_tac. exact Usp. }
clear_frames. collapse_md.
(* the realigned stack pointer sp1 becomes atom 40; the frame keeps the saves [sp0 - 88, sp0), and sp1's own slot
   [sp1, sp1 + 8) (s8's spill at 0x8afd0) is a region of its own *)
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (snt_sp1_facts (spZ regs + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia. clear Hsp1r.
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
  (snt_denot_and_m32 E 2 (spZ regs) (-96) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2.
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
let rs' := eval vm_compute in (trim_stack rs (-88) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
assert (VO : forall Ev n, img_env VAL A_LIM Ev -> (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew Ev n) = VAL n)
  by (intros Ev n HEv Hn; exact (HEv n Hn)).
change (A_OBJ 0) with 241%nat in Hob0. change (A_OBJ 1) with 242%nat in Hob1. change (A_OBJ 12) with 253%nat in Hob12.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HEv := rnHEI Ev in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 40%nat) 0 8 0 8 []) HS eq_refl
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
(* 0x8af70 .. 0x8af9c: s1 := sp1, s3 := line, the shadow base (s7) and the use-after-return flag (1, the record's
   constant cell), s4 := id, the flag test falls through, a0 := 64, the call of frame_alloc_0 *)
sca_resh HS.
paj_run_tok RUN HS HJ SHOK SC_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E' ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb E' rs' stk sp0 fp b0 bc fr ly own) end.
  eapply awr_ok_cons_stack_off with (n := 40%nat) (d := sp1 - spZ regs);
    [reflexivity | rewrite E40, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | rewrite (AG 2%nat) by lia; exact Usp | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
pmkst HS. collapse_md.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* the call of frame_alloc_0 (class 0, a 64-byte frame) *)
pose proof (palf_sm B TLF 0 ltac:(cbn; tauto)) as HSM0. change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in HSM0.
rewrite HSM0.
pose proof (count_cid_le_length 0 (frames S)) as Hcnt.
assert (HFS0 : 8 <= fs_frames 0) by (vm_compute; intros Hx; discriminate Hx).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 (ASTACK_MALLOC0 fx) ltac:(lia) W (ms_regs msX) (ms_mem msX)
    SUP_CALL_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2, E40, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes; lia.
  - rewrite R3, (AG 3%nat), E3 by lia. exact Hgp.
  - rewrite R4, (AG 4%nat), E4 by lia. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta. clear R1 R2 R3 R4.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
rewrite Hes in HK.
(* back at 0x8afa0: the frame region keeps sp1's slot and the saves (both at or above sp1) *)
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
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
rewrite Ha0 in E52. unfold w64 in E52.
(* the frame F (atom 52), its flag address FL (atom 64) and its shadow SB + F / 8 (atom 65), as sup_resp: the 24
   header bytes, the flag word at F + 56, and the 8 shadow bytes (written, not read, by this part) *)
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
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 65 0 0 8 []) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    try change (fs_frame_bytes 0 / 8) with 8; rewrite E65, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
      apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; lia)))
    | apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    try change (fs_frame_bytes 0 / 8) with 8; rewrite E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi; unfold SB; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 52%nat) 0 24 0 24 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    rewrite E52, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    try change (fs_frame_bytes 0 / 8) with 8; rewrite E52, E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFhigh HFq HF8; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 52%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 64 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    rewrite E52, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 56 8 _ FL);
    [cbn [sv_denot]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    try change (fs_frame_bytes 0 / 8) with 8; rewrite E52, E65, E40; evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFhigh HFq HF8; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ssp HS.
clear SHOK.
(* 0x8afa0 .. 0x8b02c: s2 = s8 := F (not 0: `bnez s2` skips the real-stack fallback), sp1's slot := F, s5 := F + 32,
   s7 := F's shadow, the frame header (magic, description, pc), the shadow f8 f8 f3 f3 at +4 .. +7 and f1 f1 f1 f1
   at +0 .. +3, up to 0x8b030 *)
paj_run_to_sh RUNTOP HS HJ2 (AF_sup_call + SC_PC_A).
{ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; rewrite ?E52, ?E65, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      first [ exfalso; clear - Hr; lia
            | left; rewrite FFS; lia
            | right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8;
                      fold F; unfold SB in *; lia ] ] | ]);
  destruct Hin. }
pmkst HS. collapse_md.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx _ => rename Ex into Ef end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msf end.
(* the state at 0x8b030: the registers sup_call_s3.v's sc_regs names *)
assert (G : forall k, (k < 32)%nat -> forall r : bv 5, Z.of_nat k = bv_unsigned r -> ew Ef k = getr regs r)
  by (intros k Hk r Hr; rewrite (AG k Hk); exact (EE k r Hr)).
prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (18%bv : bv 5) P18. prreg HS (24%bv : bv 5) P24.
prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (25%bv : bv 5) P25. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
assert (P23 : getr (ms_regs msf) 23 = w64 (SB + F / 8)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?H ?msx) =>
  pose proof (st_ok_pi_restrict_reg H Ex ssx msx (23%bv : bv 5) HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssx) (23%bv : bv 5)) in
  change (sr_get (ss_regs ssx) (23%bv : bv 5)) with e in Hr end.
  cbn [ms_regs restrict mkst] in Hr. rewrite Hr.
  cbn [sv_denot]. rewrite E65, unsigned_lit_small by (unfold SB; lia). rewrite Z.add_0_r. reflexivity. }
assert (HRG : sc_regs regs (ms_regs msf) F).
{ unfold sc_regs.
  split; [unfold spZ at 1; rewrite P2, E40, unsigned_lit_small by lia; unfold sc_sp1, sp1; f_equal; f_equal; lia|].
  split; [rewrite P8; apply G; [lia | reflexivity]|].
  split; [rewrite P18, E52; reflexivity|]. split; [rewrite P24, E52; reflexivity|].
  split; [rewrite P19; apply G; [lia | reflexivity]|]. split; [rewrite P20; apply G; [lia | reflexivity]|].
  split; [rewrite P21, E52, unsigned_lit_small by lia; reflexivity|].
  split; [exact P23|]. split; [rewrite P25; unfold w64; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]|].
  split; [rewrite P3; apply G; [lia | reflexivity]|]. split; [rewrite P4; apply G; [lia | reflexivity]|].
  split; [rewrite P26; apply G; [lia | reflexivity]|]. rewrite P27; apply G; [lia | reflexivity]. }
(* the saves: the frame region at s0's entry value sp0 holds the entry's ra, s0 .. s9 *)
assert (HFR : sc_frame (rdW W (ms_mem msf)) (spZ regs) regs).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (ss_mem ssx) in
    let i := idx_of_base rs 2%nat in
    pose proof (st_ok_pi_region_nth Ex ssx msx i _ HS eq_refl) as HRS end.
  cbn [ms_mem restrict] in HRS.
  intros j r Hj. apply aval_mem_view. unfold sc_saved in Hj.
  do 11 (destruct j as [|j]; [cbn [nth_error] in Hj; injection Hj as <-;
    lazymatch goal with |- val_mem _ _ (_ - 8 - 8 * Z.of_nat ?jj) _ _ =>
      let od := eval vm_compute in (-8 - 8 * Z.of_nat jj) in
      eapply (sca_saved _ _ 2%nat _ _ _ _ _ (spZ regs) od _ regs _ _ HRS) end;
    [ rewrite (AG 2%nat) by lia; exact Usp
    | cbn [In]; repeat (first [left; reflexivity | right])
    | apply G; [lia | reflexivity]
    | lia ] |]).
  cbn [nth_error] in Hj. destruct j; cbn in Hj; discriminate Hj. }
(* the flag-byte word at F + 56 *)
assert (HFLW : rdword (rdW W (ms_mem msf)) (F + 56) = Some FL).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (st_ok_pi_region_nth Ex ssx msx 0 _ HS eq_refl) as HRF end.
  cbn [ms_mem restrict] in HRF.
  apply (rdword_of_val_mem SEGS); [|lia].
  exact (field_of_region _ _ 52%nat F _ _ _ _ _ 56 8%N (SOff 64 0) FL HRF
    ltac:(rewrite E52, unsigned_lit_small by lia; reflexivity) ltac:(cbn [In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
(* the journal's kept bytes (its footprint is empty): the entry's blocks, and the program's statics *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KF2 & KF3 & _).
assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> rdW W (ms_mem msf) (p + i) = rdW W mem (p + i)).
{ intros p n i Hin Hi. apply (KF2 p n i Hin); [rewrite Eab; exact Hin | exact Hi | apply inFP_nil]. }
assert (KG : forall a, inFP cmd_PG a -> rdW W (ms_mem msf) a = rdW W mem a).
{ intros a Ha. destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Ha) as (H1 & H2 & H3).
  apply (KF3 a H1 H2 H3). apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | apply inFP_nil]. }
assert (HOL : forall pn, In pn O -> In pn (ablocks B ly S)).
{ destruct HREP as (Q & HA & HO). intros pn Hpn. exact (lay_blocks_in _ (rdW W mem) _ _ R Q HA pn (proj1 (HO pn) Hpn)). }
assert (HREP3 : rec_repA B ly S2 (rdW W (ms_mem msf)) R O).
{ apply (rec_repA_kept B ly S (rdW W mem) ly S2 (rdW W (ms_mem msf)) R O HREP).
  - intros pn Hpn. rewrite Eab. exact (HOL pn Hpn).
  - intros a [Ha | [Ha | Ha]].
    + apply KG. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
    + apply KG. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
    + destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hpn & Hr).
      replace a with (p + (a - p)) by lia. apply (KB p n (a - p) (HOL _ Hpn)). lia. }
assert (HSTR3 : astr_atR (rdW W (ms_mem msf)) pl line).
{ destruct HLINE as ((p & k & Hpk & Hp1 & Hp2) & _ & HSTR & _).
  apply (astr_atR_kept_r (rdW W mem)); [|exact HSTR].
  intros x Hx. replace x with (p + (x - p)) by lia. apply (KB p k (x - p) Hpk).
  unfold req_size. destruct (Z.eqb_spec k 0); lia. }
assert (HMO : mo_le MT S S2 0) by (rewrite ES2; apply (mo_le_set_fs_r MT MTFL); apply (mo_le_refl MT MTL)).
(* the journal widened to sup_call's footprint: no byte of it is 0 *)
assert (HNO : ~ YI16.sink_open_fp (SC_FP O)).
{ intros Ho. destruct (sc_fp_cases O 0 Ho) as [Hp | (p & n & Hpn & Hr)].
  - apply Exists_exists in Hp as (r & Hr & Har). unfold TFIB_PROG_STATIC in Hr. unfold in_zr in Har.
    destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Har; lia.
  - pose proof (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOL _ Hpn)) as (_ & Hp4 & _). lia. }
pose proof (ajournal_fp_widen SEGS B _ _ _ (SC_FP O) _ _ _ _ _ _ _ _ _ _ _ _ HJ2 (fun a Ha => False_ind _ (inFP_nil a Ha)) HNO) as HJW.
replace (BASE + 19200) with (BASE + AF_sup_call + SC_PC_A) by (unfold AF_sup_call, SC_PC_A; lia).
eapply (HAS ly S W regs mem md ch id pl line R O fpos F FL ly S2 W); [exact HFRM | exact HPRE0 |].
exact (conj (conj HJW (conj eq_refl (conj eq_refl (conj HRG (conj HFR HFLW))))) (conj Eab (conj Hbb2 (conj HMO (conj HREP3 HSTR3))))).
Qed.
End e.
End f.
End w.
