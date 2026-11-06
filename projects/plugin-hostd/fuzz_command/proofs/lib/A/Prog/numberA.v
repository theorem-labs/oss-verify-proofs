(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v (a walk) and ACa2.v (a class-1 side-stack frame): tnumber_spec of lib/A/Prog/number_c.v, from number's entry (0x8e430) through __asan_stack_malloc_0 and strtol to strtol's return, then numberB.v's n_segB. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c number.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import number_c numberE numberK PaArt numberR numberB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecCells CmdRecImg CmdRecRest.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the shadow byte of an address of an 8-aligned range is in the range's shadow, and outside it when the address
   is outside *)
Lemma n_div8_in : forall x lo n, lo mod 8 = 0 -> n mod 8 = 0 -> lo <= x < lo + n -> lo / 8 <= x / 8 < lo / 8 + n / 8.
Proof. intros x lo n H1 H2 H3. Z.div_mod_to_equations. lia. Qed.
Lemma n_div8_out : forall x lo n, lo mod 8 = 0 -> n mod 8 = 0 -> ~ (lo <= x < lo + n) -> ~ (lo / 8 <= x / 8 < lo / 8 + n / 8).
Proof. intros x lo n H1 H2 H3 H4. apply H3. Z.div_mod_to_equations. lia. Qed.
Lemma n_m32 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.
Lemma n_m64 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.
Lemma n_m4096 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.
Lemma n_div8_bound : forall x, 0 <= x < 2 ^ 47 -> 0 <= x / 8 < 2 ^ 44.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.
(* the 8-byte hull of the shadow of [F + 32, F + 40) for a 64-aligned frame F is the frame's 8 shadow bytes *)
Lemma n_hull8 : forall F s, F mod 64 = 0 -> 0 <= F ->
shadow_addr (F + 32) / 8 * 8 <= s < shadow_addr (F + 32 + 8 - 1) / 8 * 8 + 8 -> SB + F / 8 <= s < SB + F / 8 + 8.
Proof. intros F s H0 H1 H. unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. unfold SB in *. Z.div_mod_to_equations. lia. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis STRTOL : forall fx0 : YK11.FPState, @RtNumber.astrtol_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strtol) 0xa7098 0x6045d8.
(* the record hypotheses; IMG is the image facts over the walk's abstract SEGS, which the pinned
   image gives (CmdRecImg.v cmd_img_facts_tfib) *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
(* LAWS and ML are base lemmas: the core's AR_laws_ok, and CmdRecRest's cmd_model_laws (the allocator model's laws at the record's
   universe, over the core's ts_universe). The two record facts this walk uses are base lemmas over
   `SEGS B LAWS HB` (CmdRecFacts.v): CmdRecCells.cmd_rec_cells (also over IMG), the stack-protector cells and
   the errno cell strtol's musl body reads, and CmdRecImg.cmd_heap_tail_vis, the tail of a heap string's last 8-byte
   word, which the strtol wrapper's loop reads *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let ML : model_laws (as_universe B) := CmdRecRest.cmd_model_laws B HB.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Theorem number_walk : tnumber_spec B MT.
Proof.
unfold tnumber_spec.
intros ly S W regs mem md ch w out wd HPRE HROD H10 Hw64 H11 Ho64 HBLK HWS HWL Hout4 HOUT Hapart Hfr6 HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (LT : ly_stk_lo ly mod 4096 = 0 /\ ly_stk_hi ly mod 4096 = 0 /\ kHighMemBeg <= ly_stk_lo ly).
{ pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & L1 & L2 & L3).
  unfold page_aligned in L1, L2. exact (conj L1 (conj L2 L3)). }
destruct LT as (Llo & Lhi & Lhm).
assert (FFS : NUMBER_STK = 12400) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 errno_low) as [HEN0 HEN1]. pose proof (proj1 (proj2 errno_low)) as HENimg.
(* the word: a C string in a live block *)
destruct HBLK as (pb & kb & Hpbin & Hpb1 & Hpb2).
destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hpbin) as (Hpb16 & Hpb4096 & Hpbceil & Hpbapp & Hpbpres & _).
set (len := Z.of_nat (length wd)) in *.
assert (Hlen0 : 0 <= len) by (subst len; lia).
pose proof (req_size_pos0 kb ltac:(lia)) as [Hkb0 Hkbr].
(* the result cell: inside a caller's side-stack frame, or on the caller's real stack *)
assert (HOUTL : (exists cid pos, In (cid, pos) (frames S) /\
   frame_addr ly cid pos <= out /\ out + 4 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
 (spZ regs <= out /\ out + 4 <= ly_top ly)) by (destruct HOUT as [(Hf & _) | (Hs1 & Hs2 & _)]; [left; exact Hf | right; exact (conj Hs1 Hs2)]).
assert (HOUTR : 4096 <= out /\ out + 4 <= 2 ^ 47 /\ (out + 4 <= kLowShadowBeg \/ kHighMemBeg <= out) /\
  (out + 4 <= alloc_ceiling \/ spZ regs <= out)).
{ destruct HOUTL as [(ocid & opos & Hoin & Hoa & Hob) | (Hos & Hot)].
- destruct (frames_bounds SEGS B LAWS ly S W mem md ocid opos HAR Hoin) as (Hf4 & Hfc & Hfa).
  unfold in_app in Hfa. lia.
- lia. }
destruct HOUTR as (Hout0 & Hout47 & Hosh & Hoc).
lazymatch type of Hosh with ?T => change (nam T) in Hosh end. lazymatch type of Hoc with ?T => change (nam T) in Hoc end.
assert (HOUTB : forall a, pb <= a < pb + req_size kb -> ~ (out <= a < out + 4)).
{ intros a Ha Hao. destruct HOUTL as [(ocid & opos & Hoin & Hoa & Hob) | (Hos & Hot)].
- pose proof (sep_block_frame SEGS B LAWS ly S W mem md pb kb ocid opos HAR Hpbin Hoin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia. }
assert (HOUTI : forall a, out <= a < out + 4 -> ~ in_img SEGS a).
{ intros a Ha Hi. destruct HOUTL as [(ocid & opos & Hoin & Hoa & Hob) | (Hos & Hot)].
- exact (frm_img SEGS B LAWS ly S W mem md ocid opos a HAR Hoin ltac:(lia) Hi).
- pose proof (Hsegs a Hi). lia. }
assert (HOP0 : forall a, out <= a < out + 4 -> apresent (w_H W) mem a).
{ intros a Ha. destruct HOUT as [((ocid & opos & Hoin & Hoa & Hob) & _) | (Hos & Hot & Hopr)].
- destruct (al_frames _ _ LAWS _ _ _ _ _ ocid opos HAR Hoin) as (_ & _ & Hfp & _). exact (proj1 (Hfp a ltac:(lia))).
- replace a with (out + (a - out)) by lia. apply Hopr. lia. }
assert (Hwr : 4096 <= w <= 2 ^ 47 - 1 /\ 4096 <= out <= 2 ^ 47 - 4) by lia.
pose proof (n_entry B LAWS TL TLF NUMBER_STK W ly S regs mem md ch w out HPRE ltac:(rewrite FFS; lia) H10 H11
  (proj1 Hwr) (proj2 Hwr) Hout4) as HS.
pose proof (ajournal_init SEGS B NUMBER_STK [(out, out + 4)] ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs (n_extra (spZ regs) (as_uar_cell B)))) in HS. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 (nsp1 (spZ regs))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
set (sp0 := spZ regs) in *.
destruct (nsp1_facts sp0 Hal16) as (Hs1al & Hs1).
(* lia's cost grows with every disjunction in the context: keep the disjunctive facts under the opaque nam *)
assert (Hs1b : sp0 - 112 <= nsp1 sp0 <= sp0 - 96) by lia.
lazymatch type of Hs1 with ?T => change (nam T) in Hs1 end.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (Usp1 : bv_unsigned (ew E 33) = nsp1 sp0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_number)) with (Z_to_bv 64 (BASE + AF_number)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ unfold ss_n0, n_regions0, n_stk_lo, n_stk_hi, n_stk_s1; cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (nsp1 sp0 - sp0)); [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the entry run writes its stack slots only *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 112 <= a < sp0) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Usp1 in Hrr; clear - Hrr Hs1b; lia |]);
  destruct Hin)) as UNa.
clear HF HFr. rename HG into HGa.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
pose proof (palf_sm B TLF 0 ltac:(clear; cbn; tauto)) as SM0e. change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in SM0e.
rewrite SM0e.
pose proof (count_cid_le_length 0 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 (SM0 fx) ltac:(lia) W (ms_regs msX) (ms_mem msX) NUMBER_STK sp0 [(out, out + 4)] ly S W mem md [] ly S _ 0 (nsp1 sp0 - sp0) _ HJ) end.
- (unfold spZ; rewrite R2, E33, unsigned_lit_small by lia; lia).
- (destruct Hs1 as [Hq|Hq]; rewrite Hq; [replace (sp0 - 96 - sp0) with (-96) by lia | replace (sp0 - 112 - sp0) with (-112) by lia]; reflexivity).
- (lia). - (rewrite FFS, Hes; lia).
- (rewrite R3, E3; exact Hgp). - (rewrite R4, E4; exact Htp).
- (exact R1). - (apply ret_ok_codeptr_v; [lia | reflexivity]).
- (change (fs_frames 0) with 16384; lia). }
cbv beta. clear R2 R3 R4 R1 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJc & (fS2 & ES2)).
pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & Kuar1 & Kgot1 & Kguar1).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & Kuar2 & Kgot2 & Kguar2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot1, Kgot2. rewrite (pal_cell B TL) in Kcell1, Kcell2. rewrite (palf_got_uar B TLF) in Kguar1, Kguar2.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E34 : ew E 34 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (palf_uar_img B TLF) as Huar.
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2;3;4;5;6]%nat HS2.
match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | rewrite FFS; lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | rewrite FFS; lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp1 | lia | rewrite FFS; lia | lia | lia | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
[exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kguar1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kguar2) | lia].
- apply (region_kept_val_at E _ _ 34 (as_uar_cell B) 4 1);
[rewrite E34; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar2) | lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
(* the frame of class 0 the call returned, its flag cell and its shadow *)
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
destruct (frame_al64 SEGS B ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFal32, HFapp, HFpres, HFSpres, HF4096, HFceil, HFimg, HF64, HFLpres, HFLown, HFLrng, Hz, Hflag.
set (Ev1 := YN3v.havoc E 1024 (map (getr regs2) CLOB)) in HS.
assert (AG1 : forall n, (n < 1024)%nat -> ew Ev1 n = ew E n) by (intros n Hn; subst Ev1; apply ew_havoc_old; exact Hn).
assert (E1028 : ew Ev1 1028 = Z_to_bv 64 F) by (subst Ev1; change 1028%nat with (1024 + 4)%nat; rewrite (ew_havoc_new E 1024 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map CLOB]; exact Ha0).
assert (HEI1 : img_env VAL A_LIM Ev1) by (subst Ev1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
pose proof (st_ok_pi_havoc_hi 1040 Ev1 _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS; rename HS3 into HS.
set (Ev2 := YN3v.havoc Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) in HS.
assert (AG2 : forall n, (n < 1024)%nat -> ew Ev2 n = ew E n) by (intros n Hn; subst Ev2; rewrite ew_havoc_old by lia; apply AG1; exact Hn).
assert (E2_1028 : ew Ev2 1028 = Z_to_bv 64 F) by (subst Ev2; rewrite ew_havoc_old by lia; exact E1028).
assert (E2_1040 : ew Ev2 1040 = Z_to_bv 64 FL) by (subst Ev2; exact (ew_havoc_new Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2_1041 : ew Ev2 1041 = Z_to_bv 64 (SB + F / 8)) by (subst Ev2; exact (ew_havoc_new Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env VAL A_LIM Ev2) by (subst Ev2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U2 : bv_unsigned (ew Ev2 2) = sp0) by (rewrite AG2 by lia; exact Usp).
assert (U33 : bv_unsigned (ew Ev2 33) = nsp1 sp0) by (rewrite AG2 by lia; exact Usp1).
assert (U32 : bv_unsigned (ew Ev2 32) = SB) by (rewrite AG2, E32 by lia; apply unsigned_lit_small; unfold SB; lia).
assert (U34 : bv_unsigned (ew Ev2 34) = as_uar_cell B) by (rewrite AG2, E34 by lia; apply unsigned_lit_small; lia).
assert (U1028 : bv_unsigned (ew Ev2 1028) = F) by (rewrite E2_1028; apply unsigned_lit_small; lia).
assert (U1040 : bv_unsigned (ew Ev2 1040) = FL) by (rewrite E2_1040; apply unsigned_lit_small; lia).
assert (U1041 : bv_unsigned (ew Ev2 1041) = SB + F / 8).
{ rewrite E2_1041; apply unsigned_lit_small. assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SB; lia. }
assert (UO0 : bv_unsigned (ew Ev2 241) = VAL (A_OBJ 0)) by exact (HEI2 (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (UO1 : bv_unsigned (ew Ev2 242) = VAL (A_OBJ 1)) by exact (HEI2 (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (UO12 : bv_unsigned (ew Ev2 253) = VAL (A_OBJ 12)) by exact (HEI2 (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
lazymatch type of Hsep with ?T => change (nam T) in Hsep end.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; rewrite HF64, Z.add_0_r in D; exact D).
assert (HF8d : F / 8 = 8 * (F / 64)) by (rewrite HFq at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : F / 8 * 8 = F) by lia.
assert (HF8m : (F / 8) mod 8 = 0) by (rewrite HF8d, Z.mul_comm; apply Z_mod_mult).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44) by lia.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 1028 (mkAF 4096 (2 ^ 47) 6) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1028; change (2 ^ 6) with 64; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1040 (mkAF 4096 (2 ^ 47) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1040; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1041 (mkAF (SB + 512) (SB + 2 ^ 44) 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1041; change (2 ^ 3) with 8;
split; [lia|]; split; [unfold SB; rewrite Zplus_mod, HF8m; reflexivity | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 1028 32 1041 F SB E2_1028 ltac:(lia)
ltac:(rewrite AG2 by lia; exact E32) E2_1041)) as HS3;
clear HS; rename HS3 into HS end.
nnorm HS.
assert (Hz8 : forall i, 0 <= i < 8 -> aview SEGS (w_H W) mem2 (SB + F / 8 + i) = Some 0).
{ intros i Hi. pose proof (Hz i Hi) as Q. unfold shadow_of_addr in Q. exact Q. }
assert (HFS8 : forall i, 0 <= i < 8 -> apresent (w_H W) mem2 (SB + F / 8 + i)).
{ intros i Hi. exact (proj1 (HFSpres i Hi)). }
pose proof (conj Hob0 (conj Hob1 (conj Hob12 (conj Huar (conj Hsep (conj HFimg (conj HF4096 (conj HFceil (conj HFapp
(conj Hceil (conj Hslo (conj Hshi (conj H47 (conj Hs1 (conj C1 (conj HF8b (conj HF8 FFS))))))))))))))))) as AM.
lazymatch type of AM with ?T => change (nam T) in AM end.
addreg HS (YP09.mkRegion (Some 1028%nat) 40 64 40 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ F 56 8 _ FL);
[cbn [sv_denot]; rewrite E2_1040, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ]).
addreg HS (YP09.mkRegion (Some 1028%nat) 32 40 32 40 [])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ]).
addreg HS (YP09.mkRegion (Some 1028%nat) 0 32 0 32 [])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ]).
addreg HS (YP09.mkRegion (Some 1041%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))])
ltac:(rewrite U1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (HFS8 o ltac:(lia))
| apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ (SB + F / 8) 0 8 _ 0);
[reflexivity | zside | zside | rewrite Z.add_0_r; apply val_mem_zero8; exact Hz8] ]).
assert (INF : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 -> in_frames ly [(0, fpos)] a).
{ intros a Ha. exists 0, fpos. split; [left; reflexivity|]. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. fold F. unfold SB in Ha. lia. }
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own => let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 1041%nat (SB + F / 8)); [reflexivity | exact U1041 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; apply INF; lia |].
do 3 (eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 1028%nat F); [reflexivity | exact U1028 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; apply INF; lia |]).
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (nsp1 sp0 - sp0)); [reflexivity | rewrite U33; lia | cbn; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the run to the strtol call writes the frame, its shadow and its stack slots only *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (SB + F / 8 <= a < SB + F / 8 + 8) \/ (F <= a < F + 64) \/ (sp0 - 112 <= a < sp0)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33, ?U1028, ?U1041 in Hrr; clear - Hrr Hs1b; lia |]);
  destruct Hin)) as UNb.
clear HF HFr. rename HG into HGb.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pmkst HS.
rewrite U1028 in R11. rewrite AG2 in R10 by lia. rewrite E10, H10 in R10. rewrite AG2, E33 in R2 by lia.
pose proof (proj1 HJ2) as HAR3.
assert (HpbT : In (pb, kb) (ablocks B ly S2)) by (rewrite Eab; exact Hpbin).
pose proof (sep_block_frame SEGS B LAWS ly S2 W _ _ pb kb 0 fpos HAR3 HpbT Hfin2) as HWF.
unfold zdisjoint in HWF. cbn [fst snd] in HWF. change (fs_frame_bytes 0) with 64 in HWF. fold F in HWF.
lazymatch type of HWF with ?T => change (nam T) in HWF end.
(* the word's bytes are those of the entry: a live block, outside the footprint *)
assert (WK : forall i, 0 <= i <= len -> aview SEGS (w_H W) (ms_mem ms0) (w + i) = aview SEGS (w_H W) mem (w + i)).
{ intros i Hi. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
replace (w + i) with (pb + (w + i - pb)) by lia. apply (F2 pb kb (w + i - pb) Hpbin HpbT); [lia|].
intros (r & [<-|[]] & Hr). cbn [fst snd] in Hr. apply (HOUTB (pb + (w + i - pb))); lia. }
assert (HSTRT : astr_at SEGS W (ms_mem ms0) w wd).
{ apply astr_atR_view. apply (n_astr_kept (aview SEGS (w_H W) mem) _ w wd); [|exact HWS]. intros i Hi. apply WK. subst len. lia. }
(* the shadow byte of `end` (frame + 32) is 0: the run poisoned the frame f1 f1 f1 f1 00 f3 f3 f3 *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity)) as HRsh; cbn [ms_mem restrict] in HRsh end.
pose proof (field_of_region _ _ 1041 (SB + F / 8) _ _ _ _ _ 4 1 (SLit 0) 0 HRsh U1041 ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as Vsh4.
pose proof (aview_of_val_mem1 SEGS _ _ _ _ Vsh4 ltac:(lia)) as Ash4.
destruct (CmdRecCells.cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR3) as (_ & HGD3 & ev3 & HEV3).
assert (Hshv : forall a, SB + F / 8 <= a < SB + F / 8 + 8 -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Ha. eapply apresent_grows; [exact HGb|]. replace a with (SB + F / 8 + (a - (SB + F / 8))) by lia. apply HFS8. lia. }
eapply SRr_bind.
{ eapply (aj_strtol_atS SEGS B LAWS Hsegs errno_low _ _ _ (STRTOL fx) W (ms_regs ms0) (ms_mem ms0) NUMBER_STK sp0 [(out, out + 4)] ly S W mem md [(0, fpos)] ly S2 _ 0 w (F + 32) wd ev3 (nsp1 sp0 - sp0) _ HJ2).
- exact R10. - exact R11. - exact R12. - lia. - lia.
- unfold spZ. rewrite R2, unsigned_lit_small by lia. lia.
- destruct Hs1 as [Hq|Hq]; rewrite Hq; [replace (sp0 - 96 - sp0) with (-96) by lia | replace (sp0 - 112 - sp0) with (-112) by lia]; reflexivity.
- lia. - rewrite Hes, FFS; lia.
- rewrite R3, AG2, E3 by lia. exact Hgp. - rewrite R4, AG2, E4 by lia. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- exact HGD3. - exact HSTRT. - unfold astr_len. fold len. lia.
- eapply (aread_ok_of_block SEGS B LAWS (3 * ESTACK) ly S2 W (ms_regs ms0) (ms_mem ms0) _ pb kb);
  [exact HAR3 | exact HpbT | lia | unfold astr_len; fold len; lia | unfold astr_len; fold len; lia |
   unfold spZ; rewrite R2, unsigned_lit_small by lia; rewrite Hes; lia].
- (* the word's `+ 8` band premise: a string in the live block (pb, kb) *)
  apply (amem8_of_block SEGS B LAWS ly S W mem md pb kb w (astr_len wd) HAR Hpbin Hpb1); unfold astr_len; fold len; lia.
- apply (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB ly S2 W (ms_mem ms0) _ pb kb (w + astr_len wd) HAR3 HpbT). unfold astr_len. fold len. lia.
- intros a Ha. split; [right; right; right; left; apply INF; lia | lia].
- intros a Ha _ _. apply (apresent_writable SEGS). eapply apresent_grows; [exact HGb|]. apply (proj1 (HFpres a ltac:(lia))).
- lia. - lia.
- (* the end pointer's `amem_range e 16`: e + 16 = F + 48 stays inside the 64-byte fake frame *)
  exact (amem_range_sub_app F 64 (F + 32) 16 HFapp HFceil ltac:(lia) ltac:(lia) ltac:(lia)).
- intros x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
replace (SB + x / 8) with (SB + F / 8 + 4); [exact Ash4|].
assert (x / 8 = F / 8 + 4) by (symmetry; apply Z.div_unique with (r := x - F - 32); lia). lia.
- intros s Hs. apply n_aview_present. apply Hshv. exact (n_hull8 F s HF64 ltac:(lia) Hs).
- unfold astr_len. fold len. unfold nam in HWF. lia.
- destruct (Z_le_gt_dec (F + 32 + 8) (as_errno B)) as [Hq|Hq]; [left; exact Hq|].
  destruct (Z_le_gt_dec (as_errno B + 4) (F + 32)) as [Hq2|Hq2]; [right; exact Hq2|]. exfalso.
  apply (frm_img SEGS B LAWS ly S2 W _ _ 0 fpos (Z.max (F + 32) (as_errno B)) HAR3 Hfin2 ltac:(change (fs_frame_bytes 0) with 64; fold F; lia)).
  apply HENimg. lia.
- (* the end pointer's word is 8-aligned: F + 32 in the 64-aligned frame *)
  replace (F + 32) with ((8 * (F / 64) + 4) * 8) by lia. apply Z_mod_mult.
- (* the end pointer's word is off the image's span: a byte of the frame is a client byte (AR's al_client_img,
     the law under frm_off_imgP) *)
  intros a Ha. apply (al_client_img _ _ LAWS ly S2 W _ _ a HAR3). right. left. exists 0, fpos.
  split; [exact Hfin2 | change (fs_frame_bytes 0) with 64; fold F; lia].
- (* the word apart from the errno cell: its bytes are in the live block (pb, kb), not image bytes (blk_img); the
     errno cell's are (api_env) *)
  destruct (Z_le_gt_dec (as_errno B + 4) w) as [Hz1|Hz1]; [left; exact Hz1|].
  destruct (Z_le_gt_dec (w + astr_len wd + 1) (as_errno B)) as [Hz2|Hz2]; [right; exact Hz2|]. exfalso.
  apply (blk_img SEGS B LAWS ly S W mem md pb kb (Z.max w (as_errno B)) HAR Hpbin);
    [unfold astr_len in Hz2; fold len in Hz2; lia | apply HENimg; lia].
- exact HEV3.
- intros a Ha Ho He. unfold aerrno_cell in He.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  assert (Hai : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  rewrite (F3 a Hai Ho He); [apply HROD; [left; exact Ha | exact Ho | exact He]|].
  apply fp_spares_closed.
  + intros (r & [<-|[]] & Hr). cbn [fst snd] in Hr. lia.
  + intros (r & [<-|[]] & Hr). cbn [fst snd] in Hr. exact (HOUTI a ltac:(lia) Hai). }
cbv beta.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hres & Hend & Herr & Hfr4 & Hpres4 & Hsame4).
pose proof (proj1 HJ4) as HAR4.
(* the result cell against the frame: a caller's frame is disjoint from it, the stack lies above it *)
assert (HOF : out + 4 <= F \/ F + 64 <= out).
{ destruct HOUTL as [(ocid & opos & Hoin & Hoa & Hob) | (Hos & Hot)].
  - destruct (in_split _ _ Hoin) as (l1 & l2 & Hsp).
    pose proof (sep_frames_pos SEGS B LAWS ly S2 W mem2 md2 (0, fpos) (ocid, opos) [] l1 l2 HAR2
      ltac:(rewrite Hfrs2, Hsp; reflexivity)) as Hdj.
    unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 0) with 64 in Hdj. fold F in Hdj. lia.
  - unfold nam in Hoc. lia. }
lazymatch type of HOF with ?T => change (nam T) in HOF end.
assert (HFNE : forall a, F <= a < F + 64 -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He. exact (frm_img SEGS B LAWS ly S2 W mem2 md2 0 fpos a HAR2 Hfin2 ltac:(change (fs_frame_bytes 0) with 64; fold F; lia) (HENimg a He)). }
(* the bytes no step of the walk writes keep the entry's value: the stack windows, the new frame and its shadow
   and the errno cell are all the steps write (the end pointer's word is inside the frame) *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - NUMBER_STK <= a < sp0) -> ~ (F <= a < F + 64) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 8) -> ~ (as_errno B <= a < as_errno B + 4) ->
  (alloc_ceiling <= a \/ exists cid pos, In (cid, pos) (frames S) /\
    (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8))) ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha K1 K2 K3 K4 K5.
  rewrite (Hfr4 a Ha); [| intros Q; apply K2; lia | exact K4 |
    intros Q; apply K1; destruct Hs1 as [Hq|Hq]; rewrite Hq in Q; rewrite FFS; rewrite Hes in Q; lia].
  rewrite (UNb a Ha); [| intros [Q|[Q|Q]]; [apply K3 | apply K2 | apply K1]; lia].
  destruct HK as (KK1 & _ & _ & KK4 & _).
  assert (KS : aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
  { destruct K5 as [K5 | (cid & pos & Hin & Hzr)].
    - apply KK1; [lia | destruct Hs1 as [Hq|Hq]; rewrite Hq; rewrite Hes; lia].
    - exact (KK4 cid pos a Hin Hzr (fun q => q)). }
  rewrite KS. apply UNa; [exact Ha | intros Q; apply K1; lia]. }
assert (OUTK' : forall a, out <= a < out + 4 -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha. unfold nam in Hosh, Hoc, HOF. apply KEEP; [lia | lia | lia | unfold kLowShadowBeg in Hosh; unfold SB; lia | unfold iv_apart in Hapart; lia |].
  destruct HOUTL as [(ocid & opos & Hoin & Hoa & Hob) | (Hos & Hot)]; [right | left; lia].
  exists ocid, opos. split; [exact Hoin|]. left. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
assert (OUTK : forall i, 0 <= i < 4 -> rdW W mem4 (out + i) = rdW W mem (out + i)) by (intros i Hi; apply OUTK'; lia).
assert (HOP : forall a, out <= a < out + 4 -> apresent (w_H W) mem4 a).
{ intros a Ha. apply (apresent_of_aview SEGS (w_H W) mem4 a); [lia | exact (HOUTI a Ha) |].
  rewrite (OUTK' a Ha). apply n_aview_present. exact (HOP0 a Ha). }
(* the result cell's shadow at strtol's return: the caller's frame's shadow, kept by every step, or the stack's
   zero shadow (AR's zshadow_ok) *)
assert (HORA : range_addressable (rdW W mem4) SHADOW_OFF out 4).
{ destruct HOUT as [((ocid & opos & Hoin & Hoa & Hob) & HRAo) | (Hos & Hot & _)].
  - destruct (al_frames _ _ LAWS _ _ _ _ _ ocid opos HAR Hoin) as (Hc32 & Hcapp & _ & _).
    destruct (frame_al64 SEGS B ly S W mem md ocid opos HAR Hoin) as (_ & Hcb64 & _).
    pose proof (n_m32 _ Hc32) as Hc8. pose proof (n_m64 _ Hcb64) as Hcb8.
    pose proof (n_m64 _ HF64) as HF8'.
    intros x Hx. destruct (HRAo x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
    rewrite <- Hs. unfold shadow_of_addr.
    pose proof (n_div8_bound x ltac:(lia)) as Hx8.
    pose proof (n_div8_out x F 64 HF8' eq_refl ltac:(unfold nam in HOF; lia)) as HxF. change (64 / 8) with 8 in HxF.
    pose proof (n_div8_in x (frame_addr ly ocid opos) (fs_frame_bytes ocid) Hc8 Hcb8 ltac:(lia)) as Hxc.
    unfold in_app, kLowShadowBeg in HFapp. rewrite <- SB_SHADOW_OFF. unfold SB in *.
    apply KEEP; [lia | lia | lia | lia | lia |].
    right. exists ocid, opos. split; [exact Hoin|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
    rewrite <- SB_SHADOW_OFF. unfold SB. lia.
  - pose proof (al_zshadow _ _ LAWS ly S2 W mem4 md4 _ HAR4 ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
    cbn [fst snd] in HZ.
    apply (range_addressable_sub _ _ (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)); [| lia | lia].
    apply zero_shadow_range; [exact (n_m4096 _ Llo) |
      rewrite Zminus_mod, (n_m4096 _ Lhi), (n_m4096 _ Llo); reflexivity | exact HZ]. }
(* the word at strtol's return: its bytes are the entry's (a live block outside the footprint) *)
assert (WK4 : forall i, 0 <= i <= len -> aview SEGS (w_H W) mem4 (w + i) = aview SEGS (w_H W) mem (w + i)).
{ intros i Hi. pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  replace (w + i) with (pb + (w + i - pb)) by lia. apply (F2 pb kb (w + i - pb) Hpbin HpbT); [lia|].
  intros (r & [<-|[]] & Hr). cbn [fst snd] in Hr. apply (HOUTB (pb + (w + i - pb))); lia. }
assert (HWB : astr_at SEGS W mem4 w wd).
{ apply astr_atR_view. apply (n_astr_kept (aview SEGS (w_H W) mem) _ w wd); [|exact HWS]. intros i Hi. apply WK4. subst len. lia. }
assert (HWB0 : aview SEGS (w_H W) mem4 w = Some (n_byte0 wd)).
{ destruct HWB as [HWB1 _]. pose proof (HWB1 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
  change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb. }
assert (HWRA : range_addressable (rdW W mem4) SHADOW_OFF w (len + 1))
  by exact (range_addressable_of_block SEGS B LAWS ly S2 W mem4 md4 pb kb w (len + 1) HAR4 HpbT Hpb1 ltac:(lia)).
assert (HWP : forall a, w <= a <= w + len -> (a < kLowShadowBeg \/ kHighShadowEnd <= a) /\ a < alloc_ceiling /\
  (a < F \/ F + 64 <= a) /\ (a < out \/ out + 4 <= a)).
{ intros a Ha. unfold nam in HWF. unfold in_app in Hpbapp. rewrite C2. rewrite C3 in Hpbapp. split; [lia|]. split; [lia|]. split; [lia|].
  destruct (Z_lt_le_dec a out) as [Hq|Hq]; [left; exact Hq|]. destruct (Z_le_gt_dec (out + 4) a) as [Hq2|Hq2]; [right; exact Hq2|].
  exfalso. apply (HOUTB a); lia. }
(* strtol's return: the state of ss_nB (numberE.v) *)
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (sp0 - NUMBER_STK <= a < sp0 - 96) -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) (ms_mem ms0) a).
{ intros a Ha K1 K2 K3. apply Hfr4; [exact Ha | intros Q; apply K1; lia | exact K2 |
    intros Q; apply K3; destruct Hs1 as [Hq|Hq]; rewrite Hq in Q; rewrite FFS; rewrite Hes in Q; lia]. }
assert (HF8t : F / 8 + 8 <= 2 ^ 44) by lia.
jafter_call_keep_hi HS 1042%nat regs4 (mrestrict (w_H W) mem4) HP4 [0;1;3;5]%nat HS2.
match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
{ unfold in_app, kLowShadowBeg in HFapp. cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  all: eapply region_kept_aview; [first [exact U1041 | exact U1028 | exact U2] | intros a Ha | exact Hpres4].
  all: apply KEEP4; [unfold SB in *; lia | unfold SB in *; lia | first [apply HFNE; lia | unfold SB in *; lia] | unfold SB in *; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
set (Ev3 := YN3v.havoc Ev2 1042 (map (getr regs4) CLOB)) in HS.
assert (AG3 : forall n, (n < 1042)%nat -> ew Ev3 n = ew Ev2 n) by (intros n Hn; subst Ev3; apply ew_havoc_old; exact Hn).
assert (E3_1046 : ew Ev3 1046 = getr regs4 10)
  by (subst Ev3; change 1046%nat with (1042 + 4)%nat; rewrite (ew_havoc_new Ev2 1042 (map (getr regs4) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (HEI3 : img_env VAL A_LIM Ev3) by (subst Ev3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
pose proof (st_ok_pi_havoc_hi 1058 Ev3 _ _ [Z_to_bv 64 (w + __intscan_c.s10_end wd); Z_to_bv 64 (n_byte0 wd)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS; rename HS3 into HS.
set (Ev4 := YN3v.havoc Ev3 1058 [Z_to_bv 64 (w + __intscan_c.s10_end wd); Z_to_bv 64 (n_byte0 wd)]) in HS.
assert (HEI4 : img_env VAL A_LIM Ev4) by (subst Ev4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (AG4 : forall n, (n < 1024)%nat -> ew Ev4 n = ew E n)
  by (intros n Hn; subst Ev4; rewrite ew_havoc_old by lia; rewrite AG3 by lia; apply AG2; exact Hn).
assert (AH4 : forall n, (1024 <= n < 1042)%nat -> ew Ev4 n = ew Ev2 n)
  by (intros n Hn; subst Ev4; rewrite ew_havoc_old by lia; apply AG3; lia).
assert (E4_1058 : ew Ev4 1058 = Z_to_bv 64 (w + __intscan_c.s10_end wd)) by (subst Ev4; exact (ew_havoc_new Ev3 1058 [Z_to_bv 64 (w + __intscan_c.s10_end wd); Z_to_bv 64 (n_byte0 wd)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E4_1059 : ew Ev4 1059 = Z_to_bv 64 (n_byte0 wd)) by (subst Ev4; exact (ew_havoc_new Ev3 1058 [Z_to_bv 64 (w + __intscan_c.s10_end wd); Z_to_bv 64 (n_byte0 wd)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E4_1046 : ew Ev4 1046 = Z_to_bv 64 (__intscan_c.s10_val wd)) by (subst Ev4; rewrite ew_havoc_old by lia; rewrite E3_1046, Hres; reflexivity).
assert (E4_1028 : ew Ev4 1028 = Z_to_bv 64 F) by (rewrite AH4 by lia; exact E2_1028).
assert (E4_1040 : ew Ev4 1040 = Z_to_bv 64 FL) by (rewrite AH4 by lia; exact E2_1040).
assert (E4_1041 : ew Ev4 1041 = Z_to_bv 64 (SB + F / 8)) by (rewrite AH4 by lia; exact E2_1041).
assert (E4_32 : ew Ev4 32 = Z_to_bv 64 SB) by (rewrite AG4 by lia; exact E32).
assert (E4_33 : ew Ev4 33 = Z_to_bv 64 (nsp1 sp0)) by (rewrite AG4 by lia; exact E33).
assert (AGR4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev4 n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite AG4 by lia. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
pose proof (number.end_le wd) as HEL. fold len in HEL.
assert (HB0 : 0 <= n_byte0 wd < 256).
{ unfold n_byte0. pose proof (bv_unsigned_in_range 8 (nth 0 (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R8.
  change (bv_modulus 8) with 256 in R8. lia. }
assert (U4_2 : bv_unsigned (ew Ev4 2) = sp0) by (rewrite AG4 by lia; exact Usp).
assert (U4_10 : bv_unsigned (ew Ev4 10) = w) by (rewrite AG4 by lia; rewrite E10, H10; unfold w64; apply unsigned_lit_small; lia).
assert (U4_11 : bv_unsigned (ew Ev4 11) = out)
  by (rewrite (AGR4 11%nat 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (U4_1028 : bv_unsigned (ew Ev4 1028) = F) by (rewrite E4_1028; apply unsigned_lit_small; lia).
assert (U4_1041 : bv_unsigned (ew Ev4 1041) = SB + F / 8) by (rewrite E4_1041; apply unsigned_lit_small; unfold SB; lia).
assert (U4_1058 : bv_unsigned (ew Ev4 1058) = w + __intscan_c.s10_end wd) by (rewrite E4_1058; apply unsigned_lit_small; lia).
assert (U4_1059 : bv_unsigned (ew Ev4 1059) = n_byte0 wd) by (rewrite E4_1059; apply unsigned_lit_small; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 1058 (mkAF 4096 (2 ^ 47 - 1) 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U4_1058; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ex _ _ 1059 (mkAF 0 255 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U4_1059; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
nnorm HS.
(* the token runs after strtol only read memory: every kept region becomes read-only *)
n_rewin HS 1041%nat 0 0 0 ltac:(intros o Ho; lia).
n_rewin HS 1028%nat 0 0 0 ltac:(intros o Ho; lia).
n_rewin HS 1028%nat 40 40 40 ltac:(intros o Ho; lia).
n_rewin HS 2%nat (-80) (-80) (-80) ltac:(intros o Ho; lia).
(* and three regions are added: the end pointer's word, the word's first byte, the result cell *)
clear AM. pose proof (HOUTB w ltac:(lia)) as HOW0.
pose proof (conj HF8b (conj HF8t (conj HFapp (conj HFceil (conj Hceil (conj Hslo (conj FFS (conj C1 (conj HWF (conj Hpb1
  (conj Hpb2 (conj Hkbr (conj Hpbapp (conj Hpbceil (conj Hlen0 (conj HOF (conj Hosh (conj Hoc (conj HOW0 (conj Hout0
  (conj Hout47 (conj HF4096 (conj HEL (conj C3 (conj Lhm Hs1))))))))))))))))))))))))) as AM.
lazymatch type of AM with ?T => change (nam T) in AM end.
addreg HS (YP09.mkRegion (Some 1028%nat) 32 40 32 32 [YP09.mkChunk 32 (CVal 8 (SOff 1058 0))])
  ltac:(rewrite U4_1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
  apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ F 32 8 _ (w + __intscan_c.s10_end wd));
  [cbn [sv_denot]; rewrite E4_1058, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | first [zside | lia] | first [zside | lia] |
   exact (val_mem_of_rdword SEGS _ _ _ _ Hend)]).
addreg HS (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 1059 0))])
  ltac:(rewrite U4_10; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
  apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ w 0 1 _ (n_byte0 wd));
  [cbn [sv_denot]; rewrite E4_1059, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | first [zside | lia] | first [zside | lia] |
   rewrite Z.add_0_r; exact (n_val1 SEGS _ _ w _ HWB0)]).
addreg HS (YP09.mkRegion (Some 11%nat) 0 4 0 0 [])
  ltac:(rewrite U4_11; split; [lia|]; split; [lia|]; split; [intros o Ho; lia | apply Forall_nil]).
clear AM.
refine (n_segB B ASF FFL LAWS ML ly S W regs mem md ch w out wd _ md4 S2 fpos Ev4 HPRE Hout4 HOUTL _ _ HEI4 HS HJ4
  Hfrs2 Eab (ex_intro _ fS2 ES2) _ AGR4 H10 H11 E4_32 E4_33 E4_1028 E4_1040 E4_1041 E4_1046 E4_1058 E4_1059
  HWB HWRA HWP HORA OUTK HOP); fold len; lia.
Qed.
End e.
End f.
End d.
