(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's phase p4 on image B (lib/B/W_LLVMFuzzerTestOneInput_gone_p4.v,
   a Theorem Labs lane's, fee5272ac13: the check_no_loss_read loop, GC1 to GT0), for the conversion of ARM_gone to the cut
   invariants of lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.  _gone_p4.v is not edited.
   - CITED from _gone_p4.v: its AR-free names (the run states, gp4_keep, gp4_keep_trans, gp4_azs_sub, gp4_abk_*,
     gp4_cs_pres, ...), with the Section variables they were generalized over;
   - RESTATED over ARx at the ghost list []: B's Section gp4c, the walk of check_no_loss_read with the kept post (image
     B proves the call inline because the kit's cnlr_spec post does not keep errno's bytes): gp4c_entry_x and
     gp4c_cnlr_x, with W1Verify's check_bounded conversion (the callee's journal W_journal_x's gx form at G = [], post
     cut_x's aleafx_post_x); and, merged per item with SmallX's image-A twin lib/A/W_LLVMFuzzerTestOneInput_gone_p4_x.v
     (95a5de32ab2), the phase's states and steps (gp4_jr_x, gp4_head_x, gp4_tail_x, the loop, gp4_c1_t0_x).
   Section hypotheses beyond cut_x's header: _gone.v's TL, HZS, HERR, RIR, HGCELLS, HROMPIN verbatim (AR-free), HPST
   (the generic placement's fact, as on image A).  Every ghost list is [] (cut_x's HP0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p4.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p4.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ================================================================== check_no_loss_read, kept form
   lib/B/W_check_no_loss_read.v's walk (cnlr_entry and pb_check_no_loss_read, copied with the gp4c_ prefix), with
   the post in W_contract.v's aleafx_post form: the kept clause of A's p4 Section gp4c (every byte outside the
   callee's 16-byte frame keeps its view and its writability).  cnlr_spec's aleaf_post does not carry the model
   across the call: its journal does not keep errno's four bytes (Reusable/YCbq.v:362, :370), and amodel_at reads
   errno (lib/B/W_rep.v:176). *)
(* @@ SECTION gp4c *)
Section gp4c.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* @@ B-ONLY-HDR Context ctx:SK *)
Context {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* @@ HDR-CITED-IN-AX Hypothesis TL *)
Hypothesis TL : PALib B.
(* @@ B-ONLY-AR[TL] Let HBgot *)
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* @@ CONFLICT Let RUN *)
(* the callee's own journal is W_journal_x's gx form at G = [] (W1Verify's check_bounded conversion) *)
Let HG0 : gx_ok segs B [] := gx_ok_nil segs B.
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS [] HG0 0 [].
(* @@ RESOLVED Let BR *)
Let BR := paj_branch (PI := PB_fr).
(* @@ B-ONLY-HDR Let RET *)
Let RET := paj_ret_at (PL := PL_fr) (PI := PB_fr).
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
(* @@ B-ONLY-AR[LAWS,TL,afn_pre,al_const] Lemma gp4c_entry *)
Lemma gp4c_entry_x : forall W ly S regs mem md ch p v,
AFN0 CNLR_STK ly S W regs mem md ch ->
getr regs 10 = w64 p ->
p mod 16 = 0 -> 0x10000 <= p -> p + 28 <= 0x5fc000 -> azs B p 28 ->
(p + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= p) -> (p + 28 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= p) ->
val_mem segs (mrestrict (w_H W) mem) (p + 24) 4 v ->
0 <= v < 2 ^ 32 ->
st_ok_pi segs VAL (Eimg (Ereg regs (gp4c_extra v))) ss_gp4c
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_fr_check_no_loss_read)) mem (seg_rom segs)))
/\ sh_ok segs gp4c_Bx gp4c_SH (Eimg (Ereg regs (gp4c_extra v))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNLR_STK = 16) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S [] W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (gp4c_extra v))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EG : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_gp4c. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold gp4c_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite EC, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EC) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val segs E _ (VAL (A_OBJ 30)) 0 8 gp4c_Bx SB);
[cbn [sv_denot gp4c_Bx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat p E10) by lia. unfold gp4c_OBJ. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val segs E _ p 24 4 _ v); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
+ apply pairwise_disjoint_of_extents. unfold gp4c_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat p E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EC) by (pose proof (pa_val_range (A_OBJ 30)); lia). cbn [base_val]. rewrite Usp.
unfold gp4c_OBJ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hp0 Hp1 Hd0 Hd30 C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [gp4c_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hp0 Hp1 Hp16 Hal16 C1 C3 WS Hstk0 Rv. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, gp4c_SH. constructor; [|constructor].
assert (UBx : U E gp4c_Bx = SHADOW_OFF).
{ unfold U, gp4c_Bx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity. }
assert (Up : U E (SOff 10 0) = p).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity. }
split; cbn [she_m she_lo she_hi].
+ rewrite UBx, Up, Z.add_0_r. unfold gp4c_OBJ. rewrite Z.sub_0_r.
  exact (azs_range_addressable_x B ARx LAWS ly S [] W mem md p 28 HAR Hzs).
+ unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up. unfold gp4c_OBJ, SHADOW_OFF. intros a Ha. lia.
Qed.
(* copied from lib/A/W_check_bounded.v cb_nowr5: only the stack region has a writable window *)
(* @@ B-ONLY-HDR Ltac gp4c_nowr *)
Ltac gp4c_nowr :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat (rewrite ew_ewset_other in Hr by lia);
  repeat match goal with Hu : bv_unsigned (ew _ 2) = _ |- _ => rewrite Hu in Hr end;
  first [lia | match goal with Hno : ~ _ |- _ => apply Hno; unfold CNLR_STK in *; lia end] |]);
destruct Hin.
(* copied from lib/A/W_check_bounded.v cb_pres *)
(* @@ B-ONLY-HDR Ltac gp4c_pres *)
Ltac gp4c_pres :=
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
repeat match goal with
| HG' : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2), Hp : apresent ?H ?m1 a |- _ =>
  lazymatch goal with _ : apresent H m2 a |- _ => fail | _ => idtac end;
  assert (apresent H m2 a) by (eapply apresent_grows; [exact HG' | exact Hp])
end; assumption.
(* pb_check_no_loss_read (lib/B/W_check_no_loss_read.v) with the post of aleafx_post *)
(* @@ B-ONLY-AR[LAWS,RUN,afn_pre,ajournal_gx_nil,aleafx_post,paj_run] Lemma gp4c_cnlr *)
Lemma gp4c_cnlr_x : forall W ly S regs mem md ch p v,
AFN0 CNLR_STK ly S W regs mem md ch ->
getr regs 10 = w64 p ->
p mod 16 = 0 -> 0x10000 <= p -> p + 28 <= 0x5fc000 -> azs B p 28 ->
(p + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= p) -> (p + 28 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= p) ->
val_mem segs (mrestrict (w_H W) mem) (p + 24) 4 v ->
0 <= v < 2 ^ 32 -> (v = 0 \/ 2 ^ 31 <= v) ->
SRr segs W (cfg_at segs (BASE + AF_fr_check_no_loss_read) regs mem md)
  (aleafx_post_x B PST ARx CNLR_STK regs ly S [] W mem md (fun _ => True)).
Proof.
intros W ly S regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv Hsign.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (gp4c_entry_x W ly S regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv) as [HS SHOK].
assert (HJ : ajournal_gx_x segs B PST ARx [] 0 [] CNLR_STK (spZ regs) [] ly S [] W mem md [] ly S [] W mem md 0)
  by (apply ajournal_gx_nil_x; exact (ajournal_x_init segs B PST ARx CNLR_STK [] ly S [] W regs mem md ch HPRE)).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs (gp4c_extra v))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (gp4c_extra v)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_fr_check_no_loss_read)) with (Z_to_bv 64 (BASE + AF_fr_check_no_loss_read)).
(* 0x85dd4-0x85e08: the frame, the two UBSan traps on E (decided by the runner from atom 10's fact) and the shadow
   check of E+24 (decided from gp4c_SH), up to the abort test *)
paj_run_tok_x RUN HS HJ SHOK gp4c_Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CNLR_STK <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
  by (intros a Ha Hno; apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha); gp4c_nowr).
(* 0x85e0c bgtz a0: the abort arm, refuted from the contract's functional half *)
psrr_branch_tok RUN BR HS SHOK gp4c_Bspan.
-
exfalso. cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
lazymatch type of Hc with bv_signed ?z < _ => assert (Hz : bv_signed z = 0) by reflexivity; rewrite Hz in Hc end.
lazymatch type of Hc with _ < bv_signed (sv_denot ?Ev _) =>
assert (Hsx : bv_unsigned (sv_denot Ev (SExt true 32 (SOff 32 0))) = sx32 v)
by (rewrite U_sext32'; f_equal; apply (U_atom Ev 32 v); [rewrite !ew_ewset_other by lia; exact E32 | lia]) end.
destruct Hsign as [-> | Hge].
+ rewrite sx32_small in Hsx by lia. rewrite bv_signed_small in Hc by (rewrite Hsx; lia). rewrite Hsx in Hc. lia.
+ assert (Hhi : sx32 v = v + 2 ^ 64 - 2 ^ 32)
  by (unfold sx32; rewrite Z.mod_small by lia; destruct (Z.ltb_spec v (2 ^ 31)); [lia | reflexivity]).
  rewrite Hhi in Hsx. rewrite bv_signed_hi in Hc by (rewrite Hsx; lia). rewrite Hsx in Hc. lia.
-
(* 0x85e10-0x85e18: the return *)
paj_run_tok_x RUN HS HJ SHOK gp4c_Bspan. { apply awr_ok_x_of0; awr_ok_tac. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CNLR_STK <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
  by (intros a Ha Hno;
      match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
        rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by gp4c_nowr end;
      apply KEEP0; assumption).
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleafx_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_gx_materialize_x segs B PST ARx LAWS Hsegs). exact HJ.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok segs _ Ev _ _ regs (gp4c_extra v) HS);
  [ split; [intros m Hm; rewrite !ew_ewset_other by lia; exact (proj1 HAE m Hm) | rewrite !ed_ewset; exact (proj2 HAE)]
  | vm_compute; reflexivity ] end.
+ cbn [ms_mem]. gp4c_pres.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP1 a Ha Hno)|].
  apply (writable_kept (w_H W) mem (ms_mem ms0) a). clear Ha Hno. revert a. gp4c_pres.
+ exact I.
Qed.
(* @@ END gp4c *)
End gp4c.

(* ================================================================== phase p4 *)
(* @@ MERGED Ltac gp4_in *)
Ltac gp4_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* a run over read-only regions leaves the memory as it was *)
(* @@ RESOLVED Ltac gp4_mem *)
Ltac gp4_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* @@ SECTION gp4 *)
Section gp4.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ MERGED Variable MT *)
Variable MT : ameter_ops.
(* @@ MERGED Variables XM_LIB *)
Variables XM_LIB : Z -> Z.
(* @@ MERGED Variables RLO *)
Variables RLO RHI : Z.
(* @@ MERGED Variable fr_live_pre *)
Variable fr_live_pre : astate -> Prop.
(* @@ AX-ONLY Variables LIBROOM *)
Variables LIBROOM NP : astate -> Prop.
(* @@ MERGED Variable G_fr *)
Variable G_fr : list (Z * Z).
(* @@ MERGED Variable fr_FP *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* @@ AX-ONLY Hypothesis HP0 *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
(* @@ MERGED Hypothesis HG *)
Hypothesis HG : gx_ok segs B G_fr.
(* @@ AX-ONLY Variable LSx *)
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* @@ RESOLVED Variable RINV *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* the allocator instance (lib/B/W_kit.v): check_no_loss_read's walk reads the GOT slot of the shadow base and the
   shadow cell through it, and its pal_env places errno below kLowMemEnd *)
(* @@ HDR-CITED-IN-AX Hypothesis TL *)
Hypothesis TL : PALib B.
(* g_s lies in the instance's zero-shadow ranges: check_no_loss_read's shadow check of &g_s[q] *)
(* @@ RESOLVED Hypothesis HZS *)
Hypothesis HZS : GN_HZS B.
(* errno's place: the base's model obligation, verbatim *)
(* @@ HDR-CITED-IN-AX Hypothesis HERR *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* the slots the loop calls check_no_loss_read on have no pending record (relay_instance_gone drained them) *)
(* @@ RESOLVED Hypothesis RIR *)
Hypothesis RIR : GN_RI_read RINV.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* @@ MERGED Let RUN *)
Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ MERGED Let RUNTO *)
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
(* @@ RESOLVED Let BR *)
Let BR := paj_branch (PI := PB_fr).

(* the walk's facts, by name *)
(* the size bound of a live block (W_kit_x.v's BLKN text; tk_x's gk_amodel_kept_x / gk_ainput_kept_x take it) *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* @@ AX-ONLY Hypothesis HPST *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* @@ AX-ONLY Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* @@ AX-ONLY Local_Notation AJ0 *)
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AJi0 *)
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AFN0 *)
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
(* @@ AX-ONLY Local_Notation LFB0 *)
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
(* @@ AX-ONLY Ltac hp0a *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
(* @@ AX-ONLY Ltac hp0g *)
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* ---- _gone_p4.v's AR-free items that take section arguments, cited with them ---- *)
(* @@ RESOLVED Definition gp4_jr *)
Definition gp4_jr_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk.
(* @@ CONFLICT Definition gp4_keep *)
(* @@ CONFLICT Lemma gp4_keep_trans *)
(* @@ MERGED Lemma gp4_azs_sub *)
Local Notation gp4_azs_sub := (W_LLVMFuzzerTestOneInput_gone_p4.gp4_azs_sub B).
(* @@ RESOLVED Definition gp4_head_post *)
Definition gp4_head_post_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gp4_mid) regs' mem' md' /\
    gp4_jr_x cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_CS -> getr regs' r = getr regs r) /\
    gp4_keep cx W mem W' mem'.
(* _gone_p4.v:671 gp4_head *)
(* @@ CONFLICT Lemma gp4_head *)
Lemma gp4_head_x : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat) rd,
  LFB0 cx ->
  gp4_jr_x cx fpos ly S W mem md kk -> gp4_saved cx W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat q) rd -> (rd = 0 \/ (rd = 1 /\ gp4_vok W mem q)) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_head_post_x cx fpos ly S W regs mem).
Proof.
  intros cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R27 R20 R21 HRD Hrd.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (Hrd01 : 0 <= rd <= 1) by (destruct Hrd as [-> | (-> & _)]; lia).
  assert (Hc4 : (lf_F cx + 192 + 4 * Z.of_nat q) mod 4 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
    replace (lf_F cx + 192 + 4 * Z.of_nat q) with ((8 * (lf_F cx / 32) + 48 + Z.of_nat q) * 4) by lia.
    apply Z_mod_mult. }
  unfold gp4_jr_x in HJ.
  destruct (gp4_entry_c1 W regs mem (lf_F cx + 192 + 4 * Z.of_nat q) rd R21 ltac:(lia) ltac:(lia) Hc4
    R27 Hrd01 HRD) as [HS SHOK].
  remember (Eimg (Ereg regs (gp4_c1_extra rd))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (gp4_c1_extra rd)) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q))
    by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E32 : ew E 32 = Z_to_bv 64 rd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_c1)) with (Z_to_bv 64 (BASE + AF_gn_c1)).
  paj_run_tok_x RUN HS HJ SHOK gp4_Bspan.
  { apply awr_ok_x_cons; [intros x Hx; cbn [gp4_c1_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
                         | apply awr_ok_x_nil]. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* reads[q] = 0: no call *)
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_gp4_mid.
    { apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
                           | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (gp4_c1_extra rd)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_head_post_x.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)); reflexivity|].
    split; [exact HJ|]. split; [exact KR|].
    intros x Hx Hno. apply gp4_abk_refl.
  - (* reads[q] = 1: check_no_loss_read(&g_s[q]) *)
    assert (Hrd1 : rd = 1 /\ gp4_vok W mem q).
    { destruct Hrd as [-> | H]; [|exact H]. exfalso.
      rewrite branch_eq_U, (U_atom E 32 0 E32), U_lit in Hc by lia. discriminate Hc. }
    destruct Hrd1 as (-> & v & Mv & Rv & Hsign).
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_fr_check_no_loss_read.
    { apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
                           | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (gp4_c1_extra 1)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. gp4_reg HS (10%bv : bv 5) Q10.
    assert (Q10v : getr (ms_regs ms0) 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat q)).
    { rewrite Q10. gp4_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 20 _ ltac:(rewrite ?ew_ewset_other by lia; exact E20)) by lia end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(gp4_in)), R2. unfold w64. apply unsigned_lit_small. lia. }
    destruct (gn_afn_pre_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV
                cx ly S fpos kk W mem mdc rc0 CNLR_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(gp4_in)). exact R3. }
    { rewrite (KR 4%bv ltac:(gp4_in)). exact R4. }
    { rewrite (KR 8%bv ltac:(gp4_in)). exact R8. }
    { unfold CNLR_STK. lia. }
    { unfold CNLR_STK. lia. }
    (* check_no_loss_read's premises at p = &g_s[q] *)
    assert (Hv0 : VAL (A_OBJ 0) = 646992) by (vm_compute; reflexivity).
    assert (Hv30 : VAL (A_OBJ 30) = 681528) by (vm_compute; reflexivity).
    assert (Hp16 : (rg_s fr_RG + ASRC * Z.of_nat q) mod 16 = 0).
    { rewrite HRS, HAS.
      replace (6131296 + 96 * Z.of_nat q) with ((383206 + 6 * Z.of_nat q) * 16) by lia. apply Z_mod_mult. }
    assert (Hzs : azs B (rg_s fr_RG + ASRC * Z.of_nat q) 28)
      by (apply (gp4_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
    eapply SRr_bind.
    { exact (gp4c_cnlr_x B PST ARx LAWS TL W ly S rc0 mem mdc ch (rg_s fr_RG + ASRC * Z.of_nat q) v HPREc Q10v
               Hp16 ltac:(lia) ltac:(lia) Hzs ltac:(right; lia) ltac:(right; lia) Mv Rv Hsign). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HKEEP & _).
    rewrite Hsp1 in HJc, HKEEP.
    (* check_no_loss_read's journal inside this function's: W2's ajournal_gx_sub at G_fr, lifted from G = [] *)
    assert (HJc' : AJ0 G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CNLR_STK (lf_F cx) [] ly S [] W mem mdc []
                ly S [] W2 mem2 md2 0 _ HJc).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
       CNLR_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
       ltac:(unfold CNLR_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply SRr_ret. unfold gp4_head_post_x.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1;
            change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)); reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (gp4_cs_pres rc0 regs2 HP2 r Hr); exact (KR r Hr)|].
    intros a Ha Hno. exact (HKEEP a Ha Hno).
Qed.

(* ---- 0x84b6c -> 0x84b5c (q + 1 < 4) or 0x84b78 (q = 3) ---- *)
(* @@ MERGED Definition gp4_tail_post *)
Definition gp4_tail_post_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (q : nat) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md' kk', gp4_jr_x cx fpos ly S W mem md' kk' /\
    (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    ((((q + 1) < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_c1) regs' mem md' /\
      getr regs' 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat (q + 1)) /\
      getr regs' 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat (q + 1))) \/
     ((q + 1)%nat = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem md')).
(* _gone_p4.v:802 gp4_tail *)
(* @@ RESOLVED Lemma gp4_tail *)
Lemma gp4_tail_x : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat),
  gp4_jr_x cx fpos ly S W mem md kk -> (q < 4)%nat -> 2 ^ 46 <= lf_F cx -> lf_F cx + 256 <= 2 ^ 47 ->
  lf_F cx mod 32 = 0 ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) -> getr regs 27 = w64 SB ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gp4_mid) regs mem md) (gp4_tail_post_x cx fpos ly S W regs mem q).
Proof.
  intros cx fpos ly S kk W regs mem md q HJ Hq HF0 HF1 HF32 R20 R21 R22 R27.
  unfold gp4_jr_x in HJ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
  assert (Hc4 : (lf_F cx + 192 + 4 * Z.of_nat q) mod 4 = 0)
    by (replace (lf_F cx + 192 + 4 * Z.of_nat q) with ((8 * (lf_F cx / 32) + 48 + Z.of_nat q) * 4) by lia;
        apply Z_mod_mult).
  assert (Hd4 : (lf_F cx + 208) mod 4 = 0)
    by (replace (lf_F cx + 208) with ((8 * (lf_F cx / 32) + 52) * 4) by lia; apply Z_mod_mult).
  destruct (gp4_entry_md W regs mem (lf_F cx + 192 + 4 * Z.of_nat q) (lf_F cx + 208) R21 R22 R27
    ltac:(lia) ltac:(lia) Hc4 ltac:(lia) ltac:(lia) Hd4) as [HS SHOK].
  remember (Eimg (Ereg regs gp4_md_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp4_md_extra) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q))
    by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 (lf_F cx + 192 + 4 * Z.of_nat q))
    by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (lf_F cx + 208)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)).
  paj_run_tok_x RUN HS HJ SHOK gp4_Bspan. { apply awr_ok_x_nil. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* s5 + 4 <> s6: back to the head *)
    rewrite branch_ne_U, (U_atom_off E 21 _ 4 E21), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq1 : ((q + 1) < 4)%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [discriminate Hc | lia]. }
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_gn_c1. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs gp4_md_extra) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp4_reg HS (20%bv : bv 5) Q20. gp4_reg HS (21%bv : bv 5) Q21.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post_x. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. left.
    split; [exact Hq1|].
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gn_c1)) with (Z_to_bv 64 (BASE + AF_gn_c1)); reflexivity|].
    split; [gp4_off Q20 20%nat 96 E20 | gp4_off Q21 21%nat 4 E21].
  - (* s5 + 4 = s6: the loop is done *)
    rewrite branch_ne_U, (U_atom_off E 21 _ 4 E21), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq4 : (q + 1)%nat = 4%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [lia | discriminate Hc]. }
    paj_run_to_tok_x RUNTO HS HJ SHOK gp4_Bspan AF_gn_t0. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs gp4_md_extra) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post_x. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. right.
    split; [exact Hq4|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)). reflexivity.
Qed.

(* ---- the loop, by induction on the slots left ---- *)
(* _gone_p4.v:863 gp4_loop_post *)
(* @@ RESOLVED Definition gp4_loop_post *)
Definition gp4_loop_post_x (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem' md' /\
    gp4_jr_x cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    gp4_keep cx W mem W' mem'.
(* _gone_p4.v:868 gp4_loopX *)
(* @@ RESOLVED Lemma gp4_loopX *)
Lemma gp4_loopX_x : forall (k : nat) cx fpos ly S (q : nat) kk (W : world segs) regs mem md,
  LFB0 cx -> k = (4 - q)%nat -> (q < 4)%nat ->
  gp4_jr_x cx fpos ly S W mem md kk -> gp4_saved cx W mem -> gp4_cells cx W mem q ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_loop_post_x cx fpos ly S W regs mem).
Proof.
  induction k as [|k IH]; intros cx fpos ly S q kk W regs mem md HB Hk Hq HJ HSV HCL R2 R3 R4 R8 R27 R20 R21 R22;
    [lia|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  (* g_s's cells (low image memory) are far below the callee's window [F - 16, F) *)
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  pose proof YM05.alloc_ceiling_value as AC.
  pose proof gk_ceil_lo as HCL0.
  destruct (HCL q ltac:(lia)) as (rd & HRD & Hrd).
  eapply SRr_bind;
    [exact (gp4_head_x cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R27 R20 R21 HRD Hrd)|].
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & KP1).
  eapply SRr_bind.
  { apply (gp4_tail_x cx fpos ly S kk1 W1 regs1 mem1 md1 q HJ1 Hq); [lia | lia | exact HF32 | | | |].
    - rewrite (KR1 20%bv ltac:(gp4_in)). exact R20.
    - rewrite (KR1 21%bv ltac:(gp4_in)). exact R21.
    - rewrite (KR1 22%bv ltac:(gp4_in)). exact R22.
    - rewrite (KR1 27%bv ltac:(gp4_in)). exact R27. }
  intros W2 c2 Hwle2 (-> & regs2 & md2 & kk2 & HJ2 & KR2 & [(Hq1 & -> & Q20 & Q21) | (Hq4 & ->)]).
  - (* the next slot *)
    assert (KRR : forall r, In r GP4_K2 -> getr regs2 r = getr regs r)
      by (intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))).
    eapply SRr_mono.
    { apply (IH cx fpos ly S (q + 1)%nat kk2 W1 regs2 mem1 md2 HB ltac:(lia) Hq1 HJ2).
      - intros o r Hin. apply (gk_sv8_kept W W1 mem mem1); [|exact (HSV o r Hin)].
        intros x Hx.
        assert (Ho : 8 <= o <= 104).
        { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
        apply KP1; unfold CNLR_STK in *; lia.
      - intros j Hj. destruct (HCL j ltac:(lia)) as (rj & Hcj & Hrj). exists rj. split.
        + apply (akept_vm W mem); [|exact Hcj]. intros x Hx. apply KP1; unfold CNLR_STK in *; lia.
        + destruct Hrj as [Hr0 | (Hr1 & vj & Mvj & Rvj & Hsj)]; [left; exact Hr0|]. right. split; [exact Hr1|].
          exists vj. split; [|split; [exact Rvj | exact Hsj]].
          apply (akept_vm W mem); [|exact Mvj]. intros x Hx. apply KP1; unfold CNLR_STK, ASRC in *; lia.
      - rewrite (KRR 2%bv ltac:(gp4_in)). exact R2.
      - rewrite (KRR 3%bv ltac:(gp4_in)). exact R3.
      - rewrite (KRR 4%bv ltac:(gp4_in)). exact R4.
      - rewrite (KRR 8%bv ltac:(gp4_in)). exact R8.
      - rewrite (KRR 27%bv ltac:(gp4_in)). exact R27.
      - exact Q20.
      - exact Q21.
      - rewrite (KRR 22%bv ltac:(gp4_in)). exact R22. }
    intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR' & KP').
    exists regs', mem', md', kk'. split; [reflexivity|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KRR r Hr)|].
    exact (gp4_keep_trans cx W W1 W' mem mem1 mem' KP1 KP').
  - (* the last slot: 0x84b78 *)
    apply SRr_ret. exists regs2, mem1, md2, kk2. split; [reflexivity|]. split; [exact HJ2|].
    split; [intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))|]. exact KP1.
Qed.

(* ================================================================== GP4 *)
(* _gone_p4.v:924 gp4_c1_t0 *)
(* @@ CONFLICT Lemma gp4_c1_t0 *)
Lemma gp4_c1_t0_x : forall q cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GC1_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 q W c ->
  SRr segs W c (GT0_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1).
Proof.
  intros q cx t m m1 W c HB HC.
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & HGST & HGD & HLSx & HKR & H24 & R20 & R21 & R22 & Hq &
    HCL & HAWR & H208 & HPF).
  pose proof HGST as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP).
  pose proof HKR as (K2 & K8 & K9 & K18 & K19 & K27 & K3 & K4).
  pose proof HGD as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  pose proof YM05.alloc_ceiling_value as AC. pose proof gk_ceil_lo as HCL0.
  pose proof HERR as (HE0 & HE1).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (HCEIL : GK_CEIL8 = alloc_ceiling + 8) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HCS : CNLR_STK = 16) by reflexivity.
  assert (Hq4 : (q < 4)%nat) by exact Hq.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx).
  { destruct HB as (_ & HPRE0). unfold fr_lib_pre_cf_x in HPRE0. symmetry. tauto. }
  (* the cells reads[j] and the slots behind them *)
  assert (HCL' : gp4_cells cx W mem q).
  { intros j Hj. exists (gn_reads m j). split; [exact (HCL j ltac:(lia))|].
    destruct (gp4_reads01 m j) as [H0 | H1]; [left; exact H0 | right; split; [exact H1|]].
    exists 0. split; [|split; [lia | left; reflexivity]].
    pose proof HMOD as (_ & HSL & _). specialize (HSL j ltac:(lia)). unfold aslot in HSL.
    destruct (nth j (lm_hs m1) None) as [h|] eqn:Hnth.
    - destruct (RIR cx t m hs qs c2 O2 cap2 out2 m1 j h HRI Hpairs Hafter Hrok ltac:(lia) H1 Hnth) as [Hpe _].
      destruct HSL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hn & _) & _).
      unfold hl_n in Hn. rewrite Hpe in Hn. cbn [length Z.of_nat] in Hn.
      replace (rg_s fr_RG + ASRC * Z.of_nat j + 24) with (rg_s fr_RG + ASRC * Z.of_nat j + 16 + 8) by lia.
      exact Hn.
    - destruct HSL as [HZ _]. exact (gp4_zero4 _ _ 24 HZ ltac:(lia) ltac:(unfold ASRC; lia)). }
  eapply SRr_mono.
  { exact (gp4_loopX_x (4 - q) cx fpos ly S q kk W regs mem md HB eq_refl Hq4 HJ (proj1 HFR) HCL'
      K2 K3 K4 K8 K27 R20 R21 R22). }
  intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR & KP).
  (* what is kept: every byte below alloc_ceiling + 8, and every byte from s1 up *)
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; lia).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; lia).
  assert (HFFs : 0 <= SB + frame_addr ly 1 fpos / 8 /\ SB + frame_addr ly 1 fpos / 8 + 16 <= GK_CEIL8).
  { pose proof (Z.div_pos (frame_addr ly 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd1.
    pose proof (Z.mul_div_le (frame_addr ly 1 fpos) 8 ltac:(lia)) as Hd2. lia. }
  assert (HFR' : gframe cx fake_shadow_open (frame_addr ly 1 fpos) W' mem')
    by (apply (gp4_gframe_kept cx fake_shadow_open (frame_addr ly 1 fpos) W W' mem mem' HFR eq_refl KL KH);
        lia).
  assert (HFL' : sv8 W' mem' (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos))
    by (apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact HFL]).
  pose proof (gk_amodel_kept_x B ARx LAWS BLKN ly S W mem md W' mem' m1 HAR HMOD HE0 ltac:(lia) KL) as HMOD'.
  pose proof (gk_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W' mem' HAR HIN HlenP KL) as HIN'.
  pose proof (gk_rom_kept W W' mem mem' HRV KL) as HRV'.
  pose proof (gk_jt_kept W W' mem mem' HJT KL) as HJT'.
  exists regs', mem', md', ly, S, kk', fpos. split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD' | split; [exact HSEP | exact HNP]]].
    split; [exact HJ'|]. split; [exact HFR'|]. split; [exact HFL'|].
    split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H16]|].
    split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H144]|].
    split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H88]|].
    split; [exact HIN'|]. split; [exact HRV' | exact HJT']. }
  split; [exact HGD|]. split; [exact HLSx|].
  split.
  { unfold gn_kregs. repeat split; rewrite KR; first [assumption | unfold GP4_K2; gp4_in]. }
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H24]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H208]|].
  apply (gp4_prefix_kept cx m W W' mem mem' _ HPF). intros a Ha. apply KL. lia.
Qed.
(* @@ END gp4 *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp4R.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Let RUNG := paj_run_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let BRR := paj_branch_xR (PI := PB_fr) (R := R).



Definition gp4_jr_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk.

Definition gp4_head_post_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gp4_mid) regs' mem' md' /\
    gp4_jr_xR cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_CS -> getr regs' r = getr regs r) /\
    gp4_keep cx W mem W' mem'.

Lemma gp4_head_xR : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat) rd,
  LFB0 cx ->
  gp4_jr_xR cx fpos ly S W mem md kk -> gp4_saved cx W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat q) rd -> (rd = 0 \/ (rd = 1 /\ gp4_vok W mem q)) ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_head_post_xR cx fpos ly S W regs mem).
Proof.
  intros cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R27 R20 R21 HRD Hrd.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  assert (Hrd01 : 0 <= rd <= 1) by (destruct Hrd as [-> | (-> & _)]; lia).
  assert (Hc4 : (lf_F cx + 192 + 4 * Z.of_nat q) mod 4 = 0).
  { pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
    replace (lf_F cx + 192 + 4 * Z.of_nat q) with ((8 * (lf_F cx / 32) + 48 + Z.of_nat q) * 4) by lia.
    apply Z_mod_mult. }
  unfold gp4_jr_xR in HJ.
  destruct (gp4_entry_c1 W regs mem (lf_F cx + 192 + 4 * Z.of_nat q) rd R21 ltac:(lia) ltac:(lia) Hc4
    R27 Hrd01 HRD) as [HS SHOK].
  remember (Eimg (Ereg regs (gp4_c1_extra rd))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (gp4_c1_extra rd)) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q))
    by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E32 : ew E 32 = Z_to_bv 64 rd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_c1)) with (Z_to_bv 64 (BASE + AF_gn_c1)).
  paj_run_tok_xR RUNG HS HJ SHOK gp4_Bspan.
  { apply awr_ok_x_cons; [intros x Hx; cbn [gp4_c1_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
                         | apply awr_ok_x_nil]. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUNG BRR HS SHOK gp4_Bspan.
  - (* reads[q] = 0: no call *)
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp4_Bspan AF_gp4_mid.
    { apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
                           | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (gp4_c1_extra rd)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold gp4_head_post_xR.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)); reflexivity|].
    split; [exact HJ|]. split; [exact KR|].
    intros x Hx Hno. apply gp4_abk_refl.
  - (* reads[q] = 1: check_no_loss_read(&g_s[q]) *)
    assert (Hrd1 : rd = 1 /\ gp4_vok W mem q).
    { destruct Hrd as [-> | H]; [|exact H]. exfalso.
      rewrite branch_eq_U, (U_atom E 32 0 E32), U_lit in Hc by lia. discriminate Hc. }
    destruct Hrd1 as (-> & v & Mv & Rv & Hsign).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp4_Bspan AF_fr_check_no_loss_read.
    { apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
                           | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (gp4_c1_extra 1)) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. gp4_reg HS (10%bv : bv 5) Q10.
    assert (Q10v : getr (ms_regs ms0) 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat q)).
    { rewrite Q10. gp4_U.
      lazymatch goal with |- U ?Ev _ = _ =>
        rewrite (U_atom Ev 20 _ ltac:(rewrite ?ew_ewset_other by lia; exact E20)) by lia end.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(gp4_in)), R2. unfold w64. apply unsigned_lit_small. lia. }
    destruct (gn_afn_pre_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx HG LSx RINV R
                cx ly S fpos kk W mem mdc rc0 CNLR_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(gp4_in)). exact R3. }
    { rewrite (KR 4%bv ltac:(gp4_in)). exact R4. }
    { rewrite (KR 8%bv ltac:(gp4_in)). exact R8. }
    { unfold CNLR_STK. lia. }
    { unfold CNLR_STK. lia. }
    (* check_no_loss_read's premises at p = &g_s[q] *)
    assert (Hv0 : VAL (A_OBJ 0) = 646992) by (vm_compute; reflexivity).
    assert (Hv30 : VAL (A_OBJ 30) = 681528) by (vm_compute; reflexivity).
    assert (Hp16 : (rg_s fr_RG + ASRC * Z.of_nat q) mod 16 = 0).
    { rewrite HRS, HAS.
      replace (6131296 + 96 * Z.of_nat q) with ((383206 + 6 * Z.of_nat q) * 16) by lia. apply Z_mod_mult. }
    assert (Hzs : azs B (rg_s fr_RG + ASRC * Z.of_nat q) 28)
      by (apply (gp4_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact HZS | lia | lia]).
    eapply (YA0nH.SRrG_bind _ R R_trans).
    { apply (YA0nH.SRr_SRrG _ R WLE_R); exact (gp4c_cnlr_x B PST ARx LAWS TL W ly S rc0 mem mdc ch (rg_s fr_RG + ASRC * Z.of_nat q) v HPREc Q10v
               Hp16 ltac:(lia) ltac:(lia) Hzs ltac:(right; lia) ltac:(right; lia) Mv Rv Hsign). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HKEEP & _).
    rewrite Hsp1 in HJc, HKEEP.
    (* check_no_loss_read's journal inside this function's: W2's ajournal_gx_sub at G_fr, lifted from G = [] *)
    assert (HJc' : AJ0R G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono_xR segs B PST ARx [] G_fr 0 [] CNLR_STK (lf_F cx) [] ly S [] W mem mdc []
                ly S [] W2 mem2 md2 0 _ (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc)).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S [] W mem mdc kk
       CNLR_STK (lf_F cx) 0 [] [] [] ly S [] W2 mem2 md2 0 HJ HJc'
       ltac:(unfold CNLR_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold gp4_head_post_xR.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1;
            change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)); reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (gp4_cs_pres rc0 regs2 HP2 r Hr); exact (KR r Hr)|].
    intros a Ha Hno. exact (HKEEP a Ha Hno).
Qed.

Definition gp4_tail_post_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (q : nat) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md' kk', gp4_jr_xR cx fpos ly S W mem md' kk' /\
    (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    ((((q + 1) < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_c1) regs' mem md' /\
      getr regs' 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat (q + 1)) /\
      getr regs' 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat (q + 1))) \/
     ((q + 1)%nat = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem md')).

Lemma gp4_tail_xR : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat),
  gp4_jr_xR cx fpos ly S W mem md kk -> (q < 4)%nat -> 2 ^ 46 <= lf_F cx -> lf_F cx + 256 <= 2 ^ 47 ->
  lf_F cx mod 32 = 0 ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) -> getr regs 27 = w64 SB ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + AF_gp4_mid) regs mem md) (gp4_tail_post_xR cx fpos ly S W regs mem q).
Proof.
  intros cx fpos ly S kk W regs mem md q HJ Hq HF0 HF1 HF32 R20 R21 R22 R27.
  unfold gp4_jr_xR in HJ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (Hqz : 0 <= Z.of_nat q <= 3) by lia.
  pose proof (Z.div_mod (lf_F cx) 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D.
  assert (Hc4 : (lf_F cx + 192 + 4 * Z.of_nat q) mod 4 = 0)
    by (replace (lf_F cx + 192 + 4 * Z.of_nat q) with ((8 * (lf_F cx / 32) + 48 + Z.of_nat q) * 4) by lia;
        apply Z_mod_mult).
  assert (Hd4 : (lf_F cx + 208) mod 4 = 0)
    by (replace (lf_F cx + 208) with ((8 * (lf_F cx / 32) + 52) * 4) by lia; apply Z_mod_mult).
  destruct (gp4_entry_md W regs mem (lf_F cx + 192 + 4 * Z.of_nat q) (lf_F cx + 208) R21 R22 R27
    ltac:(lia) ltac:(lia) Hc4 ltac:(lia) ltac:(lia) Hd4) as [HS SHOK].
  remember (Eimg (Ereg regs gp4_md_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp4_md_extra) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q))
    by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 (lf_F cx + 192 + 4 * Z.of_nat q))
    by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (lf_F cx + 208)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)).
  paj_run_tok_xR RUNG HS HJ SHOK gp4_Bspan. { apply awr_ok_x_nil. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUNG BRR HS SHOK gp4_Bspan.
  - (* s5 + 4 <> s6: back to the head *)
    rewrite branch_ne_U, (U_atom_off E 21 _ 4 E21), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq1 : ((q + 1) < 4)%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [discriminate Hc | lia]. }
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp4_Bspan AF_gn_c1. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs gp4_md_extra) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    gp4_reg HS (20%bv : bv 5) Q20. gp4_reg HS (21%bv : bv 5) Q21.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold gp4_tail_post_xR. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. left.
    split; [exact Hq1|].
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gn_c1)) with (Z_to_bv 64 (BASE + AF_gn_c1)); reflexivity|].
    split; [gp4_off Q20 20%nat 96 E20 | gp4_off Q21 21%nat 4 E21].
  - (* s5 + 4 = s6: the loop is done *)
    rewrite branch_ne_U, (U_atom_off E 21 _ 4 E21), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq4 : (q + 1)%nat = 4%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [lia | discriminate Hc]. }
    paj_run_to_tok_xR RUNTOG HS HJ SHOK gp4_Bspan AF_gn_t0. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs gp4_md_extra) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply (YA0nH.SRrG_ret _ R R_refl). unfold gp4_tail_post_xR. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. right.
    split; [exact Hq4|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)). reflexivity.
Qed.

Definition gp4_loop_post_xR (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem' md' /\
    gp4_jr_xR cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    gp4_keep cx W mem W' mem'.

Lemma gp4_loopX_xR : forall (k : nat) cx fpos ly S (q : nat) kk (W : world segs) regs mem md,
  LFB0 cx -> k = (4 - q)%nat -> (q < 4)%nat ->
  gp4_jr_xR cx fpos ly S W mem md kk -> gp4_saved cx W mem -> gp4_cells cx W mem q ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  YA0nH.SRrG segs R W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_loop_post_xR cx fpos ly S W regs mem).
Proof.
  induction k as [|k IH]; intros cx fpos ly S q kk W regs mem md HB Hk Hq HJ HSV HCL R2 R3 R4 R8 R27 R20 R21 R22;
    [lia|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  (* g_s's cells (low image memory) are far below the callee's window [F - 16, F) *)
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  pose proof YM05.alloc_ceiling_value as AC.
  pose proof gk_ceil_lo as HCL0.
  destruct (HCL q ltac:(lia)) as (rd & HRD & Hrd).
  eapply (YA0nH.SRrG_bind _ R R_trans);
    [exact (gp4_head_xR cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R27 R20 R21 HRD Hrd)|].
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & KP1).
  eapply (YA0nH.SRrG_bind _ R R_trans).
  { apply (gp4_tail_xR cx fpos ly S kk1 W1 regs1 mem1 md1 q HJ1 Hq); [lia | lia | exact HF32 | | | |].
    - rewrite (KR1 20%bv ltac:(gp4_in)). exact R20.
    - rewrite (KR1 21%bv ltac:(gp4_in)). exact R21.
    - rewrite (KR1 22%bv ltac:(gp4_in)). exact R22.
    - rewrite (KR1 27%bv ltac:(gp4_in)). exact R27. }
  intros W2 c2 Hwle2 (-> & regs2 & md2 & kk2 & HJ2 & KR2 & [(Hq1 & -> & Q20 & Q21) | (Hq4 & ->)]).
  - (* the next slot *)
    assert (KRR : forall r, In r GP4_K2 -> getr regs2 r = getr regs r)
      by (intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))).
    eapply YA0nH.SRrG_mono.
    { apply (IH cx fpos ly S (q + 1)%nat kk2 W1 regs2 mem1 md2 HB ltac:(lia) Hq1 HJ2).
      - intros o r Hin. apply (gk_sv8_kept W W1 mem mem1); [|exact (HSV o r Hin)].
        intros x Hx.
        assert (Ho : 8 <= o <= 104).
        { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
        apply KP1; unfold CNLR_STK in *; lia.
      - intros j Hj. destruct (HCL j ltac:(lia)) as (rj & Hcj & Hrj). exists rj. split.
        + apply (akept_vm W mem); [|exact Hcj]. intros x Hx. apply KP1; unfold CNLR_STK in *; lia.
        + destruct Hrj as [Hr0 | (Hr1 & vj & Mvj & Rvj & Hsj)]; [left; exact Hr0|]. right. split; [exact Hr1|].
          exists vj. split; [|split; [exact Rvj | exact Hsj]].
          apply (akept_vm W mem); [|exact Mvj]. intros x Hx. apply KP1; unfold CNLR_STK, ASRC in *; lia.
      - rewrite (KRR 2%bv ltac:(gp4_in)). exact R2.
      - rewrite (KRR 3%bv ltac:(gp4_in)). exact R3.
      - rewrite (KRR 4%bv ltac:(gp4_in)). exact R4.
      - rewrite (KRR 8%bv ltac:(gp4_in)). exact R8.
      - rewrite (KRR 27%bv ltac:(gp4_in)). exact R27.
      - exact Q20.
      - exact Q21.
      - rewrite (KRR 22%bv ltac:(gp4_in)). exact R22. }
    intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR' & KP').
    exists regs', mem', md', kk'. split; [reflexivity|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KRR r Hr)|].
    exact (gp4_keep_trans cx W W1 W' mem mem1 mem' KP1 KP').
  - (* the last slot: 0x84b78 *)
    apply (YA0nH.SRrG_ret _ R R_refl). exists regs2, mem1, md2, kk2. split; [reflexivity|]. split; [exact HJ2|].
    split; [intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))|]. exact KP1.
Qed.

Lemma gp4_c1_t0_xR : forall q cx t m m1 W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GC1_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 q W c ->
  YA0nH.SRrG segs R W c (GT0_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1).
Proof.
  intros q cx t m m1 W c HB HC.
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & HGST & HGD & HLSx & HKR & H24 & R20 & R21 & R22 & Hq &
    HCL & HAWR & H208 & HPF).
  pose proof HGST as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP & HNP).
  pose proof HKR as (K2 & K8 & K9 & K18 & K19 & K27 & K3 & K4).
  pose proof HGD as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx _ ly S W mem md kk fpos
    HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  pose proof YM05.alloc_ceiling_value as AC. pose proof gk_ceil_lo as HCL0.
  pose proof HERR as (HE0 & HE1).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (HCEIL : GK_CEIL8 = alloc_ceiling + 8) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HCS : CNLR_STK = 16) by reflexivity.
  assert (Hq4 : (q < 4)%nat) by exact Hq.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx).
  { destruct HB as (_ & HPRE0). unfold fr_lib_pre_cf_x in HPRE0. symmetry. tauto. }
  (* the cells reads[j] and the slots behind them *)
  assert (HCL' : gp4_cells cx W mem q).
  { intros j Hj. exists (gn_reads m j). split; [exact (HCL j ltac:(lia))|].
    destruct (gp4_reads01 m j) as [H0 | H1]; [left; exact H0 | right; split; [exact H1|]].
    exists 0. split; [|split; [lia | left; reflexivity]].
    pose proof HMOD as (_ & HSL & _). specialize (HSL j ltac:(lia)). unfold aslot in HSL.
    destruct (nth j (lm_hs m1) None) as [h|] eqn:Hnth.
    - destruct (RIR cx t m hs qs c2 O2 cap2 out2 m1 j h HRI Hpairs Hafter Hrok ltac:(lia) H1 Hnth) as [Hpe _].
      destruct HSL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hn & _) & _).
      unfold hl_n in Hn. rewrite Hpe in Hn. cbn [length Z.of_nat] in Hn.
      replace (rg_s fr_RG + ASRC * Z.of_nat j + 24) with (rg_s fr_RG + ASRC * Z.of_nat j + 16 + 8) by lia.
      exact Hn.
    - destruct HSL as [HZ _]. exact (gp4_zero4 _ _ 24 HZ ltac:(lia) ltac:(unfold ASRC; lia)). }
  eapply YA0nH.SRrG_mono.
  { exact (gp4_loopX_xR (4 - q) cx fpos ly S q kk W regs mem md HB eq_refl Hq4 HJ (proj1 HFR) HCL'
      K2 K3 K4 K8 K27 R20 R21 R22). }
  intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR & KP).
  (* what is kept: every byte below alloc_ceiling + 8, and every byte from s1 up *)
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; lia).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; lia).
  assert (HFFs : 0 <= SB + frame_addr ly 1 fpos / 8 /\ SB + frame_addr ly 1 fpos / 8 + 16 <= GK_CEIL8).
  { pose proof (Z.div_pos (frame_addr ly 1 fpos) 8 ltac:(lia) ltac:(lia)) as Hd1.
    pose proof (Z.mul_div_le (frame_addr ly 1 fpos) 8 ltac:(lia)) as Hd2. lia. }
  assert (HFR' : gframe cx fake_shadow_open (frame_addr ly 1 fpos) W' mem')
    by (apply (gp4_gframe_kept cx fake_shadow_open (frame_addr ly 1 fpos) W W' mem mem' HFR eq_refl KL KH);
        lia).
  assert (HFL' : sv8 W' mem' (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos))
    by (apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact HFL]).
  pose proof (gk_amodel_kept_x B ARx LAWS BLKN ly S W mem md W' mem' m1 HAR HMOD HE0 ltac:(lia) KL) as HMOD'.
  pose proof (gk_ainput_kept_x B ARx LAWS BLKN cx ly S W mem md W' mem' HAR HIN HlenP KL) as HIN'.
  pose proof (gk_rom_kept W W' mem mem' HRV KL) as HRV'.
  pose proof (gk_jt_kept W W' mem mem' HJT KL) as HJT'.
  exists regs', mem', md', ly, S, kk', fpos. split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD' | split; [exact HSEP | exact HNP]]].
    split; [exact HJ'|]. split; [exact HFR'|]. split; [exact HFL'|].
    split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H16]|].
    split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H144]|].
    split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H88]|].
    split; [exact HIN'|]. split; [exact HRV' | exact HJT']. }
  split; [exact HGD|]. split; [exact HLSx|].
  split.
  { unfold gn_kregs. repeat split; rewrite KR; first [assumption | unfold GP4_K2; gp4_in]. }
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H24]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]|].
  split; [apply (gk_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H208]|].
  apply (gp4_prefix_kept cx m W W' mem mem' _ HPF). intros a Ha. apply KL. lia.
Qed.

End gp4R.

End gp4.

