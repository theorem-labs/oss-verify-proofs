(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE p4 (lib/B/W_LLVMFuzzerTestOneInput_gone.v's GP4): GC1 q -> GT0, 0x84b5c -> 0x84b78, the
   check_no_loss_read loop of fuzz_reply.c:643-645 `for (k...) if (reads[k]) check_no_loss_read(&g_s[k])`, the
   image-B twin of lib/A/W_LLVMFuzzerTestOneInput_gone_p4.v (a working branch 32b23a20c3e), read
   from B's objdump:
     0x84b5c  lw   a0,0(s5)           reads[q] (s5 = F + 192 + 4q)
     0x84b60  beqz a0,84b6c
     0x84b64  mv   a0,s4              s4 = &g_s[q]
     0x84b68  jal  85dd4 <check_no_loss_read>
     0x84b6c  addi s5,s5,4; addi s4,s4,96; bne s5,s6,84b5c   (s6 = F + 208)
   The loop is gp4_loopX, by induction on the slots left: one trip is gp4_head (0x84b5c -> 0x84b6c, the call or
   not) and gp4_tail (0x84b6c -> 0x84b5c or 0x84b78).  Its post keeps every byte outside check_no_loss_read's
   16-byte frame below s1 (gp4_keep); gp4_c1_t0 carries GC1's facts to GT0 with it (the arm's transport kit
   W_LLVMFuzzerTestOneInput_gone_tk.v).
   CALLEE WALKED INLINE: the kit post cnlr_spec (lib/B/W_contract.v:484) is aleaf_post, which lacks the
   outside-frame-kept clause, so errno's view, which amodel_at's aout_at reads, is not carried (a Theorem Labs lane's ruling
   14:1xZ).  check_no_loss_read is therefore walked again here with the post in aleafx_post form (gp4c_cnlr): the
   walk and its entry state are lib/B/W_check_no_loss_read.v's (cnlr_entry and pb_check_no_loss_read, copied with
   the gp4c_ prefix so this file imports no other walk's file), plus the kept clause of A's p4 Section gp4c. *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ================================================================== check_no_loss_read, kept form
   lib/B/W_check_no_loss_read.v's walk (cnlr_entry and pb_check_no_loss_read, copied with the gp4c_ prefix), with
   the post in W_contract.v's aleafx_post form: the kept clause of A's p4 Section gp4c (every byte outside the
   callee's 16-byte frame keeps its view and its writability).  cnlr_spec's aleaf_post does not carry the model
   across the call: its journal does not keep errno's four bytes (Reusable/YCbq.v:362, :370), and amodel_at reads
   errno (lib/B/W_rep.v:186). *)
Section gp4c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run (PL := PL_fr) (PI := PB_fr) B LAWS.
Let BR := paj_branch (PI := PB_fr).
Let RET := paj_ret_at (PL := PL_fr) (PI := PB_fr).
Definition gp4c_Bx : sv := SOff 33 0.
Definition gp4c_OBJ : Z := 28.
(* the seat: E = a0 is atom 10 with lo 4096 (decides the null trap `beqz a0`, 0x85ddc) and al2 4 (decides the
   alignment trap `andi a1,a0,7; bnez a1`, 0x85de0-0x85de4); hi is the ASan user ceiling *)
Definition gp4c_regions : smem :=
[ stack_region CNLR_STK; got_regionP; bcell_regionP 33;
YP09.mkRegion (Some 10%nat) 0 gp4c_OBJ 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 32 0))] ].
Definition gp4c_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4);
(32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_gp4c : sstate := mkSS AF_fr_check_no_loss_read sr_atoms gp4c_regions None gp4c_facts.
Definition gp4c_SH : list shent := [ mkSHE 10 0 gp4c_OBJ ].
Definition gp4c_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gp4c_extra (v : Z) : list word := map (Z_to_bv 64) [v; SB].
(* copied from lib/B/W_check_no_loss_read.v cnlr_entry *)
Lemma gp4c_entry : forall W ly S regs mem md ch p v,
afn_pre segs B CNLR_STK ly S W regs mem md ch ->
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
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
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
  exact (azs_range_addressable B LAWS ly S W mem md p 28 HAR Hzs).
+ unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up. unfold gp4c_OBJ, SHADOW_OFF. intros a Ha. lia.
Qed.
(* copied from lib/A/W_check_bounded.v cb_nowr5: only the stack region has a writable window *)
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
Ltac gp4c_pres :=
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
repeat match goal with
| HG' : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2), Hp : apresent ?H ?m1 a |- _ =>
  lazymatch goal with _ : apresent H m2 a |- _ => fail | _ => idtac end;
  assert (apresent H m2 a) by (eapply apresent_grows; [exact HG' | exact Hp])
end; assumption.
(* pb_check_no_loss_read (lib/B/W_check_no_loss_read.v) with the post of aleafx_post *)
Lemma gp4c_cnlr : forall W ly S regs mem md ch p v,
afn_pre segs B CNLR_STK ly S W regs mem md ch ->
getr regs 10 = w64 p ->
p mod 16 = 0 -> 0x10000 <= p -> p + 28 <= 0x5fc000 -> azs B p 28 ->
(p + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= p) -> (p + 28 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= p) ->
val_mem segs (mrestrict (w_H W) mem) (p + 24) 4 v ->
0 <= v < 2 ^ 32 -> (v = 0 \/ 2 ^ 31 <= v) ->
SRr segs W (cfg_at segs (BASE + AF_fr_check_no_loss_read) regs mem md)
  (aleafx_post B CNLR_STK regs ly S W mem md (fun _ => True)).
Proof.
intros W ly S regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv Hsign.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (gp4c_entry W ly S regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv) as [HS SHOK].
pose proof (ajournal_init segs B CNLR_STK [] ly S W regs mem md ch HPRE) as HJ.
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
paj_run_tok RUN HS HJ SHOK gp4c_Bspan. { awr_ok_tac. exact Usp. }
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
paj_run_tok RUN HS HJ SHOK gp4c_Bspan. { awr_ok_tac. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CNLR_STK <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
  by (intros a Ha Hno;
      match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
        rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by gp4c_nowr end;
      apply KEEP0; assumption).
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleafx_post.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply ajournal_gx_nil. apply (ajournal_materialize segs B LAWS Hsegs). exact HJ.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok segs _ Ev _ _ regs (gp4c_extra v) HS);
  [ split; [intros m Hm; rewrite !ew_ewset_other by lia; exact (proj1 HAE m Hm) | rewrite !ed_ewset; exact (proj2 HAE)]
  | vm_compute; reflexivity ] end.
+ cbn [ms_mem]. gp4c_pres.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP1 a Ha Hno)|].
  apply (writable_kept (w_H W) mem (ms_mem ms0) a). clear Ha Hno. revert a. gp4c_pres.
+ exact I.
Qed.
End gp4c.

(* ================================================================== phase p4 *)
Definition AF_gp4_mid : Z := 0x2828.    (* 0x84b6c: after the call (or its skip) *)
(* the callee-saved registers; and those of them the tail keeps (all but s4, s5) *)
Definition GP4_CS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition GP4_K2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv.
Definition gp4_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* 0x84b5c: the cell reads[q] at s5 (reg 21), its value the extra atom 32 *)
Definition gp4_c1_region : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition gp4_c1_facts : facts :=
  mkFacts [ (21%nat, mkAF (2 ^ 46) (2 ^ 47) 2); (32%nat, mkAF 0 1 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_gp4_c1 : sstate := mkSS AF_gn_c1 sr_atoms [gp4_c1_region] None gp4_c1_facts.
Definition gp4_c1_Bx : sv := SOff 33 0.
Definition gp4_c1_extra (rd : Z) : list word := map (Z_to_bv 64) [rd; SB].
(* 0x84b6c: no memory read; s5 (21) and s6 (22) decide the latch *)
Definition gp4_md_facts : facts :=
  mkFacts [ (21%nat, mkAF (2 ^ 46) (2 ^ 47) 2); (22%nat, mkAF (2 ^ 46) (2 ^ 47) 2);
            (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_gp4_md : sstate := mkSS AF_gp4_mid sr_atoms [] None gp4_md_facts.
Definition gp4_md_Bx : sv := SOff 33 0.
Definition gp4_md_extra : list word := map (Z_to_bv 64) [0; SB].
(* a register of the state after a run, with its symbolic value left raw *)
Ltac gp4_reg HS r H :=
  pose proof (st_ok_pi_restrict_reg (PI := PB_fr) _ _ _ _ (r : bv 5) HS) as H;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) (r : bv 5)) in
    change (sr_get (ss_regs ss) (r : bv 5)) with e in H end;
  cbn [ms_regs restrict mkst] in H.
Ltac gp4_U := apply bv_eq;
  lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) = _ =>
    change (bv_unsigned (sv_denot Ev e)) with (U Ev e) end.
Ltac gp4_off Q nn cc HEq :=
  rewrite Q; gp4_U;
  lazymatch goal with |- U ?Ev _ = _ =>
    rewrite (U_atom_off Ev nn _ cc ltac:(rewrite ?ew_ewset_other by lia; exact HEq)) by lia end;
  unfold w64; rewrite unsigned_lit_small by lia; lia.
Ltac gp4_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* a run over read-only regions leaves the memory as it was *)
Ltac gp4_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

Section gp4.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* the allocator instance (lib/B/W_kit.v): check_no_loss_read's walk reads the GOT slot of the shadow base and the
   shadow cell through it, and its pal_env places errno below kLowMemEnd *)
Hypothesis TL : PALib B.
(* g_s lies in the instance's zero-shadow ranges: check_no_loss_read's shadow check of &g_s[q] *)
Hypothesis HZS : GN_HZS B.
(* errno's place: the base's model obligation, verbatim *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* the slots the loop calls check_no_loss_read on have no pending record (relay_instance_gone drained them) *)
Hypothesis RIR : GN_RI_read RINV.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* the walk's facts, by name *)
Definition gp4_jr (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk.
Definition gp4_keep (cx : lfcx) (W : world segs) (mem : word -> option byte) (W' : world segs)
    (mem' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx - CNLR_STK <= a < lf_F cx) -> abyte_kept W mem W' mem' a.
Definition gp4_saved (cx : lfcx) (W : world segs) (mem : word -> option byte) : Prop :=
  forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r))).
(* g_s[j].pending.n, as check_no_loss_read's functional premise takes it *)
Definition gp4_vok (W : world segs) (mem : word -> option byte) (j : nat) : Prop :=
  exists v, val_mem segs (mrestrict (w_H W) mem) (rg_s fr_RG + ASRC * Z.of_nat j + 24) 4 v /\
    0 <= v < 2 ^ 32 /\ (v = 0 \/ 2 ^ 31 <= v).
(* the cells reads[j] the loop has still to read, and the slot behind each set one *)
Definition gp4_cells (cx : lfcx) (W : world segs) (mem : word -> option byte) (q : nat) : Prop :=
  forall j, (q <= j < 4)%nat -> exists rd, gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) rd /\
    (rd = 0 \/ (rd = 1 /\ gp4_vok W mem j)).

(* ---- small facts ---- *)
Lemma gp4_abk_refl : forall (W : world segs) mem a, abyte_kept W mem W mem a.
Proof. intros W mem a. split; [reflexivity | intros H; exact H]. Qed.
Lemma gp4_abk_trans : forall (W1 W2 W3 : world segs) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof. intros W1 W2 W3 m1 m2 m3 a [A1 A2] [B1 B2]. split; [rewrite B1; exact A1 | intros H; exact (B2 (A2 H))]. Qed.
Lemma gp4_keep_trans : forall cx (W1 W2 W3 : world segs) m1 m2 m3,
  gp4_keep cx W1 m1 W2 m2 -> gp4_keep cx W2 m2 W3 m3 -> gp4_keep cx W1 m1 W3 m3.
Proof. intros cx W1 W2 W3 m1 m2 m3 K1 K2 a Ha Hno. exact (gp4_abk_trans _ _ _ _ _ _ a (K1 a Ha Hno) (K2 a Ha Hno)). Qed.
Lemma gp4_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|].
  split; [exact H8|]. split; lia.
Qed.
Lemma gp4_reads01 : forall m j, gn_reads m j = 0 \/ gn_reads m j = 1.
Proof.
  intros m j. unfold gn_reads. destruct (nth j (lm_hs m) None) as [h|]; [|left; reflexivity].
  destruct (gn_src m (hs_fd h)) as [i|]; [|left; reflexivity].
  destruct (_ =? 0); [right | left]; reflexivity.
Qed.
(* a closed slot is 96 zero bytes: its pending.n reads 0 *)
Lemma gp4_zero4 : forall (mm : word -> option byte) a o,
  garr8 segs mm a (repeat 0 (Z.to_nat ASRC)) -> 0 <= o -> o + 4 <= ASRC -> val_mem segs mm (a + o) 4 0.
Proof.
  intros mm a o HZ Ho1 Ho2 k Hk.
  assert (Hj : (Z.to_nat o + k < length (repeat 0 (Z.to_nat ASRC)))%nat)
    by (rewrite repeat_length; unfold ASRC in *; lia).
  pose proof (garr8_mbyte segs mm a _ _ HZ Hj) as Hb. rewrite nth_repeat in Hb.
  replace (a + Z.of_nat (Z.to_nat o + k)) with (a + o + Z.of_nat k) in Hb by lia.
  rewrite Hb. f_equal.
  destruct k as [|[|[|[|k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
Qed.
Lemma gp4_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma gp4_cs_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r GP4_CS -> getr regs' r = getr regs r.
Proof.
  intros regs regs' HP r Hr. apply gp4_pres; [exact HP|]. unfold GP4_CS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?r] =>
       let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia |]).
  destruct Hr.
Qed.
Lemma gp4_k2_cs : forall r, In r GP4_K2 -> In r GP4_CS.
Proof.
  intros r Hr. unfold GP4_K2 in Hr. unfold GP4_CS. cbn [In] in Hr |- *.
  repeat (destruct Hr as [<- | Hr]; [repeat (first [left; reflexivity | right]) |]). destruct Hr.
Qed.
Lemma gp4_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.

(* ---- the frame (shadow sh) and the prefix, kept (A's p4 gp4_gframe_kept / gp4_prefix_kept) ---- *)
Lemma gp4_gframe_kept : forall cx sh FF (W W' : world segs) mem mem',
  gframe cx sh FF W mem -> length sh = 16%nat ->
  (forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a) ->
  lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= GK_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= GK_CEIL8 ->
  gframe cx sh FF W' mem'.
Proof.
  intros cx sh FF W W' mem mem' HFR Hlen KL KH HF1 HF2 HFF0 HFF1 HS0 HS1.
  unfold gframe in *. cbv zeta in *.
  destruct HFR as (A1 & REST).
  split.
  { intros o r Hin. apply (gk_sv8_kept W W' mem mem'); [|exact (A1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with
  | |- _ /\ _ => split
  | |- sv8 W' mem' _ _ =>
      apply (gk_sv8_kept W W' mem mem'); [intros x Hx; first [apply KH; lia | apply KL; lia] | assumption]
  | |- awr W' mem' _ _ =>
      apply (akept_awr W mem); [intros x Hx; first [apply KH; lia | apply KL; lia] | assumption]
  | |- garr8 _ _ _ _ =>
      apply (akept_garr8 W mem); [intros x Hx; rewrite Hlen in Hx; cbn in Hx; apply KL; lia | assumption]
  end.
Qed.
Lemma gp4_prefix_kept : forall cx m (W W' : world segs) mem mem' FF,
  gn_prefix_at cx m W mem FF -> (forall a, FF + 32 <= a < FF + 80 -> abyte_kept W mem W' mem' a) ->
  gn_prefix_at cx m W' mem' FF.
Proof.
  intros cx m W W' mem mem' FF (P1 & P2 & P3 & P4 & P5) HK.
  split; [intros i Hi; rewrite (proj1 (HK (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
  split; [rewrite (proj1 (HK (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
  split; [intros a Ha; rewrite (proj1 (HK a Ha)); exact (P3 a Ha)|].
  split; [exact P4 | exact P5].
Qed.

(* ---- the entry states of the two runs ---- *)
Lemma gp4_entry_c1 : forall (W : world segs) regs mem a rd,
  getr regs 21 = w64 a -> 2 ^ 46 <= a -> a + 4 <= 2 ^ 47 -> a mod 4 = 0 ->
  getr regs 27 = w64 SB ->
  0 <= rd <= 1 -> val_mem segs (mrestrict (w_H W) mem) a 4 rd ->
  st_ok_pi segs VAL (Eimg (Ereg regs (gp4_c1_extra rd))) ss_gp4_c1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_c1)) mem (seg_rom segs)))
  /\ sh_ok segs gp4_c1_Bx [] (Eimg (Ereg regs (gp4_c1_extra rd))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem a rd H21 Ha0 Ha1 Ha4 H27 Hrd HV. rewrite restrict_mkst_fx.
  assert (HSB : SB = 2147450880) by reflexivity.
  set (E := Eimg (Ereg regs (gp4_c1_extra rd))).
  assert (E21 : ew E 21 = Z_to_bv 64 a)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
  assert (E32 : ew E 32 = Z_to_bv 64 rd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U21 : bv_unsigned (ew E 21) = a) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = rd) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = SB) by (rewrite E33; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gp4_c1. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, gp4_c1_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ a 0 4 (SOff 32 0) rd);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
        | rewrite Z.add_0_r; exact HV].
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [gp4_c1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U21, U32, U33. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [lia | exact Ha4 | reflexivity].
  - unfold sh_ok. constructor.
Qed.
Lemma gp4_entry_md : forall (W : world segs) regs mem a b,
  getr regs 21 = w64 a -> getr regs 22 = w64 b -> getr regs 27 = w64 SB ->
  2 ^ 46 <= a -> a <= 2 ^ 47 -> a mod 4 = 0 -> 2 ^ 46 <= b -> b <= 2 ^ 47 -> b mod 4 = 0 ->
  st_ok_pi segs VAL (Eimg (Ereg regs gp4_md_extra)) ss_gp4_md
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gp4_mid)) mem (seg_rom segs)))
  /\ sh_ok segs gp4_md_Bx [] (Eimg (Ereg regs gp4_md_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem a b H21 H22 H27 Ha0 Ha1 Ha4 Hb0 Hb1 Hb4. rewrite restrict_mkst_fx.
  assert (HSB : SB = 2147450880) by reflexivity.
  set (E := Eimg (Ereg regs gp4_md_extra)).
  assert (E21 : ew E 21 = Z_to_bv 64 a)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
  assert (E22 : ew E 22 = Z_to_bv 64 b)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
  assert (E33 : ew E 33 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U21 : bv_unsigned (ew E 21) = a) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = b) by (rewrite E22; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = SB) by (rewrite E33; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gp4_md. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [gp4_md_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U21, U22, U33. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [lia | exact Ha4 | exact Hb4 | reflexivity].
  - unfold sh_ok. constructor.
Qed.

(* ---- 0x84b5c -> 0x84b6c: reads[q], and check_no_loss_read(&g_s[q]) when it is set ---- *)
Definition gp4_head_post (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gp4_mid) regs' mem' md' /\
    gp4_jr cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_CS -> getr regs' r = getr regs r) /\
    gp4_keep cx W mem W' mem'.
Lemma gp4_head : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat) rd,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  gp4_jr cx fpos ly S W mem md kk -> gp4_saved cx W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat q) rd -> (rd = 0 \/ (rd = 1 /\ gp4_vok W mem q)) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_head_post cx fpos ly S W regs mem).
Proof.
  intros cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R27 R20 R21 HRD Hrd.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx _ ly S W mem md kk fpos HB HJ eq_refl) as HN.
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
  unfold gp4_jr in HJ.
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
  paj_run_tok RUN HS HJ SHOK gp4_Bspan.
  { apply awr_ok_x_cons; [intros x Hx; cbn [gp4_c1_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia
                         | apply awr_ok_x_nil]. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* reads[q] = 0: no call *)
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_gp4_mid.
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
    apply SRr_ret. unfold gp4_head_post.
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
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_fr_check_no_loss_read.
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
    destruct (gn_afn_pre B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG LS RINV
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
    { exact (gp4c_cnlr B LAWS TL W ly S rc0 mem mdc ch (rg_s fr_RG + ASRC * Z.of_nat q) v HPREc Q10v
               Hp16 ltac:(lia) ltac:(lia) Hzs ltac:(right; lia) ltac:(right; lia) Mv Rv Hsign). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HKEEP & _).
    rewrite Hsp1 in HJc, HKEEP.
    (* check_no_loss_read's journal inside this function's: W2's ajournal_gx_sub at G_fr, lifted from G = [] *)
    assert (HJc' : ajournal_gx segs B G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono segs B [] G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc []
                ly S W2 mem2 md2 0 _ HJc).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem mdc kk
       CNLR_STK (lf_F cx) 0 [] [] [] ly S W2 mem2 md2 0 HJ HJc'
       ltac:(unfold CNLR_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply SRr_ret. unfold gp4_head_post.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1;
            change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)); reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (gp4_cs_pres rc0 regs2 HP2 r Hr); exact (KR r Hr)|].
    intros a Ha Hno. exact (HKEEP a Ha Hno).
Qed.

(* ---- 0x84b6c -> 0x84b5c (q + 1 < 4) or 0x84b78 (q = 3) ---- *)
Definition gp4_tail_post (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (q : nat) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md' kk', gp4_jr cx fpos ly S W mem md' kk' /\
    (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    ((((q + 1) < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_c1) regs' mem md' /\
      getr regs' 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat (q + 1)) /\
      getr regs' 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat (q + 1))) \/
     ((q + 1)%nat = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem md')).
Lemma gp4_tail : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat),
  gp4_jr cx fpos ly S W mem md kk -> (q < 4)%nat -> 2 ^ 46 <= lf_F cx -> lf_F cx + 256 <= 2 ^ 47 ->
  lf_F cx mod 32 = 0 ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) -> getr regs 27 = w64 SB ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gp4_mid) regs mem md) (gp4_tail_post cx fpos ly S W regs mem q).
Proof.
  intros cx fpos ly S kk W regs mem md q HJ Hq HF0 HF1 HF32 R20 R21 R22 R27.
  unfold gp4_jr in HJ.
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
  paj_run_tok RUN HS HJ SHOK gp4_Bspan. { apply awr_ok_x_nil. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* s5 + 4 <> s6: back to the head *)
    rewrite branch_ne_U, (U_atom_off E 21 _ 4 E21), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq1 : ((q + 1) < 4)%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [discriminate Hc | lia]. }
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_gn_c1. { apply awr_ok_x_nil. }
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
    apply SRr_ret. unfold gp4_tail_post. split; [reflexivity|].
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
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_gn_t0. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs gp4_md_extra) Ev)
        by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE n Hn)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE2
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. right.
    split; [exact Hq4|].
    unfold cfg_at. change (w64 (fr_B0 + AF_gn_t0)) with (Z_to_bv 64 (BASE + AF_gn_t0)). reflexivity.
Qed.

(* ---- the loop, by induction on the slots left ---- *)
Definition gp4_loop_post (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem' md' /\
    gp4_jr cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    gp4_keep cx W mem W' mem'.
Lemma gp4_loopX : forall (k : nat) cx fpos ly S (q : nat) kk (W : world segs) regs mem md,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> k = (4 - q)%nat -> (q < 4)%nat ->
  gp4_jr cx fpos ly S W mem md kk -> gp4_saved cx W mem -> gp4_cells cx W mem q ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 -> getr regs 27 = w64 SB ->
  getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_loop_post cx fpos ly S W regs mem).
Proof.
  induction k as [|k IH]; intros cx fpos ly S q kk W regs mem md HB Hk Hq HJ HSV HCL R2 R3 R4 R8 R27 R20 R21 R22;
    [lia|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx _ ly S W mem md kk fpos HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  (* g_s's cells (low image memory) are far below the callee's window [F - 16, F) *)
  assert (HRS : rg_s fr_RG = 6131296) by reflexivity.
  pose proof YM05.alloc_ceiling_value as AC.
  pose proof gk_ceil_lo as HCL0.
  destruct (HCL q ltac:(lia)) as (rd & HRD & Hrd).
  eapply SRr_bind;
    [exact (gp4_head cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R27 R20 R21 HRD Hrd)|].
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & KP1).
  eapply SRr_bind.
  { apply (gp4_tail cx fpos ly S kk1 W1 regs1 mem1 md1 q HJ1 Hq); [lia | lia | exact HF32 | | | |].
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
Lemma gp4_c1_t0 : forall q cx t m m1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GC1 B MT G_fr fr_FP LS RINV cx t m m1 q W c ->
  SRr segs W c (GT0 B MT G_fr fr_FP LS RINV cx t m m1).
Proof.
  intros q cx t m m1 W c HB HC.
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & HGST & HGD & HLSx & HKR & H24 & R20 & R21 & R22 & Hq &
    HCL & HAWR & H208 & HPF).
  pose proof HGST as ((HJ & HFR & HFL & H16 & H144 & H88 & HIN & HRV & HJT) & HMOD & HSEP).
  pose proof HKR as (K2 & K8 & K9 & K18 & K19 & K27 & K3 & K4).
  pose proof HGD as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx _ ly S W mem md kk fpos HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  pose proof YM05.alloc_ceiling_value as AC. pose proof gk_ceil_lo as HCL0.
  pose proof HERR as (HE0 & HE1).
  assert (HSTK : LLVMF_STK = 32768) by reflexivity.
  assert (HCEIL : GK_CEIL8 = alloc_ceiling + 8) by reflexivity.
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HCS : CNLR_STK = 16) by reflexivity.
  assert (Hq4 : (q < 4)%nat) by exact Hq.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx).
  { destruct HB as (_ & HPRE0). unfold fr_lib_pre_cf in HPRE0. symmetry. tauto. }
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
  { exact (gp4_loopX (4 - q) cx fpos ly S q kk W regs mem md HB eq_refl Hq4 HJ (proj1 HFR) HCL'
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
  pose proof (gk_amodel_kept B LAWS ly S W mem md W' mem' m1 HAR HMOD HE0 ltac:(lia) KL) as HMOD'.
  pose proof (gk_ainput_kept B LAWS cx ly S W mem md W' mem' HAR HIN HlenP KL) as HIN'.
  pose proof (gk_rom_kept W W' mem mem' HRV KL) as HRV'.
  pose proof (gk_jt_kept W W' mem mem' HJT KL) as HJT'.
  exists regs', mem', md', ly, S, kk', fpos. split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD' | exact HSEP]].
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

End gp4.
