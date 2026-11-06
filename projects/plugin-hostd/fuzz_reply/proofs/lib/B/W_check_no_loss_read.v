(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   check_no_loss_read, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation:
   VERDICT.md (sha256 810ca1df9ca9; internal record)), after lib/A/W_check_no_loss_read.v (0040bb7650f), in the form of the
   cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v and lib/A/ACbk.v. *)
(* check_no_loss_read(E) at 0x85dd4 (image B; 0x85904 in A) reads the four bytes at E+24 behind an ASan shadow
   check and aborts when they are a positive int.  E is &g_s[j], a .bss global: the shadow check is decided inside
   paj_run_tok from the shadow entry of the struct, whose shadow is zero because it lies in one of the instance's
   zero-shadow ranges (azs, W_contract.v; AR_zshadow_law); the abort arm is refuted from the contract's functional
   half.  B's two UBSan traps (both to `unimp` at 0x85e1c; UBSan is trap mode in this pin) are the null check
   `beqz a0` (0x85ddc) and the alignment check `andi a1,a0,7; bnez a1` (0x85de0-0x85de4) of E: the runner decides
   both from the seat's fact on E's atom (lib/B/W_traps.v recipe R1, al2 4 from the contract's p mod 16 = 0), so
   neither is a branch case and no W_traps lemma is cited.  At the end of the file, cnlr_azs_g_s* discharge the
   contract's premise azs B p 28 at the start-up instance for every real argument p = g_s + 96 j, j < 4. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_journal W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0m YD2l W_rep.
(* route R: the leaf contract twins (a Theorem Labs lane's W_contract_leaf_xR.v, NAMES.md (sha256 4a0eb3e6fe06; internal record)) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_leaf_xR.
(* RelocB-2's sink-instance guard (lib/B/ReplyGuardB.v): this file states its sink as the Context SK below *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_check_no_loss_read : Z := AF_fr_check_no_loss_read.
Definition A_check_no_loss_readP : Z := BASE + A_check_no_loss_read.
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): check_no_loss_read over any allocator
   relation ARx with its laws, stated as W_contract_x.cnlr_spec_x.  The Section hypotheses beyond the AR walk's: PST /
   ARx / hl / LAWS (the generic relation) and HP0 (the unit's hidden-head set is empty in every ARx state: fuzz_reply
   calls no poison routine; a Theorem Labs lane's ruling).  The struct's shadow comes from the zero-shadow law
   (azs_range_addressable_x), not from a heap block, so HP0 goes unused and is not in the theorem. ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let HG0 : gx_ok SEGS B [] := gx_ok_nil SEGS B.
Let RUN := paj_run_x_x B PST ARx LAWS [] HG0 0 [].
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx [] 0 []).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
(* awr_ok_tac exists in Reusable.YCbq and in lib/B.YCbq: call it by full name *)
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                       | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
Definition Bx : sv := SOff 33 0.
Definition CNLR_OBJ : Z := 28.
(* the seat: E = a0 is atom 10 with lo 4096 (decides the null trap `beqz a0`, 0x85ddc) and al2 4 (decides the
   alignment trap `andi a1,a0,7; bnez a1`, 0x85de0-0x85de4); hi is the ASan user ceiling *)
Definition cnlr_regions : smem :=
[ stack_region CNLR_STK; got_regionP; bcell_regionP 33;
YP09.mkRegion (Some 10%nat) 0 CNLR_OBJ 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 32 0))] ].
Definition cnlr_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 4);
(32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_cnlr : sstate := mkSS A_check_no_loss_read sr_atoms cnlr_regions None cnlr_facts.
Definition cnlr_SH : list shent := [ mkSHE 10 0 CNLR_OBJ ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition cnlr_extra (v : Z) : list word := map (Z_to_bv 64) [v; SB].
Lemma cnlr_entry_x : forall W ly S Hp regs mem md ch p v,
afn_pre_x SEGS B ARx CNLR_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 p ->
p mod 16 = 0 -> 0x10000 <= p -> p + 28 <= 0x5fc000 -> azs B p 28 ->
(p + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= p) -> (p + 28 <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= p) ->
val_mem SEGS (mrestrict (w_H W) mem) (p + 24) 4 v ->
0 <= v < 2 ^ 32 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cnlr_extra v))) ss_cnlr
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_no_loss_readP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx cnlr_SH (Eimg (Ereg regs (cnlr_extra v))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNLR_STK = 16) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cnlr_extra v))). pose proof pa_B_ok as HBASE.
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
- unfold ss_cnlr, A_check_no_loss_readP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cnlr_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite EC, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EC) by (pose proof (pa_val_range (A_OBJ 30)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat p E10) by lia. unfold CNLR_OBJ. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ p 24 4 _ v); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
+ apply pairwise_disjoint_of_extents. unfold cnlr_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat p E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EC) by (pose proof (pa_val_range (A_OBJ 30)); lia). cbn [base_val]. rewrite Usp.
unfold CNLR_OBJ.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hp0 Hp1 Hd0 Hd30 C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cnlr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hp0 Hp1 Hp16 Hal16 C1 C3 WS Hstk0 Rv. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cnlr_SH. constructor; [|constructor].
(* the struct's shadow is zero: it lies in one of the instance's zero-shadow ranges (azs) *)
assert (UBx : U E Bx = SHADOW_OFF).
{ unfold U, Bx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity. }
assert (Up : U E (SOff 10 0) = p).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity. }
split; cbn [she_m she_lo she_hi].
+ rewrite UBx, Up, Z.add_0_r. unfold CNLR_OBJ. rewrite Z.sub_0_r.
  exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md p 28 HAR Hzs).
+ unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up. unfold CNLR_OBJ, SHADOW_OFF. intros a Ha. lia.
Qed.
Theorem pb_check_no_loss_read_x : cnlr_spec_x B PST ARx A_check_no_loss_readP.
Proof.
intros W ly S Hp regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv Hsign.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (cnlr_entry_x W ly S Hp regs mem md ch p v HPRE H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd30 Mv Rv) as [HS SHOK].
assert (HJ : AJG CNLR_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem md 0)
by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx CNLR_STK [] ly S Hp W regs mem md ch HPRE)).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs (cnlr_extra v))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cnlr_extra v)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_check_no_loss_readP) with (Z_to_bv 64 A_check_no_loss_readP).
unfold A_check_no_loss_readP, A_check_no_loss_read.
(* 0x85dd4-0x85e08: the frame, the two UBSan traps on E (decided by the runner from atom 10's fact) and the shadow
   check of E+24 (decided from cnlr_SH), up to the abort test *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. exact Usp. }
(* 0x85e0c bgtz a0: the abort arm *)
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* the abort arm: the word at p+24, read as a signed int, is positive.  The contract's functional
   half says it is 0 or has its sign bit set, so this arm is unreachable. *)
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
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. exact Usp. }
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleaf_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs). apply ajournal_gx_nil_x. exact HJ.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (cnlr_extra v) HS);
  [ split; [intros m Hm; rewrite !ew_ewset_other by lia; exact (proj1 HAE m Hm) | rewrite !ed_ewset; exact (proj2 HAE)]
  | vm_compute; reflexivity ] end.
+ exact I.
+ intros a Ha. cbn [ms_mem]. pres_chain.
(* errno: an image byte below kLowMemEnd, so outside the frame both runs write *)
+ intros jj Hjj. cbn [ms_mem].
  pose proof (pal_env B TL) as ((He0 & He1) & _). pose proof asan_consts as (C1 & _).
  pose proof Hstk as (_ & _ & Hc1 & Hc2 & _). unfold kLowMemEnd in He1. unfold CNLR_STK in Hc2.
  transitivity (aview SEGS (w_H W) (ms_mem ms) (as_errno B + jj)).
  * lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf) end; [lia|].
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia;
       rewrite ?Usp in Hr; lia|]).
    destruct Hin.
  * lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) mem) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf) end; [lia|].
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia;
       rewrite ?Usp in Hr; lia|]).
    destruct Hin.
Qed.

(* ---- route R (group G7-leaf-AB, for a Theorem Labs lane's top_x at R): pb_check_no_loss_read_x at a world relation R, a LIFT
   with no re-proof.  The strict SRr run becomes SRrG SEGS R by SRr_SRrG (WLE_R), and the post's journal
   (aleaf_post_x -> a Theorem Labs lane's aleaf_post_xR) goes to R by ajournal_xR_mono; W_contract_leaf_xR.v
   cnlr_spec_xR_of_x is those two steps. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Theorem pb_check_no_loss_read_xR : cnlr_spec_xR B PST ARx R A_check_no_loss_readP.
Proof. apply (cnlr_spec_xR_of_x B PST ARx R WLE_R). exact pb_check_no_loss_read_x. Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_check_no_loss_read's statement is the AR
   walk's, byte-identical, now a corollary of pb_check_no_loss_read_x at ARx := ARi0 (cgif's AR with the head set
   empty), PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's ruling (a)) in place of LAWS: the
   instance builds it once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridge is W_contract_x
   cnlr_spec_x_AR0. ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Theorem pb_check_no_loss_read : cnlr_spec B (BASE + AF_fr_check_no_loss_read).
Proof.
change (cnlr_spec B A_check_no_loss_readP).
apply cnlr_spec_x_AR0.
eapply pb_check_no_loss_read_x; eassumption.
Qed.
End cAR.
End b.
End a.
(* cnlr_spec's premise `azs B p 28` at the start-up instance, for every real argument p = &g_s[j] = g_s + 96 j
   (j < 4: g_s is 4 x struct source of 96 bytes, W_rep.v rg_s; 0x5d8e60 on both images).  The start-up record
   (YF0m.v TfibSyms) pins as_zero_shadow B = Tfib_zero_shadow (ts_zsh), and that table holds g_s's own range
   (0x5d8e60, 0x180), which covers [g_s + 96 j, g_s + 96 j + 28) for each j: the last one ends at 0x5d8f9c. *)
Lemma cnlr_azs_g_s_zs : forall B, as_zero_shadow B = YF0m.Tfib_zero_shadow -> forall j, 0 <= j < 4 ->
azs B (W_rep.rg_s W_rep.fr_globals + 96 * j) 28.
Proof.
intros B HZ j Hj. exists (0x5d8e60, 0x5d8fe0 - 0x5d8e60). rewrite HZ. split.
- unfold YF0m.Tfib_zero_shadow. cbn [In]. do 8 right. left. reflexivity.
- cbn [fst snd]. unfold W_rep.fr_globals. cbn [W_rep.rg_s].
  change ((0x5d8fe0 - 0x5d8e60) / 8 * 8) with 0x180. split; [reflexivity | lia].
Qed.
Lemma cnlr_azs_g_s : forall B, YF0m.TfibSyms B -> forall j, 0 <= j < 4 ->
azs B (W_rep.rg_s W_rep.fr_globals + 96 * j) 28.
Proof. intros B TB. exact (cnlr_azs_g_s_zs B (YF0m.ts_zsh B TB)). Qed.
(* the B top's RG is fr_globals_b (W_asm.v), whose g_s is the same address *)
Lemma cnlr_azs_g_s_b : forall B, YF0m.TfibSyms B -> forall j, 0 <= j < 4 ->
azs B (W_rep.rg_s W_rep.fr_globals_b + 96 * j) 28.
Proof. exact cnlr_azs_g_s. Qed.
(* at the instance itself, the B top's TB = YD2l.TfibB *)
Corollary cnlr_azs_g_s_tfib : forall j, 0 <= j < 4 -> azs YD2l.TfibB (W_rep.rg_s W_rep.fr_globals_b + 96 * j) 28.
Proof. exact (cnlr_azs_g_s_b YD2l.TfibB YD2l.TfibB_syms). Qed.
