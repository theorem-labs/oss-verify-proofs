(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the entry segment of fuzz_reply's send_line walk on IMAGE B
   (fuzz_reply.asan-ubsan 0x82854), in the form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a cut
   at a loop head) and lib/A/ACfj.v (segments joined at cut points).  Structure ported from image A's
   lib/A/W_send_line_entry.v (a working branch 9367674296a, sl_entry) and from the old image-B walk
   a working branch 37280b674f71 lib/B/Prog/send_line_front.v (the entry to the loop top 0x828f8). *)
(* The entry runs the prologue (13 saved registers into the 144-byte frame at 40(sp) .. 136(sp)), the three early
   tests of relay.c:68-70 (g_client < 0, len = 0, g_client_broken) and the setup of the loop's registers
   (fuzz_reply.c:282-290: sent = 0, the flag line <> 0, EINTR, the shadow base, the kept auipc registers and the five
   spilled ones at 0(sp) .. 32(sp)).  A test that holds goes to the epilogue X, and W_send_line_cx.v's sl_epi returns
   with the model's off post; else the state at the loop head L is SLI with sent = 0 and the loop segment (the
   hypothesis sl_loop_stmt) finishes.  No call, no shadow check and no UBSan check before L: the globals are read
   through their objects (PLdHi), and the only stores are into the frame. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin W_traps W_send_line_rb W_send_line_cx.
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
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* placement: the two objects the entry reads by PLdHi *)
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
(* placement: the cells send_line reads or writes are pairwise disjoint (W_send_line_cx.v HRGD, same text) *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Let RUN := paj_run_x B LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* ---- The entry state at send_line (0x82854). ----
   Atoms: 32 = the 4 bytes of g_client, 33 = g_client_broken, 34 = the shadow base SB. *)
Definition BxE : sv := SOff 34 0.
Definition ent_regions : smem :=
[ stack_region SL_FRAME; got_regionP; bcell_regionP 34;
  YP09.mkRegion (Some (A_OBJ 9)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
  YP09.mkRegion (Some (A_OBJ 10)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition ent_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF SB SB 0) ] [] [].
Definition ss_ent : sstate := mkSS A_send_line sr_atoms ent_regions None ent_facts.
Definition ent_extra (cl br : Z) : list word := map (Z_to_bv 64) [cl; br; SB].
Lemma sl_ent_entry : forall W ly S regs mem md ch c O mx no cap out,
afn_pre SEGS B SL_STK ly S W regs mem md ch ->
aout_at B RG ly S W mem c O mx no cap out ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ent_extra (ct_cl c mod 2 ^ 32) (ct_br c)))) ss_ent
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_send_line)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch c O mx no cap out HPRE HOUT.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & Mcl & _ & Mbr & _ & _ & _ & _ & _ & _ & _ & _ & Hcl & Hbr & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SL_STK = 16528) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ent_extra (ct_cl c mod 2 ^ 32) (ct_br c)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (ct_cl c mod 2 ^ 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (ct_br c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO9 : ew E (A_OBJ 9) = Z_to_bv 64 (VAL (A_OBJ 9))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO10 : ew E (A_OBJ 10) = Z_to_bv 64 (VAL (A_OBJ 10))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 9 ltac:(lia)) as HclR. pose proof (pa_obj_img 10 ltac:(lia)) as HbrR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
pose proof (Z.mod_pos_bound (ct_cl c) (2 ^ 32) ltac:(lia)) as Rcl.
unfold ss_ent. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ent_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. unfold SL_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
    [cbn [sv_denot]; rewrite EO30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 BxE SB);
    [cbn [sv_denot BxE]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 9) (VAL (A_OBJ 9)) EO9) by (pose proof (pa_val_range (A_OBJ 9)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 9)) 0 4 (SOff 32 0) (ct_cl c mod 2 ^ 32));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r, HV9. exact Mcl.
  + rewrite (VB (A_OBJ 10) (VAL (A_OBJ 10)) EO10) by (pose proof (pa_val_range (A_OBJ 10)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 10)) 0 1 (SOff 33 0) (ct_br c));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r, HV10. exact Mbr.
- apply pairwise_disjoint_of_extents. unfold ent_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
  rewrite (VB (A_OBJ 9) (VAL (A_OBJ 9)) EO9) by (pose proof (pa_val_range (A_OBJ 9)); lia).
  rewrite (VB (A_OBJ 10) (VAL (A_OBJ 10)) EO10) by (pose proof (pa_val_range (A_OBJ 10)); lia).
  cbn [base_val]. rewrite Usp. rewrite HV9, HV10.
  pose proof HRGD as ((D1 & D2 & D3 & _) & (D4 & D5 & _) & (D6 & _) & _).
  rewrite <- HV9, <- HV10 in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj in *. cbn [fst snd] in *. unfold SL_FRAME.
  revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HclR HbrR D1 D2 D3 D4 D5 D6. clear.
  unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ent_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Rcl Hbr. clear.
  unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Ltac w_in := repeat (first [left; reflexivity | right]).
(* ---- What the entry's runs keep. ----  They store only into the frame [sp0 - 144, sp0), which lies above
   alloc_ceiling, so every byte below alloc_ceiling keeps its view, and presence only grows. *)
Lemma keep_step : forall E rs (W : world SEGS) mem m1 m2 sp0,
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
(forall a, in_wrange E rs a -> sp0 - SL_FRAME <= a < sp0) -> alloc_ceiling <= sp0 - SL_FRAME ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) /\
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m2).
Proof.
intros E rs W mem m1 m2 sp0 HF HGr Hwr Hlo KL GR. pose proof asan_consts as (C1 & _). split.
- intros a Ha. rewrite <- (KL a Ha).
  apply (aview_kept_out E rs (w_H W) m1 m2 HF a ltac:(lia)). intros Hw. apply Hwr in Hw. lia.
- intros x Hx. apply HGr. apply GR. exact Hx.
Qed.
Ltac wr_frame Usp :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); cbn [ss_mem add_cond ss_ent ent_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP] in Hr;
   rewrite ?Usp in Hr; unfold SL_FRAME in *; lia|]);
destruct Hin.
Lemma kept_lo : forall (W : world SEGS) mem m' a,
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem x) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m') ->
0 <= a < alloc_ceiling -> abyte_kept W mem W m' a.
Proof.
intros W mem m' a HK HGr Ha. split; [exact (HK a Ha)|].
unfold arm. apply writable_kept. intros Hp. exact (apresent_grows _ _ _ _ HGr Hp).
Qed.
(* Every byte of aout's footprint lies below alloc_ceiling: the globals in the image, the g_out block in the heap. *)
Lemma aout_fp_low : forall ly S W mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (GL : forall x l, In (x, l) (G_SL B RG) -> x <= a < x + l -> 0 <= a < alloc_ceiling).
{ intros x l Hin Hx.
  assert (HI : inG (G_SL B RG) a) by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI). lia. }
assert (GO : forall x l, In (x, l) [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] -> x <= a < x + l ->
  0 <= a < alloc_ceiling).
{ intros x l Hin Hx.
  assert (HI : inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HGO HI). lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- apply (GO (rg_send_max RG) 8); [w_in | lia].
- apply (GL (rg_nout RG) 8); [unfold G_SL; w_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_SL; w_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_SL; w_in | lia].
- apply (GO (rg_client RG) 4); [w_in | lia].
- apply (GL (rg_client_broken RG) 1); [unfold G_SL; w_in | lia].
- apply (GO (rg_send_dead RG) 1); [w_in | lia].
- apply (GL (rg_send_eintr RG) 1); [unfold G_SL; w_in | lia].
- apply (GL (as_errno B) 4); [unfold G_SL; w_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  destruct (al_blocks _ _ LAWS ly S W mem md out cap HAR Hin) as (_ & H4096 & Hcl & _).
  pose proof (req_size_pos cap ltac:(lia)). lia.
Qed.
(* The bytes of the line lie below alloc_ceiling: in a live block, or in the image. *)
Lemma line_low : forall ly S W mem md out line len,
AR SEGS B ly S W mem md -> sl_line_ok B ly S out line len ->
forall a, line <= a < line + len -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md out line len HAR HL a Ha. pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct HL as [-> | [(q & m & Hin & _ & Hq & Hqm) | (Himg & _ & _)]].
- lia.
- destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hin) as (_ & H4096 & Hcl & _).
  pose proof (req_size_pos m). lia.
- pose proof (pa_segs_low a (Himg a Ha)). lia.
Qed.
(* A line of positive length starts above 0: a live block starts at 4096 or above, the image at 0x10000. *)
Lemma line_pos : forall ly S W mem md out line len,
AR SEGS B ly S W mem md -> sl_line_ok B ly S out line len -> 0 < len -> 0 < line.
Proof.
intros ly S W mem md out line len HAR HL Hl.
destruct HL as [-> | [(q & m & Hin & _ & Hq & Hqm) | (Himg & _ & _)]].
- lia.
- destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hin) as (_ & H4096 & _). lia.
- pose proof (pa_img_range line (Himg line ltac:(lia))). lia.
Qed.
Lemma aout_perm : forall ly S W mem c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out -> exists rest, Permutation (ablocks B ly S) (aout_blks cap out ++ rest).
Proof.
intros ly S W mem c O mx no cap out HOUT.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks. destruct (cap =? 0) eqn:Hc0.
- exists (ablocks B ly S). reflexivity.
- destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply in_split in Hin as (l1 & l2 & Heq). exists (l1 ++ l2). rewrite Heq. cbn [app].
  apply Permutation_sym, Permutation_middle.
Qed.
Lemma aout_blks_in : forall ly S W mem c O mx no cap out,
aout_at B RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W mem c O mx no cap out HOUT b Hb.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|]. destruct Hb as [<- | []].
destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin].
Qed.
(* aout_at and the line move from the entry memory to a memory the entry's runs left. *)
Lemma aout_moved : forall ly S W mem md m' c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem x) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m') ->
aout_at B RG ly S W m' c O mx no cap out.
Proof.
intros ly S W mem md m' c O mx no cap out HAR HOUT KL GR.
apply (aout_at_kept B RG ly S W mem ly S W m' c O mx no cap out HOUT).
- intros r Hr a Ha. apply (kept_lo W mem m' a KL GR). exact (aout_fp_low ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha).
- exact (aout_blks_in ly S W mem c O mx no cap out HOUT).
Qed.
Lemma rom_moved : forall (W : world SEGS) mem m',
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem x) ->
rom_view SEGS W mem -> rom_view SEGS W m'.
Proof.
intros W mem m' KL HR a Ha. pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hlo : 0 <= a < alloc_ceiling).
{ destruct Ha as (sg & Hsg & _ & Hr). pose proof (pa_segs_low a ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
rewrite (KL a Hlo). exact (HR a Ha).
Qed.
Lemma line_moved : forall ly S W mem md m' out line Bl,
AR SEGS B ly S W mem md -> sl_line_ok B ly S out line (Z.of_nat (length Bl)) ->
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem x) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m') ->
garr8 SEGS (arm W mem) line (bzs Bl) -> garr8 SEGS (arm W m') line (bzs Bl).
Proof.
intros ly S W mem md m' out line Bl HAR HL KL GR HB. apply (akept_garr8 W mem); [|exact HB].
intros x Hx. unfold bzs in Hx. rewrite length_map in Hx.
apply (kept_lo W mem m' x KL GR). exact (line_low ly S W mem md out line _ HAR HL x Hx).
Qed.

(* ---- The three tests, read off the symbolic conditions. ---- *)
Lemma bltz_cl : forall E (cl : Z), ew E 32 = Z_to_bv 64 (cl mod 2 ^ 32) -> (cl = 3 \/ cl = -1) ->
branch_taken BC_LT (sv_denot E (SExt true 32 (SOff 32 0))) (sv_denot E (SLit 0)) = (cl <? 0).
Proof.
intros E cl H32 Hcl. cbn [branch_taken]. rewrite bv_lts_signed.
assert (Hz : bv_signed (sv_denot E (SLit 0)) = 0) by reflexivity. rewrite Hz.
assert (Hsx : bv_unsigned (sv_denot E (SExt true 32 (SOff 32 0))) = sx32 (cl mod 2 ^ 32)).
{ rewrite U_sext32'. f_equal. pose proof (Z.mod_pos_bound cl (2 ^ 32) ltac:(lia)). exact (U_atom E 32 _ H32 ltac:(lia)). }
destruct Hcl as [-> | ->].
- change (3 mod 2 ^ 32) with 3 in Hsx. rewrite sx32_small in Hsx by lia.
  rewrite bv_signed_small by (rewrite Hsx; lia). rewrite Hsx. reflexivity.
- change (-1 mod 2 ^ 32) with (2 ^ 32 - 1) in Hsx.
  assert (Hhi : sx32 (2 ^ 32 - 1) = 2 ^ 64 - 1) by reflexivity. rewrite Hhi in Hsx.
  rewrite bv_signed_hi by (rewrite Hsx; lia). rewrite Hsx. reflexivity.
Qed.
Lemma beqz_len : forall E (len : Z), ew E 11 = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff 11 0)) (sv_denot E (SLit 0)) = (len =? 0).
Proof. intros E len H Hl. rewrite branch_eq_U, (U_atom E 11 len H Hl), U_lit by lia. reflexivity. Qed.
Lemma bnez_br : forall E (br : Z), ew E 33 = Z_to_bv 64 br -> (br = 0 \/ br = 1) ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 33 0) (SLit 1))) (sv_denot E (SLit 0)) = negb (br =? 0).
Proof.
intros E br H Hb. rewrite branch_ne_U, U_and_lit, (U_atom E 33 br H), U_lit by lia.
destruct Hb as [-> | ->]; reflexivity.
Qed.

(* ---- The frame's 13 saved registers, read off the stack region of a symbolic state. ---- *)
Definition sl_saved_atoms : list nat := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%nat.
Lemma saved_of_region : forall E (W : world SEGS) memX regs lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W) memX) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
(forall i, (i < 13)%nat -> In (YP09.mkChunk (-104 + 8 * Z.of_nat i) (CVal 8 (SOff (nth i sl_saved_atoms 0%nat) 0))) cs) ->
(forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
sl_saved W memX (bv_unsigned (ew E 2) - SL_FRAME) regs.
Proof.
intros E W memX regs lo hi wlo whi cs HR Hin EREG i Hi.
assert (Hew : ew E (nth i sl_saved_atoms 0%nat) = getr regs (nth i SL_SAVED 0%bv)).
{ apply EREG; (do 13 (destruct i as [|i]; [first [reflexivity | cbn [nth sl_saved_atoms]; lia] |])); lia. }
replace (bv_unsigned (ew E 2) - SL_FRAME + 40 + 8 * Z.of_nat i) with (bv_unsigned (ew E 2) + (-104 + 8 * Z.of_nat i))
  by (unfold SL_FRAME; lia).
apply (slot_of_region E _ _ cs lo hi wlo whi _ (SOff (nth i sl_saved_atoms 0%nat) 0) _ HR eq_refl (Hin i Hi)).
- cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (nth i SL_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Ltac saved_in := let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi; do 13 (destruct i as [|i]; [cbn; w_in|]); lia.

(* ---- An early return: g_client < 0, len = 0 or g_client_broken.  The epilogue restores the frame and the model's
   post is the off one: nothing of the stream changes, and g_out's block is the old one (sl_post's last conjunct). ---- *)
Lemma sl_off_exit : forall W ly S regs mem md ch c O mx no cap out Bl regsX memX mdX,
afn_pre SEGS B SL_STK ly S W regs mem md ch ->
aout_at B RG ly S W mem c O mx no cap out ->
send_line_c.send_off (ct_cl c) (ct_br c) (Z.of_nat (length Bl)) = true ->
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S W mem md [] ly S W memX mdX 0 ->
spZ regsX = spZ regs - SL_FRAME -> getr regsX 3 = getr regs 3 -> getr regsX 4 = getr regs 4 ->
sl_saved W memX (spZ regs - SL_FRAME) regs ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) memX a = aview SEGS (w_H W) mem a) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) memX) ->
SRr SEGS W (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX)
(sl_post B MT RG regs ly S W mem md c O mx no cap out Bl).
Proof.
intros W ly S regs mem md ch c O mx no cap out Bl regsX memX mdX HPRE HOUT Hoff HJ Hsp H3 H4 HSV KL GR.
pose proof HPRE as (HAR & Hra & _).
apply (sl_epi B RG LAWS HG W ly S mem md (spZ regs) _ ly S W regsX memX mdX 0 regs _ HJ eq_refl Hsp H3 H4 Hra HSV).
intros regs' mem' md' HP Hm' HJ'.
assert (Hlive : sl_live c (Z.of_nat (length Bl)) = false)
  by (unfold sl_live, send_line_c.send_live; rewrite Hoff; reflexivity).
assert (KL' : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a)
  by (intros a Ha; rewrite (aview_eq_of SEGS (w_H W) memX mem' a (Hm' _)); exact (KL a Ha)).
assert (GR' : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem'))
  by (intros x Hx; rewrite Hm'; exact (GR x Hx)).
exists ly, S, regs', mem', md', 0, out.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP|].
split; [intros a _ _ _ Hp; exact (apresent_grows _ _ _ _ GR' Hp)|].
unfold sl_cost, sl_cap, sl_O, sl_no. rewrite Hlive.
split; [exact (mo_le_refl MT MTL S)|].
change (send_line_b_c.send_line_cap false mx no cap (Z.of_nat (length Bl))) with cap.
split; [destruct (aout_perm _ _ _ _ _ _ _ _ _ _ HOUT) as (rest & Hp); exists rest; split; exact Hp|].
assert (Hctl : sl_ctl c (Z.of_nat (length Bl)) = c)
  by (destruct c as [cl br dd ei ev]; unfold sl_ctl; cbn [ct_cl ct_br ct_dd ct_ei ct_ev] in *; rewrite Hoff; reflexivity).
rewrite Hctl. split; [exact (aout_moved ly S W mem md mem' c O mx no cap out HAR HOUT KL' GR') | intros _; reflexivity].
Qed.

(* ---- The loop head L with sent = 0: SLI, then the loop segment. ---- *)
Lemma sl_to_loop : @sl_loop_stmt fx rc SK PI B MT MMAX RG ->
forall W ly S regs mem md ch c O mx no cap out line Bl regsL memL mdL,
afn_pre SEGS B SL_STK ly S W regs mem md ch ->
aout_at B RG ly S W mem c O mx no cap out -> rom_view SEGS W mem ->
garr8 SEGS (arm W mem) line (bzs Bl) -> 0 <= line -> line + Z.of_nat (length Bl) < 2 ^ 63 ->
sl_line_ok B ly S out line (Z.of_nat (length Bl)) ->
(forall a, line <= a < line + Z.of_nat (length Bl) -> ~ inG (G_SL B RG) a) ->
sl_maxr c mx no cap (Z.of_nat (length Bl)) < MMAX ->
blocks_bytes S + tr_peak (sl_tr c mx no cap (Z.of_nat (length Bl))) <= LIVE_MAX ->
mo_ok MT S (sl_cost MT c mx no cap (Z.of_nat (length Bl))) ->
ct_cl c = 3 -> ct_br c = 0 -> 0 < Z.of_nat (length Bl) ->
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK (spZ regs) (ablocks_fp (aout_blks cap out)) ly S W mem md [] ly S W memL mdL 0 ->
spZ regsL = spZ regs - SL_FRAME -> getr regsL 3 = getr regs 3 -> getr regsL 4 = getr regs 4 ->
sl_regsL regsL (Z.of_nat (length Bl)) line 0 ->
sl_spill W memL (spZ regs - SL_FRAME) ->
sl_saved W memL (spZ regs - SL_FRAME) regs ->
(forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) memL a = aview SEGS (w_H W) mem a) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) memL) ->
SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post B MT RG regs ly S W mem md c O mx no cap out Bl).
Proof.
intros LOOP W ly S regs mem md ch c O mx no cap out line Bl regsL memL mdL HPRE HOUT HROM HBL Hl0 Hl63 HLOK HLG HCAP HLIVE HMO
  Hcl Hbr Hlen HJ Hsp H3 H4 HRL HSP HSV KL GR.
pose proof HPRE as (HAR & Hra & _ & Hgp & Htp & _).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdd & Hei & _).
set (len := Z.of_nat (length Bl)) in *.
assert (Hlive : ct_dd c = 0 -> sl_live c len = true).
{ intros Hd. unfold sl_live, send_line_c.send_live, send_line_c.send_off. rewrite Hcl, Hbr, Hd.
  replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
destruct (aout_perm _ _ _ _ _ _ _ _ _ _ HOUT) as (rest & Hperm).
apply (LOOP (Z.to_nat (2 * len + ct_ei c)) regs ly S W mem md c O mx no cap out line Bl W regsL memL mdL 0 (ct_ei c));
  [|fold len; lia].
unfold SLI. cbv zeta. fold len.
exists ly, S, 0, (ct_ev c), cap, out, 0, rest.
split; [exact HJ|]. split; [exact Hsp|]. split; [exact H3|]. split; [exact H4|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hra|].
split; [exact HRL|]. split; [exact HSP|]. split; [exact HSV|].
split; [exact Hcl|]. split; [exact Hbr|]. split; [lia|]. split; [left; reflexivity|]. split; [lia|]. split; [intros _; reflexivity|].
split; [destruct (Z.eqb_spec (ct_ei c) 1); destruct (Z.eqb_spec (ct_ei c) 0); cbn [andb]; first [reflexivity | lia]|].
split.
{ change (Z.to_nat 0) with 0%nat. rewrite firstn_O, app_nil_r, Z.add_0_r.
  replace (CTL 3 0 (ct_dd c) (ct_ei c) (ct_ev c)) with c by (destruct c as [cl br dd ei ev]; simpl in Hcl, Hbr; subst; reflexivity).
  exact (aout_moved ly S W mem md memL c O mx no cap out HAR HOUT KL GR). }
split; [exact (line_moved ly S W mem md memL out line Bl HAR HLOK KL GR HBL)|].
split; [exact Hl0|]. split; [exact Hl63|]. split; [exact (rom_moved W mem memL KL HROM)|]. split; [exact HLOK|].
split; [exact HLG|].
split; [intros Hd; unfold sl_cap; rewrite (Hlive Hd), Z.add_0_r, Z.sub_0_r; reflexivity|].
split; [intros _; split; reflexivity|].
split; [intros Hd; unfold sl_maxr in HCAP; rewrite (Hlive Hd) in HCAP; rewrite Z.add_0_r, Z.sub_0_r; exact HCAP|].
split; [intros Hd; unfold sl_tr in HLIVE; rewrite (Hlive Hd) in HLIVE; rewrite Z.add_0_r, Z.sub_0_r; exact HLIVE|].
split; [intros a _ _ _ Hp; exact (apresent_grows _ _ _ _ GR Hp)|].
split; [exact HMO|]. split; [exact (mo_le_refl MT MTL S)|].
split; [intros Hd; unfold sl_cost; rewrite (Hlive Hd), Z.add_0_r, Z.sub_0_r; lia|].
split; [intros _; reflexivity|].
split; [exact Hperm|]. split; [exact Hperm|]. reflexivity.
Qed.

(* ---- The walk. ---- *)
Theorem sl_entry : @sl_entry_stmt fx rc SK PI B MT MMAX RG.
Proof.
intros LOOP W ly S regs mem md ch c O mx no cap out line Bl HPRE H10 H11 HOUT HROM HBL Hl0 Hl63 HLOK HLG HCAP HLIVE HMO.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (sl_ent_entry W ly S regs mem md ch c O mx no cap out HPRE HOUT) as HS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajournal_gx_init SEGS B (G_SL B RG) 0 [] SL_STK (ablocks_fp (aout_blks cap out)) ly S W regs mem md ch HPRE
  ltac:(lia) eq_refl ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcl & Hbr & Hdd & Hei & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SL_STK = 16528) by reflexivity.
assert (Hlo : alloc_ceiling <= spZ regs - SL_FRAME) by (unfold SL_FRAME; lia).
set (len := Z.of_nat (length Bl)) in *.
remember (Eimg (Ereg regs (ent_extra (ct_cl c mod 2 ^ 32) (ct_br c)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (EHI : forall j, (j < 39)%nat -> ew E (A_HI j) = Z_to_bv 64 (VAL (A_HI j)))
  by (intros j Hj; subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (E2 : ew E 2 = getr regs 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs 4) by (apply EREG; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 line) by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 len) by (rewrite (EREG 11%nat 11%bv) by (first [lia | reflexivity]); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 (ct_cl c mod 2 ^ 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (ct_br c)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS BxE [] E (mrestrict (w_H W) mem)) by constructor.
assert (Rlen : 0 <= len < 2 ^ 64) by lia.
assert (KL0 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by reflexivity.
assert (GR0 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem)) by (intros x Hx; exact Hx).
clear HE.
unfold cfg_at. change (w64 A_send_lineP) with (Z_to_bv 64 (BASE + A_send_line)).
(* the prologue, the load of g_client, the bltz *)
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
destruct (keep_step E _ W mem _ _ (spZ regs) HFr HG0 ltac:(wr_frame Usp) Hlo KL0 GR0) as [KL1 GR1]. clear HF HFr HG0.
psrr_branch_tok RUN BR HS SHOK Bspan; rename Hc into B1; rewrite (bltz_cl E (ct_cl c) E32 Hcl) in B1.
-
(* g_client < 0: the epilogue *)
assert (Hoff : send_line_c.send_off (ct_cl c) (ct_br c) len = true)
  by (unfold send_line_c.send_off; rewrite B1; reflexivity).
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_sl_epi. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
destruct (keep_step E _ W mem _ _ (spZ regs) HFr HG0 ltac:(wr_frame Usp) Hlo KL1 GR1) as [KL2 GR2]. clear HF HFr HG0.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pmkst HS.
apply (sl_off_exit W ly S regs mem md ch c O mx no cap out Bl _ _ _ HPRE HOUT Hoff HJ).
+ unfold spZ in *. cbn [ms_regs]. rewrite X2, Usp, unsigned_lit_small by (unfold SL_FRAME in *; lia). unfold SL_FRAME. lia.
+ cbn [ms_regs]. rewrite X3. exact E3.
+ cbn [ms_regs]. rewrite X4. exact E4.
+ rewrite <- Usp. apply (saved_of_region E W _ regs _ _ _ _ _ HR0); [saved_in | exact EREG].
+ exact KL2.
+ exact GR2.
-
assert (Hcl3 : ct_cl c = 3) by (destruct Hcl as [Hc3 | Hc3]; [exact Hc3 | rewrite Hc3 in B1; vm_compute in B1; discriminate B1]).
(* the beqz on len *)
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
destruct (keep_step E _ W mem _ _ (spZ regs) HFr HG0 ltac:(wr_frame Usp) Hlo KL1 GR1) as [KL2 GR2]. clear HF HFr HG0.
psrr_branch_tok RUN BR HS SHOK Bspan; rename Hc into B2; rewrite (beqz_len E len E11 Rlen) in B2.
+
(* len = 0: the epilogue *)
assert (Hoff : send_line_c.send_off (ct_cl c) (ct_br c) len = true)
  by (unfold send_line_c.send_off; rewrite B2, orb_true_r; reflexivity).
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_sl_epi. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
destruct (keep_step E _ W mem _ _ (spZ regs) HFr HG0 ltac:(wr_frame Usp) Hlo KL2 GR2) as [KL3 GR3]. clear HF HFr HG0.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pmkst HS.
apply (sl_off_exit W ly S regs mem md ch c O mx no cap out Bl _ _ _ HPRE HOUT Hoff HJ).
* unfold spZ in *. cbn [ms_regs]. rewrite X2, Usp, unsigned_lit_small by (unfold SL_FRAME in *; lia). unfold SL_FRAME. lia.
* cbn [ms_regs]. rewrite X3. exact E3.
* cbn [ms_regs]. rewrite X4. exact E4.
* rewrite <- Usp. apply (saved_of_region E W _ regs _ _ _ _ _ HR0); [saved_in | exact EREG].
* exact KL3.
* exact GR3.
+
assert (Hlen0 : 0 < len) by (apply Z.eqb_neq in B2; lia).
assert (Hline0 : 0 < line) by exact (line_pos ly S W mem md out line len HAR HLOK Hlen0).
(* mv s1; the spill of the auipc at 0(sp); the load of g_client_broken; the bnez *)
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
destruct (keep_step E _ W mem _ _ (spZ regs) HFr HG0 ltac:(wr_frame Usp) Hlo KL2 GR2) as [KL3 GR3]. clear HF HFr HG0.
psrr_branch_tok RUN BR HS SHOK Bspan; rename Hc into B3; rewrite (bnez_br E (ct_br c) E33 Hbr) in B3.
*
(* g_client_broken: the epilogue *)
assert (Hoff : send_line_c.send_off (ct_cl c) (ct_br c) len = true).
{ unfold send_line_c.send_off. apply Bool.orb_true_iff. left. apply Bool.orb_true_iff. right.
  apply Z.eqb_eq. destruct Hbr as [Hb | Hb]; rewrite Hb in B3; [vm_compute in B3; discriminate B3 | exact Hb]. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_sl_epi. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
destruct (keep_step E _ W mem _ _ (spZ regs) HFr HG0 ltac:(wr_frame Usp) Hlo KL3 GR3) as [KL4 GR4]. clear HF HFr HG0.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pmkst HS.
apply (sl_off_exit W ly S regs mem md ch c O mx no cap out Bl _ _ _ HPRE HOUT Hoff HJ).
-- unfold spZ in *. cbn [ms_regs]. rewrite X2, Usp, unsigned_lit_small by (unfold SL_FRAME in *; lia). unfold SL_FRAME. lia.
-- cbn [ms_regs]. rewrite X3. exact E3.
-- cbn [ms_regs]. rewrite X4. exact E4.
-- rewrite <- Usp. apply (saved_of_region E W _ regs _ _ _ _ _ HR0); [saved_in | exact EREG].
-- exact KL4.
-- exact GR4.
*
assert (Hbr0 : ct_br c = 0) by (destruct Hbr as [Hb | Hb]; [exact Hb | rewrite Hb in B3; vm_compute in B3; discriminate B3]).
(* the setup of the loop's registers, to L *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_sl_loop. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
destruct (keep_step E _ W mem _ _ (spZ regs) HFr HG0 ltac:(wr_frame Usp) Hlo KL3 GR3) as [KL4 GR4]. clear HF HFr HG0.
prreg HS (2%bv : bv 5) L2. prreg HS (3%bv : bv 5) L3. prreg HS (4%bv : bv 5) L4.
prreg HS (8%bv : bv 5) L8. prreg HS (9%bv : bv 5) L9. prreg HS (23%bv : bv 5) L23. prreg HS (24%bv : bv 5) L24.
prreg HS (25%bv : bv 5) L25. prreg HS (27%bv : bv 5) L27. prreg HS (21%bv : bv 5) L21. prreg HS (26%bv : bv 5) L26.
prreg HS (22%bv : bv 5) L22.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pmkst HS.
apply (sl_to_loop LOOP W ly S regs mem md ch c O mx no cap out line Bl _ _ _ HPRE HOUT HROM HBL Hl0 Hl63 HLOK HLG HCAP HLIVE HMO
  Hcl3 Hbr0 Hlen0 HJ).
-- unfold spZ in *. cbn [ms_regs]. rewrite L2, Usp, unsigned_lit_small by (unfold SL_FRAME in *; lia). unfold SL_FRAME. lia.
-- cbn [ms_regs]. rewrite L3. exact E3.
-- cbn [ms_regs]. rewrite L4. exact E4.
-- cbn [ms_regs]. unfold sl_regsL.
   split; [rewrite L8; exact E11|]. split; [rewrite L9; exact E10|]. split; [rewrite L23; reflexivity|].
   split; [rewrite L24, E10; exact (trap_w_snez line ltac:(lia))|].
   split; [rewrite L25; exact E34|]. split; [rewrite L27; reflexivity|].
   split; [rewrite L21; exact (EHI 17%nat ltac:(lia))|]. split; [rewrite L26; exact (EHI 20%nat ltac:(lia))|].
   rewrite L22; exact (EHI 23%nat ltac:(lia)).
-- unfold sl_spill. rewrite <- Usp.
   split; [|split; [|split; [|split]]].
   ++ replace (bv_unsigned (ew E 2) - SL_FRAME) with (bv_unsigned (ew E 2) + -144) by (unfold SL_FRAME; lia).
      apply (slot_of_region E _ _ _ _ _ _ _ _ (SOff (A_HI 18) 0) _ HR0 eq_refl); [cbn; w_in | | pose proof (pa_val_range (A_HI 18)); lia].
      cbn [sv_denot]. rewrite (EHI 18%nat ltac:(lia)), Z.add_0_r, unsigned_lit_small by (pose proof (pa_val_range (A_HI 18)); lia). reflexivity.
   ++ replace (bv_unsigned (ew E 2) - SL_FRAME + 8) with (bv_unsigned (ew E 2) + -136) by (unfold SL_FRAME; lia).
      apply (slot_of_region E _ _ _ _ _ _ _ _ (SOff (A_HI 22) 0) _ HR0 eq_refl); [cbn; w_in | | pose proof (pa_val_range (A_HI 22)); lia].
      cbn [sv_denot]. rewrite (EHI 22%nat ltac:(lia)), Z.add_0_r, unsigned_lit_small by (pose proof (pa_val_range (A_HI 22)); lia). reflexivity.
   ++ replace (bv_unsigned (ew E 2) - SL_FRAME + 16) with (bv_unsigned (ew E 2) + -128) by (unfold SL_FRAME; lia).
      apply (slot_of_region E _ _ _ _ _ _ _ _ (SOff (A_HI 24) 0) _ HR0 eq_refl); [cbn; w_in | | pose proof (pa_val_range (A_HI 24)); lia].
      cbn [sv_denot]. rewrite (EHI 24%nat ltac:(lia)), Z.add_0_r, unsigned_lit_small by (pose proof (pa_val_range (A_HI 24)); lia). reflexivity.
   ++ replace (bv_unsigned (ew E 2) - SL_FRAME + 24) with (bv_unsigned (ew E 2) + -120) by (unfold SL_FRAME; lia).
      apply (slot_of_region E _ _ _ _ _ _ _ _ (SOff (A_HI 25) 0) _ HR0 eq_refl); [cbn; w_in | | pose proof (pa_val_range (A_HI 25)); lia].
      cbn [sv_denot]. rewrite (EHI 25%nat ltac:(lia)), Z.add_0_r, unsigned_lit_small by (pose proof (pa_val_range (A_HI 25)); lia). reflexivity.
   ++ replace (bv_unsigned (ew E 2) - SL_FRAME + 32) with (bv_unsigned (ew E 2) + -112) by (unfold SL_FRAME; lia).
      apply (slot_of_region E _ _ _ _ _ _ _ _ (SOff (A_HI 21) 0) _ HR0 eq_refl); [cbn; w_in | | pose proof (pa_val_range (A_HI 21)); lia].
      cbn [sv_denot]. rewrite (EHI 21%nat ltac:(lia)), Z.add_0_r, unsigned_lit_small by (pose proof (pa_val_range (A_HI 21)); lia). reflexivity.
-- rewrite <- Usp. apply (saved_of_region E W _ regs _ _ _ _ _ HR0); [saved_in | exact EREG].
-- exact KL4.
-- exact GR4.
Qed.
End c.
End b.
End a.
