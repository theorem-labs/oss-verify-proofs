(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632 for reac-pw/fuzz_qdisc's image A (fuzz_qdisc.asan sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e, h-small-a3): it walks check_slots 0x7e870 against lib/A/QPgCSpec.v's qdisc_check_specX on the CONCRETE image tfibsegs / tfibtbl_lib, so knock's PAImg layer is gone (paj_run_tok / psrr_branch_tok / paj_ret_at -> the kit's aj_run_tok / srr_branch_tok / SRr_ret_at, step_entry -> check_entry over entry_st_ok_full); step_regions -> the 16-byte save slot stack_region 16 and the divisor cell 0x10350 (a base-None region with the literal chunk QD_MAGIC, paid by the contract's val_mem premise), knock's kp_region, step_SH and GOT / shadow-cell regions are dropped (no object, no shadow check, no shadow base); step_facts keeps only atom 2 (sp); knock's kawr / kwr (stack or object) -> awr_stk / kwr_stk (stack only), kept_step -> lib/A/QPgSlots.v's kept_run; knock's obj_at post is dropped (check_slots returns void), and the four `bne a0,a3` abort branches are refuted with lib/Prog/qdisc_div.v's lemmas; the arithmetic lemmas and the plumbing (qd_run, qd_keep, qd_branch, qd_leaf) are lib/A/QPgSlots.v's. *)
(* check_slots, 0x7e870, 116 bytes, 29 instructions. a0 = slots_spec lead fps (the contract's premise),
   a1 = lead (0 <= lead <= 65535), a2 = fps (an int). 0x7e870 addi sp,sp,-16 and 0x7e874 sd ra,8(sp) open a frame;
   that store into [sp - 16, sp) is the walk's only write (awr_stk: it lies in [sp0 - STK, sp0) by the contract's two
   stack-window premises; kwr_stk: no write leaves it). The loads are the divisor cell and the saved ra; neither is
   shadow-checked. Branches (a3 holds the result; u is not zero-extended here):
   B1 0x7e87c blez a2 -- BC_GE 0 fps, `fps <= 0` by br_ge0.
      TAKEN (fps <= 0): to 0x7e8c8, a3 = sext.w 1 = 1 = slots_spec (qdisc_spec_nonpos).
      not taken (0 < fps): u = max 0 (lead - 300) (U_use), p = u * fps < 2^47 (0x7e894 mul; U_prod,
      qdisc_product_range).
   B2 0x7e89c bltu a2,a1 -- p < 10^6.  TAKEN: to 0x7e8c8, a3 = 1 = slots_spec (qdisc_spec_small).
   B3 0x7e8b0 bltu a3,a2 -- 10^12 + 999999 < p.
      TAKEN: 0x7e8c4 mv a3,a1 with a1 = 10^6: a3 = 10^6 = slots_spec (qdisc_spec_cap).
      not taken: 0x7e8b4-0x7e8c0 load QD_MAGIC from 0x10350, mulhu, srli 18 = p / 10^6 (U_quot, qdisc_magic_shift),
      0x7e8c4 / 0x7e8c8 keep it (U_sextw0, qdisc_n_range): a3 = p / 10^6 = slots_spec (qdisc_spec_mid).
   B4 0x7e8cc bne a0,a3, reached on each of those four paths. Its TAKEN side jumps to the abort call at 0x7e8dc and is
      refuted on every path: a0 = slots_spec lead fps (U10, the premise) and a3 is that same value (the path's
      qdisc_spec_* lemma above), so the engine's `negb (a0 =? a3) = true` becomes `negb true = true` (Z.eqb_refl).
      not taken: 0x7e8d0 ld ra,8(sp), 0x7e8d4 addi sp,sp,16, 0x7e8d8 ret, with ra and sp restored. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw1 AWalkFw2 ACfm QPgCSpec QPgRt QPgSlots.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec qdisc_div.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition check_regions : smem := [ stack_region 16; qd_magic_region ].
(* sp in [2^46, 2^47], 16-aligned: it places the save slot's window outside the shadow band, so the engine needs no
   shadow entry for it (knock A/APgStep.v:41 step_facts' atom 2) *)
Definition check_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] [].
Definition ss_check : sstate := mkSS A_QD_CHECK sr_atoms check_regions None check_facts.
(* the write-range obligation: the save slot [sp - 16, sp) lies in the caller's stack allowance
   [sp0 - STK, sp0) (the contract's two stack-window premises); every other region is read-only *)
Ltac awr_stk :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ]
end end.
(* every write window of a state lies in the save slot [sp - 16, sp) *)
Ltac kwr_stk :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = _ |- _ => rewrite B2 in Hb end; lia | lia ] | ]);
destruct Hr.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Lemma check_entry : forall (W : world tfibsegs) regs memc,
(forall a, spZ regs - 16 <= a < spZ regs -> apresent (w_H W) memc a) ->
A_QD_MAGIC + 8 <= spZ regs - 16 -> 2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) memc) A_QD_MAGIC 8 QD_MAGIC ->
st_ok tfibsegs (Ereg regs rt_extra) ss_check (restrict (w_H W) (mkst regs (Z_to_bv 64 A_QD_CHECK) memc (seg_rom tfibsegs))).
Proof.
intros W regs memc Hpres Hlo Hhi Hal HV.
rewrite restrict_mkst_fx.
set (E := Ereg regs rt_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold ss_check. apply (entry_st_ok_full tfibsegs); change (Ereg regs rt_extra) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold check_regions, stack_region, qd_magic_region. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
unfold A_QD_MAGIC in Hlo.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_QD_MAGIC.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0x10350) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0x10350 8 (SLit QD_MAGIC) QD_MAGIC); [reflexivity | unfold QD_MAGIC; zside | zside |].
exact HV.
- apply pairwise_disjoint_of_extents.
unfold check_regions, stack_region, qd_magic_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp. unfold A_QD_MAGIC in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [check_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Theorem qdisc_pb_checkX : qdisc_check_specX tfibsegs B MT A_QD_CHECK A_QD_MAGIC.
Proof using MTL TL LAWS ML.
unfold qdisc_check_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs lead fps
HJ Hra Hra4 Hgp Htp H10 H11 Hlead H12 Hfps Hal16 Hwlo Hwhi HV Hev.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_check_STK in Hwlo.
pose proof (check_entry W regs memc ltac:(intros a Ha; apply Hpres; lia) ltac:(unfold A_QD_MAGIC; lia) ltac:(lia) Hal16 HV) as HS.
remember (Ereg regs rt_extra) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs rt_extra) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (slots_spec lead fps)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 lead) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 fps) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
clear HE.
assert (SHOK : sh_ok tfibsegs RTBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
(* a0 = slots_spec lead fps, the value the abort test compares with (contract premise) *)
pose proof (slots_spec_range lead fps) as Bs.
assert (U10 : U E (SOff 10 0) = slots_spec lead fps) by (apply (U_atom E 10); [exact E10 | lia]).
(* u = max 0 (lead - 300): 0x7e880-0x7e88c (addiw/sltu/addi/and) *)
pose proof (U_use E 11 lead E11 Hlead) as Uu. unfold sv_use in Uu.
unfold cfg_at. change (w64 A_QD_CHECK) with (Z_to_bv 64 A_QD_CHECK).
(* 0x7e870 addi sp,sp,-16; sd ra,8(sp); addi a3,zero,1; stop at 0x7e87c blez a2 *)
qd_run awr_stk. qd_keep kwr_stk.
qd_branch Hb1.
- (* blez TAKEN (fps <= 0, br_ge0): to 0x7e8c8, a3 = sext.w 1 = 1 = slots_spec (qdisc_spec_nonpos) *)
rewrite (br_ge0 E 12 fps E12 Hfps) in Hb1. apply negb_true_iff, Z.ltb_ge in Hb1.
qd_run awr_stk. qd_keep kwr_stk.
qd_branch Hn.
+ (* 0x7e8cc bne a0,a3 TAKEN would reach the abort: refuted, a0 = slots_spec lead fps = 1 = a3 *)
exfalso. rewrite branch_ne_U, U10, U_lit in Hn by lia. rewrite (qdisc_spec_nonpos lead fps Hb1), Z.eqb_refl in Hn.
discriminate Hn.
+ clear Hn. qd_run awr_stk. qd_keep kwr_stk.
qd_leaf ltac:(intros a Ha Hz; exact (KE a Ha Hz)) idtac.
- (* blez not taken: 0 < fps *)
rewrite (br_ge0 E 12 fps E12 Hfps) in Hb1. apply negb_false_iff, Z.ltb_lt in Hb1.
(* p = u * fps (0x7e894 mul), below 2^47 (qdisc_product_range) *)
pose proof (U_prod E _ 12 _ fps Uu ltac:(lia) E12 ltac:(lia)) as Up.
remember (Z.max 0 (lead - 300) * fps) as p eqn:Hp.
assert (Bp : 0 <= p < 2 ^ 47) by (rewrite Hp; apply qdisc_product_range; lia).
qd_run awr_stk. qd_keep kwr_stk.
qd_branch Hb2.
+ (* 0x7e89c bltu a2,a1 TAKEN (p < 10^6): to 0x7e8c8, a3 = 1 = slots_spec (qdisc_spec_small) *)
rewrite branch_ltu_U, Up, U_lit in Hb2 by lia. apply Z.ltb_lt in Hb2.
qd_run awr_stk. qd_keep kwr_stk.
qd_branch Hn.
* (* bne a0,a3 TAKEN (abort): refuted, a0 = slots_spec lead fps = 1 = a3 *)
exfalso. rewrite branch_ne_U, U10, U_lit in Hn by lia. rewrite (qdisc_spec_small lead fps p Hb1 Hp Hb2), Z.eqb_refl in Hn.
discriminate Hn.
* clear Hn. qd_run awr_stk. qd_keep kwr_stk.
qd_leaf ltac:(intros a Ha Hz; exact (KE a Ha Hz)) idtac.
+ (* not taken: 10^6 <= p *)
rewrite branch_ltu_U, Up, U_lit in Hb2 by lia. apply Z.ltb_ge in Hb2.
qd_run awr_stk. qd_keep kwr_stk.
qd_branch Hb3.
* (* 0x7e8b0 bltu a3,a2 TAKEN (10^12 + 999999 < p): 0x7e8c4 mv a3,a1 = 10^6 = slots_spec (qdisc_spec_cap) *)
rewrite branch_ltu_U, Up, U_lit in Hb3 by lia. apply Z.ltb_lt in Hb3.
qd_run awr_stk. qd_keep kwr_stk.
qd_branch Hn.
-- (* bne a0,a3 TAKEN (abort): refuted, a0 = slots_spec lead fps = 10^6 = a3 *)
exfalso. rewrite branch_ne_U, U10, U_lit in Hn by lia. rewrite (qdisc_spec_cap lead fps p Hb1 Hp Hb3), Z.eqb_refl in Hn.
discriminate Hn.
-- clear Hn. qd_run awr_stk. qd_keep kwr_stk.
qd_leaf ltac:(intros a Ha Hz; exact (KE a Ha Hz)) idtac.
* (* not taken (p <= 10^12 + 999999): 0x7e8b4-0x7e8c0 load QD_MAGIC from 0x10350, mulhu, srli 18 = p / 10^6
     (qdisc_magic_shift through U_quot), = slots_spec (qdisc_spec_mid) *)
rewrite branch_ltu_U, Up, U_lit in Hb3 by lia. apply Z.ltb_ge in Hb3.
pose proof (qdisc_n_range p ltac:(lia)) as Bq.
pose proof (U_sextw0 E _ _ (U_quot E _ p Up ltac:(lia)) ltac:(lia)) as Uq.
qd_run awr_stk. qd_keep kwr_stk.
qd_branch Hn.
-- (* bne a0,a3 TAKEN (abort): refuted, a0 = slots_spec lead fps = p / 10^6 = a3 *)
exfalso. rewrite branch_ne_U, U10, Uq in Hn. rewrite (qdisc_spec_mid lead fps p Hb1 Hp ltac:(lia)), Z.eqb_refl in Hn.
discriminate Hn.
-- clear Hn. qd_run awr_stk. qd_keep kwr_stk.
qd_leaf ltac:(intros a Ha Hz; exact (KE a Ha Hz)) idtac.
Qed.
End d.
End b.
