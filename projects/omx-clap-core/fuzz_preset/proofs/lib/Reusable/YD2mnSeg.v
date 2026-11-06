(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: memnorm twins of the core segments, written against core blob <sha> of each file, image B'
   (#102 asan-ubsan pin d663f82d, twin c90d4fa5; the core at commit 7edddd96814e):
   lib/Reusable/YD26.v 48c354d2e319 (m1c_run :93, rd0_run :127), lib/Reusable/YD25.v 9e60b8120ee2 (rd_to_RW :244,
   cp_run :676), lib/Reusable/YD23.v 97c0e322294f (mg_run :174), lib/Reusable/YD2g.v 0286d3258d4e (short_run :50,
   h1_run :59, ovr_run :68, p_run :77), lib/Reusable/YD2c.v b485f48b5d88 (pb_run :68, bq_run :77), lib/Reusable/YD2d.v
   766837b18247 (pe_run :240, pm_run :323), lib/Reusable/YD2e.v 7992b35d2cff (pc_run :205, pl_run :216),
   lib/Reusable/YD1r.v f5e3900b745c (vp_run :337, br_run :346, l2_run :355). The asan-ubsan twin (port/a2b.py
   f5113cbc90e5) of lib/A/AD2mnSeg.v; rd0_run's pc is YD26's YImgCellsB.B_MAIN_PC_OFF_54 (B' 0x81280; A' 0x81194).
   This file states no image numeral: its moves to B' are all in YImgCellsB.
   The original statements do not move; each twin <name>_mn is a NEW lemma.
   (The segments on the path from main to the driver loop head, port/mnloop-prefix-leaves.md §3 and §4.)
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma / runner invariant twin).

   The form of a twin: the original's premises, then P (ms_mem ms) for the start memory; the post is the original post
   and `exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')` (the form of PresetD1rB.v's H_memnorm_drv_B). P is any
   memory invariant with the engine's laws srr_inv_laws (YC80x.v); the run goes through YC80x.SRr_msteps_inv by the
   runner twins of lib/Reusable/YA0oInv.v (srr_run_with_inv / srr_run_to_with_inv). A branch does not change the
   memory, so srr_branch_with is used as it stands. At P := YAkMemnorm.memnorm tfibsegs the laws are
   YSRrMemnorm.srr_inv_laws_memnorm_k. Each proof is the original's, with the runner tactic replaced by its twin. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgCellsB.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t YD20 YD1v YD1y YD26 YD24 YE22 YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD21 YD25 YD23 YD2h YD1w YD2f YD2b YD2g YD1s YD2c YD2d YD29 YD2e YD1r.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE2k YD1u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YA0oInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the post of a twin after the run: the original's at_* post (its three conjuncts after the equation), then P of the
   end memory *)
Ltac mn_ret HS HPM HF HFr :=
apply SRr_ret; split;
[ split; [reflexivity|];
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; split; [reflexivity|];
  split; [exact HS|]; split; [exact HF | exact HFr]
| do 2 eexists; split; [reflexivity | exact HPM] ].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws tfibsegs P.
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.

(* YD23.v:174 mg_run *)
Lemma mg_run_mn : forall E (W : world tfibsegs) ms md buf cap,
st_ok tfibsegs E S_G (restrict (w_H W) ms) -> gvals E buf cap -> cap < 2 ^ 26 -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_G S_MG E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md buf cap HS G Hcap HPM. pose proof HWXi as HWX.
srr_branch_with tfibtbl_lp_ok HS.
{ exfalso. rewrite branch_ne_U in Hc.
change (SAlu ALU_SRL (SAlu ALU_ADD (SOff 58 0) (SOff 78 0)) (SLit 26)) with sv_big in Hc.
rewrite (G_big E buf cap G), U_SLit in Hc.
rewrite Z.div_small in Hc by (destruct G as (_ & _ & _ & _ & _ & Hc'); lia). discriminate Hc. }
{ srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr. }
Qed.

(* YD26.v:127 rd0_run *)
Lemma rd0_run_mn : forall E2 (W : world tfibsegs) regs mem md,
st_ok tfibsegs E2 (add_cond ss_m1r (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0))) (restrict (w_H W) (mkst regs (Z_to_bv 64 YImgCellsB.B_MAIN_PC_OFF_54) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 YImgCellsB.B_MAIN_PC_OFF_54) mem (seg_rom tfibsegs)) md)
(fun W' c' => YD26.at_after (add_cond ss_m1r (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0))) ss_rd0 E2 W mem md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E2 W regs mem md HS HPM. pose proof HWXi as HWX.
srr_run_to_with_inv tfibtbl_drv_ok PLAW HS HPM A_RD. mn_ret HS HPM HF HFr.
Qed.

(* YD25.v:676 cp_run *)
Lemma cp_run_mn : forall E3 (W : world tfibsegs) regs mem md,
st_ok tfibsegs E3 S_CHK' (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHK_END) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_CHK_END) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st S_CHK' S_CP E3 W mem md W' c' /\ exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E3 W regs mem md HS HPM. pose proof HWXi as HWX.
srr_run_to_with_inv tfibtbl_lp_ok PLAW HS HPM A_icpt_memcpy. mn_ret HS HPM HF HFr.
Qed.

(* YD2g.v:59 h1_run *)
Lemma h1_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E S_H6 (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_H6 S_H1 E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* YD2g.v:77 p_run *)
Lemma p_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_H1 cond_OK) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_H6 S_P E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* YD2g.v:50 short_run (the header's short arm: tail_at_pinv_B carries memnorm to the exit leaf too) *)
Lemma short_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_HDR cond_SH) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_HDR S_SHORT E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* YD2g.v:68 ovr_run (the header's overrun arm) *)
Lemma ovr_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_H1 cond_OV) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_H6 S_OVR E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* YD2c.v:68 pb_run *)
Lemma pb_run_mn : forall (c0 : bool) E (W : world tfibsegs) ms md,
st_ok tfibsegs E (if c0 then ssP0 else ssP1) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (if c0 then ssP0 else ssP1) (if c0 then sB0 else sB1) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 E W ms md HS HPM. pose proof HWXi as HWX.
destruct c0; srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* YD2c.v:77 bq_run *)
Lemma bq_run_mn : forall (c0 : bool) E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (if c0 then sB0 else sB1) (if c0 then cond_CL0 else cond_CL1)) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (if c0 then sB0 else sB1) (if c0 then sQ0 else sQ1) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 E W ms md HS HPM. pose proof HWXi as HWX.
destruct c0; srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* YD2d.v:240 pe_run *)
Lemma pe_run_mn : forall (c0 : bool) k E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (sQ c0 k) cond_PL0) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (sQ c0 k) (if c0 then sPE0 else sPE1 k) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 k E W ms md HS HPM. pose proof HWXi as HWX. pose proof sPE_eq as [Q0 Q1].
destruct c0; unfold sQ in *; [rewrite <- Q0 | rewrite <- (Q1 k)]; unfold sPE, sQ;
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* YD2d.v:323 pm_run *)
Lemma pm_run_mn : forall (c0 : bool) k E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (sQ c0 k) cond_PL1) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (sQ c0 k) (if c0 then sPM0 else sPM1 k) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 k E W ms md HS HPM. pose proof HWXi as HWX. pose proof sPM_eq as [Q0 Q1].
destruct c0; unfold sQ in *; [rewrite <- Q0 | rewrite <- (Q1 k)]; unfold sPM, sQ;
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* YD2e.v:205 pc_run *)
Lemma pc_run_mn : forall (c0 : bool) k E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E (add_cond (if c0 then S_PMr0 else S_PMr1 k) (cPTR A_PBLK)) (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_PM) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_PM) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st (if c0 then S_PMr0 else S_PMr1 k) (if c0 then S_PC0 else S_PC1 k) E W mem md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 k E W regs mem md HS HPM. pose proof HWXi as HWX. pose proof S_PC_eq as [Q0 Q1].
destruct c0; [rewrite <- Q0 | rewrite <- (Q1 k)]; srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* YD2e.v:216 pl_run *)
Lemma pl_run_mn : forall (c0 : bool) k E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E (if c0 then S_PCr0 else S_PCr1 k) (restrict (w_H W) (mkst regs (Z_to_bv 64 A_PC_RET) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_PC_RET) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st (if c0 then S_PCr0 else S_PCr1 k) (if c0 then S_PL0 else S_PL1 k) E W mem md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 k E W regs mem md HS HPM. pose proof HWXi as HWX. pose proof S_PL_eq as [Q0 Q1].
destruct c0; [rewrite <- Q0 | rewrite <- (Q1 k)]; srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* YD1r.v:337 vp_run *)
Lemma vp_run_mn : forall E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E S_LR (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st S_LR S_VP E W mem md W' c' /\ exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W regs mem md HS HPM. pose proof HWXi as HWX. rewrite <- S_VP_eq.
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* YD1r.v:346 br_run *)
Lemma br_run_mn : forall E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E S_VPr (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st S_VPr S_BR E W mem md W' c' /\ exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W regs mem md HS HPM. pose proof HWXi as HWX. rewrite <- S_BR_eq.
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* YD1r.v:355 l2_run *)
Lemma l2_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_BR cond_BRt) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_BR S_L2 E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. rewrite <- S_L2_eq.
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

Section f.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).

(* YD26.v:93 m1c_run *)
Lemma m1c_run_mn : forall (W : world tfibsegs) ms md,
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_m1c sp inp xw xd a0 p W ms md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros W ms md HS HPM. pose proof HWXi as HWX.
srr_run_with_inv tfibtbl_drv_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* YD25.v:244 rd_to_RW *)
Lemma rd_to_RW_mn : forall E (W : world tfibsegs) ms md len cap,
YD25.eagree sp inp xw xd a0 p E -> st_ok tfibsegs E S_RD (restrict (w_H W) ms) ->
bv_unsigned (ew E A_LEN) = len -> bv_unsigned (ew E A_CAP) = cap -> 0 <= len < cap -> cap <= 2 ^ 26 ->
P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_RW E W (Z.min (cap - len) 65536) (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md len cap HE HS E58 E59 Hlen Hcap HPM. pose proof HWXi as HWX.
pose proof (U_want E len cap E58 E59 ltac:(lia) ltac:(lia)) as Uw.
pose proof reabs_chk_RW as (CKa & CKb & OBL & Ma & Mb & _ & _ & AT77).
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfibtbl_lp_ok HS.
-
rewrite branch_ltu_U in Hc. change (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit (-1))) (SOff 59 0)) with sv_want in Hc. rewrite Uw, U_SLit in Hc. change (zcanon 65536) with 65536 in Hc. apply Z.ltb_lt in Hc.
srr_run_to_with_inv tfibtbl_lp_ok PLAW HS HPM RWPC.
apply SRr_ret. split; [split; [reflexivity|] | do 2 eexists; split; [reflexivity | exact HPM]].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split.
+ rewrite Z.min_l by lia. unfold S_RW. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 reabs_chk_RW)))))) at 1.
lazymatch type of HS with st_ok _ _ ?ssa ?msx =>
apply (st_ok_reabs tfibsegs LT77 E (ewset E A_WANT (Z_to_bv 64 (cap - len))) ssa msx RW_regs LH_mem RW_facts HS) end.
* split; [| intros d _; reflexivity]. intros n Hn. unfold LT77 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
* exact CKa.
* apply Forall_forall. intros [r j] Hin. vm_compute in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. cbn [fst snd ms_regs restrict].
rewrite ew_ewset_same.
lazymatch goal with |- _ = getr _ ?r => lazymatch type of HS with st_ok _ _ ?ss0 (restrict _ ?ms0) => rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss0 ms0 r HS) end end.
match goal with |- _ = sv_denot E ?v => let v' := eval vm_compute in v in change v with v' end.
change (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit (-1))) (SOff 59 0)) with sv_want.
rewrite (denot_lit_U E sv_want), Uw. reflexivity.
* rewrite OBL. constructor; [| constructor]. cbn [fst snd]. unfold afact_ok, fact_want. cbn [af_lo af_hi af_al2].
rewrite ew_ewset_same, u64_lit by lia. rewrite Z.mod_1_r. repeat split; lia.
* cbn [ms_mem restrict]. rewrite <- Ma. apply (mem_ok_agree tfibsegs 77 E); [| rewrite Ma; exact AT77 | exact (st_ok_mem_ok tfibsegs _ _ _ HS)].
split; [| reflexivity]. intros n Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
+ pose proof skel_iter as (_ & _ & _ & _ & _ & _ & SKa & _).
split; [apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HF1) | apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HFr1)];
(eapply frame_of_skel'; [exact (eq_sym SKa) |]); [exact HF | exact HFr].
-
rewrite branch_ltu_U in Hc. change (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit (-1))) (SOff 59 0)) with sv_want in Hc. rewrite Uw, U_SLit in Hc. change (zcanon 65536) with 65536 in Hc. apply Z.ltb_ge in Hc.
srr_run_to_with_inv tfibtbl_lp_ok PLAW HS HPM RWPC.
apply SRr_ret. split; [split; [reflexivity|] | do 2 eexists; split; [reflexivity | exact HPM]].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split.
+ rewrite Z.min_r by lia. unfold S_RW. rewrite <- (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 reabs_chk_RW))))))) at 1.
lazymatch type of HS with st_ok _ _ ?ssb ?msx =>
apply (st_ok_reabs tfibsegs LT77 E (ewset E A_WANT (Z_to_bv 64 65536)) ssb msx RW_regs LH_mem RW_facts HS) end.
* split; [| intros d _; reflexivity]. intros n Hn. unfold LT77 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
* exact CKb.
* apply Forall_forall. intros [r j] Hin. vm_compute in Hin. destruct Hin as [Heq|[]]. injection Heq as <- <-. cbn [fst snd ms_regs restrict].
rewrite ew_ewset_same.
lazymatch goal with |- _ = getr _ ?r => lazymatch type of HS with st_ok _ _ ?ss0 (restrict _ ?ms0) => rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss0 ms0 r HS) end end.
match goal with |- _ = sv_denot E ?v => let v' := eval vm_compute in v in change v with v' end. cbn [sv_denot]. reflexivity.
* rewrite OBL. constructor; [| constructor]. cbn [fst snd]. unfold afact_ok, fact_want. cbn [af_lo af_hi af_al2].
rewrite ew_ewset_same, u64_lit by lia. rewrite Z.mod_1_r. repeat split; lia.
* cbn [ms_mem restrict]. rewrite <- Mb. apply (mem_ok_agree tfibsegs 77 E); [| rewrite Mb; exact AT77 | exact (st_ok_mem_ok tfibsegs _ _ _ HS)].
split; [| reflexivity]. intros n Hn. rewrite ew_ewset_other by (unfold A_WANT; lia). reflexivity.
+ pose proof skel_iter as (_ & _ & _ & _ & _ & _ & _ & SKb).
split; [apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HF1) | apply (frame_of_trans E LH_mem _ _ _ _ eq_refl HFr1)];
(eapply frame_of_skel'; [exact (eq_sym SKb) |]); [exact HF | exact HFr].
Qed.
End f.
End c.
