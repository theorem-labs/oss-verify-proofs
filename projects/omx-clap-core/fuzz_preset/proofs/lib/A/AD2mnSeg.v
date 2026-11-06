(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: memnorm twins of the core segments, written against core blob <sha> of each file, image A'
   (#102 asan pin 1be0f53d, twin bff8519b; the core at commit b19e45bf552a):
   lib/A/AD26.v d3c4938c4380 (m1c_run :95, rd0_run :129), lib/A/AD25.v 9126f0c398a5 (rd_to_RW :240, cp_run :659),
   lib/A/AD23.v 1528c0d85010 (mg_run :171), lib/A/AD2g.v 16018f44d51c (short_run :50, h1_run :59, ovr_run :68,
   p_run :77), lib/A/AD2c.v
   b7ad0272218e (pb_run :69, bq_run :78), lib/A/AD2d.v 22004a37378e (pe_run :242, pm_run :325), lib/A/AD2e.v
   ea84e36fdb33 (pc_run :207, pl_run :218), lib/A/AD1r.v d33d8f723e32 (vp_run :333, br_run :342, l2_run :351).
   Moved from image A (commit 5f6a2b85e1b9) to A': rd0_run's return pc main+0x54, 0x81100 -> 0x81194 (the
   same move as AD26.v's; A' main is 0x81140), the only image numeral of this file.
   The original statements do not move; each twin <name>_mn is a NEW lemma.
   (The segments on the path from main to the driver loop head, port/mnloop-prefix-leaves.md §3 and §4.)
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma / runner invariant twin).

   The form of a twin: the original's premises, then P (ms_mem ms) for the start memory; the post is the original post
   and `exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')` (the form of PresetD1rA.v's H_memnorm_drv_A). P is any
   memory invariant with the engine's laws srr_inv_laws (YC80x.v); the run goes through YC80x.SRr_msteps_inv by the
   runner twins of lib/Reusable/YA0oInv.v (srr_run_with_inv / srr_run_to_with_inv). A branch does not change the
   memory, so srr_branch_with is used as it stands. At P := YAkMemnorm.memnorm tfibsegs the laws are
   YSRrMemnorm.srr_inv_laws_memnorm_k. Each proof is the original's, with the runner tactic replaced by its twin. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD26 AD24 AE22 ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f AD2b AD2g AD1s AD2c AD2d AD29 AD2e AD1r.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AE2k AD1u.
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

(* AD23.v:171 mg_run *)
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

(* AD26.v:129 rd0_run *)
Lemma rd0_run_mn : forall E2 (W : world tfibsegs) regs mem md,
st_ok tfibsegs E2 (add_cond ss_m1r (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0))) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81194) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81194) mem (seg_rom tfibsegs)) md)
(fun W' c' => AD26.at_after (add_cond ss_m1r (mkAC Instr.BC_NE (SOff A_BUF 0) (SLit 0))) ss_rd0 E2 W mem md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E2 W regs mem md HS HPM. pose proof HWXi as HWX.
srr_run_to_with_inv tfibtbl_drv_ok PLAW HS HPM A_RD. mn_ret HS HPM HF HFr.
Qed.

(* AD25.v:656 cp_run *)
Lemma cp_run_mn : forall E3 (W : world tfibsegs) regs mem md,
st_ok tfibsegs E3 S_CHK' (restrict (w_H W) (mkst regs (Z_to_bv 64 A_CHK_END) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_CHK_END) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st S_CHK' S_CP E3 W mem md W' c' /\ exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E3 W regs mem md HS HPM. pose proof HWXi as HWX.
srr_run_to_with_inv tfibtbl_lp_ok PLAW HS HPM A_icpt_memcpy. mn_ret HS HPM HF HFr.
Qed.

(* AD2g.v:59 h1_run *)
Lemma h1_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E S_H6 (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_H6 S_H1 E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* AD2g.v:77 p_run *)
Lemma p_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_H1 cond_OK) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_H6 S_P E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* AD2g.v:50 short_run (the header's short arm: tail_at_pinv_A carries memnorm to the exit leaf too) *)
Lemma short_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_HDR cond_SH) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_HDR S_SHORT E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* AD2g.v:68 ovr_run (the header's overrun arm) *)
Lemma ovr_run_mn : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_H1 cond_OV) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st S_H6 S_OVR E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W ms md HS HPM. pose proof HWXi as HWX. srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* AD2c.v:69 pb_run *)
Lemma pb_run_mn : forall (c0 : bool) E (W : world tfibsegs) ms md,
st_ok tfibsegs E (if c0 then ssP0 else ssP1) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (if c0 then ssP0 else ssP1) (if c0 then sB0 else sB1) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 E W ms md HS HPM. pose proof HWXi as HWX.
destruct c0; srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* AD2c.v:78 bq_run *)
Lemma bq_run_mn : forall (c0 : bool) E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (if c0 then sB0 else sB1) (if c0 then cond_CL0 else cond_CL1)) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (if c0 then sB0 else sB1) (if c0 then sQ0 else sQ1) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 E W ms md HS HPM. pose proof HWXi as HWX.
destruct c0; srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* AD2d.v:241 pe_run *)
Lemma pe_run_mn : forall (c0 : bool) k E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (sQ c0 k) cond_PL0) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (sQ c0 k) (if c0 then sPE0 else sPE1 k) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 k E W ms md HS HPM. pose proof HWXi as HWX. pose proof sPE_eq as [Q0 Q1].
destruct c0; unfold sQ in *; [rewrite <- Q0 | rewrite <- (Q1 k)]; unfold sPE, sQ;
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* AD2d.v:324 pm_run *)
Lemma pm_run_mn : forall (c0 : bool) k E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (sQ c0 k) cond_PL1) (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_st (sQ c0 k) (if c0 then sPM0 else sPM1 k) E W (ms_mem ms) md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros c0 k E W ms md HS HPM. pose proof HWXi as HWX. pose proof sPM_eq as [Q0 Q1].
destruct c0; unfold sQ in *; [rewrite <- Q0 | rewrite <- (Q1 k)]; unfold sPM, sQ;
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM; mn_ret HS HPM HF HFr.
Qed.

(* AD2e.v:207 pc_run *)
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

(* AD2e.v:218 pl_run *)
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

(* AD1r.v:333 vp_run *)
Lemma vp_run_mn : forall E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E S_LR (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_LLVMF) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st S_LR S_VP E W mem md W' c' /\ exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W regs mem md HS HPM. pose proof HWXi as HWX. rewrite <- S_VP_eq.
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* AD1r.v:342 br_run *)
Lemma br_run_mn : forall E (W : world tfibsegs) regs mem md,
st_ok tfibsegs E S_VPr (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs))) ->
P mem ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 RA_EMIT) mem (seg_rom tfibsegs)) md)
(fun W' c' => at_st S_VPr S_BR E W mem md W' c' /\ exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros E W regs mem md HS HPM. pose proof HWXi as HWX. rewrite <- S_BR_eq.
srr_run_with_inv tfibtbl_lp_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* AD1r.v:351 l2_run *)
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

(* AD26.v:95 m1c_run *)
Lemma m1c_run_mn : forall (W : world tfibsegs) ms md,
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms) -> P (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md) (fun W' c' => at_m1c sp inp xw xd a0 p W ms md W' c' /\
  exists ms' md', c' = mkCfg ms' md' /\ P (ms_mem ms')).
Proof.
intros W ms md HS HPM. pose proof HWXi as HWX.
srr_run_with_inv tfibtbl_drv_ok PLAW HS HPM. mn_ret HS HPM HF HFr.
Qed.

(* AD25.v:240 rd_to_RW *)
Lemma rd_to_RW_mn : forall E (W : world tfibsegs) ms md len cap,
AD25.eagree sp inp xw xd a0 p E -> st_ok tfibsegs E S_RD (restrict (w_H W) ms) ->
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
