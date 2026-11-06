(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths and module names changed; 163 of its 188 lines of code are new or changed and 247 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of RMC (0x862d8, memchr's return): `beqz a0`
   to REF1 0x86bcc when sl has no ']'; `mv s4,a0; addi a0,a0,1; bne a0,s7` to REF1 when the first ']' is not sl's
   last byte; `addi s10,s11,1; bgeu s10,s4` to BK0 0x863e4 when k = 1 (the strip of [1, k) is empty), else
   `sub a1,s4,s11; add a1,s11,a1; addi a0,s11,1` into the forward strip L1 0x862fc with q = 1. No byte is read or
   written: the seed's slots are read-only (m_file_s_hdra_w.v). The HDRA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
m_file_s_hdra_t m_file_s_hdra_m m_file_s_hdra_e m_file_s_hdra_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the engine's a1 = s11 + (s4 - s11) at 0x862f8: s4 + s11 * 2^64, which is s4 *)
Lemma hda8_add_mul0 : forall x y : word,
  alu64 ALU_ADD x (mul_div M_MUL y (Z_to_bv 64 18446744073709551616)) = x.
Proof.
intros x y. rewrite alu_add, m_mul. unfold v_add, v_mul.
assert (H0 : bv_unsigned (Z_to_bv 64 18446744073709551616) = 0) by (rewrite Z_to_bv_unsigned; reflexivity).
rewrite H0, Z.mul_0_r.
assert (H1 : bv_unsigned (Z_to_bv 64 0) = 0) by (rewrite Z_to_bv_unsigned; reflexivity).
rewrite H1, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hda_rmc : forall n, HDA_REF1_stmt B n -> HDA_BK0_stmt B n -> HDA_L1_stmt B n -> HDA_RMC_stmt B n.
Proof.
intros n REF1 BK0 L1. unfold HDA_RMC_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k HL HR R24 HH Hk HMC R10 R27 R21 R22 R23.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & _ & _ & HCOK & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] HDA_RMC
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk0; subst E; apply mfE_reg; exact Hk0).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) []) as E32. fold E in E32.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof (hda_line_le rest) as HLr.
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp1 & _) & _).
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
unfold mf_at.
destruct (Nat.ltb_spec k (length (hda_sl rest i j))) as [HkL|HkL].
2:{ (* sl has no ']': a0 = 0, to REF1 *)
  assert (U10 : U E (SOff 10 0) = 0) by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  - paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF1; [hda_awr_ro|].
    pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
    pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
    pmkst HS.
    apply (REF1 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest HL').
    + mf_regs_carry HS EE E32 HR.
    + hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
    + rewrite <- HFIN, (hda_hdr_refuse_nf mcc _ (line + 1) HMC). reflexivity.
    + hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
    + hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
  - rewrite branch_eq_U, U10, U_lit in Hc by lia. discriminate Hc. }
(* the first ']' at k < |sl|: a0 = s + k, k >= 1 since sl[0] = '[' *)
pose proof (hda_memchr_some _ _ _ HMC) as (_ & HRk & _).
assert (Hk1 : (1 <= k)%nat).
{ destruct k as [|k0]; [|lia]. exfalso. unfold hda_sl in HRk. rewrite hda_slice_nth in HRk by lia.
  rewrite Nat.add_0_r, HLB in HRk. lia. }
assert (U10 : U E (SOff 10 0) = p + Z.of_nat (i + k))
  by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia]).
assert (U10' : U E (SOff 10 1) = p + Z.of_nat (i + k) + 1)
  by (apply U_atom_off; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia | lia]).
assert (U23 : U E (SOff 23 0) = p + Z.of_nat j)
  by (apply U_atom; [rewrite (EE 23%nat 23%bv eq_refl), R23; reflexivity | lia]).
assert (U27 : U E (SOff 27 1) = p + Z.of_nat i + 1)
  by (apply U_atom_off; [rewrite (EE 27%nat 27%bv eq_refl), R27; reflexivity | lia | lia]).
assert (HRh : hda_regs B v lyc pos regs1) by (unfold hda_regs; repeat split; assumption).
psrr_branch_tok RUN BR HS SHOK Bspan.
{ rewrite branch_eq_U, U10, U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* a0 = s + k + 1, s4 = s + k; `bne a0,s7` *)
paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
pose proof (hda_frame_ro E _ (w_H Wc) _ (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
pose proof (hda_line_carry B n v lyc Sc Wc _ _ (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL1.
clear KA HF HFr HG HL. rename HL1 into HL. rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* close + 1 <> e: m_header refuses, to REF1 *)
  rewrite branch_ne_U, U10', U23 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HSk : S k <> length (hda_sl rest i j)) by (rewrite Lsl; lia).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF1; [hda_awr_ro|].
  pose proof (hda_frame_ro E _ (w_H Wc) _ (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (hda_line_carry B n v lyc Sc Wc _ _ (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
  pmkst HS.
  apply (REF1 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest HL').
  + mf_regs_carry HS EE E32 HR.
  + hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
  + rewrite <- HFIN, (hda_hdr_refuse_end mcc _ (line + 1) k HMC HSk). reflexivity.
  + hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  + hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
- (* close + 1 = e: the close is sl's last byte; s10 = s + 1, `bgeu s10,s4` *)
  rewrite branch_ne_U, U10', U23 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HSk : S k = length (hda_sl rest i j)) by (rewrite Lsl; lia).
  assert (HC : hda_close rest i j k) by (split; assumption).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
  pose proof (hda_frame_ro E _ (w_H Wc) _ (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (hda_line_carry B n v lyc Sc Wc _ _ (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL1.
  clear KA HF HFr HG HL. rename HL1 into HL. rename ms into ms2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* k = 1: the strip of [1, k) is empty, to BK0 with q = k = 1 *)
    rewrite branch_geu_U, U27, U10 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    assert (Ek : k = 1%nat) by lia. subst k.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_BK0; [hda_awr_ro|].
    pose proof (hda_frame_ro E _ (w_H Wc) _ (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
    pose proof (hda_line_carry B n v lyc Sc Wc _ _ (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
    pmkst HS.
    apply (BK0 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest i j 1%nat 1%nat HL').
    * hda_regs_carry HS EE E32 HRh.
    * exact HH.
    * exact HC.
    * lia.
    * apply hda_all_blank_nil.
    * left; reflexivity.
    * hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
    * hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
    * hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
    * hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
    * prreg HS (20%bv : bv 5) Q20. rewrite Q20, (EE 10%nat 10%bv eq_refl), R10. reflexivity.
    * prreg HS (26%bv : bv 5) Q26.
      rewrite Q26, (EE 27%nat 27%bv eq_refl), R27. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal; lia.
  + (* 1 < k: into the forward strip L1 with q = 1, a0 = s10 = s + 1, a1 = s4 = s + k *)
    rewrite branch_geu_U, U27, U10 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L1; [hda_awr_ro|].
    pose proof (hda_frame_ro E _ (w_H Wc) _ (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
    pose proof (hda_line_carry B n v lyc Sc Wc _ _ (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
    pmkst HS.
    apply (L1 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest i j k 1%nat HL').
    * hda_regs_carry HS EE E32 HRh.
    * exact HH.
    * exact HC.
    * lia.
    * apply hda_all_blank_nil.
    * hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
    * hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
    * hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
    * hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
    * prreg HS (20%bv : bv 5) Q20. rewrite Q20, (EE 10%nat 10%bv eq_refl), R10. reflexivity.
    * prreg HS (26%bv : bv 5) Q26.
      rewrite Q26, (EE 27%nat 27%bv eq_refl), R27. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal; lia.
    * prreg HS (10%bv : bv 5) Q10.
      rewrite Q10, (EE 27%nat 27%bv eq_refl), R27. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal; lia.
    * prreg HS (11%bv : bv 5) Q11.
      rewrite Q11, hda8_add_mul0, (EE 10%nat 10%bv eq_refl), R10. reflexivity.
Qed.
End e.
End f.
End d.
