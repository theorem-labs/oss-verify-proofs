(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths and module names changed; 95 of its 118 lines of code are new or changed and 249 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of BK0 (0x863e4, the header strip's forward
   exit): `bgeu s10,s4` to LEN 0x86490 when q = k (nothing is left for the backward strip: the header bytes are
   [k, k)), else `addi a0,s4,-1` into the backward strip L2 0x863ec with r = k. No byte is written: the seed's
   slots are read-only (m_file_s_hdra_w.v). The HDRA segment lane of the G2 walk owner's G2. *)
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

Lemma hda_bk0 : forall n, HDA_LEN_stmt B n -> HDA_L2_stmt B n -> HDA_BK0_stmt B n.
Proof.
intros n LEN L2. unfold HDA_BK0_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q HL HR HH HC Hq HB0 Hq2 R27 R21 R22 R23 R20 R26.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & _ & _ & HCOK & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] HDA_BK0
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk; subst E; apply mfE_reg; exact Hk).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) []) as E32. fold E in E32.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof (hda_line_le rest) as HLr.
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp1 & _) & _).
pose proof HC as (HMC & HSK).
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
assert (U26 : U E (SOff 26 0) = p + Z.of_nat (i + q)).
{ apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity | lia]. }
assert (U20 : U E (SOff 20 0) = p + Z.of_nat (i + k)).
{ apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]. }
unfold mf_at.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* q = k: to LEN with r = q = k *)
  rewrite branch_geu_U, U26, U20 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Eqk : q = k) by lia. subst q.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_LEN; [hda_awr_ro|].
  pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
  pmkst HS.
  apply (LEN v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest i j k k k HL').
  + hda_regs_carry HS EE E32 HR.
  + exact HH.
  + exact HC.
  + rewrite Lsl in HSK. split; [lia|]. split; [rewrite Lsl; lia|]. split; [exact HB0|]. split; [left; reflexivity|].
    split; [apply hda_all_blank_nil | left; reflexivity].
  + hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  + hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
  + hda_rg HS EE 26%nat (26%bv : bv 5). exact R26.
  + hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
- (* q < k: a0 = s4 - 1, into the backward strip L2 with r = k *)
  rewrite branch_geu_U, U26, U20 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L2; [hda_awr_ro|].
  pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
  pmkst HS.
  apply (L2 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest i j k q k HL').
  + hda_regs_carry HS EE E32 HR.
  + exact HH.
  + exact HC.
  + lia.
  + lia.
  + exact HB0.
  + exact Hq2.
  + apply hda_all_blank_nil.
  + hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  + hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  + hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
  + hda_rg HS EE 26%nat (26%bv : bv 5). exact R26.
  + hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
  + prreg HS (10%bv : bv 5) Q10. rewrite Q10, (EE 20%nat 20%bv eq_refl), R20. unfold w64.
    rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.
End e.
End f.
End d.
