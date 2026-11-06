(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 95 of its 138 lines of code are new or changed and 410 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of NB0 (0x86a50, the name strip's forward
   exit): `mv s6,s7`, then `bgeu s5,s4` (0x86a54) to FIN 0x86aac when a = r (the name is empty: [r, r)), else
   0x86a58..0x86a60 (`a1 = s4 + (s5 - s4)`, `a0 = s4 - 1`) into the backward strip L4 0x86a64 with z = r. No byte is
   loaded or written: the seed's slots are read-only (m_file_s_hdra_w.v). The HDRA segment lane of the G2 walk owner's G2. *)
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

(* 0x86a58..0x86a5c `sub a1,s5,s4; add a1,s4,a1`, as the symbolic engine leaves it: s4 * 2^64 + s5, that is s5 *)
Lemma hda6_a1 : forall x y : word, alu64 ALU_ADD (mul_div M_MUL x (Z_to_bv 64 18446744073709551616)) y = y.
Proof.
intros x y. apply bv_eq. cbn [alu64 alu mul_div]. rewrite bv_add_unsigned, bv_mul_unsigned, Z_to_bv_unsigned.
change (bv_wrap 64 18446744073709551616) with 0. rewrite Z.mul_0_r. change (bv_wrap 64 0) with 0.
rewrite Z.add_0_l. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

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

Lemma hda_nb0 : forall n, HDA_FIN_stmt B n -> HDA_L4_stmt B n -> HDA_NB0_stmt B n.
Proof.
intros n FIN L4. unfold HDA_NB0_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r a
  HL HR R24 HH HC HK Ha HBa Ha2 R27 R23 R21 R20.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & _ & _ & HCOK & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] HDA_NB0
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk; subst E; apply mfE_reg; exact Hk).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) []) as E32. fold E in E32.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof HK as (HST & Hq8 & Hieq & Hsp).
pose proof HST as (Hs1 & Hs2 & _).
pose proof (hda_line_le rest) as HLr.
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp1 & _) & _).
pose proof HC as (HMC & HSK).
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
assert (U21 : U E (SOff 21 0) = p + Z.of_nat (i + a)).
{ apply U_atom; [rewrite (EE 21%nat 21%bv eq_refl), R21; reflexivity | lia]. }
assert (U20 : U E (SOff 20 0) = p + Z.of_nat (i + r)).
{ apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]. }
unfold mf_at.
(* `mv s6,s7`, up to the `bgeu s5,s4` *)
paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA1.
clear HFr HF HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a = r: the name is empty, to FIN with z = a = r *)
  rewrite branch_geu_U, U21, U20 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Ear : a = r) by lia. subst a.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_FIN; [hda_awr_ro|].
  pose proof (hda_frame_ro E _ (w_H Wc) _ (ms_mem ms0) HFr ltac:(vm_compute; reflexivity)) as KA2.
  assert (KA : forall x, rdW Wc (ms_mem ms0) x = rdW Wc memc x) by (intros x; rewrite KA2; apply KA1).
  pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms0) _ pos mcc cur line p rest HL HJ KA) as HL'.
  pmkst HS.
  apply (FIN v lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ pos mcc cur line p rest i j k q r r r HL').
  + mf_regs_carry HS EE E32 HR.
  + hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
  + exact HH.
  + exact HC.
  + exact HK.
  + split; [lia|]. split; [lia|]. split; [exact HBa|]. split; [left; reflexivity|].
    split; [apply hda_all_blank_nil | left; reflexivity].
  + hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  + prreg HS (22%bv : bv 5) Q22. rewrite Q22, (EE 23%nat 23%bv eq_refl). exact R23.
  + hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
  + hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  + hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
- (* a < r: a1 = s5, a0 = s4 - 1, into the backward strip L4 with z = r *)
  rewrite branch_geu_U, U21, U20 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L4; [hda_awr_ro|].
  pose proof (hda_frame_ro E _ (w_H Wc) _ (ms_mem ms0) HFr ltac:(vm_compute; reflexivity)) as KA2.
  assert (KA : forall x, rdW Wc (ms_mem ms0) x = rdW Wc memc x) by (intros x; rewrite KA2; apply KA1).
  pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms0) _ pos mcc cur line p rest HL HJ KA) as HL'.
  pmkst HS.
  apply (L4 v lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ pos mcc cur line p rest i j k q r a r HL').
  + mf_regs_carry HS EE E32 HR.
  + hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
  + exact HH.
  + exact HC.
  + exact HK.
  + lia.
  + lia.
  + exact HBa.
  + exact Ha2.
  + apply hda_all_blank_nil.
  + hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  + prreg HS (22%bv : bv 5) Q22. rewrite Q22, (EE 23%nat 23%bv eq_refl). exact R23.
  + hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
  + hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  + prreg HS (11%bv : bv 5) Q11. rewrite Q11, hda6_a1, (EE 21%nat 21%bv eq_refl). exact R21.
  + hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
  + prreg HS (10%bv : bv 5) Q10. rewrite Q10, (EE 20%nat 20%bv eq_refl), R20. unfold w64.
    rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.
End e.
End f.
End d.
