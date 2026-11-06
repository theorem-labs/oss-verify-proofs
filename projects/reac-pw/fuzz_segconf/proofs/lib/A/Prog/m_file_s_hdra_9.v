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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 198 of its 239 lines of code are new or changed and 412 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of RIEQ (0x864b4, ieq's return). `beqz a0`
   to REF2 0x8652c when the header's first 7 bytes are not "segment"; else s5 = b + 7, the inline check of s5 (an
   obligation on the text's addressability), `lbu a0,0(s5)` (the byte hb[7] = sl[q + 7] at b + 7, a read-only text
   region at s10 = atom 26), `beq a0,9` / `bne a0,s3` to REF2 when it is neither '\t' nor ' ', `bgeu s5,s4` (never
   taken: b + 7 < be), then s6 = be, a0 = b + 7, s10 = 120(s1) into the name strip L3 0x864ec with a = q + 7. No byte
   is written. The HDRA segment lane of the G2 walk owner's G2. *)
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

(* the header byte hb[7] at b + 7 (b in s10 = atom 26), its value the seed's extra atom 52 *)
Definition hda9_txt : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 0 [YP09.mkChunk 7 (CVal 1 (SOff 52 0))].

(* the line's facts across the run just made, which changed no byte (its slots and text region are read-only) *)
Ltac hda9_carry HFr HJ HF HG HLc :=
  let KA := fresh "KA" in let HL' := fresh "HL" in
  pose proof (hda_frame_ro _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KA;
  pose proof (hda_line_carry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLc HJ KA) as HL';
  clear KA HF HFr HG HLc; rename HL' into HLc.

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

Lemma hda_rieq : forall n, HDA_REF2_stmt B n -> HDA_L3_stmt B n -> HDA_RIEQ_stmt B n.
Proof.
intros n REF2 L3. unfold HDA_RIEQ_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r HL HR HH HC HST Hqr
  R10 R27 R23 R26 R20 R22.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & HSTR & HADDR & HCOK & _).
pose proof HADDR as (Hp0 & Hp1 & _ & HRA & _).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof (hda_line_le rest) as HLr.
pose proof HC as (HMC & HSK).
pose proof HST as (Hs1 & Hs2 & _).
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
(* the byte hb[7] = sl[q + 7] *)
set (b := nth (i + q + 7) rest 0).
assert (Hb : rdW Wc memc (p + Z.of_nat (i + q + 7)) = Some b) by (apply hda_txt_byte; [exact HSTR | lia]).
destruct (aview_byte SEGS (w_H Wc) memc _ _ Hb) as (bb & _ & _ & Hbr).
assert (Hbsl : nth (q + 7) (hda_sl rest i j) 0 = b).
{ unfold hda_sl, b. rewrite hda_sl_nth by lia. f_equal. lia. }
(* the seed, the slots read-only, the text byte's region and the checked address's fact *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [b] HDA_RIEQ
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS1. clear HS0.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) [b]) in HS1.
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk; subst E; apply mfE_reg; exact Hk).
assert (E52 : ew E 52 = Z_to_bv 64 b) by (subst E; apply (mfE_xs regs1 v lyc pos cur (mf_next p rest) [b] 0); unfold A_TEXT; lia).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) [b]) as E32. fold E in E32.
assert (E36 : ew E 36 = Z_to_bv 64 (SHADOW_OFF + frame_addr lyc 1 pos / 8)).
{ subst E. pose proof (mfE_extra regs1 v lyc pos cur (mf_next p rest) [b] 4 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth mf_extra map app] in X. exact X. }
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [b] 26
  (p + Z.of_nat (i + q)) 8 [YP09.mkChunk 7 (CVal 1 (SOff 52 0))] line p rest true true [] false false [] false
  CX CORE RB LOOP) as (ROK & RDJ & RFT).
{ rewrite (mfE_reg regs1 v lyc pos cur (mf_next p rest) [b] 26 26%bv eq_refl), R26. reflexivity. }
{ lia. } { lia. } { lia. }
{ constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (p + Z.of_nat (i + q)) 7 1 (SOff 52 0) b).
  - cbn [sv_denot]. fold E. rewrite E52, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia.
  - replace (p + Z.of_nat (i + q) + 7) with (p + Z.of_nat (i + q + 7)) by lia.
    exact (mf_val1_of_aview (w_H Wc) memc _ _ Hb). }
fold E in ROK, RDJ, RFT.
pose proof (st_ok_pi_add_region E _ _ hda9_txt HS1 eq_refl ROK (hda_alld_ro E hda9_txt _ _ _ _ _ _ _ _ RDJ)) as HS2.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pi_add_fact E _ _ 26%nat _ HS2 RFT) as HS. clear HS2.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
(* the values the branches compare *)
set (ie := ieq (slice q (q + 7) (hda_sl rest i j)) S_segment) in R10.
assert (U10 : U E (SOff 10 0) = seg_spec.b2z ie).
{ apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | destruct ie; cbn; lia]. }
assert (U26 : U E (SOff 26 0) = p + Z.of_nat (i + q)).
{ apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity | lia]. }
assert (U26_7 : U E (SOff 26 7) = p + Z.of_nat (i + q) + 7).
{ rewrite U_SOff, (EE 26%nat 26%bv eq_refl), R26. unfold w64. rewrite unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia. }
assert (U20 : U E (SOff 20 0) = p + Z.of_nat (i + r)).
{ apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]. }
assert (U19 : U E (SOff 19 0) = 32).
{ apply U_atom; [rewrite (EE 19%nat 19%bv eq_refl), R19; reflexivity | lia]. }
assert (U52 : U E (SExt false 8 (SOff 52 0)) = b) by exact (hda_U_zext8 E 52 b E52 Hbr).
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
unfold mf_at.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* ieq = 0: to REF2 *)
  rewrite branch_eq_U, U10, U_lit in Hc by lia.
  assert (Hie : ie = false) by (destruct ie; [discriminate Hc | reflexivity]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF2; [hda_awr_ro|].
  pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL'.
  pmkst HS.
  apply (REF2 v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest HL').
  + hda_regs_carry HS EE E32 HR.
  + rewrite <- HFIN, (hda_hdr_refuse_ieq mcc _ (line + 1) k q r HMC HST Hqr Hie). reflexivity.
  + hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
- (* ieq = 1: the check of b + 7, the byte, `beq a0,9` *)
  rewrite branch_eq_U, U10, U_lit in Hc by lia.
  assert (Hie : ie = true) by (destruct ie; [reflexivity | discriminate Hc]).
  paj_run_tok RUN HS HJ SHOK Bspan.
  + (* the check of b + 7: inside the text's addressable range *)
    cbn [ms_mem mkst].
    eapply obl_of_range; [exact HRA | exact U32 | rewrite U26_7; lia | rewrite U26_7; lia].
  + hda_awr_ro.
  + (* at `beq a0,a1` 0x864d4; the check havocked two scratch atoms 1024, 1025 *)
    pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
    pose proof (hda_line_carry B n v lyc Sc Wc memc mdc (ms_mem ms) _ pos mcc cur line p rest HL HJ KA) as HL1.
    clear KA HF HFr HG.
    assert (E1_ : forall n0, (n0 < 1024)%nat -> ew (ewset (ewset E 1024 w) 1025 w0) n0 = ew E n0)
      by (intros n0 Hn0; rewrite !ew_ewset_other by lia; reflexivity).
    assert (V52 : U (ewset (ewset E 1024 w) 1025 w0) (SExt false 8 (SOff 52 0)) = b)
      by (apply hda_U_zext8; [rewrite E1_ by lia; exact E52 | exact Hbr]).
    assert (V19 : U (ewset (ewset E 1024 w) 1025 w0) (SOff 19 0) = 32) by (rewrite U_SOff, E1_, <- U_SOff by lia; exact U19).
    assert (V26_7 : U (ewset (ewset E 1024 w) 1025 w0) (SOff 26 7) = p + Z.of_nat (i + q) + 7)
      by (rewrite U_SOff, E1_, <- U_SOff by lia; exact U26_7).
    assert (V20 : U (ewset (ewset E 1024 w) 1025 w0) (SOff 20 0) = p + Z.of_nat (i + r))
      by (rewrite U_SOff, E1_, <- U_SOff by lia; exact U20).
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* b = 9: to `bgeu s5,s4` 0x864dc *)
      rewrite branch_eq_U, V52, U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
      paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
      hda9_carry HFr HJ HF HG HL1.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* taken: b + 7 >= be, impossible *)
         rewrite branch_geu_U, V26_7, V20 in Hc1. apply negb_true_iff, Z.ltb_ge in Hc1. lia.
      -- (* s6 = be, a0 = b + 7, s10 = 120(s1): to L3 with a = q + 7 *)
         paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L3; [hda_awr_ro|].
         hda9_carry HFr HJ HF HG HL1.
         pmkst HS.
         apply (L3 v lyc Sc Wc (ms_regs ms1) (ms_mem ms1) _ pos mcc cur line p rest i j k q r (q + 7)%nat HL1).
         ++ unfold mf_regs_at.
            split; [hda_rg HS EE 2%nat (2%bv : bv 5); exact R2|]. split; [hda_rg HS EE 3%nat (3%bv : bv 5); exact R3|].
            split; [hda_rg HS EE 4%nat (4%bv : bv 5); exact R4|]. split; [hda_rg HS EE 8%nat (8%bv : bv 5); exact R8|].
            split; [prreg HS (9%bv : bv 5) Q9; rewrite Q9, (EE 2%nat 2%bv eq_refl); exact R2|].
            split; [prreg HS (18%bv : bv 5) Q18; rewrite Q18, E32; reflexivity|].
            split; [hda_rg HS EE 19%nat (19%bv : bv 5); exact R19|]. split; [hda_rg HS EE 25%nat (25%bv : bv 5); exact R25|].
            prreg HS (26%bv : bv 5) Q26. rewrite Q26, E36. reflexivity.
         ++ hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
         ++ exact HH.
         ++ exact HC.
         ++ split; [exact HST|]. split; [exact Hqr|]. split; [exact Hie|]. rewrite Hbsl, Hc0. reflexivity.
         ++ lia.
         ++ apply hda_all_blank_nil.
         ++ hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
         ++ hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
         ++ prreg HS (21%bv : bv 5) Q21. rewrite Q21, (EE 26%nat 26%bv eq_refl), R26. unfold w64.
            rewrite unsigned_lit_small by lia. f_equal; lia.
         ++ prreg HS (10%bv : bv 5) Q10. rewrite Q10, (EE 26%nat 26%bv eq_refl), R26. unfold w64.
            rewrite unsigned_lit_small by lia. f_equal; lia.
         ++ hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
         ++ prreg HS (22%bv : bv 5) Q22. rewrite Q22, (EE 22%nat 22%bv eq_refl), R22, (EE 26%nat 26%bv eq_refl), R26.
            unfold w64. rewrite alu_add. unfold v_add. rewrite !unsigned_lit_small by lia. f_equal; lia.
    * (* b <> 9: `bne a0,s3` 0x864d8 *)
      rewrite branch_eq_U, V52, U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
      paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
      hda9_carry HFr HJ HF HG HL1.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* b <> 32: to REF2 *)
         rewrite branch_ne_U, V52, V19 in Hc1. apply negb_true_iff, Z.eqb_neq in Hc1.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF2; [hda_awr_ro|].
         hda9_carry HFr HJ HF HG HL1.
         pmkst HS.
         apply (REF2 v lyc Sc Wc (ms_regs ms1) (ms_mem ms1) _ pos mcc cur line p rest HL1).
         ++ hda_regs_carry HS EE E32 HR.
         ++ rewrite <- HFIN, (hda_hdr_refuse_sp mcc _ (line + 1) k q r HMC HST Hqr); [reflexivity|].
            unfold sp_tab. rewrite Hbsl. apply orb_false_intro; apply Z.eqb_neq; lia.
         ++ hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
      -- (* b = 32: to `bgeu s5,s4` 0x864dc *)
         rewrite branch_ne_U, V52, V19 in Hc1. apply negb_false_iff, Z.eqb_eq in Hc1.
         paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
         hda9_carry HFr HJ HF HG HL1.
         psrr_branch_tok RUN BR HS SHOK Bspan.
         ++ (* taken: b + 7 >= be, impossible *)
            rewrite branch_geu_U, V26_7, V20 in Hc2. apply negb_true_iff, Z.ltb_ge in Hc2. lia.
         ++ (* s6 = be, a0 = b + 7, s10 = 120(s1): to L3 with a = q + 7 *)
            paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L3; [hda_awr_ro|].
            hda9_carry HFr HJ HF HG HL1.
            pmkst HS.
            lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
              apply (L3 v lyc Sc Wc (ms_regs m) (ms_mem m) _ pos mcc cur line p rest i j k q r (q + 7)%nat HL1) end.
            ** unfold mf_regs_at.
               split; [hda_rg HS EE 2%nat (2%bv : bv 5); exact R2|]. split; [hda_rg HS EE 3%nat (3%bv : bv 5); exact R3|].
               split; [hda_rg HS EE 4%nat (4%bv : bv 5); exact R4|]. split; [hda_rg HS EE 8%nat (8%bv : bv 5); exact R8|].
               split; [prreg HS (9%bv : bv 5) Q9; rewrite Q9, (EE 2%nat 2%bv eq_refl); exact R2|].
               split; [prreg HS (18%bv : bv 5) Q18; rewrite Q18, E32; reflexivity|].
               split; [hda_rg HS EE 19%nat (19%bv : bv 5); exact R19|]. split; [hda_rg HS EE 25%nat (25%bv : bv 5); exact R25|].
               prreg HS (26%bv : bv 5) Q26. rewrite Q26, E36. reflexivity.
            ** hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
            ** exact HH.
            ** exact HC.
            ** split; [exact HST|]. split; [exact Hqr|]. split; [exact Hie|]. rewrite Hbsl, Hc1. reflexivity.
            ** lia.
            ** apply hda_all_blank_nil.
            ** hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
            ** hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
            ** prreg HS (21%bv : bv 5) Q21. rewrite Q21, (EE 26%nat 26%bv eq_refl), R26. unfold w64.
               rewrite unsigned_lit_small by lia. f_equal; lia.
            ** prreg HS (10%bv : bv 5) Q10. rewrite Q10, (EE 26%nat 26%bv eq_refl), R26. unfold w64.
               rewrite unsigned_lit_small by lia. f_equal; lia.
            ** hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
            ** prreg HS (22%bv : bv 5) Q22. rewrite Q22, (EE 22%nat 22%bv eq_refl), R22, (EE 26%nat 26%bv eq_refl), R26.
               unfold w64. rewrite alu_add. unfold v_add. rewrite !unsigned_lit_small by lia. f_equal; lia.
Qed.
End e.
End f.
End d.
