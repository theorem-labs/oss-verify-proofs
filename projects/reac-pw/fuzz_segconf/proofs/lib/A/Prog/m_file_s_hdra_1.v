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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 185 of its 226 lines of code are new or changed and 412 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of L1 (0x862fc, the header strip's forward
   loop over [s + 1, close)), by induction on the bytes left k - q. One pass: the inline check of the cursor a0
   (atom 10), `lbu a2,0(s10)` (the byte sl[q] at s10 = atom 26, a read-only text region), `bltu s3,a2` and the mask
   test exit to BK0 0x863e4 on a non-blank byte; on a blank one `bne s10+1,s4` goes back to L1 with q + 1, or, at the
   end, `mv s10,a1` to BK0 with q = k. The HDRA segment lane of the G2 walk owner's G2. *)
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

(* the text byte at the cursor s10 (atom 26), its value the seed's extra atom 52 *)
Definition hda1_txt : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))].

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

(* the line's facts at the end of the last run, from those at its start (the run changed no byte) *)
Ltac hda1_carry HLo HLn :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m1),
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m1 ?md1 _ |- _ =>
    pose proof (hda_line_carry B _ _ _ _ _ m0 _ m1 md1 _ _ _ _ _ _ HLo HJ
      (hda_frame_ro _ _ (w_H W) m0 m1 HFr ltac:(vm_compute; reflexivity))) as HLn;
    clear HFr; try (match goal with HF : frame_of _ _ m0 m1 |- _ => clear HF end)
  end.
Lemma hda_l1 : forall n, HDA_BK0_stmt B n -> HDA_L1_stmt B n.
Proof.
intros n BK0.
assert (IND : forall d v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q, (k - q = d)%nat ->
  hda_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest -> hda_regs B v lyc pos regs1 ->
  hda_hdr v mcc line rest i j -> hda_close rest i j k ->
  (1 <= q < k)%nat -> hda_all_blank (hda_sl rest i j) 1 q ->
  getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 21 = w64 (mv_c v) -> getr regs1 22 = w64 (line + 1) ->
  getr regs1 23 = w64 (p + Z.of_nat j) -> getr regs1 20 = w64 (p + Z.of_nat (i + k)) ->
  getr regs1 26 = w64 (p + Z.of_nat (i + q)) -> getr regs1 10 = w64 (p + Z.of_nat (i + q)) ->
  getr regs1 11 = w64 (p + Z.of_nat (i + k)) ->
  mf_at B v Wc regs1 memc mdc HDA_L1).
2: { unfold HDA_L1_stmt. intros. eapply IND; eauto. }
induction d as [|d IH];
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q Hd HL HR HH HC Hq HB0
  R27 R21 R22 R23 R20 R26 R10 R11; [lia|].
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & HSTR & HADDR & HCOK & _).
pose proof HADDR as (Hp0 & Hp1 & _).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof (hda_line_le rest) as HLr.
pose proof HC as (HMC & HSK).
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
(* the byte at the cursor *)
set (b := nth (i + q) rest 0).
assert (Hb : rdW Wc memc (p + Z.of_nat (i + q)) = Some b) by (apply hda_txt_byte; [exact HSTR | lia]).
destruct (aview_byte SEGS (w_H Wc) memc _ _ Hb) as (bb & _ & Hbz & Hbr).
assert (Hbsl : nth q (hda_sl rest i j) 0 = b) by (unfold hda_sl, b; apply hda_sl_nth; lia).
(* the seed, the slots read-only, s3 and s9 pinned, the text byte's region and the checked address's fact *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [b] HDA_L1
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS1. clear HS0.
set (E := mfE regs1 v lyc pos cur (mf_next p rest) [b]) in HS1.
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk; subst E; apply mfE_reg; exact Hk).
assert (E52 : ew E 52 = Z_to_bv 64 b) by (subst E; apply (mfE_xs regs1 v lyc pos cur (mf_next p rest) [b] 0); unfold A_TEXT; lia).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) [b]) as E32. fold E in E32.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [b] 26
  (p + Z.of_nat (i + q)) 1 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))] line p rest true true [] false false [] false
  CX CORE RB LOOP) as (ROK & RDJ & RFT).
{ rewrite (mfE_reg regs1 v lyc pos cur (mf_next p rest) [b] 26 26%bv eq_refl), R26. reflexivity. }
{ lia. } { lia. } { lia. }
{ constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (p + Z.of_nat (i + q)) 0 1 (SOff 52 0) b).
  - cbn [sv_denot]. fold E. rewrite E52, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia.
  - rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc _ _ Hb). }
fold E in ROK, RDJ, RFT.
pose proof (st_ok_pi_add_region E _ _ hda1_txt HS1 eq_refl ROK (hda_alld_ro E hda1_txt _ _ _ _ _ _ _ _ RDJ)) as HS2.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pi_add_fact E _ _ 26%nat _ HS2 RFT) as HS3. clear HS2.
assert (RFT10 : afact_ok E 10 (mkAF 4096 (2 ^ 47 - 8) 0)).
{ unfold afact_ok in RFT |- *. rewrite (EE 10%nat 10%bv eq_refl), R10.
  rewrite (EE 26%nat 26%bv eq_refl), R26 in RFT. exact RFT. }
pose proof (st_ok_pi_add_fact E _ _ 10%nat _ HS3 RFT10) as HS4. clear HS3.
pose proof (ast_ok_pi_set_reg_fp E _ _ 19%bv (SLit 32) HS4 eq_refl ltac:(cbn; rewrite R19; reflexivity)) as HS5.
clear HS4.
pose proof (ast_ok_pi_set_reg_fp E _ _ 25%bv (SLit 0x100002200) HS5 eq_refl ltac:(cbn; rewrite R25; reflexivity)) as HS.
clear HS5. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_atom] in HS.
pose proof CORE as (HJ & _).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (U26 : U E (SOff 26 0) = p + Z.of_nat (i + q)).
{ apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity | lia]. }
assert (U10 : U E (SOff 10 0) = p + Z.of_nat (i + q)).
{ apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia]. }
assert (U20 : U E (SOff 20 0) = p + Z.of_nat (i + k)).
{ apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]. }
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (UBYTE : U E (SExt false 8 (SOff 52 0)) = b) by (apply hda_U_zext8; [exact E52 | lia]).
unfold mf_at.
paj_run_tok RUN HS HJ SHOK Bspan.
{ (* the check of the cursor's byte *)
  try (constructor; [|constructor]; unfold ob_holds; cbn [ob_x ob_n]).
  rewrite U10. apply (obl_of_range SEGS _ _ E (SOff 32 0) _ 1 p (Z.of_nat (length rest) + 1)); [|exact UB|lia|lia].
  exact (proj1 (proj2 (proj2 (proj2 HADDR)))). }
{ hda_awr_ro. }
(* the run's memory is the seed's: carry the line's facts *)
hda1_carry HL HL1. clear HL.
assert (U32 : U E (SLit 32) = 32) by reflexivity.
assert (U0 : U E (SLit 0) = 0) by reflexivity.
(* the facts at the end of the next run come from hda1_carry *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* 32 < b: not blank, to BK0 *)
  rewrite branch_ltu_U in Hc. hda_U Hc. rewrite U32, UBYTE in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_BK0; [hda_awr_ro|].
  hda1_carry HL1 HL2. pmkst HS.
  apply (BK0 v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k q HL2).
  - hda_regs_carry HS EE E32 HR.
  - exact HH.
  - exact HC.
  - lia.
  - exact HB0.
  - right. rewrite Hbsl. apply hda_nonblank_gt. exact Hc.
  - hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  - hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  - hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
  - hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
  - hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
  - hda_rg HS EE 26%nat (26%bv : bv 5). exact R26. }
(* b <= 32: the mask test *)
rewrite branch_ltu_U in Hc. hda_U Hc. rewrite U32, UBYTE in Hc. apply Z.ltb_ge in Hc.
paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
hda1_carry HL1 HL2. clear HL1.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* the mask bit is 0: not blank, to BK0 *)
  rewrite branch_eq_U in Hc0. hda_U Hc0. rewrite (hda_U_mask E 52 b E52 ltac:(lia)), U0 in Hc0.
  apply Z.eqb_eq in Hc0.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_BK0; [hda_awr_ro|].
  hda1_carry HL2 HL3. pmkst HS.
  apply (BK0 v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k q HL3).
  - hda_regs_carry HS EE E32 HR.
  - exact HH.
  - exact HC.
  - lia.
  - exact HB0.
  - right. rewrite Hbsl. apply (hda_nonblank_of_mask b ltac:(lia) Hc0).
  - hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  - hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  - hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
  - hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
  - hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
  - hda_rg HS EE 26%nat (26%bv : bv 5). exact R26. }
(* a blank byte: the bytes [1, q + 1) are blank *)
rewrite branch_eq_U in Hc0. hda_U Hc0. rewrite (hda_U_mask E 52 b E52 ltac:(lia)), U0 in Hc0.
apply Z.eqb_neq in Hc0. pose proof (hda_blank_of_mask b ltac:(lia) Hc0) as Hblank.
assert (HB1 : hda_all_blank (hda_sl rest i j) 1 (S q)) by (apply hda_all_blank_snoc; [exact HB0 | rewrite Hbsl; exact Hblank]).
paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
hda1_carry HL2 HL3. clear HL2.
assert (U261 : U E (SOff 26 1) = p + Z.of_nat (i + q) + 1).
{ rewrite U_SOff, (EE 26%nat 26%bv eq_refl), R26. unfold w64. rewrite unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia. }
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* q + 1 <> k: back to L1 with q + 1 *)
  rewrite branch_ne_U in Hc1. hda_U Hc1. rewrite U261, U20 in Hc1. apply negb_true_iff, Z.eqb_neq in Hc1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L1; [hda_awr_ro|].
  hda1_carry HL3 HL4. pmkst HS.
  apply (IH v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k (S q) ltac:(lia) HL4).
  - hda_regs_carry HS EE E32 HR.
  - exact HH.
  - exact HC.
  - lia.
  - exact HB1.
  - hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  - hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  - hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
  - hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
  - hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
  - prreg HS (26%bv : bv 5) Q26. hda_ew Q26. rewrite Q26, (EE 26%nat 26%bv eq_refl), R26. unfold w64.
    rewrite unsigned_lit_small by lia. f_equal. lia.
  - prreg HS (10%bv : bv 5) Q10. hda_ew Q10. rewrite Q10, (EE 10%nat 10%bv eq_refl), R10. unfold w64.
    rewrite unsigned_lit_small by lia. f_equal. lia.
  - hda_rg HS EE 11%nat (11%bv : bv 5). exact R11. }
(* q + 1 = k: s10 = a1 = close, to BK0 with q = k *)
rewrite branch_ne_U in Hc1. hda_U Hc1. rewrite U261, U20 in Hc1. apply negb_false_iff, Z.eqb_eq in Hc1.
assert (Ek : S q = k) by lia.
paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_BK0; [hda_awr_ro|].
hda1_carry HL3 HL4. pmkst HS.
apply (BK0 v lyc Sc Wc _ _ _ pos mcc cur line p rest i j k k HL4).
- hda_regs_carry HS EE E32 HR.
- exact HH.
- exact HC.
- lia.
- rewrite <- Ek. exact HB1.
- left. reflexivity.
- hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
- hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
- hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
- hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
- hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
- prreg HS (26%bv : bv 5) Q26. hda_ew Q26. rewrite Q26, (EE 11%nat 11%bv eq_refl). exact R11.
Qed.
End e.
End f.
End d.
