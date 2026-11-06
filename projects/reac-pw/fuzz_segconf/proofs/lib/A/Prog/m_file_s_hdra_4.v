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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 212 of its 254 lines of code are new or changed and 411 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of L3 (0x864ec, the name strip's forward
   loop): the check of the cursor a0 = s + a, `lbu a1,0(s5)` (the byte sl[a]), `bltu s3,a1` and the mask test `beqz`
   to NB0 0x86a50 on a non-blank byte, else `addi a0,a0,1; addi s5,s5,1; bne s4,a0` back to L3 with a + 1, or (at
   a + 1 = r) 0x8651c `j 86a4c`, `mv s5,s6` to NB0 with a = r. By induction on r - a. No byte is written: the seed's
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

(* the text byte at the cursor s5 (atom 21), its value the seed's extra atom 52 *)
Definition hda4_txt : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))].

(* after a run that wrote no byte: the reader over its end memory is the seed's (KA carried through the runs) *)
Ltac hda4_ka W :=
  match goal with
  | HFr : frame_of ?Ex _ (mrestrict _ ?m0) (mrestrict _ ?m1), KA : forall x, aview _ _ ?m0 x = aview _ _ ?mc x |- _ =>
    let K := fresh "KA" in
    pose proof (fun x => eq_trans (hda_frame_ro Ex _ (w_H W) m0 m1 HFr ltac:(vm_compute; reflexivity) x) (KA x)) as K;
    clear HFr KA;
    repeat match goal with
    | HF : frame_of _ _ m0 m1 |- _ => clear HF
    | HG : mem_grows (mrestrict _ m0) (mrestrict _ m1) |- _ => clear HG
    end
  end.
(* the line's facts at the end memory of the runs (the KA hypothesis hda4_ka keeps), as HL' *)
Ltac hda4_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest HL HJ :=
  match goal with
  | KA : forall x, aview _ _ ?m1 x = aview _ _ memc x |- _ =>
    pose proof (hda_line_carry B n v lyc Sc Wc memc mdc m1 _ pos mcc cur line p rest HL HJ KA) as HL'
  end.

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

Lemma hda_l3 : forall n, HDA_NB0_stmt B n -> HDA_L3_stmt B n.
Proof.
intros n NB0.
assert (IND : forall d v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r a, (r - a = d)%nat ->
  hda_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest -> mf_regs_at B v lyc pos regs1 ->
  getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
  hda_hdr v mcc line rest i j -> hda_close rest i j k -> hda_hok rest i j k q r ->
  (q + 7 <= a < r)%nat -> hda_all_blank (hda_sl rest i j) (q + 7) a ->
  getr regs1 27 = w64 (p + Z.of_nat i) -> getr regs1 23 = w64 (line + 1) ->
  getr regs1 21 = w64 (p + Z.of_nat (i + a)) -> getr regs1 10 = w64 (p + Z.of_nat (i + a)) ->
  getr regs1 20 = w64 (p + Z.of_nat (i + r)) -> getr regs1 22 = w64 (p + Z.of_nat (i + r)) ->
  mf_at B v Wc regs1 memc mdc HDA_L3).
2: { unfold HDA_L3_stmt. intros. eapply IND; eauto. }
induction d as [|d IH];
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r a Hd HL HR R24 HH HC HK Ha HB0
  R27 R23 R21 R10 R20 R22; [lia|].
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (mf_regs_base_of B v lyc pos regs1 HR) as RB.
pose proof LOOP as (_ & _ & _ & HSTR & HADDR & HCOK & _).
pose proof HADDR as (Hp0 & Hp1 & _ & HRA & _).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof (hda_line_le rest) as HLr.
pose proof HC as (HMC & HSK).
pose proof HK as (HST & Hqr & HIEQ & HSP).
pose proof HST as (Hs1 & Hs2 & _).
pose proof CORE as (HJ & _).
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
(* the byte at the cursor *)
set (b := nth (i + a) rest 0).
assert (Hb : rdW Wc memc (p + Z.of_nat (i + a)) = Some b) by (apply hda_txt_byte; [exact HSTR | lia]).
destruct (aview_byte SEGS (w_H Wc) memc _ _ Hb) as (bb & _ & _ & Hbr).
assert (Hbsl : nth a (hda_sl rest i j) 0 = b) by (unfold hda_sl, b; apply hda_sl_nth; lia).
(* the seed, the slots read-only, the text byte's region, the facts of s5 and a0, s3 and s9 pinned *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [b] HDA_L3
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS1. clear HS0.
set (E := mfE regs1 v lyc pos cur (mf_next p rest) [b]) in HS1.
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk; subst E; apply mfE_reg; exact Hk).
assert (E52 : ew E 52 = Z_to_bv 64 b)
  by (subst E; apply (mfE_xs regs1 v lyc pos cur (mf_next p rest) [b] 0); unfold A_TEXT; lia).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) [b]) as E32. fold E in E32.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [b] 21
  (p + Z.of_nat (i + a)) 1 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))] line p rest true true [] false false [] false
  CX CORE RB LOOP) as (ROK & RDJ & RFT).
{ rewrite (mfE_reg regs1 v lyc pos cur (mf_next p rest) [b] 21 21%bv eq_refl), R21. reflexivity. }
{ lia. } { lia. } { lia. }
{ constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (p + Z.of_nat (i + a)) 0 1 (SOff 52 0) b).
  - cbn [sv_denot]. fold E. rewrite E52, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia.
  - rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc _ _ Hb). }
fold E in ROK, RDJ, RFT.
pose proof (st_ok_pi_add_region E _ _ hda4_txt HS1 eq_refl ROK (hda_alld_ro E hda4_txt _ _ _ _ _ _ _ _ RDJ)) as HS2.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pi_add_fact E _ _ 21%nat _ HS2 RFT) as HS3. clear HS2.
assert (RFT10 : afact_ok E 10 (mkAF 4096 (2 ^ 47 - 8) 0)).
{ unfold afact_ok in RFT |- *. rewrite (EE 10%nat 10%bv eq_refl), R10.
  rewrite (EE 21%nat 21%bv eq_refl), R21 in RFT. exact RFT. }
pose proof (st_ok_pi_add_fact E _ _ 10%nat _ HS3 RFT10) as HS4. clear HS3.
pose proof (ast_ok_pi_set_reg_fp E _ _ (19%bv : bv 5) (SLit 32) HS4 eq_refl
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R19; reflexivity)) as HS5. clear HS4.
pose proof (ast_ok_pi_set_reg_fp E _ _ (25%bv : bv 5) (SLit 0x100002200) HS5 eq_refl
  ltac:(cbn [ms_regs restrict mkst sv_denot]; rewrite R25; reflexivity)) as HS. clear HS5.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts add_atom] in HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (U10 : U E (SOff 10 0) = p + Z.of_nat (i + a)).
{ apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity | lia]. }
assert (U20 : U E (SOff 20 0) = p + Z.of_nat (i + r)).
{ apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]. }
assert (U52 : U E (SExt false 8 (SOff 52 0)) = b) by (apply hda_U_zext8; [exact E52 | lia]).
assert (U10p : U E (SOff 10 1) = p + Z.of_nat (i + a) + 1).
{ rewrite U_SOff, (EE 10%nat 10%bv eq_refl), R10. unfold w64. rewrite unsigned_lit_small by lia.
  apply zcanon_id. unfold M64. lia. }
unfold mf_at.
pose proof (fun x => @eq_refl _ (rdW Wc memc x)) as KA0.
(* 0x864ec .. 0x864fc: the check of a0, the byte sl[a] into a1; stop at `bltu s3,a1` *)
paj_run_tok RUN HS HJ SHOK Bspan;
  [ rewrite U10; cbn [ms_mem mkst]; eapply obl_of_range;
    [ exact HRA | apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia | lia | lia ]
  | hda_awr_ro | ].
hda4_ka Wc.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 32 < sl[a]: not blank, to NB0 *)
  rewrite branch_ltu_U in Hc. hda_U Hc. rewrite U52, U_lit in Hc by lia. apply Z.ltb_lt in Hc.
  assert (NBa : blank (nth a (hda_sl rest i j) 0) = false) by (rewrite Hbsl; apply hda_nonblank_gt; lia).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_NB0; [hda_awr_ro|].
  hda4_ka Wc.
  hda4_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest HL HJ.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
    apply (NB0 v lyc Sc Wc (ms_regs m) (ms_mem m) _ pos mcc cur line p rest i j k q r a HL') end.
  + mf_regs_carry HS EE E32 HR.
  + hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
  + exact HH.
  + exact HC.
  + exact HK.
  + lia.
  + exact HB0.
  + right. exact NBa.
  + hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
  + hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
  + hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
  + hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
- (* sl[a] <= 32: the mask test *)
  rewrite branch_ltu_U in Hc. hda_U Hc. rewrite U52, U_lit in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
  hda4_ka Wc.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the mask bit is 0: not blank, to NB0 *)
    rewrite branch_eq_U in Hc0. hda_U Hc0. rewrite (hda_U_mask E 52 b E52 ltac:(lia)), U_lit in Hc0 by lia.
    apply Z.eqb_eq in Hc0.
    assert (NBa : blank (nth a (hda_sl rest i j) 0) = false)
      by (rewrite Hbsl; exact (hda_nonblank_of_mask b ltac:(lia) Hc0)).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_NB0; [hda_awr_ro|].
    hda4_ka Wc.
    hda4_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest HL HJ.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
      apply (NB0 v lyc Sc Wc (ms_regs m) (ms_mem m) _ pos mcc cur line p rest i j k q r a HL') end.
    * mf_regs_carry HS EE E32 HR.
    * hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
    * exact HH.
    * exact HC.
    * exact HK.
    * lia.
    * exact HB0.
    * right. exact NBa.
    * hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
    * hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
    * hda_rg HS EE 21%nat (21%bv : bv 5). exact R21.
    * hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
  + (* the mask bit is 1: blank; a0 and s5 step, `bne s4,a0` *)
    rewrite branch_eq_U in Hc0. hda_U Hc0. rewrite (hda_U_mask E 52 b E52 ltac:(lia)), U_lit in Hc0 by lia.
    apply Z.eqb_neq in Hc0.
    assert (BLa : blank (nth a (hda_sl rest i j) 0) = true)
      by (rewrite Hbsl; exact (hda_blank_of_mask b ltac:(lia) Hc0)).
    pose proof (hda_all_blank_snoc _ _ _ HB0 BLa) as HB1.
    paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
    hda4_ka Wc.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* a + 1 < r: back to L3 with a + 1 *)
      rewrite branch_ne_U in Hc1. hda_U Hc1. rewrite U20, U10p in Hc1. apply negb_true_iff, Z.eqb_neq in Hc1.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_L3; [hda_awr_ro|].
      hda4_ka Wc.
      hda4_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest HL HJ.
      pmkst HS.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
        apply (IH v lyc Sc Wc (ms_regs m) (ms_mem m) _ pos mcc cur line p rest i j k q r (S a)) end.
      -- lia.
      -- exact HL'.
      -- mf_regs_carry HS EE E32 HR.
      -- hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
      -- exact HH.
      -- exact HC.
      -- exact HK.
      -- lia.
      -- exact HB1.
      -- hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
      -- hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
      -- prreg HS (21%bv : bv 5) Q. hda_ew Q. rewrite Q, (EE 21%nat 21%bv eq_refl), R21. unfold w64.
         rewrite unsigned_lit_small by lia. f_equal; lia.
      -- prreg HS (10%bv : bv 5) Q. hda_ew Q. rewrite Q, (EE 10%nat 10%bv eq_refl), R10. unfold w64.
         rewrite unsigned_lit_small by lia. f_equal; lia.
      -- hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
      -- hda_rg HS EE 22%nat (22%bv : bv 5). exact R22.
    * (* a + 1 = r: 0x8651c `j 86a4c`, `mv s5,s6`, to NB0 with a = r *)
      rewrite branch_ne_U in Hc1. hda_U Hc1. rewrite U20, U10p in Hc1. apply negb_false_iff, Z.eqb_eq in Hc1.
      assert (Er : r = S a) by lia.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_NB0; [hda_awr_ro|].
      hda4_ka Wc.
      hda4_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest HL HJ.
      pmkst HS.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
        apply (NB0 v lyc Sc Wc (ms_regs m) (ms_mem m) _ pos mcc cur line p rest i j k q r r HL') end.
      -- mf_regs_carry HS EE E32 HR.
      -- hda_rg HS EE 24%nat (24%bv : bv 5). exact R24.
      -- exact HH.
      -- exact HC.
      -- exact HK.
      -- lia.
      -- rewrite Er. exact HB1.
      -- left. reflexivity.
      -- hda_rg HS EE 27%nat (27%bv : bv 5). exact R27.
      -- hda_rg HS EE 23%nat (23%bv : bv 5). exact R23.
      -- prreg HS (21%bv : bv 5) Q. hda_ew Q. rewrite Q, (EE 22%nat 22%bv eq_refl). exact R22.
      -- hda_rg HS EE 20%nat (20%bv : bv 5). exact R20.
Qed.
End e.
End f.
End d.
