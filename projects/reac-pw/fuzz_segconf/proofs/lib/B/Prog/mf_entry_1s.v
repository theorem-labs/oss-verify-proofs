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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 177 of its 214 lines of code are new or changed and 416 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the snprintf call step
   0x862a8 -> 0x862ac of the segment S_MF_ENTRY (lib/B/Prog/mf_entry_d.v), the statement MFE_SNP_STEP of
   lib/B/Prog/mf_entry_1c.v. A walk lane of the image-B m_file-family owner's G2B (a sub-lane), piece mf_entry_1s.v.
   proves no function (kind: segment lemma; the snprintf call step 0x862a8 -> 0x862ac of S_MF_ENTRY in m_file's
   image-B walk). No instruction of m_file is executed here.
   ADAPTED from lib/B/Prog/m_file_sn.v's mf_snp_field_call (the same wrapper at the same trampoline): the destination
   is c->reading = c + seg_spec.MC_READING (0x23b4) and the %s argument is the label w (the label pointer, or the
   literal "reac-pw.conf" at 0x210a0), a C string txt that may be 96 bytes or longer.

   mfe_snp_step: snprintf(c->reading, 96, "%s", w) at 0x862a8 (B.s line 92: a0 = s9 + 0x23b4 from 0x86280 /
   0x86284, a1 = 96 from 0x8629c, a2 = 0x21080 "%s" from 0x86298, a3 = s6 from 0x862a4; `jal` to the snprintf
   trampoline 0x43af0), from the wrapper's entry (pc = SIGMA SS___interceptor_trampoline_snprintf, ra = BASE +
   MFE_RET_SNP = the return 0x862ac, sp = s1).
   The contract is image B's row 4 (RtPFSeg.seg_asnprintf_realizes CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR at the trampoline,
   CMD_GOTW, A_SSP_GUARD), at the walk's FP state (rounding mode 0, sa_frm0). Its post is FP-existential: PaFx.v
   srr_art_postF_of_pf turns it into art_postF, aj_art_own_atF takes the journal step and srr_after_artF continues at
   the FP state fx1 the wrapper returns.
   Where things lie: the written bytes [c + 0x23b4, c + 0x23b4 + sn_len 95 txt) lie in [c + 0x23b4, c + 0x2414),
   the block's last 96 bytes: inside M_FILE_FP's last range [c + MC_NKEPT, c + MC_READING + 96) and inside the live
   mconf block (the block (b, m) of m_file_pre's sa_heap, live at the call by the Permutation of the blocks), which is
   awr_byte's second arm. The block lies below the allocator ceiling, so below the callee's window
   [s1 - SEG_SNP_K, s1) (s1 >= sp0 - 336 and STK_m_file = 8592 >= 8192 + 336 + 64), and off the image
   (SegPaLib.blk_off_imgP: below 0x10000 or at or above kImgEnd = 0x602000), which gives dest_off_globals and keeps
   the read-only list CMD_SNP_CR, the stack-protector cells and the format off the written regions. The
   destination's slack word: the block's in_app with 8 bytes past its end (m_file_sn.v's sn_amem_app).
   The %s argument (w, txt): lib/B/Prog/mf_entry_k.v's mf_label_arg gives pf_arg_asan at APtr txt and the family's
   cmd_args_slack / cmd_args_amem bands from MFE_SNP_STEP's premises on w (0 < w, sa_str, sa_addr, |txt| <= 65535,
   the three places, and the read span apart from the 96 bytes of c->reading, hence from the sn_len 95 txt <= 96
   bytes written).
   The format "%s" at the current state: m_file_k.v's mf_lit_now_j (sa_lit from the journal); the unowned
   read-only bytes (rt_rom_view): m_file_k.v's mf_rom_now_j. Neither takes RELRO, so this file does not take it.
   The text written: the contract writes sn_bytes 95 txt (sn_len 95 txt bytes); lib/B/Prog/mf_entry_m.v's
   mf_sn_bytes turns it into snprintf_s 96 F_s [AS txt] ++ [0] (txt has no NUL by sa_str; |txt| may be >= 96, where
   snprintf truncates).
   Section hypotheses: SSP (AR gives the stack-protector cells at SegInstB.gotwA / guardA, m_file_k.v's text) and
   ASNP (the snprintf row at every FP state). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFCmd RtPFShared RtPFPf RtPFSeg RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m mf_entry_d mf_entry_1c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_k m_file_sn mf_entry_m mf_entry_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Local Ltac mfe_dj := unfold zdisjoint; cbn [fst snd]; lia.
Local Ltac mfe_f2 := apply Forall_cons; [mfe_dj | apply Forall_cons; [mfe_dj | apply Forall_nil]].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
(* the callee, at every FP state: image B's row 4 (the image-B m_file segment table's corrected text) *)
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.

(* snprintf(c->reading, 96, "%s", w) from the wrapper's entry: snprintf_s 96 F_s [AS txt] and its NUL at
   c->reading, at BASE + MFE_RET_SNP, at the FP state the wrapper returns, nothing else changed outside the callee's
   window *)
Lemma mfe_snp_step : MFE_SNP_STEP B.
Proof.
unfold MFE_SNP_STEP.
intros v lyc Sc Wc regsc memc mdc pos w txt CX LS FRM HJ HPm HSA HST Hw0 HSTR HWA HWL HWLOC HWDJ
  R2 R3 R4 R1 R10 R11 R12 R13 KC.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi.
pose proof HMP as (Hc0 & Hc16 & _ & HCH & _).
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (HK : RtPFSeg.SEG_SNP_K = 8192) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSM : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HMR : seg_spec.MC_READING = 9140) by reflexivity.
assert (HMN : seg_spec.MC_NKEPT = 9132) by reflexivity.
assert (Hret : 0 <= MFE_RET_SNP < 2 ^ 40) by (unfold MFE_RET_SNP, AF_m_file; lia).
assert (Hret2 : MFE_RET_SNP mod 2 = 0) by (unfold MFE_RET_SNP, AF_m_file; reflexivity).
destruct (sn_s1 (mv_sp v) Hal16) as (Hs1 & Ho16).
assert (Hs1r : mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320) by lia.
clear Hs1.
(* the mconf block: live at the call, below the allocator ceiling, off the image *)
destruct HCH as (b & m & Hin0 & Hbc & Hec).
assert (Hin : In (b, m) (ablocks B lyc Sc)) by exact (Permutation_in _ (Permutation_sym HPm) Hin0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
pose proof (blk_off_imgP B lyc Sc Wc memc mdc b m HAR Hin) as Hoffimg.
assert (Hcb : b <= mv_c v /\ mv_c v + 9236 <= b + req_size m) by lia.
assert (Hoi : 0x602000 <= mv_c v \/ mv_c v + 9236 <= 0x10000) by (unfold off_img in Hoffimg; lia).
clear Hoffimg.
assert (Hs1b : mv_c v + 9244 <= mf_s1 (mv_sp v) - 8192 /\ mf_s1 (mv_sp v) <= 2 ^ 47) by lia.
assert (Hsp : spZ regsc = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hsp' : spZ regsc = mf_s1 (mv_sp v)) by lia.
(* the text: txt has no NUL; snprintf writes snprintf_s 96 F_s [AS txt] (fewer than 96 bytes) and its NUL *)
pose proof HSTR as ((_ & Htz) & _).
destruct (mf_sn_bytes txt Htz) as [Hsn Hsl].
destruct (mf_reading_bytes txt Htz) as (_ & Hrl & _).
pose proof HWA as (HW0 & HW63 & _).
(* the %s argument (w, txt): its read span is apart from the bytes written *)
assert (HDJ : sa_disj w (seg_spec.cstr_span w txt) (mv_c v + seg_spec.MC_READING)
  (RtPFShared.sn_len (96 - 1) txt)) by (unfold sa_disj in *; rewrite Hsl; lia).
destruct (mf_label_arg SEGS B LAWS lyc Sc Wc memc mdc w (mv_c v + seg_spec.MC_READING) txt
  RtPFSeg.SEG_SNP_K (spZ regsc) (RtPFShared.sn_len (96 - 1) txt) HAR Hw0 HSTR HWA HWL HWLOC HDJ
  ltac:(rewrite Hsl; lia) ltac:(rewrite HK; lia) ltac:(rewrite Hsp', HK; lia) ltac:(rewrite Hsp'; lia))
  as (ARG & ASL & AAM).
(* the facts the contract reads at the call state *)
pose proof (mf_rom_now_j B v lyc Sc Wc memc mdc pos CX HJ) as HROM.
pose proof (mf_lit_now_j B v lyc Sc Wc memc mdc pos F_s CX HJ ltac:(unfold M_FILE_LITS; left; reflexivity))
  as (Hf0 & ((HFZ & _) & _) & HFP & _ & _).
destruct (HFP lyc Sc Wc memc mdc HAR) as (_ & _ & FAM & FRA & FHV).
clear HFP.
destruct (SSP lyc Sc Wc memc mdc HAR) as (HG1 & cval & HG2).
rewrite <- sn_gotw, <- sn_guard in HG1. rewrite <- sn_guard in HG2.
pose proof sn_fmt_nums as (FN1 & FN2).
pose proof sn_img_bounds as (I1 & I2).
assert (HFL : Z.of_nat (length F_s) = 2) by (rewrite sn_fs; reflexivity).
rewrite HFL in FAM, FRA, FHV.
set (f := SegInstB.seg_litA_fz F_s) in *.
assert (Hf : f = 0x21080) by exact sn_fs_at.
assert (HraT : YK0s.ret_ok (getr regsc 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | exact Hret2]).
destruct (ecall_pre_stk_at SEGS B RtPFSeg.SEG_SNP_K SegInstB.STK_m_file (mv_sp v)
  (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
  lyc Sc Wc memc mdc 0 regsc (mf_s1 (mv_sp v) - mv_sp v) HJ Hsp Ho16 ltac:(lia) ltac:(rewrite HK, Hes; lia)
  ltac:(rewrite HK, HSTK; lia) HraT R3 R4) as (EPRE & ESTK & EPRES).
(* a3 = w *)
assert (HA3 : argZ regsc 3 = w).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R13. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
(* 0x862a8: snprintf(c->reading, 96, "%s", w) writes snprintf's text and its NUL into the block's last 96 bytes *)
unfold MF_POST.
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFSeg.SEG_SNP_K
    (fun a => mv_c v + seg_spec.MC_READING <= a < mv_c v + seg_spec.MC_READING
      + RtPFShared.sn_len (96 - 1) txt)
    (SIGMA SS___interceptor_trampoline_snprintf) Wc regsc memc SegInstB.STK_m_file (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
    lyc Sc mdc 0 (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + MFE_RET_SNP)) _ HJ Hsp Ho16 ltac:(lia) ltac:(lia)
    ltac:(rewrite HK, HSTK; lia) R1).
  - (* the written cells: M_FILE_FP's last range, inside the live block *)
    intros a Ha. cbv beta in Ha. rewrite Hsl in Ha. unfold awr_byte. right; left. split.
    + exists (mv_c v + seg_spec.MC_NKEPT, mv_c v + seg_spec.MC_READING + 96).
      split; [unfold M_FILE_FP; right; right; right; right; left; reflexivity|]. cbn [fst snd]. lia.
    + exists b, m. split; [exact Hin | lia].
  - apply srr_art_postF_of_pf; [exact EPRES|].
    apply (ASNP fx lyc Sc Wc regsc memc mdc (mv_c v + seg_spec.MC_READING) 96 f []
      (map (argZ regsc) [3; 4; 5; 6; 7] ++ []) txt cval).
    + exact EPRE.
    + exact ESTK.
    + exact EPRES.
    + exact R10.
    + exact R11.
    + exact R12.
    + (* rt_rom_view: the unowned read-only bytes *)
      exact HROM.
    + apply Forall_forall. intros x Hx. destruct (sn_cr_img x Hx) as (X1 & X2 & X3). lia.
    + apply Forall_forall. intros x Hx. destruct (sn_cr_img x Hx) as (X1 & X2 & X3).
      unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl. mfe_f2.
    + exact HG1.
    + exact HG2.
    + unfold RtPFCmd.CMD_GOTW; lia.
    + unfold RtPFCmd.CMD_GOTW; lia.
    + unfold RtAPI.A_SSP_GUARD; lia.
    + unfold RtAPI.A_SSP_GUARD; lia.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl. unfold RtPFCmd.CMD_GOTW. mfe_f2.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl. unfold RtAPI.A_SSP_GUARD. mfe_f2.
    + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
    + cbn [length]. rewrite Hsp'. lia.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl. cbn [length]. mfe_f2.
    + (* FR_seg CMD_IMG_LO CMD_GOTW: the format "%s", one string argument w *)
      unfold RtPFSeg.FR_seg, RtPFSeg.seg_fam. exists F_s, [RtPFSeg.PRel RtPFPf.Ps], [RtPFPf.APtr txt].
      split.
      { (* fmt_at *)
        split; [lia|]. split.
        { intros i Hi. rewrite HFL in Hi.
          replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia.
          rewrite (HFZ (Z.to_nat i)) by (rewrite length_app, sn_fs; cbn [length]; lia). reflexivity. }
        rewrite HFL. split.
        { unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl. mfe_f2. }
        split; [exact FAM|]. split; [exact FRA | exact (FHV ltac:(lia))]. }
      split; [rewrite sn_fs; reflexivity|].
      split; [apply Forall_cons; [exact I | apply Forall_nil]|].
      split.
      { cbn [map app RtPFShared.pf_args_asan]. split; [|exact I]. rewrite HA3. exact ARG. }
      split.
      { cbn [RtPFSeg.seg_text RtPFSeg.seg_step option_map]. rewrite app_nil_r. reflexivity. }
      split; [exact I|].
      split; [exact FN1|]. split; [exact FN2|].
      split.
      { cbn [map app RtPFCmd.cmd_args_slack]. rewrite HA3. split; [|exact I].
        rewrite mf_str_end_span. exact ASL. }
      split; [rewrite sn_fs; discriminate|].
      { cbn [map app RtPFCmd.cmd_args_amem]. rewrite HA3. split; [|exact I]. exact AAM. }
    + lia.
    + lia.
    + lia.
    + rewrite Hsl. lia.
    + unfold RtPFShared.snp_out. rewrite Hsp', HK, Hsl. cbn [pairwise].
      split; [|split; [apply Forall_nil | exact I]]. apply Forall_cons; [mfe_dj | apply Forall_nil].
    + (* dest_ok: block bytes the runtime does not own, below the callee's window *)
      intros a Ha. rewrite Hsl in Ha. destruct (Hbpres a ltac:(lia)) as [Hpr Hno].
      split; [exact (apresent_writable SEGS _ _ _ Hpr)|]. split; [exact Hno|]. rewrite Hsp', Hes. lia.
    + rewrite Hsl. apply (sn_amem_app b (req_size m)); [exact Hbapp | lia | lia | lia].
    + apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc b m); [exact HAR | exact Hin | | ];
        rewrite ?Hsl; lia.
    + apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc b m); [exact HAR | exact Hin | | | ];
        rewrite ?Hsl; lia.
    + (* dest_off_globals: the block is off the image *)
      rewrite Hsl. mfe_dj.
    + exact FRM. }
(* back at BASE + MFE_RET_SNP = 0x862ac at the FP state fx1 the wrapper returns *)
cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & (HA0 & HBY) & HK2).
apply (KC fx1 regs2 mem2 md2 Hfx HJ2 HP2).
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HBY (Z.of_nat i)) by (rewrite Hsl; lia).
  rewrite Hsn, Nat2Z.id. reflexivity.
- intros a Ha Hw Hdst. apply (HK2 a Ha).
  + intros Hc. apply Hw. lia.
  + intros Hc. cbv beta in Hc. apply Hdst. rewrite Hsl in Hc. lia.
Qed.

About mfe_snp_step.
Print Assumptions mfe_snp_step.
End e.
End f.
End d.

About mfe_snp_step.
Print Assumptions mfe_snp_step.
