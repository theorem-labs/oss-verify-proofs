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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 74 of its 127 lines of code are new or changed and 400 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3..., twin 80e82127e8ca...): the walk
   of fuzz_catalogue_row (0x8a7d8 = BASE + AF_fuzz_catalogue_row, 200 bytes, 50 instructions, frame 64 bytes, no
   side-stack frame, no UBSan trap branch; catalogue.c:29-35) against image B's copy lib/B/Prog/fuzz_catalogue_row_c.v
   of fuzz_catalogue_row_contract, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of
   apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing lib/B/Prog/SegPa.v).
   rule 24 (reuse), RELOCATION: reused lib/A/Prog/fuzz_catalogue_rowA.v + fuzz_catalogue_rowA_k.v +
   fuzz_catalogue_rowA_s.v (the image-A m_file-family lane, commit 01bfbfa568f9, closed against G2 FINAL
   6f783602b5e3; itself adapted from proofs/reac-pw/fuzz_pin/lib/A/PPgRow.v at commit
   b4e9443a2b9c): the same code, the differing words pc-relative only (0x8a808 ld / 0x8a814 addi after auipc: the
   .got word 0xa3210 and the table fuzz_catalogue 0xa20a0; the jal targets), which image B's listing states as the
   same atoms as image A's (A_OBJ 0, A_OBJ 77, the trampolines by name).
   The segments are fuzz_catalogue_row_s.v's (the loop) over the kit fuzz_catalogue_row_k.v; this file runs the
   prologue (0x8a7d8 .. 0x8a824: the frame of eight saved registers, s1 = n, s2 = p, the shadow base through the
   GOT word and the cell, s0 = s3 = fuzz_catalogue, s5 its shadow address, s6 = 11) to the loop head of row 0 and
   states the contract.
   The Section hypotheses: TL (PALib: the shadow base's GOT word and cell are listing objects 0 and 12, and errno
   is in the image), VOBJS (the listing's objects at the image's addresses; object 77 is fuzz_catalogue), and the
   two wrappers at their trampolines, the image-A wrapper lane's rows 16 (RtString.astrlen_realizes, lib/B/Rt/RtString.v) and 19
   (the kit's abcmp_realizes, lib/B/YG0d.v). Image B's numbers are lib/B/Prog/SegInstB.v's (the image-B harness lane; SegInstA's
   names): STK_fuzz_catalogue_row = 64 + 2 * ESTACK (image B's 64-byte frame, addi sp,sp,-64 at 0x8a7d8, and bcmp's
   2 * ESTACK window below it, both calls running at sp0 - 64), catA = 0xa20a0, RLO_A / RHI_A = SEG_RLO / SEG_RHI. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB fuzz_catalogue_row_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import fuzz_catalogue_row_k fuzz_catalogue_row_s.
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
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the record hypotheses: PALib (lib/B/Prog/SegPaLib.v; image A's lib/A/Prog/SegRecRest.v seg_palib discharges the
   same record at its instance) and the listing's objects against the image's addresses (lib/B/Prog/SegObj.v;
   SegAddr.v seg_objs) *)
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
(* the two wrappers fuzz_catalogue_row calls, at their trampolines, at every FP state: the image-A wrapper lane's interface
   rows 16 (strlen, image B trampoline 0x43a98) and 19 (bcmp, image B trampoline 0x43ac4) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* 0x8a7d8 .. 0x8a824: the frame, the eight saved registers, s1 = n, s2 = p, the shadow base, s0 = s3 = the table,
   s5 = its shadow address, s6 = 11; then the loop from row 0 *)
Lemma fcr_entry_ok : forall ly S W (regs : bvmap 5 word) mem md ch p n sb,
fcr_cx B ly S W regs mem md ch p n sb ->
SRr SEGS W (cfg_at SEGS (BASE + AF_fuzz_catalogue_row) regs mem md) (fcr_post B ly S W regs mem md sb).
Proof.
intros ly S W regs mem md ch p n sb CX.
pose proof (fcr_heads B TL ASTRLEN ABCMP 11 0 eq_refl ltac:(unfold pin_spec.CAT_N; lia)) as H0.
pose proof CX as (HPRE & HROD & H10 & Hp64 & H11 & Hn64 & Hn & HSB & HSA & HLOC & HCAT).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_fuzz_catalogue_row = 8256) by reflexivity.
destruct (fcr_entry_seed B TL W regs mem ly S md HAR Hstk Hpres) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_fuzz_catalogue_row [] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (fcr_E0 regs)) by (unfold fcr_E0; apply Eimg_env).
set (E := fcr_E0 regs) in *.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r)
  by (intros n0 r Hn0; subst E; unfold fcr_E0; pose proof (bv_unsigned_in_range 5 r) as Hr5;
      change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn0).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold fcr_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E318 : ew E 318 = Z_to_bv 64 catA)
  by (change 318%nat with (A_OBJ 77%nat); rewrite <- (fcr_V77 VOBJS);
      exact (img_env_atomP E (A_OBJ 77%nat) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 (BASE + AF_fuzz_catalogue_row)) with (Z_to_bv 64 (BASE + AF_fuzz_catalogue_row)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan FCR_HEAD.
{ awr_ok_tac. exact Usp. }
pmkst HS.
(* every byte outside the stack window is kept *)
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem) (mrestrict _ ?mm) |- _ =>
assert (KEEP : kept_out (rdW W mem) (rdW W mm) (spZ regs - STK_fuzz_catalogue_row) (spZ regs))
by (intros a Ha Hna; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - STK_fuzz_catalogue_row <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; try rewrite Usp in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hna ]) end.
(* the eight saved words, from the stack region *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict mkst] in HR0 end.
pose proof (fcr_frame_of_region E _ (spZ regs) regs _ _ _ _ _ HR0 Usp
  ltac:(intros j r Hj; do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; repeat (first [left; reflexivity | right]) |]);
        destruct j; cbn in Hj; discriminate Hj)
  ltac:(intros r Hr; apply EE; rewrite Z2Nat.id by lia; symmetry; apply Z_to_bv_small; change (bv_modulus 5) with 32; lia)) as HFR.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (H0 ly S W regs mem md ch p n sb rg mm mdq CX);
[ unfold fcr_mid; split; [exact HJ | split; [exact KEEP | exact HFR]]
| unfold fcr_regs_at; repeat split;
  lazymatch goal with |- getr _ ?k = _ =>
    let Q := fresh "Q" in rawreg HS k Q; rewrite Q; clear Q;
    first
    [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply EE; reflexivity
    | cbn [sv_denot]; rewrite Usp; unfold w64; f_equal; lia
    | rewrite denot_lit_U; unfold w64; f_equal;
      rewrite ?U_SAlu; cbn [zalu_raw]; rewrite ?U_SOff, ?U_SLit; rewrite ?E32, ?E318;
      unfold pin_spec.row_addr, catA, pin_spec.CAT_ROW, SB; vm_compute; reflexivity ]
  end
| reflexivity ]
end.
Qed.

(* the contract, at image B's numbers *)
Theorem fuzz_catalogue_row_walkB :
fuzz_catalogue_row_contract SEGS B (BASE + AF_fuzz_catalogue_row) STK_fuzz_catalogue_row RLO_A RHI_A catA.
Proof.
unfold fuzz_catalogue_row_contract.
intros ly S W regs mem md ch p n sb HPRE HROD H10 Hp64 H11 Hn64 HSB Hn HSA HLOC HCAT HEV.
exact (fcr_entry_ok ly S W regs mem md ch p n sb
  (conj HPRE (conj HROD (conj H10 (conj Hp64 (conj H11 (conj Hn64 (conj Hn (conj HSB (conj HSA (conj HLOC HCAT))))))))))).
Qed.
(* inside the Sections: the walk's hypotheses as its assumptions *)
About fuzz_catalogue_row_walkB.
Print Assumptions fuzz_catalogue_row_walkB.
End e.
End f.
End d.
About fuzz_catalogue_row_walkB.
Print Assumptions fuzz_catalogue_row_walkB.
