(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths and module names changed; 95 of its 123 lines of code are new or changed and 244 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan, pin sha256 48c5355bdacb...): the walk of fuzz_catalogue_row
   (0x8a038 = BASE + AF_fuzz_catalogue_row, 200 bytes, 50 instructions, frame 64 bytes, no side-stack frame;
   catalogue.c:29-35) against lib/A/Prog/fuzz_catalogue_row_c.v's fuzz_catalogue_row_contract at image A's numbers
   (SegInstA.v: STK_fuzz_catalogue_row, RLO_A, RHI_A, catA), in plugin-hostd/fuzz_command's lib/A/Prog form
   (afn_pre at the entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}`).
   rule 24 (reuse): adapted proofs/reac-pw/fuzz_pin/lib/A/PPgRow.v at commit b4e9443a2b9c
   (pin_pb_rowX; same code, 43 of 50 words equal, the 7 others pc-relative), restated into fuzz_command's
   afn_pre / apost_base form over the image-A owner's fuzz_catalogue_row_c.v in the shape of fuzz_command's rec_shape_of walk
   (lib/A/Prog/rec_shape_of.v at origin/ossv/recipes 501c0d516c69: the prologue to the loop head, then the loop);
   plain template the plain / image-B owner's lib/Prog/fuzz_catalogue_row.v (440d61eaa8c8).
   The segments are fuzz_catalogue_rowA_s.v's (the loop) over the kit fuzz_catalogue_rowA_k.v; this file runs the
   prologue (0x8a038 .. 0x8a084: the frame of eight saved registers, s1 = n, s2 = p, the shadow base through the
   GOT word and the cell, s0 = s3 = fuzz_catalogue, s5 its shadow address, s6 = 11) to the loop head of row 0 and
   states the contract.
   The Section hypotheses: TL (PALib: the shadow base's GOT word and cell are listing objects 0 and 12, and errno
   is in the image), VOBJS (the listing's objects at the image's addresses; object 77 is fuzz_catalogue), and the
   two wrappers at their trampolines, the interceptor-layer owner's rows 16 (RtString.astrlen_realizes) and 19 (the kit's
   abcmp_realizes). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA fuzz_catalogue_row_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import fuzz_catalogue_rowA_k fuzz_catalogue_rowA_s.
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
(* the record hypotheses: PALib (SegPaLib.v; SegRecRest.v seg_palib gives it at PB_seg) and the listing's objects
   against the image's addresses (SegObj.v; SegRecRest.v seg_val_objs_PB) *)
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
(* the two wrappers fuzz_catalogue_row calls, at their trampolines, at every FP state: the interceptor-layer owner's interface
   rows 16 (strlen 0x43a0c) and 19 (bcmp 0x43a38) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* 0x8a038 .. 0x8a084: the frame, the eight saved registers, s1 = n, s2 = p, the shadow base, s0 = s3 = the table,
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

(* the contract, at image A's numbers *)
Theorem fuzz_catalogue_row_walk :
fuzz_catalogue_row_contract SEGS B (BASE + AF_fuzz_catalogue_row) STK_fuzz_catalogue_row RLO_A RHI_A catA.
Proof.
unfold fuzz_catalogue_row_contract.
intros ly S W regs mem md ch p n sb HPRE HROD H10 Hp64 H11 Hn64 HSB Hn HSA HLOC HCAT HEV.
exact (fcr_entry_ok ly S W regs mem md ch p n sb
  (conj HPRE (conj HROD (conj H10 (conj Hp64 (conj H11 (conj Hn64 (conj Hn (conj HSB (conj HSA (conj HLOC HCAT))))))))))).
Qed.
(* inside the Sections: the walk's hypotheses as its assumptions *)
About fuzz_catalogue_row_walk.
Print Assumptions fuzz_catalogue_row_walk.
End e.
End f.
End d.
About fuzz_catalogue_row_walk.
Print Assumptions fuzz_catalogue_row_walk.
