(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_cmp_scan: the scan loop L2 of image B's LLVMFuzzerTestOneInput cmp segment, the path the
   refused plain decode takes (a0 = -1 at +0x6f0, so `bgez a0` at +0x700 falls through):
     +0x718 bltu a4, a3 -> +0xb84     (UBSan: out + i wraps; refuted, i < olen)
     +0x71c .. +0x744                  the byte out + i, its shadow check (slow path +0x750 .. +0x75c, resolved by the
                                       engine's token: the byte is addressable), a2 |= (byte != 0xa5), i += 1
     +0x748 bne s10, a3 -> +0x718      the loop test
     +0x74c j +0x760; +0x760 bnez a2 -> +0xb88   (abort; refuted, every byte is the 0xa5 fill)
     +0x764 blez a0 -> +0x830; +0x830 ld a0, 88(s1); +0x834 jal free
   The in-line report call +0x75c is never reached: the token's slow block needs the byte addressable, which the
   shadow entry gives. The loop is by induction on olen - i, a Theorem Labs lane's GrantEntrySweepS2.v:236 gsw_rows_loop form
   (a turn's state built afresh at the head, run to the loop test, the taken edge back to the head by run_to). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YN1y.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YC5d YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_segX_cmp_defs
LLVMFuzzerTestOneInput_segX_cmp_kit LLVMFuzzerTestOneInput_segX_cmp_st.
Import ListNotations.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section scan. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := decodesegsB0.
#[local] Notation VAL := decodeb_val.
#[local] Notation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HPCF : pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free.
Variable cx : dctx.
Variables (ly : alayout) (S : astate) (W : world SEGS) (out res mode nch ns : Z).
Hypothesis Hin : In (out, dec_b_olen nch ns) (ablocks B ly S).
Variable Q : world SEGS -> config -> Prop.
(* What the rest of the segment does from the call of free #1 (cm_tail of
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_tail.v). *)
Hypothesis KFREE : forall regs mem md,
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 -> cm_mem cx out res mode nch ns W mem ->
  YK11.getr regs 10 = w64 out -> YK11.getr regs 1 = w64 (DEC_A_LLVMF + 0x838) ->
  YK11.getr regs 22 = w64 (dec_b_len (d_n cx)) -> YK11.getr regs 27 = w64 res ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (YK11.seg_rom SEGS)) md) Q.

Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let RUNTO := @paj_run_to fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

Lemma cm_scan : forall (n : nat) i regs mem md,
  Z.to_nat (dec_b_olen nch ns - i) = n -> 0 <= i < dec_b_olen nch ns ->
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 ->
  cm_mem cx out res mode nch ns W mem -> dec_b_filled W mem out (dec_b_olen nch ns) ->
  YK11.getr regs 10 = w64 (-1) -> YK11.getr regs 12 = w64 0 -> YK11.getr regs 13 = w64 i ->
  YK11.getr regs 14 = w64 (18446744073709551615 - out) -> YK11.getr regs 17 = w64 SHADOW_OFF ->
  YK11.getr regs 22 = w64 (dec_b_len (d_n cx)) -> YK11.getr regs 26 = w64 (dec_b_olen nch ns) ->
  YK11.getr regs 27 = w64 res ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x718)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros n. induction n as [|n IH]; intros i regs mem md Hn Hi HC HM HFILL R10 R12 R13 R14 R17 R22 R26 R27.
{ lia. }
set (olen := dec_b_olen nch ns) in *.
pose proof HC as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR Hin) as (_ & Ho4096 & Hoceil & Hoapp & _ & _ & Hm).
pose proof (req_size_pos olen ltac:(lia)) as [_ Hrq].
pose proof (@alloc_ceiling_val rc) as [ACR _].
destruct (@cm_stokL2 fx rc B LAWS cx W ly S regs mem md dec_ev_6f0 out res mode nch ns olen i HC HM Hin HFILL Hi R17 R13)
  as [HS SHOK].
assert (EPC : w64 (DEC_A_LLVMF + 0x718) = Z_to_bv 64 (BASE + 0x718)) by (unfold w64; f_equal; vm_compute; reflexivity).
rewrite EPC in HS. clear EPC.
remember (cm_env cx regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) (out + i) 0)
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply cm_env_img).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs r)
  by (intros k r Hk; subst E; apply cm_env_reg; exact Hk).
assert (E2 : ew E 2 = YK11.getr regs 2) by exact (ER 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = YK11.getr regs 3) by exact (ER 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = YK11.getr regs 4) by exact (ER 4%nat 4%bv eq_refl).
assert (E8 : ew E 8 = YK11.getr regs 8) by exact (ER 8%nat 8%bv eq_refl).
assert (E9 : ew E 9 = YK11.getr regs 9) by exact (ER 9%nat 9%bv eq_refl).
assert (E10 : ew E 10 = w64 (-1)) by (rewrite (ER 10%nat 10%bv eq_refl); exact R10).
assert (E12 : ew E 12 = w64 0) by (rewrite (ER 12%nat 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = w64 i) by (rewrite (ER 13%nat 13%bv eq_refl); exact R13).
assert (E14 : ew E 14 = w64 (18446744073709551615 - out)) by (rewrite (ER 14%nat 14%bv eq_refl); exact R14).
assert (E17 : ew E 17 = w64 SHADOW_OFF) by (rewrite (ER 17%nat 17%bv eq_refl); exact R17).
assert (E22 : ew E 22 = w64 (dec_b_len (d_n cx))) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22).
assert (E26 : ew E 26 = w64 olen) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 res) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
assert (E33 : ew E 33 = w64 out) by (subst E; apply cm_env_33).
clear HE.
(* +0x718: `bltu a4, a3` into the UBSan trap, refuted: i < olen leaves out + i in range *)
psrr_branch_tok RUN BR HS SHOK cm_Bspan.
{ exfalso. rewrite branch_ltu_U in Hc.
  rewrite (U_atom E 14 (18446744073709551615 - out)) in Hc by first [exact E14 | lia].
  rewrite (U_atom E 13 i) in Hc by first [exact E13 | lia].
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* +0x71c .. +0x748: the byte, its shadow check, the loop test *)
paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
cm_memeq HF.
psrr_branch_tok RUN BR HS SHOK cm_Bspan.
- (* i + 1 < olen: back to the head *)
  cm_norm Hc. rewrite cm_bne in Hc. unfold w64 in Hc. cm_unlit Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cm_Bspan 0x718; [cm_awr_ro|].
  cm_memeq HF. pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
  lazymatch goal with |- context [mkCfg _ ?mdx] => set (md2 := mdx) end.
  lazymatch type of HS with context [restrict _ ?msf] =>
    assert (Q2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs 2) by (cm_val HS);
    assert (Q3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs 3) by (cm_val HS);
    assert (Q4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs 4) by (cm_val HS);
    assert (Q8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs 8) by (cm_val HS);
    assert (Q9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs 9) by (cm_val HS);
    assert (HC2 : dec_b_core B cx ly S W (ms_regs msf) mem md2 dec_ev_6f0)
      by exact (cm_core_regs B cx ly S W regs mem md dec_ev_6f0 (ms_regs msf) md2 HC HJ Q2 Q3 Q4 Q8 Q9);
    apply (IH (i + 1) (ms_regs msf) mem md2); [lia | lia | exact HC2 | exact HM | exact HFILL | cm_val HS ..]
  end.
- (* i + 1 = olen: every byte read was the fill *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
  cm_memeq HF.
  (* +0x760 `bnez a2` into the abort: a2 = 0 | 0 *)
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  { exfalso. cm_norm Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
  cm_memeq HF.
  (* +0x764 `blez a0`: a0 = -1, so on to +0x830 *)
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  2:{ exfalso. cm_norm Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
  cm_memeq HF. pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
  change (pa_sigma DB___interceptor_trampoline_free) with (decodeb_sigma DB___interceptor_trampoline_free).
  rewrite <- HPCF.
  lazymatch goal with |- context [mkCfg _ ?mdx] => set (md2 := mdx) end.
  lazymatch type of HS with context [restrict _ ?msf] =>
    assert (Q2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs 2) by (cm_val HS);
    assert (Q3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs 3) by (cm_val HS);
    assert (Q4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs 4) by (cm_val HS);
    assert (Q8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs 8) by (cm_val HS);
    assert (Q9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs 9) by (cm_val HS);
    assert (HC2 : dec_b_core B cx ly S W (ms_regs msf) mem md2 dec_ev_6f0)
      by exact (cm_core_regs B cx ly S W regs mem md dec_ev_6f0 (ms_regs msf) md2 HC HJ Q2 Q3 Q4 Q8 Q9);
    apply (KFREE (ms_regs msf) mem md2 HC2 HM); [cm_val HS | | cm_val HS | cm_val HS]
  end.
  cm_ra HS. unfold w64. f_equal; vm_compute; reflexivity.
Qed.
End scan.
