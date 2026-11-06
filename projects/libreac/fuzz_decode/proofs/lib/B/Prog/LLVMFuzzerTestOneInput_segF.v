(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segF: the image-B cmp segment of libreac/fuzz_decode's LLVMFuzzerTestOneInput,
   llvm_b_cmp_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v (+0x6f0 .. +0x83c, llvm_b_st_6f0 -> llvm_b_st_840).

   The head, +0x6f0 .. +0x7c0 / +0x718 (cm_head below):
     +0x6f0 .. +0x6fc  s3 - 1 | ns against a0; `bne` into the abort +0xb88, refuted: a0 = plain_ok ? ns : -1 and
                       s3 = plain_ok ? 1 : 0 (llvm_b_st_6f0), so the two sides agree (cm_or_check's arithmetic)
     +0x700 bgez a0    plain_ok: a0 = ns > 0, on to +0x764; not plain_ok: a0 = -1, into the scan loop L2 at +0x718
     +0x764 blez a0, +0x768 beqz s11 (UBSan: copy null), +0x774 bltu -51, copy (UBSan: copy + 50 wraps; discharged by
                       the engine from atom 34), +0x780 blez s7: all refuted on the plain_ok path (ns > 0, copy >= 4096,
                       nch > 0); +0x784 .. +0x7b8 the loops' registers, +0x7bc sd 3 * ns, 48(s1)
   then lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_scan.v (L2, the refused path) or
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_loop.v (L3 / L4, the accepted path), both ending at the call of free #1,
   and lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_tail.v (free #1 and reac_upstream_channels, up to llvm_b_st_840).
   Engine and shape: a Theorem Labs lane's walks of record (a working branch, lib/A/Prog/GrantEntrySweepS2.v, S4.v, S1.v) on
   this unit's Pa kit; the cut-state shape is cgif_file_fuzzer's lib/A/ACf5.v; the composition of the stages is
   cgif lib/A/ACfj.v's (SRr_bind of each stage's statement). *)
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
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require DecodeCallocWrapB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_segX_cmp_defs
LLVMFuzzerTestOneInput_segX_cmp_kit LLVMFuzzerTestOneInput_segX_cmp_st LLVMFuzzerTestOneInput_segX_cmp_scan
LLVMFuzzerTestOneInput_segX_cmp_loop LLVMFuzzerTestOneInput_segX_cmp_tail.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_decode_plain_le_c reac_upstream_channels_cg.
Import ListNotations.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Module CPlainF := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_c.
Module LUpChannelsF := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_cg.

Section head. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := decodesegsB0.
#[local] Notation VAL := decodeb_val.
#[local] Notation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HPCF : pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free.
Hypothesis HCELLS : dec_crt_cells B.
Hypothesis HROS : dec_ro_rd_unowned B.
Hypothesis HRNE : dec_rom_no_errno B.
Hypothesis ABCMP : @abcmp_realizes fx rc SEGS B (decodeb_sigma DB___interceptor_trampoline_bcmp).
Variable cx : dctx.
(* The entry's read-only view, which the journal carries to every state (cm_rom_rd). *)
Hypothesis HROMcx : rom_view SEGS (d_W cx) (d_mem cx).
Hypothesis Hnlen : d_n cx = Z.of_nat (length (d_pl cx)).
Variables (ly : alayout) (S : astate) (W : world SEGS) (out res mode nch ns : Z).
Hypothesis Hinout : In (out, dec_b_olen nch ns) (ablocks B ly S).
Hypothesis Hinres : In (res, dec_b_len (d_n cx)) (ablocks B ly S).
Variable Q : world SEGS -> config -> Prop.
Hypothesis KFREE : forall regs mem md,
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 -> cm_mem cx out res mode nch ns W mem ->
  YK11.getr regs 10 = w64 out -> YK11.getr regs 1 = w64 (DEC_A_LLVMF + 0x838) ->
  YK11.getr regs 22 = w64 (dec_b_len (d_n cx)) -> YK11.getr regs 27 = w64 res ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (YK11.seg_rom SEGS)) md) Q.

Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let RUNTO := @paj_run_to fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

Lemma cm_olen_pos : 1 <= dec_b_olen nch ns.
Proof.
unfold dec_b_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:Hb; [|lia].
apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1, H2. clear - H1 H2. nia.
Qed.

(* +0x6f0 .. the scan loop's head (+0x718) or the bcmp loops' head (+0x7c0). *)
Lemma cm_head : forall regs mem md,
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 ->
  cm_mem cx out res mode nch ns W mem ->
  -128 <= nch <= 127 -> -128 <= ns <= 127 ->
  (CPlainF.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true ->
     garr8 SEGS (mrestrict (w_H W) mem) out
       (map (fun b : byte => bv_unsigned b) (CPlainF.plain_out (d_body cx) nch ns))) ->
  (CPlainF.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = false -> dec_b_filled W mem out (dec_b_olen nch ns)) ->
  YK11.getr regs 10 = w64 (if CPlainF.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns then ns else -1) ->
  YK11.getr regs 19 = w64 (if CPlainF.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns then 1 else 0) ->
  YK11.getr regs 22 = w64 (dec_b_len (d_n cx)) -> YK11.getr regs 23 = w64 nch ->
  YK11.getr regs 26 = w64 (dec_b_olen nch ns) -> YK11.getr regs 27 = w64 res ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x6f0)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros regs mem md HC HM Hnchb Hnsb Hpt Hpf.
pose proof HC as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out _ HAR Hinout) as (_ & Ho4096 & Hoceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res _ HAR Hinres) as (_ & Hr4096 & Hrceil & _ & Hrpres & _).
pose proof (req_size_pos (dec_b_olen nch ns) ltac:(pose proof cm_olen_pos; lia)) as [_ Hrqo].
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(unfold dec_b_len; lia)) as [Hrq1 Hrqr].
pose proof (@alloc_ceiling_val rc) as [ACR _].
pose proof cm_olen_pos as Holen1.
pose proof (@cm_stokR fx rc B cx W ly S regs mem md dec_ev_6f0 out res mode nch ns 0x6f0 HC HM
  ltac:(lia) ltac:(lia)) as HS.
remember (cm_env cx regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 0)
  as E eqn:HE.
assert (SHOK : sh_ok SEGS cm_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply cm_env_img).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs r)
  by (intros kk r Hkk; subst E; apply cm_env_reg; exact Hkk).
assert (E2 : ew E 2 = YK11.getr regs 2) by exact (ER 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = YK11.getr regs 3) by exact (ER 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = YK11.getr regs 4) by exact (ER 4%nat 4%bv eq_refl).
assert (E8 : ew E 8 = YK11.getr regs 8) by exact (ER 8%nat 8%bv eq_refl).
assert (E9 : ew E 9 = YK11.getr regs 9) by exact (ER 9%nat 9%bv eq_refl).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; apply cm_env_32).
assert (E33 : ew E 33 = w64 out) by (subst E; apply cm_env_33).
assert (E39 : ew E 39 = w64 (res + 50)) by (subst E; apply cm_env_39).
assert (E36 : ew E 36 = w64 (ns mod 2 ^ 64)) by (subst E; apply cm_env_36).
assert (E37 : ew E 37 = w64 (nch mod 2 ^ 32)) by (subst E; apply cm_env_37).
destruct (CPlainF.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns) eqn:Hp;
  intros R10 R19 R22 R23 R26 R27; cbv iota in R10, R19;
  (assert (E10 : ew E 10 = YK11.getr regs 10) by exact (ER 10%nat 10%bv eq_refl)); rewrite R10 in E10;
  (assert (E19 : ew E 19 = YK11.getr regs 19) by exact (ER 19%nat 19%bv eq_refl)); rewrite R19 in E19;
  (assert (E23 : ew E 23 = YK11.getr regs 23) by exact (ER 23%nat 23%bv eq_refl)); rewrite R23 in E23;
  (assert (E22 : ew E 22 = w64 (dec_b_len (d_n cx))) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22));
  (assert (E26 : ew E 26 = w64 (dec_b_olen nch ns)) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26));
  (assert (E27 : ew E 27 = w64 res) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27));
  clear HE ER.
- (* ---- plain_ok: on to the bcmp loops ---- *)
  destruct (cm_plain_ok_facts _ _ _ _ Hp) as (Hlen & Hnch0 & Hns0 & Hprod).
  assert (Hs64 : ns mod 2 ^ 64 = ns) by (apply Z.mod_small; lia).
  assert (Hn32 : nch mod 2 ^ 32 = nch) by (apply Z.mod_small; lia).
  rewrite Hs64 in E36. rewrite Hn32 in E37.
  specialize (Hpt eq_refl). clear Hpf.
  (* +0x6fc: a0 = ns against (1 - 1) | ns *)
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|]. cm_memeq HF.
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  { exfalso. cm_norm Hc. unfold w64 in Hc. cm_unlit Hc. change (1 + -1) with 0 in Hc.
    rewrite cm_or0, cm_bne, Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc.
  (* +0x700 `bgez a0`: taken *)
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|]. cm_memeq HF.
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  2:{ exfalso. cm_norm Hc. unfold w64 in Hc. rewrite cm_bge in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* +0x764 `blez a0`: not taken *)
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|]. cm_memeq HF.
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  { exfalso. cm_norm Hc. unfold w64 in Hc. rewrite cm_bge in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  (* +0x768 `beqz s11` into the UBSan trap: the copy is not null *)
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|]. cm_memeq HF.
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  { exfalso. cm_norm Hc. rewrite cm_beq in Hc. unfold w64 in Hc. cm_unlit Hc. apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  (* +0x774 is the engine's; +0x780 `blez s7`: nch > 0 *)
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|]. cm_memeq HF.
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  { exfalso. cm_norm Hc. unfold w64 in Hc. rewrite cm_bge in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  (* +0x784 .. +0x7b8: the loops' registers *)
  paj_run_to_tok RUNTO HS HJ SHOK cm_Bspan 0x7bc; [cm_awr_ro|]. cm_memeq HF.
  pmkst HS. rewrite Hmem. rewrite Hmem in HJ. clear Hmem.
  lazymatch goal with |- context [mkCfg _ ?mdx] => set (md2 := mdx) end.
  lazymatch type of HS with context [restrict _ ?msf] =>
    assert (G2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs 2) by (cm_val HS);
    assert (G3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs 3) by (cm_val HS);
    assert (G4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs 4) by (cm_val HS);
    assert (G8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs 8) by (cm_val HS);
    assert (G9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs 9) by (cm_val HS);
    assert (G10 : YK11.getr (ms_regs msf) 10 = w64 (3 * ns))
      by (cm_valU HS; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom _ 36 ns) by first [exact E36 | lia];
          rewrite U_lit by lia; rewrite zcanon_id by (unfold M64; lia); lia);
    assert (G18 : YK11.getr (ms_regs msf) 18 = w64 0) by (cm_val HS);
    assert (G20 : YK11.getr (ms_regs msf) 20 = w64 0) by (cm_val HS);
    assert (G21 : YK11.getr (ms_regs msf) 21 = w64 (18446744073709551615 - out))
      by (cm_valU HS; rewrite (U_not _ 33 out) by first [exact E33 | lia]; lia);
    assert (G22 : YK11.getr (ms_regs msf) 22 = w64 0) by (cm_val HS);
    assert (G23 : YK11.getr (ms_regs msf) 23 = w64 (3 * nch))
      by (cm_valU HS; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom _ 37 nch) by first [exact E37 | lia];
          rewrite U_lit by lia; rewrite zcanon_id by (unfold M64; lia); lia);
    assert (G25 : YK11.getr (ms_regs msf) 25 = w64 (18446744073709551615 - (res + 50)))
      by (cm_valU HS; rewrite (U_not _ 39 (res + 50)) by first [exact E39 | lia]; lia);
    assert (G27 : YK11.getr (ms_regs msf) 27 = w64 0) by (cm_val HS);
    set (r2 := ms_regs msf) in *
  end.
  assert (HC2 : dec_b_core B cx ly S W r2 mem md2 dec_ev_6f0)
    by exact (cm_core_regs B cx ly S W regs mem md dec_ev_6f0 r2 md2 HC HJ G2 G3 G4 G8 G9).
  clear HS SHOK HEI E2 E3 E4 E8 E9 E10 E19 E22 E23 E26 E27 E32 E33 E36 E37 E39.
  (* +0x7bc `sd a0, 48(s1)`: the one store of the segment, on the head state's write window *)
  pose proof (@cm_stok fx rc B cx W ly S r2 mem md2 dec_ev_6f0 out res mode nch ns 0x7bc 0 0 HC2 HM
    ltac:(lia) ltac:(lia)) as HS.
  assert (EPC : w64 (DEC_A_LLVMF + 0x7bc) = Z_to_bv 64 (BASE + 0x7bc)) by (unfold w64; f_equal; vm_compute; reflexivity).
  rewrite EPC in HS. clear EPC.
  pose proof HC2 as (HJ2 & _ & _ & R9 & _ & Hsp0b & _).
  destruct (cm_sp1 B cx ly S W r2 mem md2 dec_ev_6f0 HC2) as (Hsp1lo & Hsp1hi & _ & _).
  assert (Hsp64 : 0 <= d_sp1 cx < 2 ^ 64) by lia.
  pose proof (@cm_awr rc B cx r2 out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 0
    ly S 0x7bc R9 Hsp64 Hsp0b) as HAWR.
  pose proof (cm_E9 cx r2 out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 0 R9 Hsp64)
    as F9u.
  remember (cm_env cx r2 out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 0)
    as E2 eqn:HE2.
  assert (SHOK : sh_ok SEGS cm_Bx [] E2 (mrestrict (w_H W) mem)) by constructor.
  assert (HEI : img_env VAL A_LIM E2) by (subst E2; apply cm_env_img).
  assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = YK11.getr r2 r)
    by (intros kk r Hkk; subst E2; apply cm_env_reg; exact Hkk).
  assert (F2 : ew E2 2 = YK11.getr r2 2) by exact (ER 2%nat 2%bv eq_refl).
  assert (F3 : ew E2 3 = YK11.getr r2 3) by exact (ER 3%nat 3%bv eq_refl).
  assert (F4 : ew E2 4 = YK11.getr r2 4) by exact (ER 4%nat 4%bv eq_refl).
  assert (F8 : ew E2 8 = YK11.getr r2 8) by exact (ER 8%nat 8%bv eq_refl).
  assert (F9 : ew E2 9 = YK11.getr r2 9) by exact (ER 9%nat 9%bv eq_refl).
  assert (F10 : ew E2 10 = w64 (3 * ns)) by (rewrite (ER 10%nat 10%bv eq_refl); exact G10).
  assert (F18 : ew E2 18 = w64 0) by (rewrite (ER 18%nat 18%bv eq_refl); exact G18).
  assert (F20 : ew E2 20 = w64 0) by (rewrite (ER 20%nat 20%bv eq_refl); exact G20).
  assert (F21 : ew E2 21 = w64 (18446744073709551615 - out)) by (rewrite (ER 21%nat 21%bv eq_refl); exact G21).
  assert (F22 : ew E2 22 = w64 0) by (rewrite (ER 22%nat 22%bv eq_refl); exact G22).
  assert (F23 : ew E2 23 = w64 (3 * nch)) by (rewrite (ER 23%nat 23%bv eq_refl); exact G23).
  assert (F25 : ew E2 25 = w64 (18446744073709551615 - (res + 50))) by (rewrite (ER 25%nat 25%bv eq_refl); exact G25).
  assert (F27 : ew E2 27 = w64 0) by (rewrite (ER 27%nat 27%bv eq_refl); exact G27).
  clear HE2 ER.
  paj_run_to_tok RUNTO HS HJ2 SHOK cm_Bspan 0x7c0; [exact HAWR|].
  pmkst HS.
  lazymatch goal with |- context [mkCfg _ ?mdx] => set (md3 := mdx) end.
  lazymatch type of HS with context [restrict _ ?msf] => set (ms3 := msf) in * end.
  (* what the store changed: 48(s1) alone *)
  assert (KRAW : forall x : word, ~ (d_sp1 cx + 48 <= bv_unsigned x < d_sp1 cx + 56) -> ms_mem ms3 x = mem x).
  { intros x Hx. apply HF. intros (r & Hr & Ha). unfold cm_ss in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | []]. unfold cm_spill in Ha.
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite F9u in Ha. lia. }
  assert (KAV : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 48 <= a < d_sp1 cx + 56) ->
    aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hn. unfold aview, mbyte, mrestrict. rewrite KRAW; [reflexivity|].
    rewrite unsigned_lit_small by lia. exact Hn. }
  pose proof HC2 as (_ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFpres & _ & Hpay & _).
  pose proof HJ2 as (HAR3 & Hly3 & _).
  pose proof HC2 as (HJc & _). pose proof HJc as (HARo & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & Hstk00 & Hceil & Hslo & Hshi & H47 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & HlyF & _).
  assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
  assert (SHV : SHADOW_OFF = 0x7fff8000) by reflexivity.
  assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs2; left; reflexivity).
  assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly S W _ _ DEC_FCLASS (d_fpos cx) HAR3 Hin0) as (Hfb1 & Hfb2 & _).
  rewrite EFA in Hfb1, Hfb2. change (fs_frame_bytes DEC_FCLASS) with 64 in Hfb2.
  assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
    by (intros a Ha; apply KAV; lia).
  assert (KH : forall a, d_SH cx <= a < d_SH cx + 8 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
  { intros a Ha. unfold d_SH, shadow_addr in Ha.
    pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)).
    assert (d_F cx / 8 <= 17592186044416)
      by (change 17592186044416 with (2 ^ 47 / 8); apply Z.div_le_mono; lia).
    rewrite SHV in Ha. apply KAV; lia. }
  (* the registers at +0x7c0 are those of +0x7bc *)
  lazymatch type of HS with context [restrict _ ?msf] =>
    assert (H2 : YK11.getr (ms_regs msf) 2 = YK11.getr r2 2) by (cm_val HS);
    assert (H3 : YK11.getr (ms_regs msf) 3 = YK11.getr r2 3) by (cm_val HS);
    assert (H4 : YK11.getr (ms_regs msf) 4 = YK11.getr r2 4) by (cm_val HS);
    assert (H8 : YK11.getr (ms_regs msf) 8 = YK11.getr r2 8) by (cm_val HS);
    assert (H9 : YK11.getr (ms_regs msf) 9 = YK11.getr r2 9) by (cm_val HS)
  end.
  assert (HC3 : dec_b_core B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 dec_ev_6f0).
  { apply (cm_core_kept B cx ly S W r2 mem md2 dec_ev_6f0 ly S W (ms_regs ms3) (ms_mem ms3) md3 dec_ev_6f0 HC2 HJ2).
    - exact Hfrs2.
    - exact H8.
    - exact H9.
    - unfold spZ. rewrite H2. reflexivity.
    - exact H3.
    - exact H4.
    - intros a Ha. apply KAV; lia.
    - exact KF.
    - intros a Ha. destruct (HFpres a Ha) as [Hh (b & Hb)]. split; [exact Hh|]. exists b.
      rewrite KRAW; [exact Hb|]. rewrite unsigned_lit_small by lia. lia.
    - exact Hpay.
    - intros i Hi. rewrite <- Hnlen in Hi.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ (d_p cx) (d_n cx) HAR3 (Hpay ltac:(lia))) as (_ & Hp4096 & Hpceil & _).
      pose proof (req_size_pos (d_n cx) ltac:(lia)) as [_ Hrqp].
      apply KAV; lia. }
  assert (HM3 : cm_memL cx W out res mode nch ns (ms_mem ms3)).
  { pose proof HJ2 as (HAR4 & _).
    split; [|split].
    - apply (cm_mem_kept B cx ly S W mem md2 ly S W (ms_mem ms3) md3 out res mode nch ns HCELLS HARo HAR4
        (cm_rom_rd B cx _ _ _ _ _ _ _ _ HROS HRNE HROMcx HJc) (cm_rom_rd B cx _ _ _ _ _ _ _ _ HROS HRNE HROMcx HJ2)).
      + intros a Ha Hn. apply KAV; lia.
      + exact KF.
      + exact KH.
      + intros i Hi.
        assert (Hbl : Z.of_nat (length (d_body cx)) <= dec_b_len (d_n cx)).
        { unfold d_body, dec_b_len, dec_b_u. rewrite length_skipn. lia. }
        apply KAV; lia.
      + exact HM.
    - (* 48(s1) = 3 * ns, from the run's own state *)
      pose proof (cm_region_nth _ _ _ 0 _ HS eq_refl) as HR3.
      destruct HR3 as (_ & _ & _ & HCs). cbn [YP09.r_chunks] in HCs. inversion HCs as [|c cs HC48 _]; subst.
      cbn [YP09.r_base base_val] in HC48.
      assert (D10 : forall Ex, ew Ex 10 = ew E2 10 -> sv_denot Ex (SOff 10 0) = Z_to_bv 64 (3 * ns)).
      { intros Ex Hx. rewrite denot_lit_U. f_equal. apply (U_atom Ex 10 (3 * ns)); [rewrite Hx; exact F10 | lia]. }
      pose proof (val_of_chunk_ok SEGS _ _ _ 48 8%N (SOff 10 0) (3 * ns) HC48 (D10 _ eq_refl)
        ltac:(cbn; lia) ltac:(cbn; lia)) as V48.
      unfold dec_b_slot. rewrite <- F9u.
      apply DecodeCallocWrapB.val_mem_rdwordB; [lia | exact V48].
    - apply (cm_garr8_kept (w_H W) (w_H W) mem (ms_mem ms3)); [|exact Hpt].
      rewrite length_map, cm_plain_len. intros i Hi. apply KAV; lia. }
  (* +0x7c0: the bcmp loops *)
  apply (@cm_outer fx rc B LAWS HPCF HCELLS HROS HRNE ABCMP cx HROMcx Hnlen ly S W out res mode nch ns Hinout Hinres Hp
           ltac:(lia) ltac:(lia) Q KFREE (Z.to_nat nch) 0 (ms_regs ms3) (ms_mem ms3) md3);
    [lia | lia | exact HC3 | exact HM3 |].
  unfold cm_rL3; repeat split; cm_val HS.
- (* ---- not plain_ok: on to the scan loop ---- *)
  specialize (Hpf eq_refl). clear Hpt.
  (* +0x6fc: a0 = -1 against (0 - 1) | ns *)
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|]. cm_memeq HF.
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  { exfalso. cm_norm Hc. unfold w64 in Hc. cm_unlit Hc. change (0 + -1) with (-1) in Hc.
    rewrite cm_or_m1, cm_bne, Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc.
  (* +0x700 `bgez a0`: not taken, a0 = -1 *)
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|]. cm_memeq HF.
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  { exfalso. cm_norm Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cm_Bspan 0x718; [cm_awr_ro|]. cm_memeq HF.
  pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
  lazymatch goal with |- context [mkCfg _ ?mdx] => set (md2 := mdx) end.
  lazymatch type of HS with context [restrict _ ?msf] =>
    assert (G2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs 2) by (cm_val HS);
    assert (G3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs 3) by (cm_val HS);
    assert (G4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs 4) by (cm_val HS);
    assert (G8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs 8) by (cm_val HS);
    assert (G9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs 9) by (cm_val HS);
    apply (@cm_scan fx rc B LAWS HPCF cx ly S W out res mode nch ns Hinout Q KFREE
             (Z.to_nat (dec_b_olen nch ns)) 0 (ms_regs msf) mem md2);
    [ lia | lia
    | exact (cm_core_regs B cx ly S W regs mem md dec_ev_6f0 (ms_regs msf) md2 HC HJ G2 G3 G4 G8 G9)
    | exact HM | exact Hpf
    | cm_val HS | cm_val HS | cm_val HS
    | cm_valU HS; rewrite (U_not _ 33 out) by first [exact E33 | lia]; lia
    | cm_val HS | cm_val HS | cm_val HS | cm_val HS ]
  end.
Qed.
End head.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)
Section seg. Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem llvm_b_cmp_ok :
  llvm_b_cmp_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_cmp_stmt.
intros HPCF HUTR HCELLS HROS HRNE LAWS ML MTL ABCMP AFREE LUC cx W' c' HB HR H6f0.
destruct H6f0 as (fx & ly & S & regs & mem & md & res & out & mode & nch & ns & -> & Hfz & HC & Hperm & Hres4 &
  Hout4 & Hmle & Hmok & Hfrs & R10 & R18 & R19 & R20 & R21 & R22 & R23 & R26 & R27 & Hmode & Hfsh & Hbody & Hpt &
  Hpf & S24 & S32 & S40 & S56 & S64 & S72 & S80 & S88 & S112).
destruct (cm_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx HB)
  as (_ & _ & _ & _ & _ & _ & _ & Hnlen & _).
assert (HM : cm_mem cx out res mode nch ns W' mem).
{ split; [exact Hfrs|]. split; [exact Hfsh|]. split; [exact Hmode|]. split; [exact Hbody|].
  split; [exact S24|]. split; [exact S32|]. split; [exact S40|]. split; [exact S56|].
  split; [exact S64|]. split; [exact S72|]. split; [exact S80|]. split; [exact S88 | exact S112]. }
assert (Hinout : In (out, dec_b_olen nch ns) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
assert (Hinres : In (res, dec_b_len (d_n cx)) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app; right. apply in_or_app; left. left; reflexivity. }
pose proof Hmode as (_ & Hnchb & Hnsb & _).
apply (@cm_head fx rc B LAWS HPCF HCELLS HROS HRNE (ABCMP fx) cx HR Hnlen ly S W' out res mode nch ns Hinout Hinres
         (llvm_b_st_840 B MT cx)); [| exact HC | exact HM | exact Hnchb | exact Hnsb | exact Hpt | exact Hpf
         | exact R10 | exact R19 | exact R22 | exact R23 | exact R26 | exact R27].
intros regs2 mem2 md2 HC2 HM2 Ra0 Rra R22' R27'.
exact (@cm_tail rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI fx
         HPCF HUTR HCELLS HROS HRNE LAWS MTL AFREE LUC cx W' ly S regs2 mem2 md2 out res mode nch ns HB HR Hfz HC2 Hperm
         Hres4 Hmle Hmok HM2 Ra0 Rra R22' R27').
Qed.
End seg.
