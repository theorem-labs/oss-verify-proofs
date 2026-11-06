(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase CmdRep CmdObj CmdRo CmdZsh
  CmdRecBase CmdRecCells CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_reply_k check_reply_m check_reply_t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require check_reply_s1 check_reply_s2 check_reply_s3
  check_reply_s4 check_reply_s4b check_reply_s5 check_reply_s6 check_reply_s7 check_reply_s8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

(* the recorder's four GOT words (cmd_got_ok) are bytes of cmd_ro_ok (CmdRo.v RO_ptr_a7068 .. RO_ptr_a7080) *)
Ltac cr_got_word HBY a :=
  let H := fresh "H" in pose proof HBY as H;
  repeat lazymatch type of H with
  | abytes_atR _ a _ /\ _ => fail
  | _ /\ _ => apply proj2 in H
  end;
  try (lazymatch type of H with _ /\ _ => apply proj1 in H end);
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; rewrite (H k ltac:(cbv [RO_ptr_a7068 RO_ptr_a7070 RO_ptr_a7078 RO_ptr_a7080 length map]; lia));
  do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
Lemma cr_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [HBY _]. unfold cmd_ro_bytes in HBY. unfold cmd_got_ok, aval_mem.
split; [cr_got_word HBY 0xa7068|]. split; [cr_got_word HBY 0xa7070|]. split; [cr_got_word HBY 0xa7078|].
cr_got_word HBY 0xa7080.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own: the program callees and the runtime entries (check_reply_c.v:97-110) *)
Hypothesis CRA : forall fx0 : YK11.FPState, @tcheck_reply_answer_spec fx0 rc SK PI B MT.
Hypothesis SRC : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis RCD : forall fx0 : YK11.FPState, @trec_code_declared_spec fx0 rc SK PI B MT.
Hypothesis RSO : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis SRM : forall fx0 : YK11.FPState, @tsyntax_reply_matches_spec fx0 rc SK PI B MT.
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState, @amemchr0_nf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_memchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) A_SSP_GOT A_SSP_GUARD.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).

(* the walk's engine facts, the walk hypotheses with cgif's names (LAWS, TL, TLF, ML, SMP, HB, SIGP), and
   IMG, the image facts the kit's cmd_rec_cells, cmd_ro_ok_of_aro, cmd_ro_in_img and CmdRecImg's lemmas take, whose
   fields cif_relro_img and cif_ro_below_ofl are RRO and ro_below_ofl at CMD_RLO / CMD_RHI *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis HB : CmdBSyms B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.

(* the segments chained; the three after snprintf at every FP state *)
Theorem cr_walk : CR_ENTRY_stmt B RLO RHI.
Proof.
pose proof (cif_relro_img _ _ IMG) as RRO.
pose proof (cif_ro_below_ofl _ _ IMG : ro_below_ofl SEGS RLO RHI) as RO.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG) as CMD_RO_AT.
assert (EPIF : forall fx0 : YK11.FPState, CR_EPI_stmt (fx := fx0) B RLO RHI)
  by (intros fx0; eapply (check_reply_s8.cr_s8 (fx := fx0)); eassumption).
assert (STRCMPF : forall fx0 : YK11.FPState, CR_STRCMP_stmt (fx := fx0) B RLO RHI).
{ intros fx0. pose proof (EPIF fx0) as EPI0. eapply (check_reply_s5.cr_s5 (fx := fx0)); eassumption. }
assert (RSNPF : forall fx0 : YK11.FPState, CR_RSNP_stmt (fx := fx0) B RLO RHI).
{ intros fx0. pose proof (STRCMPF fx0) as STRCMP0. eapply (check_reply_s4b.cr_s4b (fx := fx0)); eassumption. }
pose proof (EPIF fx) as EPI.
assert (JOIN : CR_JOIN_stmt B RLO RHI) by (eapply check_reply_s7.cr_s7; eassumption).
assert (STRLEN : CR_STRLEN_stmt B RLO RHI) by (eapply check_reply_s6.cr_s6_of; eassumption).
assert (SNP : CR_SNP_stmt B RLO RHI) by (eapply check_reply_s4.cr_s4; eassumption).
assert (CODE : CR_CODE_stmt B RLO RHI) by (eapply check_reply_s3.cr_s3; eassumption).
assert (MC : CR_MC_stmt B RLO RHI) by (eapply check_reply_s2.cr_s2; eassumption).
eapply check_reply_s1.cr_s1; eassumption.
Qed.

Theorem pb_check_reply : tcheck_reply_spec B MT.
Proof.
unfold tcheck_reply_spec.
intros ly S W regs mem md ch w ww p0 n rep ans xr w0 R O HPRE HFRM Hfr7 HROD HROK HVO H10 Hw64 HREC Hn1 Hry Hno0
  Hrep Hrep64 Htr Hans Hans64 Hta Hw8 Hspw Hwhi Hww Hww64 Hnv Hn HN0 HAOK HRY HEV.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR) as (HFL & HGRD & (ev & HERR)).
pose proof (cr_got_of_ro _ HROK) as HGOT.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & PAlo & PAhi & _).
unfold page_aligned in PAlo, PAhi. unfold WORDS_W, WORDS_N in *.
(* the words' fields lie in the stack window, whose shadow AR's zshadow_ok gives *)
assert (HWRA : range_addressable (rdW W mem) SHADOW_OFF (w + 16) 12).
{ pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR (or_introl eq_refl)) as Zs.
  apply (range_addressable_sub _ _ (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)).
  - apply zero_shadow_range; [exact (mod4096_8 _ PAlo) | | exact Zs].
    rewrite Zminus_mod, (mod4096_8 _ PAlo), (mod4096_8 _ PAhi). reflexivity.
  - lia.
  - lia. }
(* w and ly_stk_hi ly are 8-aligned, so the words' last 8-byte word ends inside the window *)
assert (HWHI : w + 32 <= ly_stk_hi ly).
{ pose proof (mod4096_8 _ PAhi) as Hh8.
  pose proof (Z.div_mod w 8 ltac:(lia)) as Dw. pose proof (Z.div_mod (ly_stk_hi ly) 8 ltac:(lia)) as Dh.
  rewrite Hw8 in Dw. rewrite Hh8 in Dh. lia. }
assert (HN0' : n <> 0 ->
  in_blockA (ablocks B ly S) ww 8 /\ aval_mem (rdW W mem) ww 8 p0 /\
  in_blockA (ablocks B ly S) p0 (Z.of_nat (length w0) + 1) /\ astr_atR (rdW W mem) p0 w0 /\
  atail_vis SEGS W mem (p0 + Z.of_nat (length w0))).
{ intros Hn0. destruct (HN0 Hn0) as (A1 & _ & A2 & _ & A4 & A5 & A6). exact (conj A1 (conj A2 (conj A4 (conj A5 A6)))). }
assert (CX : cr_cx B RLO RHI (mkCRV ly S W regs mem md ch w ww p0 n rep ans ev xr w0 R O)).
{ unfold cr_cx. cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_w c_ww c_p0 c_n c_rep c_ans c_ev c_xr c_w0 c_R c_O].
  exact (conj HPRE (conj Hfr7 (conj HROD (conj HGOT (conj HROK (conj (cmd_ro_in_img SEGS B LAWS HB IMG) (conj HVO
    (conj HGRD (conj H10 (conj HREC (conj Hn1 (conj Hry (conj Hno0 (conj Hrep (conj Htr (conj Hans (conj Hta (conj Hw8
    (conj Hspw (conj HWRA (conj Hww (conj Hnv (conj Hn (conj HN0' (conj HAOK (conj HRY (conj HFL (conj HERR (conj HEV
    HWHI))))))))))))))))))))))))))))). }
assert (BD : cr_bd (mkCRV ly S W regs mem md ch w ww p0 n rep ans ev xr w0 R O)).
{ unfold cr_bd. cbn [c_w c_rep c_ans c_ww c_n c_p0].
  refine (conj Hw64 (conj Hrep64 (conj Hans64 (conj Hww64 (conj _ _))))).
  - intros Hn0. destruct (HN0 Hn0) as (_ & _ & _ & Hp0 & _). exact Hp0.
  - intros Hn0. destruct (HN0 Hn0) as (_ & Hwa & _). exact Hwa. }
exact (cr_walk (mkCRV ly S W regs mem md ch w ww p0 n rep ans ev xr w0 R O) CX BD HFRM).
Qed.
End e.
End f.
End d.
