(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, with its module paths changed; 107 of its 128 lines of code are new or changed and 301 lines of the source are left out. *)
(* The inlined owed_scribble_text loop of check_text_scribble at image A: 0x83908-0x83918, where the text byte is
   not a dot that a digit follows. The byte the turn appends is the text byte itself when it is below 128, and
   0x3f when it is not; the step is one text byte. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36 AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall CPgWalkIntr check_text_scribble_A
check_text_scribble_A_LD.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Lemma ctl_alt_holds : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q,
ctl_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 ->
ctl_join B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q ->
ctl_alt B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q.
Proof using TL LAWS ML.
unfold ctl_alt, ctl_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q ch n tb S2 fpos SP1 E0 fuel Q
  HPRE JOIN EZ msZ mdZ o i pre HS HAT E417 E418 E419 Ho Hfuel Hi HFLD Hplen HMOD HND HWANT.
destruct HPRE as (HE & H10 & H11 & H12 & Hn & Hstr & Hoq & Hoch & Hdst & Hdisj & EE & E32
  & Hfin2 & Hfrs2 & Eab & HSP1 & HSP1al).
red in HAT. destruct HAT as (AG & E33 & E38 & E60 & E61 & HJ & KT & HIO).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HJ0) as HAR.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble HE
  ltac:(unfold T_check_text_scribble, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold T_check_text_scribble, ESTACK in *.
pose proof (proj1 HJ) as HAR2.
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B lyc S2 W (ms_mem msZ) mdZ 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *.
assert (HZfr : forall a, F <= a < F + 64 -> cw_fresh B lyc Sc a).
{ intros a Ha. apply (cw_fresh_own B LAWS lyc Sc lyc S2 W (ms_mem msZ) mdZ 0 fpos a HAR2 Hfrs2
    ltac:(rewrite Eab; apply Permutation_refl) ltac:(intros; reflexivity)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
assert (B2 : spZ regs = bv_unsigned (ew E0 2)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
(* the text byte of this turn is a byte *)
pose proof Hstr as (Hq0 & Hgtb & Hin0 & Hcrd).
destruct (cts_cstring tb Hin0) as (Hzl & Hz0 & Hnz).
assert (Hilt : (Z.to_nat i < length tb)%nat) by lia.
destruct (Hgtb (Z.to_nat i) Hilt) as (_ & Hc8).
set (c := nth (Z.to_nat i) tb 0) in *.
pose proof HJ as HJn. clear HJ. rename HJn into HJ.
assert (SHOK : sh_ok tfibsegs CW_Bx [] EZ (mrestrict (w_H W) (ms_mem msZ))) by constructor.
assert (HWK : forall a, F + 32 <= a < F + 40 ->
  aview tfibsegs (w_H W) (ms_mem msZ) a = aview tfibsegs (w_H W) (ms_mem msZ) a) by (intros; reflexivity).
ctl_ufacts SP1 (spZ regs) E33 AG B2.
(* 0x83908 slli a0,a5,0x38; stop at 0x8390c bgez a0 *)
cw_run ctl_awr.
ctl_wkeep F. ctl_keep F HZfr.
cw_branch Hs.
all: lazymatch goal with HSx : st_ok _ ?Ev _ _ |- _ =>
     rewrite (ctl_bgez Ev _ (c * 2 ^ 56) (ctl_sll56 Ev 419 c E419 Hc8) ltac:(nia)) in Hs end.
- (* the byte is below 128: it is stored as it is *)
  assert (Hlt : c < 128) by (apply Z.ltb_lt in Hs; nia).
  cw_run_to ctl_awr 0x83918.
  ctl_wkeep F. ctl_keep F HZfr.
  rreg HS (15%bv : bv 5) R15. rreg HS (16%bv : bv 5) R16. rewrite E419 in R15.
  cw_join_win HS ctl_ss_join 490%nat ctl_deadJ_bv ltac:(idtac; ctl_join_hook).
  ctl_rebase.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (E460 : ew Ev 460 = Z_to_bv 64 c) by (rewrite ctl_ew460; exact R15);
    assert (E461 : ew Ev 461 = Z_to_bv 64 1) by (rewrite ctl_ew461; exact R16) end.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ => eapply (JOIN Ev msx mdx o i pre c 1) end end.
  1: exact HS.
  1: (red; split; [exact AG|]; split; [exact E33|]; split; [exact E38|]; split; [exact E60|];
      split; [exact E61|]; split; [eassumption|]; split; [exact KT | eapply same_io_trans; [exact HIO | cpw_io]]).
  1: exact E417. 1: exact E418. 1: exact E460. 1: exact E461.
  1: lia. 1: exact Hfuel. 1: lia. 1: lia. 1: (left; reflexivity). 1: lia. 1: exact HFLD. 1: exact Hplen.
  1: (replace (pre ++ [c]) with (pre ++ [if c <? 128 then c else 63])
        by (rewrite (proj2 (Z.ltb_lt c 128) Hlt); reflexivity);
      replace (i + 1) with (1 + i) by lia;
      exact (cts_model_one tb (Z.to_nat n) o i pre Hin0 HMOD ltac:(lia) ltac:(lia) HND)).
  1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
      apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ));
      [ intros y Hy; apply HWK; rewrite Hplen in Hjj; fold F; lia | exact Hvv ]).
- (* the byte is 128 or more: 0x3f is stored *)
  assert (Hge : 128 <= c) by (apply Z.ltb_ge in Hs; nia).
  cw_run_to ctl_awr 0x83918.
  ctl_wkeep F. ctl_keep F HZfr.
  rreg HS (15%bv : bv 5) R15. rreg HS (16%bv : bv 5) R16.
  cw_join_win HS ctl_ss_join 490%nat ctl_deadJ_bv ltac:(idtac; ctl_join_hook).
  ctl_rebase.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (E460 : ew Ev 460 = Z_to_bv 64 63) by (rewrite ctl_ew460; exact R15);
    assert (E461 : ew Ev 461 = Z_to_bv 64 1) by (rewrite ctl_ew461; exact R16) end.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    lazymatch type of HS with st_ok _ ?Ev _ _ => eapply (JOIN Ev msx mdx o i pre 63 1) end end.
  1: exact HS.
  1: (red; split; [exact AG|]; split; [exact E33|]; split; [exact E38|]; split; [exact E60|];
      split; [exact E61|]; split; [eassumption|]; split; [exact KT | eapply same_io_trans; [exact HIO | cpw_io]]).
  1: exact E417. 1: exact E418. 1: exact E460. 1: exact E461.
  1: lia. 1: exact Hfuel. 1: lia. 1: lia. 1: (left; reflexivity). 1: lia. 1: exact HFLD. 1: exact Hplen.
  1: (replace (pre ++ [63]) with (pre ++ [if c <? 128 then c else 63])
        by (rewrite (proj2 (Z.ltb_ge c 128) Hge); reflexivity);
      replace (i + 1) with (1 + i) by lia;
      exact (cts_model_one tb (Z.to_nat n) o i pre Hin0 HMOD ltac:(lia) ltac:(lia) HND)).
  1: (intros jj Hjj; destruct (HWANT jj Hjj) as (Hvv & Hrr); split; [|exact Hrr];
      apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msZ));
      [ intros y Hy; apply HWK; rewrite Hplen in Hjj; fold F; lia | exact Hvv ]).
Qed.
End d.
End b.
