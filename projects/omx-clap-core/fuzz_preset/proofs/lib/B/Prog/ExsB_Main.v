(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, record f8f98a95): ex_string (fuzz_preset.c :158-212,
   B_prog_sigma AS_ex_string = 0x84350) against the tex_string_specX (lib/A/PRH_FnEx.v, kit 98f44d272006).
   THE WALK: the entry segment (ExsB_Entry.v) to the loop head LH_AT at x0 + i0 + 1; the loop head by strong induction
   on in->end - p: LH_AT p from CUT_CONT (p + 1) and CUT_ESC p (ExsB_LH.v); CUT_ESC p from CUT_CONT (p + 2) and
   CUT_HEX1 p (ExsB_Esc.v); CUT_HEX1 -> CUT_HEX1R (the first ex_hex4 call, ExsB_Hex1.v) -> CUT_UTF8 (p + 6) or
   CUT_HEX2 (ExsB_Hex1R.v); CUT_HEX2 -> CUT_HEX2R (the second ex_hex4 call, ExsB_Hex2.v) -> CUT_UTF8 (p + 12)
   (ExsB_Hex2R.v); CUT_UTF8 -> CUT_UTF8R (the ex_utf8 call) -> CUT_CONT (ExsB_Utf8.v); CUT_CONT p' from LH_AT p'
   (ExsB_Cont.v, p' > p, the induction hypothesis); the exits CUT_FAIL / CUT_QUOTE (ExsB_Exit.v).
   Section hypotheses of the walk ex_string_walk_B: LAWS (AR_laws_x of the allocator invariant), HHEAD (the head width,
   8 <= cf_head), PAL (YC1fP.PALib at PI_prog_B: the shadow base through the GOT), HHEX4 / HUTF8 (the callees' run forms,
   ExsB_Callee.v). ex_string_holds_B discharges HHEX4 with ExHex4RunB.v's ex_hex4_run_B and HUTF8 with ExUtf8RunB.v's
   ex_utf8_run_B; its Section hypotheses are LAWS, HHEAD and PAL.
   rule 24: no function proved (segment form) - proves function ex_string. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB ExsB_Stmt ExsB_Model ExsB_Lib ExsB_Sym ExsB_Exit ExsB_Cont ExsB_LH ExsB_Callee ExsB_Esc ExsB_Hex1 ExsB_Hex1R ExsB_Hex2 ExsB_Hex2R ExsB_Utf8 ExsB_Entry ExHex4RunB ExUtf8RunB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).


Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis HHEX4 : texhex4_runB SK B prh_pst ARx (B_prog_sigma AS_ex_hex4).
Hypothesis HUTF8 : texutf8_runB SK B prh_pst ARx (B_prog_sigma AS_ex_utf8).

Lemma es_cont_of : forall E p, LH_AT B ARx SK E p -> CUT_CONT B ARx SK E p.
Proof. intros E p H. eapply es_cut_cont; eassumption. Qed.

Lemma es_lh_all : forall E p, LH_AT B ARx SK E p.
Proof.
intros E.
assert (IND : forall n p, (Z.to_nat (e_x0 E + es_len E - p) <= n)%nat -> LH_AT B ARx SK E p).
{ induction n as [|n IH]; intros p Hn.
  - unfold LH_AT. intros lyc Sc Hpc regs memc mdc k acc HP HB HK HEG Hpe. exfalso. lia.
  - destruct (Z_lt_le_dec p (e_x0 E + es_len E)) as [Hlt|Hge];
      [| unfold LH_AT; intros lyc Sc Hpc regs memc mdc k acc HP HB HK HEG Hpe; exfalso; lia].
    assert (IHp : forall p', p < p' -> CUT_CONT B ARx SK E p') by (intros p' Hp'; apply es_cont_of; apply IH; lia).
    eapply es_cut_lh; [eassumption | eassumption | apply IHp; lia |].
    eapply es_cut_esc; [eassumption | eassumption | apply IHp; lia |].
    eapply es_cut_hex1; [eassumption | eassumption | eassumption |].
    eapply es_cut_hex1r; [eassumption | eassumption | |].
    + eapply es_cut_utf8; [eassumption | eassumption | eassumption |].
      eapply es_cut_utf8r; [eassumption | eassumption | apply IHp; lia].
    + eapply es_cut_hex2; [eassumption | eassumption | eassumption |].
      eapply es_cut_hex2r; [eassumption | eassumption |].
      eapply es_cut_utf8; [eassumption | eassumption | eassumption |].
      eapply es_cut_utf8r; [eassumption | eassumption | apply IHp; lia]. }
intros p. apply (IND (Z.to_nat (e_x0 E + es_len E - p))). lia.
Qed.

Theorem ex_string_walk_B : tex_string_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
unfold tex_string_specX. intros ly S Hp W regs mem md ch q x0 i0 scr d x Lam peak cnt fail ran most own. cbv zeta.
intros HFP H10 Vp Ve Vs Hq8 Hspq Hqd HWIN HSRC HINBx Hlen3 Hi0 HWD HINBs Hdx Hdq HLED.
pose (E := MkEs ly S Hp W regs mem md ch q x0 i0 scr d x Lam peak cnt fail ran most own).
assert (HP : ES_PRE B ARx E).
{ unfold ES_PRE. cbn [e_ly e_S e_Hp e_W e_regs e_mem e_md e_ch e_q e_x0 e_i0 e_scr e_d e_x e_Lam e_peak e_cnt e_fail e_ran
    e_most e_own E].
  unfold es_len. cbn [e_x E].
  exact (conj HFP (conj H10 (conj Vp (conj Ve (conj Vs (conj Hq8 (conj Hspq (conj Hqd (conj HWIN (conj HSRC
    (conj HINBx (conj Hlen3 (conj Hi0 (conj HWD (conj HINBs (conj Hdx (conj Hdq HLED))))))))))))))))). }
change (SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0) (e_regs E) (e_mem E) (e_md E)) (ES_POST B ARx SK E)).
eapply es_cut_entry. all: first [exact HP | apply es_lh_all | eassumption].
Qed.
End c.

(* the walk with both callee run forms discharged: ex_hex4 by ExHex4RunB.v's ex_hex4_run_B, ex_utf8 by ExUtf8RunB.v's
   ex_utf8_run_B *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.

Theorem ex_string_holds_B : tex_string_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
exact (ex_string_walk_B B ARx SK LAWS HHEAD PAL
  (ex_hex4_run_B SK B prh_pst ARx LAWS (pal_got_shadow (PI := PI_prog_B) B PAL) (pal_cell (PI := PI_prog_B) B PAL))
  (ex_utf8_run_B SK B prh_pst ARx LAWS (palib_core (PI := PI_prog_B) B PAL))).
Qed.
End d.

Print Assumptions ex_string_holds_B.
