(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb, facts 8f3e7e1a07f1): ex_string
   (fuzz_preset.c :185-239, A_prog_sigma AS_ex_string = 0x84034) against the kit's tex_string_specX (lib/A/PRH_FnEx.v).
   THE WALK: the entry segment (ExsA_Entry.v) to the loop head LH_AT at x0 + i0 + 1; the loop head by strong induction
   on in->end - p: LH_AT p from CUT_CONT (p + 1) and CUT_ESC p (ExsA_LH.v); CUT_ESC p from CUT_CONT (p + 2) and
   CUT_HEX1 p (ExsA_Esc.v); CUT_HEX1 -> CUT_HEX1R (the first ex_hex4 call, ExsA_Hex1.v) -> CUT_UTF8 (p + 6) or
   CUT_HEX2 (ExsA_Hex1R.v); CUT_HEX2 -> CUT_HEX2R (the second ex_hex4 call, ExsA_Hex2.v) -> CUT_UTF8 (p + 12)
   (ExsA_Hex2R.v); CUT_UTF8 -> CUT_UTF8R (the ex_utf8 call) -> CUT_CONT (ExsA_Utf8.v); CUT_CONT p' from LH_AT p'
   (ExsA_Cont.v, p' > p, the induction hypothesis); the exits CUT_FAIL / CUT_QUOTE (ExsA_Exit.v).
   PORTED from lib/B/Prog/ExsB_Main.v (a Theorem Labs lane's B' walk), VERBATIM in its composition (es_cont_of, es_lh_all,
   ex_string_walk_A, ex_string_holds_A): only the image names (prh_img_A, A_prog_listing, PI_prog_A) and the callee run
   forms (ExsA_Callee.v; proved by ExHex4RunA.v / ExUtf8RunA.v) changed. No top-level Print Assumptions (the donor's is
   not carried: it would print in every importer's build).
   Section hypotheses of ex_string_holds_A: LAWS (AR_laws_x of the allocator invariant, at cf_head), HHEAD
   (8 <= cf_head), PAL (YC1fP.PALib at PI_prog_A: the shadow base through the GOT; the A' witness is lib/A/PALibA.v
   palib_A at B := AD2l.TfibB). ex_string_walk_A also takes HHEX4 / HUTF8 (the callees' run forms), discharged in
   Section d.
   rule 24: proves function ex_string (reuse search: proof-index ex_string, index v5 2026-10-30T12:30:20Z, CONFIRM
   by lane ExStringLookupCheck; donor a Theorem Labs lane's lib/B/Prog/ExsB_*.v at a working branch 66eac2b9522a). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Lib ExsA_Sym ExsA_Exit ExsA_Cont ExsA_LH ExsA_Callee ExsA_Esc ExsA_Hex1 ExsA_Hex1R ExsA_Hex2 ExsA_Hex2R ExsA_Utf8 ExsA_Entry ExHex4RunA ExUtf8RunA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExsB_Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).


Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.
Hypothesis HHEX4 : texhex4_runA SK B prh_pst ARx (A_prog_sigma AS_ex_hex4).
Hypothesis HUTF8 : texutf8_runA SK B prh_pst ARx (A_prog_sigma AS_ex_utf8).

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

Theorem ex_string_walk_A : tex_string_specX (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
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

(* the walk with both callee run forms discharged: ex_hex4 by ExHex4RunA.v's ex_hex4_run_A, ex_utf8 by ExUtf8RunA.v's
   ex_utf8_run_A *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.

Theorem ex_string_holds_A : tex_string_specX (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof.
exact (ex_string_walk_A B ARx SK LAWS HHEAD PAL
  (ex_hex4_run_A SK B prh_pst ARx LAWS (pal_got_shadow (PI := PI_prog_A) B PAL) (pal_cell (PI := PI_prog_A) B PAL))
  (ex_utf8_run_A SK B prh_pst ARx LAWS (palib_core (PI := PI_prog_A) B PAL))).
Qed.
End d.
