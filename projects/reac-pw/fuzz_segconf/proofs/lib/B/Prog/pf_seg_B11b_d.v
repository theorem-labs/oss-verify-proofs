(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 49 of its 75 lines of code are new or changed and 492 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the INTERNAL cut statements of
   segment B11b of reac_segconf_parse_file's walk (the B11b segment lane of the image-B G3 walk owner, 2026-10-30).
   proves no function (kind: statement text); lib/B/Prog/pf_seg_B11b.v proves S_B11b with them.
   ADAPTED from the image-A G3 walk owner's image-A file lib/A/Prog/pf_a11b_d.v (a working branch, an image-A segment lane):
   the same join of the eleven tokens (pb11_J / pb11_kn are A's pf_J / pf_kn), re-cut on image B's code.

   B11b is MISS 0x88a50 -> KREFM 0x88bd0 (98 instructions with the slow path 0x89234-0x89238), inline check B#28
   (the catalogue row's shadow byte), the UBSan trap branches T23 - T27 of the join loop, the calls
   reac_box_catalogue (0x88ad8) and snprintf (0x88b9c, eleven passes). Its statement (lib/B/Prog/pf_pieces.v) is
     S_B11b : forall f0 n, HA_KREFM n -> H_MISS (fx := f0) B n.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), F the class-5 frame, SH = s5 its shadow:
     0x88a50 MISS    31 `sb zero,X(s5)` (cells 0x64 .. 0x81 known[240], 0x8a ntok: IN scope); ld s3,128(s1)
                     (slot 0x80 = F + 0x450 = &ntok); sd zero,0(s3); mv a0,s3
     0x88ad8 KCAT    jal reac_box_catalogue (a0 = &ntok; returns a0 = catA, ntok = 11)
     0x88adc KRET    ld a1,0(s3) (= 11); li a2,240; beqz a1 -> KREFM (not taken: 11); a4 = tab; s3 = ti = 0;
                     s11 = kn = 0; slot 0x68 = (tab <> 0) = 1; slot 0x60 = (tab & 7 = 0 /\ tab <> 0) = 1;
                     s8 = s7 = tab
     0x88b14 KLOOP   the join loop head, pass ti (s3 = ti, s11 = kn, s7 = s8 = tab + 296 ti, a4 = tab, a2 = 240):
                     T23 `bltu a2,s11` (240 < kn); a3 = ti ? "|" (0x21840) : "" (0x21860); a1 = tab + 296 ti;
                     T24 `beq a5,a2` (slot 0x68 against a1 = 0); T25 `bltu a1,a4` (a1 < tab); T26 the mulh
                     overflow test of 296 ti; T27 `beqz` slot 0x60; B#28 `lbu` of sh(tab + 296 ti) (`bnez` to the
                     slow path 0x89234 -> errpath_load8); s2 = tab (borrowed); a4 = ld 0(s8) = tab[ti].token;
                     a0 = slot 0x78 + kn = known + kn; a1 = 240 - kn; a2 = "%s%s" (0x21820)
     0x88b9c KSNP    jal wrapper_snprintf (snprintf(known + kn, 240 - kn, "%s%s", sep, tok))
     0x88ba0 KSRET   a2 = 240; a1 = ntok (ld 128(s1); ld 0(a1)); s3 = ti + 1; a4 = s2 = tab; s2 = '#';
                     `bgeu s3,a1` -> KREFM (taken at the eleventh pass); kn += a0; a0 = kn + 2; s7, s8 += 296;
                     `bltu a0,a2` -> KLOOP (taken: kn <= 77)
   KREFM (0x88bd0) is reached only from 0x88bb8 at ti + 1 = 11 (pf_pieces.v head comment, correction (6)): the
   exit at 0x88ae4 needs ntok = 0 and the one at 0x88bcc kn + 2 >= 240; reac_box_catalogue's post gives ntok =
   11 and pb11_kn ti <= 77 (pf_seg_B11b_f.v).

   The cut below (H_KLOOP, at every FP state as HA_KLOOP) is the loop head before pass ti, 0 <= ti < 11, in
   pf_pieces.v's form: INV_KLOOP over the machine state, and from it the walk reaches MISS's post. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The pcs B11b cuts at, as listing offsets (BASE + PF_<CUT>; BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition PF_KCAT : Z := AF_reac_segconf_parse_file + 0xca0.   (* 0x88ad8, jal reac_box_catalogue *)
Definition PF_KRET : Z := AF_reac_segconf_parse_file + 0xca4.   (* 0x88adc, where it returns *)
Definition PF_KLOOP : Z := AF_reac_segconf_parse_file + 0xcdc.  (* 0x88b14, the join loop head *)
Definition PF_KSNP : Z := AF_reac_segconf_parse_file + 0xd64.   (* 0x88b9c, jal wrapper_snprintf *)
Definition PF_KSRET : Z := AF_reac_segconf_parse_file + 0xd68.  (* 0x88ba0, where it returns *)
Lemma pb11_cut_pcs :
  seg_text + PF_KCAT = 0x88ad8 /\ seg_text + PF_KRET = 0x88adc /\ seg_text + PF_KLOOP = 0x88b14 /\
  seg_text + PF_KSNP = 0x88b9c /\ seg_text + PF_KSRET = 0x88ba0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** The join of the first ti tokens (SegModel.known_go; A's pf_J / pf_kn, the plain pf_p7_lemmas' p7_J / p7_kn) *)
Definition pb11_J (ti : nat) : list Z := known_go (firstn ti cat_toks) true 0 [].
Definition pb11_kn (ti : nat) : Z := Z.of_nat (length (pb11_J ti)).
(* the separator of pass ti: "" before the first token, "|" after *)
Definition pb11_sep (ti : nat) : list Z := if (ti =? 0)%nat then [] else [124].
Definition pb11_tok (ti : nat) : list Z := nth ti cat_toks [].
Definition pb11_args (ti : nat) : list arg := [AS (pb11_sep ti); AS (pb11_tok ti)].
(* the text pass ti renders, and its separator's literal (0x21860 "" for the first pass, 0x21840 "|" after) *)
Definition pb11_text (ti : nat) : list Z := pb11_sep ti ++ pb11_tok ti.

(** The bytes known[240] holds at the head of pass ti: nothing before the first pass, else the join so far and its
    NUL (the previous pass's snprintf wrote them). *)
Definition pb11_kmem (rd : reader) (kb : Z) (ti : nat) : Prop :=
  match ti with O => True | S _ => sa_zs rd kb (pb11_J ti ++ [0]) end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(** *** The post of B11b: the line's step is the F_badmodel refusal (H_MISS's and H_KREFM's) *)
Definition PB11_POST (v : pfv) (cf : rconf) (gi : nat) (nm val : list Z) (o : nat) (ln : Z)
  : world SEGS -> config -> Prop :=
  pf_postm B v (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm) o ln.

(** *** KLOOP (0x88b14): the head of the join loop, before pass ti (0 <= ti < 11)
    known and ntok are in scope (PF_SC_KNOWN, laid at 0x88a50-0x88ac8); known[0 .. kn ti] holds pb11_J ti and its
    NUL (nothing at ti = 0); ntok holds 11 (reac_box_catalogue's post; the loop re-reads it each pass at
    0x88ba4-0x88ba8); slots 0x60 = 0x68 = 1 (0x88b08 / 0x88b00, the two precomputed trap flags of tab = catA),
    0x70 = vp. Registers: PF_RL (s2 = '#': 0x881a8 on the first entry, 0x88bb4 on the back edge) and PF_RM, and
    s3 = ti (0x88aec / 0x88bac), s11 = kn ti (0x88af0 / 0x88bbc), s7 = s8 = row ti = catA + 296 ti (0x88b10 /
    0x88b0c, 0x88bc4 / 0x88bc8), a4 = catA (0x88ae8 / 0x88bb0), a2 = 240 (0x88ae0 / 0x88ba0). *)
Definition INV_KLOOP (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (ti : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  (ti < 11)%nat /\
  pb11_kmem (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) ti /\
  sa_val (rdW Wc memc) (pf_F v pos + PF_O_NTOK) 8%nat 11 /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x60, 1); (0x68, 1); (0x70, vp)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(19, Z.of_nat ti); (27, pb11_kn ti); (23, pin_spec.row_addr catA ti);
             (24, pin_spec.row_addr catA ti); (14, catA); (12, 240)]).
Definition H_KLOOP (n ti : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KLOOP n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KLOOP) rX memc mdc) (PB11_POST v cf gi nm val o ln).

End e.
End f.
End d.

(** ** The cut at every FP state (pf_pieces.v's HA_ form) *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_KLOOP (n ti : nat) : Prop := forall f1 : YK11.FPState, H_KLOOP (fx := f1) B n ti.
End s.
