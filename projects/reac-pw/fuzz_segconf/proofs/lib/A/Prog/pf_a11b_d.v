(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v; 57 of its 83 lines of code are new or changed and 492 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the INTERNAL cut statements of segment A11b of
   reac_segconf_parse_file's walk (segment A11b's proof, by the G3 walk owner, 2026-10-30).

   A11b is MISS 0x885a8 and LOWOUT 0x88774 -> TAIL, 121 instructions, inline check 28 (the catalogue row's
   shadow byte), the calls reac_box_catalogue (0x88634), snprintf (0x88698, eleven passes) and refuse (0x886e8).
   Its two statements S_A11b's two halves (lib/A/Prog/pf_pieces.v:772-774) are
     (HA_TAIL n -> H_MISS B n) /\ (HA_TAIL n -> H_LOWOUT B n).
   This file states only what the segment cuts itself at; pf_pieces.v is never edited.

   The code (the excerpt in the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s), with F the class-5 frame and SH its shadow:
     0x885a8 MISS      sd s9,0x18(s1) (the value pointer vp); 31 `sb zero,X(s11)` putting known[240] (cells
                       0x64..0x81) and ntok (cell 0x8a) IN scope; ld s3,0x70(s1) (= F + 0x450, &ntok);
                       sd zero,0(s3); jal reac_box_catalogue (0x88634, a0 = &ntok)
     0x88638 KRET      ld a1,0(s3) (= 11); a2 = 240; beqz a1 (dead: the contract gives 11); s7 = s8 = a0 = the
                       table; s9 = 0; s4 = SH-of-the-row; s3 = 1
     0x8865c KLOOP     the join loop, eleven passes: the separator ("" for the first row, "|" after), check 28
                       (lbu 0(s4), the row's shadow byte), ld 0(s7) (the row's token pointer),
                       snprintf(known + kn, 240 - kn, "%s%s", sep, token), then ntok is reloaded and the
                       counters move on; the back edge is `bltu kn+2, 240` at 0x886c4
     0x886c8 KEXIT     a2 = F_badmodel; s8 = c; refuse(c, lineno, F_badmodel, cur_name, val, known) at 0x886e8
     0x886ec           a0 = -8; 31 `sb a0,X(s11)` putting known and ntok OUT of scope; s3 and s4 reloaded
     0x88774 LOWOUT    three `sb a0,0x5c..0x5e(s11)` (low146 out of scope); `j` TAIL 0x88068

   The three statements below are the walk-internal cuts: H_KLOOP (the loop head, for each pass ti), H_KEXIT
   (the refusal and the teardown). Their form is pf_pieces.v's: a predicate INV_<CUT> over the machine state and
   `SRr ... (cfg_at ... (BASE + PF_<CUT>) ...)` of the segment's own post. Both are taken at EVERY FP state in
   the HA_ forms, because the eleven snprintf calls return at FP states of their own.

   The functional content is the plain one (lib/Prog/pf_pieces_spec.v, lib/Prog/pfA_facts.v and
   lib/Spec/SegModel.v): pf_J ti is the join of the first ti tokens (SegModel.known_go), pf_kn ti its length.
   Statement text only: this file proves nothing. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The pcs A11b cuts at, as listing offsets (BASE + PF_<CUT>) *)
(* 0x88634, the jal of reac_box_catalogue *)
Definition PF_KCAT : Z := AF_reac_segconf_parse_file + 0xbbc.
(* 0x88638, where that call returns *)
Definition PF_KRET : Z := AF_reac_segconf_parse_file + 0xbc0.
(* 0x8865c, the head of the join loop *)
Definition PF_KLOOP : Z := AF_reac_segconf_parse_file + 0xbe4.
(* 0x886c8, the refusal *)
Definition PF_KEXIT : Z := AF_reac_segconf_parse_file + 0xc50.

(** ** The frame's shadow while known and ntok are in scope (pf_pieces.v's pf_scope) *)
Definition PF_SC_KN : pf_scope := PFSc true true false true true.

(** ** The join of the first ti tokens (SegModel.known_go; the plain pf_p7_lemmas' p7_J / p7_kn) *)
Definition pf_J (ti : nat) : list Z := known_go (firstn ti cat_toks) true 0 [].
Definition pf_kn (ti : nat) : Z := Z.of_nat (length (pf_J ti)).
(* the separator of pass ti: "" before the first token, "|" after *)
Definition pf_sep (ti : nat) : list Z := if (ti =? 0)%nat then [] else [124].
Definition pf_tok (ti : nat) : list Z := nth ti cat_toks [].
Definition pf_args (ti : nat) : list arg := [AS (pf_sep ti); AS (pf_tok ti)].

(** The bytes known[240] holds at the head of pass ti: nothing before the first pass, else the join so far and
    its NUL (the previous pass's snprintf wrote them). *)
Definition pf_kmem (rd : reader) (kb : Z) (ti : nat) : Prop :=
  match ti with O => True | S _ => sa_zs rd kb (pf_J ti ++ [0]) end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(** *** The post of both halves of A11b's miss path: the line's step is the F_badmodel refusal *)
Definition PF_MISSPOST (v : pfv) (cf : rconf) (gi : nat) (nm val : list Z) (o : nat) (ln : Z)
  : world SEGS -> config -> Prop :=
  pf_postm B v (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm) o ln.

(** *** KLOOP (0x8865c): the head of the join loop, before pass ti (0 <= ti < 11)
    known and ntok are in scope; known[0 .. kn ti) holds pf_J ti with its NUL (nothing at ti = 0); ntok holds
    the table's row count 11; slot 0x18 holds the value pointer vp and slot 0xb0 the current entry.
    Registers: s2 = '#', s11 = SH, s5 = the next line, s10 = lineno (PF_RM); s3 = ti + 1 (0x88654 / 0x886b0),
    s9 = kn ti (0x88648 / 0x886ac), s4 = the shadow byte of row ti (0x8864c-0x88650 / 0x886bc, 0x25 = 0x128 / 8),
    s7 = row ti (0x88644 / 0x886c0), a2 = 240 (0x8863c / 0x8869c). s8 is borrowed (dead until 0x886d0) and s3's
    PF_RL value (SH + 8) is restored at 0x8876c. *)
Definition INV_KLOOP (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (ti : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  (ti < 11)%nat /\
  pf_kmem (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) ti /\
  sa_val (rdW Wc memc) (pf_F v pos + PF_O_NTOK) 8%nat 11 /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x18, vp); (0xb0, seg_spec.rseg_addr (p_c v) gi)] /\
  pf_rg rX ([(18, 0x23); (27, pf_SH v pos)] ++ PF_RM v o ln ++
            [(19, Z.of_nat ti + 1); (25, pf_kn ti);
             (20, SHADOW_OFF + pin_spec.row_addr catA ti / 8); (23, pin_spec.row_addr catA ti); (12, 240)]).
Definition H_KLOOP (n ti : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KLOOP n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ti ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KLOOP) rX memc mdc) (PF_MISSPOST v cf gi nm val o ln).

(** *** KEXIT (0x886c8): the loop is over, known holds the whole join and its NUL
    The refusal reads c (slot 0x90), the lineno (s10), F_badmodel, cur_name (slot 0x50), val (slot 0x18) and
    known (slot 0x78); then known and ntok go out of scope and s3 / s4 are reloaded, into LOWOUT. *)
Definition INV_KEXIT (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  sa_zs (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) (known ++ [0]) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x18, vp); (0xb0, seg_spec.rseg_addr (p_c v) gi)] /\
  pf_rg rX ([(18, 0x23); (27, pf_SH v pos)] ++ PF_RM v o ln).
Definition H_KEXIT (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KEXIT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KEXIT) rX memc mdc) (PF_MISSPOST v cf gi nm val o ln).

End e.
End f.
End d.

(** ** The two cuts at every FP state (pf_pieces.v's HA_ forms) *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_KLOOP (n ti : nat) : Prop := forall f1 : YK11.FPState, H_KLOOP (fx := f1) B n ti.
Definition HA_KEXIT (n : nat) : Prop := forall f1 : YK11.FPState, H_KEXIT (fx := f1) B n.
End s.
