(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 74 of its 99 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the kit of segment
   B10b of reac_segconf_parse_file's walk (S_B10b, lib/B/Prog/pf_pieces.v: HA_TAIL n -> H_INTENT n; INTENT 0x888e4
   -> TAIL 0x88600, 89 instructions, checks B#31 and B#32, UBSan trap T30, five bcmp calls, one refuse call, one
   snprintf call). The B10b segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: statement text and the
   one composition). ADAPTED from a working branch's lib/A/Prog/pf_a10b_k.v (an image-A segment lane): the same
   cut points in the C (the role value decided, the join of the store path and the bad-role path), re-derived on
   image B's code; image B adds the cut BAD (B's bad-role refusal has its own call, 0x88978).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; listing offsets against
   BASE + AF_reac_segconf_parse_file = 0x87e38):
     INTENT 0x888e4 .. 0x8895c  the five bcmp calls of reac_role_intent_parse, inlined (R:238-240, RR:114-118):
       0x888e4 auipc a0; 0x888e8 addi a1,a0,508 (0x21ae0 S_auto); li a2,5; mv a0,s7; 0x888f4 jal bcmp;
               0x888f8 beqz a0 -> 0x88980 `li s3,0; j 0x88d6c`
       0x888fc .. 0x8890c  bcmp(low, 0x21b00 S_master, 7); 0x88910 beqz -> 0x88a48 `li s3,1; j 0x88d6c`
       0x88914 .. 0x88924  bcmp(low, 0x21b20 S_slave, 6);  0x88928 beqz -> 0x88c80 `li s3,2; j 0x88d6c`
       0x8892c .. 0x8893c  bcmp(low, 0x21b40 S_tap, 4);    0x88940 beqz -> 0x88d68 `li s3,3` (falls in)
       0x88944 .. 0x88958  bcmp(low, 0x21b60 S_box, 4), s3 = 4 set at 0x88950; 0x8895c beqz -> 0x88d6c
       (s7 = low = F + 0x280 from INV_INTENT, kept by every call: callee-saved)
     BAD 0x88960 .. 0x8897c  no word matched: refuse(c = slot 0xc8, s6 = ln + 1, 0x21780 F_badrole,
       slot 0x40 = cur_name, slot 0x70 = val) at 0x88978, then 0x8897c `j 0x88dc8` = JOIN
     ROLEV 0x88d6c .. 0x88dc4  the role stores and the provenance snprintf (R:244-246):
       0x88d6c ld a0,192(s1); andi a0,a0,3; 0x88d74 bnez a0 -> unimp 0x891c8 (T30: cur & 3 <> 0)
       0x88d78 ld a3,192(s1) (cur); check B#31 (shadow of cur + 16, 0x88d7c-0x88d8c, slow 0x88fcc, stub 0x89288);
       0x88d90 sw s3,16(a3); check B#32 (cur + 20, 0x88d94-0x88da4, slow 0x88fdc, stub 0x8928c);
       0x88da8 li a0,1; 0x88dac sw a0,20(a3);
       0x88db0 .. 0x88dc4 snprintf(cur + 0xa0 = &cur->role_file, 96, 0x21340 "%s", slot 0x48 = c->reading)
       (falls into JOIN)
     JOIN 0x88dc8 .. 0x88dec  `li a0,-8`, the eight `sb a0,80..87(s5)` (low's shadow cells 0x50 .. 0x57 back to
       0xf8, R:247 scope end), 0x88dec `j 0x88600` = TAIL.
     cold: 0x88fcc .. 0x88fe8 the two checks' partial-granule arms (they fall back into the stores); 0x89288,
       0x8928c the two error calls (they do not return).

   THE CUTS INSIDE THE SEGMENT (this file fixes them; the piece files prove the four statements):
     INTENT 0x888e4  pf_pieces.INV_INTENT / H_INTENT  (the segment's entry, fixed by pf_pieces.v)
     BAD    0x88960  INV_BAD   / H_BAD                (no role word matched; the refusal's call follows)
     ROLEV  0x88d6c  INV_ROLEV / H_ROLEV              (the role value r is decided and is in s3)
     JOIN   0x88dc8  INV_JOIN  / H_JOIN               (c holds the step's final state; low still in scope)
     TAIL   0x88600  pf_pieces.INV_TAIL / H_TAIL      (the segment's exit, fixed by pf_pieces.v)
   and the four pieces are
     pf_seg_B10b_c.v  PB10_C : HA_ROLEV n -> HA_BAD n -> H_INTENT n   (the five bcmp calls and their branches)
     pf_seg_B10b_r.v  PB10_R : HA_JOIN n -> H_BAD n                   (the bad-role refusal)
     pf_seg_B10b_s.v  PB10_S : HA_JOIN n -> H_ROLEV n                 (T30, B#31, B#32, the stores, snprintf)
     pf_seg_B10b_j.v  PB10_J : HA_TAIL n -> H_JOIN n                  (the shadow stores and the jump to TAIL)
   assembled by pb10_compose below. ROLEV, BAD and JOIN are taken at EVERY FP state, as pf_pieces.v takes its own
   exit cuts: refuse and snprintf return at an FP state of their own (apost_baseF / art_postF).

   REGISTERS AT THE INNER CUTS: every cut keeps pf_pieces.v's PF_RL (s2 = '#', s5 = SH, s10 = -1) and PF_RM
   (s9 = the next line, s6 = ln + 1), which no instruction of B10b writes and every call preserves (callee-saved);
   ROLEV adds s3 = r (0x88980 / 0x88a48 / 0x88c80 / 0x88d68, or 0x88950 before the box call). cur lives in slot
   0xc0 (pf_st's fifth conjunct), c in slot 0xc8 (pf_fi), val in slot 0x70 (BAD only). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The three cut pcs inside B10b, as listing offsets *)
(* 0x88960, the bad-role refusal's arguments: no role word matched *)
Definition PF_BAD : Z := AF_reac_segconf_parse_file + 0xb28.
(* 0x88d6c, the role stores: every match arm jumps or falls here with the role value in s3 *)
Definition PF_ROLEV : Z := AF_reac_segconf_parse_file + 0xf34.
(* 0x88dc8, the join of the store path (snprintf returns here) and the refuse path (`j` at 0x8897c) *)
Definition PF_JOIN : Z := AF_reac_segconf_parse_file + 0xf90.
(* each inner cut's pc at B's base seg_text (the excerpt's addresses) *)
Lemma pb10_cut_pcs :
  seg_text + PF_INTENT = 0x888e4 /\ seg_text + PF_BAD = 0x88960 /\ seg_text + PF_ROLEV = 0x88d6c /\
  seg_text + PF_JOIN = 0x88dc8 /\ seg_text + PF_TAIL = 0x88600.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** The five role words, in the order reac_role_intent_parse compares them, with the value each gives *)
Definition PB10_WORDS : list (list Z) := [S_auto; S_master; S_slave; S_tap; S_box].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* BAD (0x88960, the fall-through of the box compare's `beqz` at 0x8895c): low has been compared with the five
   words and none matched, so reac_role_intent_parse gives None. The state is INV_INTENT's but s7 (no longer
   read): low still in scope (PF_SC_LOW), c holds cf, cur = Some gi in slot 0xc0, val at vp in buf and in slot
   0x70 (the refusal's fifth argument, 0x88974). *)
Definition INV_BAD (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)] /\
  role_intent_parse (r_low val 0 64) = None /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_BAD (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_BAD n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_BAD) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).

(* ROLEV (0x88d6c, reached from each of the five match arms): the line's role value is r, in s3 (x19). low is
   still in scope (PF_SC_LOW); c still holds cf -- no store has happened yet; cur = Some gi in slot 0xc0 (the
   stores' base, 0x88d6c / 0x88d78). *)
Definition INV_ROLEV (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (val : list Z) (r : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  role_intent_parse (r_low val 0 64) = Some r /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(19, r)]).
Definition H_ROLEV (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r,
  INV_ROLEV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_ROLEV) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).

(* JOIN (0x88dc8): the line's step is done and c holds its final state cfx -- either
   r_upd cf gi (rs_with_role r (snprintf_s 96 F_s [AS (rc_reading cf)])) after the two stores and the provenance
   snprintf, or refuse cf (ln + 1) F_badrole [AS nm; AS val] after the refuse call. low is still in scope; the
   eight `sb` that follow put it out. The counters already have the room the exit cut asks (the measure is the
   next line's). *)
Definition INV_JOIN (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cfx : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cfx (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_JOIN (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi,
  INV_JOIN n v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_JOIN) rX memc mdc) (pf_postm B v (cfx, Some gi, nm) o ln).

End e.
End f.
End d.

(** ** The three inner cuts at every FP state (refuse and snprintf return at an FP state of their own) *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_BAD (n : nat) : Prop := forall f1 : YK11.FPState, H_BAD (fx := f1) B n.
Definition HA_ROLEV (n : nat) : Prop := forall f1 : YK11.FPState, H_ROLEV (fx := f1) B n.
Definition HA_JOIN (n : nat) : Prop := forall f1 : YK11.FPState, H_JOIN (fx := f1) B n.

(* The four pieces, as the piece files state them. *)
Definition PB10_C : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_ROLEV n -> HA_BAD n -> H_INTENT (fx := f0) B n.
Definition PB10_R : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_JOIN n -> H_BAD (fx := f0) B n.
Definition PB10_S : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_JOIN n -> H_ROLEV (fx := f0) B n.
Definition PB10_J : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_TAIL B n -> H_JOIN (fx := f0) B n.

(* B10b from its four pieces: the one composition this lane owes pf_pieces.v. *)
Lemma pb10_compose : PB10_C -> PB10_R -> PB10_S -> PB10_J -> S_B10b B.
Proof.
intros HC HR HS HJ f0 n TAIL.
assert (JOIN : HA_JOIN n) by (intros f1; exact (HJ f1 n TAIL)).
assert (BAD : HA_BAD n) by (intros f1; exact (HR f1 n JOIN)).
assert (ROLEV : HA_ROLEV n) by (intros f1; exact (HS f1 n JOIN)).
exact (HC f0 n ROLEV BAD).
Qed.
End s.
