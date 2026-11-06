(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 63 of its 87 lines of code are new or changed and 494 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A: the kit of segment A10b of reac_segconf_parse_file's walk
   (S_A10b, lib/A/Prog/pf_pieces.v:765: INTENT 0x88450 -> TAIL 0x88068, 87 instructions, checks 31 and 32,
   five bcmp calls, one refuse call, one snprintf call).

   THE CODE (dis/reac_segconf_parse_file.fuzz_segconf.asan.s; listing offsets against
   BASE + AF_reac_segconf_parse_file = 0x87a78, seg_text 0x84d34):
     0x88450 .. 0x884f8  the five bcmp calls of reac_role_intent_parse, inlined (R:236-246, RR:110-120):
       bcmp(low, "auto", 5)   0x88460, taken -> 0x884f0 `mv s3,zero`    -> 0x88840 with s3 = 0
       bcmp(low, "master", 7) 0x88478, taken -> 0x885a0 `addi s3,1`     -> 0x88840 with s3 = 1
       bcmp(low, "slave", 6)  0x88490, taken -> 0x8879c `addi s3,2`     -> 0x88840 with s3 = 2
       bcmp(low, "tap", 4)    0x884a8, taken -> 0x8883c `addi s3,3`     -> 0x88840 with s3 = 3
       bcmp(low, "box", 4)    0x884c8, taken -> 0x88840 with s3 = 4 (set at 0x884c0, before the call)
       none taken: refuse(c, ln + 1, F_badrole, cur_name, val) at 0x884e8, then `j 0x8888c`
     0x88840 .. 0x888b8  the role stores and the provenance snprintf:
       check 31 (0x88840-0x88850, store4 at &seg[gi].role), `sw s3,0x10(s4)`
       check 32 (0x88858-0x88868, store4 at &seg[gi].role_set), `sw a0,0x14(s4)` with a0 = 1
       snprintf(&seg[gi].role_file, 96, "%s", c->reading) at 0x88888
     0x8888c .. 0x888b8  the join of both paths: `ld s3,0x98(s1)` (s3 = SH + 8) and the eight `sb` of -8 that
       put low out of scope (shadow cells 0x50 .. 0x57), then `j 0x88068` = TAIL.
     0x88a70 .. 0x88a90  the two checks' partial-granule arms, which fall back into the stores.
     0x88d28, 0x88d2c    the two error calls (they do not return).

   The five literals are the listing's objects (SegList.v slots 3528, 3532+, ...): A_OBJ 55 = 0x21ae0 S_auto,
   56 = 0x21b00 S_master, 57 = 0x21b20 S_slave, 58 = 0x21b40 S_tap, 59 = 0x21b60 S_box; the refuse format is
   A_OBJ 60 = 0x21780 F_badrole and the snprintf format A_OBJ 35 = 0x21340 F_s. SegInstA's seg_litA_rc gives the
   same addresses (SEG_LIT_TAB_RC), and reac_segconf_parse_file_c.PARSE_FILE_LITS holds all seven texts, so
   pf_pieces.pf_obj carries sa_lit for each of them.
   The A build compares the tap / box words by bcmp where the plain build used one word compare, so the walk
   needs only the bcmp half of O1 (pf_pieces_spec.O1_bcmp_lit's reading); the reader form it needs is
   pf_a10b_f.a10b_cmp_lit, because the kit's abcmp_realizes states its result as byte equality through the
   reader, not as memcmp_model.

   THE CUTS INSIDE THE SEGMENT (this file fixes them; the walk files prove the three statements):
     INTENT 0x88450  pf_pieces.INV_INTENT / H_INTENT  (the segment's entry, fixed by pf_pieces.v)
     ROLEV  0x88840  INV_ROLEV / H_ROLEV              (the role value r is decided and is in s3)
     JOIN   0x8888c  INV_JOIN  / H_JOIN               (c holds the step's final state; low still in scope)
     TAIL   0x88068  pf_pieces.INV_TAIL / H_TAIL      (the segment's exit, fixed by pf_pieces.v)
   and the three pieces are
     pf_a10b_b.v  pa10_b_ok : HA_JOIN n -> HA_ROLEV n -> H_INTENT n   (the bcmps and the refuse call)
     pf_a10b_s.v  pa10_s_ok : HA_JOIN n -> H_ROLEV n                  (the checks, the stores, the snprintf)
     pf_a10b_j.v  pa10_j_ok : HA_TAIL n -> H_JOIN n                   (the shadow stores and the jump to TAIL)
   assembled by pf_a10b.v. ROLEV and JOIN are reached at the FP state a call returned (refuse and snprintf are
   FP-existential), so the two inner cuts are taken at EVERY FP state, as pf_pieces.v takes its own exit cuts;
   the pieces lift their post with PaFx.srr_apost_baseF_lift.

   By the G3 walk owner, 2026-10-30. Statement text and shared facts only: no segment is proved here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
SegPgBase SegABase SegGlob SegInstA SegObj refuse_c reac_segconf_parse_file_c pf_pieces.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(** ** The two cut pcs inside A10b, as listing offsets *)
(* 0x88840, the role stores: every match arm jumps here with the role value in s3 *)
Definition PF_ROLEV : Z := AF_reac_segconf_parse_file + 0xdc8.
(* 0x8888c, the join of the store path and the refuse path *)
Definition PF_JOIN : Z := AF_reac_segconf_parse_file + 0xe14.
(* 0x884ec, where the refuse call returns *)
Definition PF_REFRET : Z := AF_reac_segconf_parse_file + 0xa74.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* ROLEV (0x88840, reached from each of the five match arms): the fold buffer low has been compared with the
   five words and the line's role value is r, in s3 (x19; set at 0x884f0 / 0x885a0 / 0x8879c / 0x8883c, or at
   0x884c0 before the box call). low is still in scope (PF_SC_LOW): the eight shadow cells 0x50 .. 0x57 are put
   back only at the join. c still holds cf -- no store has happened yet. The other loop registers are
   INV_INTENT's, which the bcmp calls preserve (they are callee-saved): s2 = '#', s8 = c, s11 = SH, s4 =
   &c->seg[gi], s9 = val, s5 = the next line, s10 = the line number. *)
Definition INV_ROLEV (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (r : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  role_intent_parse (r_low val 0 64) = Some r /\ 0 <= r <= 4 /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos); (19, r)] ++ PF_RM v o ln ++
            [(20, seg_spec.rseg_addr (p_c v) gi); (25, vp)]).
Definition H_ROLEV (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r,
  INV_ROLEV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_ROLEV) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).

(* JOIN (0x8888c): the line's step is done and c holds its final state cfx -- either
   r_upd cf gi (rs_with_role r (snprintf_s 96 F_s [AS (rc_reading cf)])) after the two stores and the
   provenance snprintf, or refuse cf (ln + 1) F_badrole [AS nm; AS val] after the refuse call. low is still in
   scope; the eight `sb` that follow put it out. The counters already have the room the exit cut asks (the
   measure is the next line's). s3 (x19) is dead here: 0x8888c reloads it from the slot 0x98. *)
Definition INV_JOIN (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cfx : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cfx (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln ++
            [(20, seg_spec.rseg_addr (p_c v) gi)]).
Definition H_JOIN (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi,
  INV_JOIN n v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_JOIN) rX memc mdc) (pf_postm B v (cfx, Some gi, nm) o ln).

End e.
End f.
End d.

(** ** The two inner cuts at every FP state (refuse and snprintf return at an FP state of their own) *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_ROLEV (n : nat) : Prop := forall f1 : YK11.FPState, H_ROLEV (fx := f1) B n.
Definition HA_JOIN (n : nat) : Prop := forall f1 : YK11.FPState, H_JOIN (fx := f1) B n.

(* The three pieces, as the walk files state them. *)
Definition PA10_B : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_JOIN n -> HA_ROLEV n -> H_INTENT (fx := f0) B n.
Definition PA10_S : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_JOIN n -> H_ROLEV (fx := f0) B n.
Definition PA10_J : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_TAIL B n -> H_JOIN (fx := f0) B n.

(* A10b from its three pieces: the one composition this segment owes pf_pieces.v. *)
Lemma pa10_compose : PA10_B -> PA10_S -> PA10_J -> S_A10b B.
Proof.
intros HB HS HJ f0 n TAIL.
assert (JOIN : HA_JOIN n) by (intros f1; exact (HJ f1 n TAIL)).
assert (ROLEV : HA_ROLEV n) by (intros f1; exact (HS f1 n JOIN)).
exact (HB f0 n JOIN ROLEV).
Qed.
End s.
