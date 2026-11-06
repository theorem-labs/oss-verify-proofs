(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 118 of its 143 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: segment A5 of reac_segconf_parse_file (the line driver, 111 instructions), its
   INTERNAL points. Segment A5's proof, 2026-10-30. Statement text only: the segment theorem pf_a5_holds
   (lib/A/Prog/pf_a5.v) chains the lemmas that prove these statements.

   S_A5 (lib/A/Prog/pf_pieces.v) is HEAD 0x87ddc -> LONG / HDR / KEY / TAIL and TAIL 0x88068 -> HEAD (pred n) / DONE.
   Its code calls six runtime / program entries; each internal point below is the state just after one of them
   returns (the point between two calls, check_round_trip.v's ST_* form), or a join / loop head. Every point carries
   the cut predicates' own parts (pf_pieces.v pf_base, pf_st, the line context of INV_HEAD), so a segment piece starts
   from a fresh seed and ends in the next point or an exit cut.

     pc       point   reached from                          what holds there besides pf_base / the line
     0x87de8  R1      HEAD, return of strchr (jal 0x87de4)   a0 = strchr(p, '\n') (t + o + LEN, or 0)
     0x87e08  R2      R1 (a0 = 0), return of strlen         a0 = LEN = strlen(p), s5 = 0, the line ends the text
     0x87e14  Q3      R1 (a0 <> 0), R2                       s7 = LEN, s5 = p' = t + pf_next s o
     0x87e24  R3      Q3, return of meta_fill_00 (0x87e20)   buf in scope, s10 = ln + 1 (INV_LONG's registers)
     0x87e94  R4      R3 (LEN < 512), return of memcpy       slot 0xb0 = cur (0x87e7c), buf holds the line, s4 = buf
     0x87eb4  L k     R4, L (k - 1)                          strip_comment's loop head: a0 = a1 = buf + k, a3 = -k,
                                                             buf holds the line and its NUL, no comment before k
     0x87f3c  C       L k (the NUL, or the cut store)         buf holds r_strip_comment line and its NUL
     0x87f48  R5      C, return of trim (jal 0x87f44)        s7 := a0 = lp, the trimmed line pf_tline s o at lp
     0x88074  R6      TAIL, return of meta_fill_f8 (0x88070) buf out of scope again

   Registers by x-number (pf_pieces.v pf_rg); LEN = length (pf_line s o); buf = F + 0x40 (PF_O_BUF); the line
   context is INV_HEAD's (pf_lctx at o, o < length s, the rest at most n bytes), the post is H_HEAD's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The internal points, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87a78) *)
Definition A5_R1 : Z := AF_reac_segconf_parse_file + 0x370.   (* 0x87de8, strchr's return *)
Definition A5_R2 : Z := AF_reac_segconf_parse_file + 0x390.   (* 0x87e08, strlen's return *)
Definition A5_Q3 : Z := AF_reac_segconf_parse_file + 0x39c.   (* 0x87e14, the join: `addiw s10,s10,1` *)
Definition A5_R3 : Z := AF_reac_segconf_parse_file + 0x3ac.   (* 0x87e24, meta_fill_00's return *)
Definition A5_R4 : Z := AF_reac_segconf_parse_file + 0x41c.   (* 0x87e94, memcpy's return *)
Definition A5_L : Z := AF_reac_segconf_parse_file + 0x43c.    (* 0x87eb4, strip_comment's loop head *)
Definition A5_C : Z := AF_reac_segconf_parse_file + 0x4c4.    (* 0x87f3c, `addi s9,zero,9` before trim *)
Definition A5_R5 : Z := AF_reac_segconf_parse_file + 0x4d0.   (* 0x87f48, trim's return *)
Definition A5_R6 : Z := AF_reac_segconf_parse_file + 0x5fc.   (* 0x88074, meta_fill_f8's return *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* buf (F + 0x40, 512 bytes) and the line's length *)
Definition a5_buf (v : pfv) (pos : Z) : Z := pf_F v pos + PF_O_BUF.
Definition a5_len (v : pfv) (o : nat) : nat := length (pf_line (p_s v) o).
(* strchr(p, '\n')'s answer at p = t + o: the line's '\n', or 0 when the line ends the text (pf_pieces_spec.v
   L_break_nl) *)
Definition a5_nl (v : pfv) (o : nat) : Z :=
  if (o + a5_len v o <? length (p_s v))%nat then p_t v + Z.of_nat (o + a5_len v o) else 0.
(* the line context of a point inside the line that starts at o (INV_HEAD's middle and its pf_st) *)
Definition a5_ln (n : nat) (v : pfv) (pos : Z) (rd : reader) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_lctx (p_s v) o ln d /\ (o < length (p_s v))%nat /\ (length (skipn o (p_s v)) <= n)%nat /\
  pf_st v pos rd cf cur nm (length (skipn o (p_s v))).

Section e.
Variable B : asyms.
(* the post of every point of the line that starts at o: H_HEAD's (and H_TAIL's) *)
Definition a5_post (v : pfv) (cf : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z)
  : world SEGS -> config -> Prop :=
  PF_POSTr B v (fst (fst (r_lines (cf, cur, nm) ln (lines (skipn o (p_s v)))))).

(* R1, 0x87de8: strchr has returned a0 = a5_nl v o; buf is still out of scope *)
Definition INV_R1 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur); (10, a5_nl v o)]).
(* R2, 0x87e08: no '\n' (the line ends the text), strlen has returned a0 = LEN; s5 = strchr's 0 *)
Definition INV_R2 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  (o + a5_len v o = length (p_s v))%nat /\
  pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur); (21, 0);
                            (10, Z.of_nat (a5_len v o))]).
(* Q3, 0x87e14: len = s7, p' = s5 = t + pf_next s o (nl + 1, or p + len) *)
Definition INV_Q3 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur);
                            (21, p_t v + Z.of_nat (pf_next (p_s v) o)); (23, Z.of_nat (a5_len v o))]).
(* R3, 0x87e24: lineno++ done (0x87e14), buf in scope (meta_fill_00): INV_LONG's registers *)
Definition INV_R3 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, pf_cur_ptr (p_c v) cur); (25, p_t v + Z.of_nat o); (23, Z.of_nat (a5_len v o))]).
(* R4, 0x87e94: LEN < 512, cur spilled to slot 0xb0 (0x87e7c), s4 = buf (0x87e80), memcpy has copied the line *)
Definition INV_R4 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\ (a5_len v o < 512)%nat /\
  sa_zs (rdW Wc memc) (a5_buf v pos) (pf_line (p_s v) o) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, a5_buf v pos); (25, p_t v + Z.of_nat o); (23, Z.of_nat (a5_len v o))]).
(* L k, 0x87eb4: buf[len] = 0 stored (0x87e9c); k bytes checked, no comment start before k; a0 = a1 = buf + k,
   a3 = -k (0x87efc-0x87f04), s4 = ' ' (0x87ea8), a6 = '\t', a7 = ';' *)
Definition INV_L (k : nat) (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\ (a5_len v o < 512)%nat /\
  sa_zs (rdW Wc memc) (a5_buf v pos) (pf_line (p_s v) o ++ [0]) /\ (k <= a5_len v o)%nat /\
  (forall j, (j < k)%nat -> r_comment_at (pf_line (p_s v) o) j = false) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, 0x20); (10, a5_buf v pos + Z.of_nat k); (11, a5_buf v pos + Z.of_nat k); (13, - Z.of_nat k);
             (16, 9); (17, 0x3b)]).
(* C, 0x87f3c: strip_comment done, buf holds r_strip_comment line and its NUL *)
Definition INV_C (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\ (a5_len v o < 512)%nat /\
  sa_zs (rdW Wc memc) (a5_buf v pos) (r_strip_comment (pf_line (p_s v) o) ++ [0]) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20)]).
(* R5, 0x87f48: trim(buf) has returned lp, the trimmed line pf_tline s o at lp inside buf; s9 = 9 (0x87f3c) *)
Definition INV_R5 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ a5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\ (a5_len v o < 512)%nat /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (a5_buf v pos) lp (pf_tline (p_s v) o) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20); (25, 9); (10, lp)]).
(* R6, 0x88074: TAIL's state with buf out of scope again (meta_fill_f8) *)
Definition INV_R6 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\
  pf_lctx (p_s v) o ln d /\ (length (skipn o (p_s v)) < n)%nat /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ [(21, p_t v + Z.of_nat o); (26, ln); (20, pf_cur_ptr (p_c v) cur)]).

(* from each point the walk reaches the line's post *)
Definition H_R1 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R1 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_R1) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_R2 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R2 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_R2) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_Q3 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_Q3 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_Q3) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_R3 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R3 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_R3) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_R4 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R4 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_R4) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_L (k : nat) (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_L k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_L) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_C (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_C n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_C) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_R5 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_R5 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_R5) rX memc mdc) (a5_post v cf cur nm o ln).
Definition H_R6 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R6 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A5_R6) rX memc mdc) (a5_post v cf cur nm o ln).
End e.
End f.
End d.
