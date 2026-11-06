(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 118 of its 143 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file
   (the line driver, 116 instructions), its INTERNAL points. The B5 segment lane of the image-B G3 walk owner, 2026-10-30. ADAPTED from
   the image-A G3 walk owner's image-A lib/A/Prog/pf_a5_d.v (commit 385fd095481f): the same points in the C, the
   pcs, registers and spill slots re-derived from image B's code
   (the neutral excerpt reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s). Statement text only:
   pf_seg_B5.v chains the lemmas that prove these statements into S_B5 (lib/B/Prog/pf_pieces.v).

   S_B5 is HEAD 0x881f8 -> LONG / HDR / KEY / TAIL (S_B5h) and TAIL 0x88600 -> HEAD (pred n) / DONE (S_B5t). Its code
   calls six entries; each internal point is the state just after one of them returns, or a join / loop head.
   Every point carries pf_pieces.v's pf_base and pf_st and INV_HEAD's line context, so each piece starts from a
   fresh seed and ends in the next point or an exit cut.

     pc       point  reached from                              what holds there besides pf_base / the line
     0x88204  R1     HEAD, strchr's return (jal 0x88200)       a0 = strchr(p, '\n') (t + o + LEN, or 0); buf out
     0x88224  R2     R1 (a0 = 0, 0x88204), strlen's return     a0 = LEN = strlen(p), the line ends the text
                     (jal 0x88220)
     0x88238  Q3     R1 (a0 <> 0: T03 0x88208, 0x88210 s7 =    s7 = LEN, s9 = p' = t + pf_next s o
                     LEN, s9 = nl + 1), R2 (T04 0x88228,
                     0x88230 s7 = LEN, s9 = p + LEN)
     0x88250  R3     Q3 (T05 0x8823c, s6 = ln + 1), the        buf in scope; INV_LONG's registers
                     return of meta_fill_00 (0x8824c)
     0x882cc  R4     R3 (LEN < 512, 0x88254), the return of    buf[0 .. LEN) = the line
                     checked_memcpy (0x882c8)
     0x882f8  L k    R4 (T07 0x882d0, buf[LEN] = 0 0x882e0,    strip_comment's loop head: a0 = a1 = buf + k,
                     the constants), L (k - 1) (0x88354)       a3 = -k, a6 = 1, a7 = ' ', t0 = '\t', t1 = ';';
                                                               buf holds the line and its NUL, no comment before k
     0x88388  C      L k (the NUL, 0x88314), the cut store     buf holds r_strip_comment line and its NUL
                     0x88384 (falls in)
     0x88390  R5     C, trim's return (jal 0x8838c)            a0 = lp, the trimmed line pf_tline s o at lp in buf
     0x8860c  R6     TAIL, meta_fill_f8's return (0x88608)     buf out of scope again

   Registers by x-number (pf_pieces.v pf_rg): a0 = 10, a1 = 11, a3 = 13, a6 = 16, a7 = 17, t0 = 5, t1 = 6, s6 = 22,
   s7 = 23, s8 = 24, s9 = 25, s11 = 27. B's line registers (plan section 5.2 B5 row, 7.1): p = s11 at HEAD, the next
   p = s9 in the body; lineno = s8 at HEAD, s6 in the body (A: s9 / s5, s10). B5 writes no spill slot (every
   `N(s1)` access of 0x881f8-0x88258, 0x882bc-0x883b4, 0x88600-0x88630 is an `ld`: 0xd8 at 0x88248 / 0x88604, 0xd0 at
   0x882bc / 0x882d8 / 0x88370 / 0x88388, 0xb0 at 0x882cc), so cur stays in slot 0xc0 (pf_st) throughout. LEN =
   length (pf_line s o); buf = F + 0x40 (PF_O_BUF); the line context is INV_HEAD's (pf_lctx at o, o < length s, the
   rest at most n bytes), the post is H_HEAD's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The internal points, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition B5_R1 : Z := AF_reac_segconf_parse_file + 0x3cc.   (* 0x88204, strchr's return *)
Definition B5_R2 : Z := AF_reac_segconf_parse_file + 0x3ec.   (* 0x88224, strlen's return *)
Definition B5_Q3 : Z := AF_reac_segconf_parse_file + 0x400.   (* 0x88238, the join: `addiw s6,s8,1` *)
Definition B5_R3 : Z := AF_reac_segconf_parse_file + 0x418.   (* 0x88250, meta_fill_00's return *)
Definition B5_R4 : Z := AF_reac_segconf_parse_file + 0x494.   (* 0x882cc, checked_memcpy's return *)
Definition B5_L : Z := AF_reac_segconf_parse_file + 0x4c0.    (* 0x882f8, strip_comment's loop head *)
Definition B5_C : Z := AF_reac_segconf_parse_file + 0x550.    (* 0x88388, `ld a0,208(s1)` before trim *)
Definition B5_R5 : Z := AF_reac_segconf_parse_file + 0x558.   (* 0x88390, trim's return *)
Definition B5_R6 : Z := AF_reac_segconf_parse_file + 0x7d4.   (* 0x8860c, meta_fill_f8's return *)
(* each point's pc at B's base seg_text (the excerpt's addresses) *)
Lemma b5_point_pcs :
  seg_text + B5_R1 = 0x88204 /\ seg_text + B5_R2 = 0x88224 /\ seg_text + B5_Q3 = 0x88238 /\
  seg_text + B5_R3 = 0x88250 /\ seg_text + B5_R4 = 0x882cc /\ seg_text + B5_L = 0x882f8 /\
  seg_text + B5_C = 0x88388 /\ seg_text + B5_R5 = 0x88390 /\ seg_text + B5_R6 = 0x8860c.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* buf (F + 0x40, 512 bytes) and the line's length *)
Definition b5_buf (v : pfv) (pos : Z) : Z := pf_F v pos + PF_O_BUF.
Definition b5_len (v : pfv) (o : nat) : nat := length (pf_line (p_s v) o).
(* strchr(p, '\n')'s answer at p = t + o: the line's '\n', or 0 when the line ends the text (pf_pieces_spec.v
   L_break_nl) *)
Definition b5_nl (v : pfv) (o : nat) : Z :=
  if (o + b5_len v o <? length (p_s v))%nat then p_t v + Z.of_nat (o + b5_len v o) else 0.
(* the line context of a point inside the line that starts at o (INV_HEAD's middle and its pf_st) *)
Definition b5_ln (n : nat) (v : pfv) (pos : Z) (rd : reader) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_lctx (p_s v) o ln d /\ (o < length (p_s v))%nat /\ (length (skipn o (p_s v)) <= n)%nat /\
  pf_st v pos rd cf cur nm (length (skipn o (p_s v))).

Section e.
Variable B : asyms.
(* the post of every point of the line that starts at o: H_HEAD's (and, at the next line's offset, H_TAIL's) *)
Definition b5_post (v : pfv) (cf : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z)
  : world SEGS -> config -> Prop :=
  PF_POSTr B v (fst (fst (r_lines (cf, cur, nm) ln (lines (skipn o (p_s v)))))).

(* R1, 0x88204: strchr has returned a0 = b5_nl v o; buf is still out of scope; p = s11, lineno = s8 *)
Definition INV_R1 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_rg rX (PF_RL v pos ++ [(27, p_t v + Z.of_nat o); (24, ln); (10, b5_nl v o)]).
(* R2, 0x88224: no '\n' (the line ends the text), strlen has returned a0 = LEN *)
Definition INV_R2 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  (o + b5_len v o = length (p_s v))%nat /\
  pf_rg rX (PF_RL v pos ++ [(27, p_t v + Z.of_nat o); (24, ln); (10, Z.of_nat (b5_len v o))]).
(* Q3, 0x88238: len = s7, p' = s9 = t + pf_next s o (nl + 1 at 0x88214, or p + len at 0x88234) *)
Definition INV_Q3 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_rg rX (PF_RL v pos ++ [(27, p_t v + Z.of_nat o); (24, ln); (25, p_t v + Z.of_nat (pf_next (p_s v) o));
                            (23, Z.of_nat (b5_len v o))]).
(* R3, 0x88250: lineno++ done (0x88238, s6 = ln + 1), buf in scope (meta_fill_00 0x8824c): INV_LONG's registers *)
Definition INV_R3 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(27, p_t v + Z.of_nat o); (23, Z.of_nat (b5_len v o))]).
(* R4, 0x882cc: LEN < 512 (0x88254), checked_memcpy(buf, at, LEN) (0x882c8) has copied the line into buf *)
Definition INV_R4 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  (b5_len v o < 512)%nat /\ sa_zs (rdW Wc memc) (b5_buf v pos) (pf_line (p_s v) o) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(23, Z.of_nat (b5_len v o))]).
(* L k, 0x882f8: buf[LEN] = 0 stored (0x882e0); k bytes checked, no comment start before k; a0 = a1 = buf + k,
   a3 = -k (0x882d4 / 0x882e4, stepped at 0x88348-0x88350), a6 = 1, a7 = ' ', t0 = '\t', t1 = ';' (0x882e8-0x882f4) *)
Definition INV_L (k : nat) (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  (b5_len v o < 512)%nat /\ sa_zs (rdW Wc memc) (b5_buf v pos) (pf_line (p_s v) o ++ [0]) /\
  (k <= b5_len v o)%nat /\ (forall j, (j < k)%nat -> r_comment_at (pf_line (p_s v) o) j = false) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(10, b5_buf v pos + Z.of_nat k); (11, b5_buf v pos + Z.of_nat k); (13, - Z.of_nat k);
             (16, 1); (17, 0x20); (5, 9); (6, 0x3b)]).
(* C, 0x88388: strip_comment done, buf holds r_strip_comment line and its NUL *)
Definition INV_C (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  (b5_len v o < 512)%nat /\ sa_zs (rdW Wc memc) (b5_buf v pos) (r_strip_comment (pf_line (p_s v) o) ++ [0]) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
(* R5, 0x88390: trim(buf) has returned lp, the trimmed line pf_tline s o at lp inside buf *)
Definition INV_R5 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ b5_ln n v pos (rdW Wc memc) cf cur nm o ln d /\
  (b5_len v o < 512)%nat /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (b5_buf v pos) lp (pf_tline (p_s v) o) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(10, lp)]).
(* R6, 0x8860c: TAIL's state with buf out of scope again (meta_fill_f8 0x88608); o is the next line's offset *)
Definition INV_R6 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\
  pf_lctx (p_s v) o ln d /\ (length (skipn o (p_s v)) < n)%nat /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (22, ln)]).

(* from each point the walk reaches the line's post *)
Definition H_R1 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R1 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_R1) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_R2 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R2 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_R2) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_Q3 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_Q3 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_Q3) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_R3 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R3 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_R3) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_R4 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R4 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_R4) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_L (k : nat) (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_L k n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_L) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_C (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_C n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_C) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_R5 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_R5 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_R5) rX memc mdc) (b5_post v cf cur nm o ln).
Definition H_R6 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_R6 n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B5_R6) rX memc mdc) (b5_post v cf cur nm o ln).
End e.
End f.
End d.
