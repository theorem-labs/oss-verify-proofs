(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 110 of its 135 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the INTERNAL cut statements of
   segment B7 of reac_segconf_parse_file's walk (the B7 segment lane of the image-B G3 walk owner, 2026-10-30). Statement text only:
   nothing is proved here and no instruction is walked.

   B7 is the header branch. pf_pieces.v fixes its outer cuts (HDR 0x883b4, HREF 0x885ec, REFTL 0x887cc,
   CLR 0x885fc and the exits TAIL 0x88600 / SEG 0x88ca0). Between them B7 has five join / re-seed points; each is
   internal to B7 (no other segment names them), and splitting the walk at them is what lets the arms be proved
   apart. They are, with the pc (BASE + AF_reac_segconf_parse_file + the offset below) and who reaches them:

     CLOSE  0x884cc (+0x694)  the ']' was found at ci and the line ends there (`beqz a1` at 0x883e8 taken):
                              a0 = lp + ci, s11 = 9 and s8 = 32 (0x883c4 / 0x883c8). B7 then stores the NUL
                              (check B#12, trap T13), trims and runs strncasecmp.
     KWOK   0x88764 (+0x92c)  the body begins with "segment" read case-insensitively (strncasecmp at 0x88500
                              returned 0): s3 = the body, s11 = 9, s8 = 32 are the two blanks body[7] is tested
                              against (0x88784, 0x88788).
     UNK    0x88508 (+0x6d0)  the F_unknown refusal's argument block: s3 = the body. Two arms reach it, the
                              keyword test at 0x88504 (not taken) and the blank test at 0x88788.
     CALL   0x885f8 (+0x7c0)  the shared refuse `jal` of the header refusals: a0 = c, a1 = lineno, a2 = the
                              format, a3 = the string. Entered from HREF's code (0x885f4, a3 = s7) and from UNK
                              (0x8851c `j`, a3 = s3). Its return is CLR 0x885fc.
     NONAME 0x88c88 (+0xe50)  the empty-name refusal (`beqz a0` at 0x887ac taken): no argument but the format.

   The post of every one of them is the post of H_HDR itself (the line's step is r_header of the whole trimmed
   line), as the unit owner's plain lane states its P4 lemmas: a piece does not re-state the step it has already
   decided, it carries the decision as a premise (B7_UNK and B7_NONAME take the r_header equation).

   THE PIECES and the files that prove them (each file takes only the Section hypotheses its own calls need):
     B7_S_REF   HA_TAIL -> H_CLR; HA_CLR -> H_CALL / H_REFTL / H_NONAME; HA_CALL -> H_HREF / H_UNK
                                                                            pf_seg_B7_ref.v (refuse, 3 sites)
     B7_S_HDR   HA_HREF, HA_CLOSE -> H_HDR                                  pf_seg_B7_hdr.v (strchr)
     B7_S_CLOSE HA_KWOK, HA_UNK -> H_CLOSE                                  pf_seg_B7_cl.v  (trim, strncasecmp)
     B7_S_KWOK  HA_UNK, HA_NONAME, HA_REFTL, HA_SEG -> H_KWOK               pf_seg_B7_kw.v  (trim, strlen)
   and pf_seg_B7.v chains them into `S_B7_holds : S_B7 B`.

   Registers by x-number (pf_pieces.v pf_rg): s1 = x9, s2 = x18, s3 = x19, s4 = x20, s5 = x21, s6 = x22,
   s7 = x23, s8 = x24, s9 = x25, s10 = x26, s11 = x27; a0 = x10 .. a4 = x14. PF_RL (s2 = '#', s5 = SH,
   s10 = -1) and PF_RM (s9 = t + pf_next s o, s6 = ln + 1) hold at every point of B7: no instruction of B7
   writes x18, x21, x26, x25 or x22 (write list by script over
   the neutral excerpt reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s, 2026-10-30). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr
  SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B7_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The five internal cut pcs, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition B7_CLOSE : Z := AF_reac_segconf_parse_file + 0x694.   (* 0x884cc, the `*close = 0` check *)
Definition B7_UNK : Z := AF_reac_segconf_parse_file + 0x6d0.     (* 0x88508, the F_unknown block *)
Definition B7_CALL : Z := AF_reac_segconf_parse_file + 0x7c0.    (* 0x885f8, the shared `jal refuse` *)
Definition B7_KWOK : Z := AF_reac_segconf_parse_file + 0x92c.    (* 0x88764, the keyword matched *)
Definition B7_NONAME : Z := AF_reac_segconf_parse_file + 0xe50.  (* 0x88c88, the empty-name refusal *)
(* each internal cut's pc at B's base seg_text (the excerpt's addresses) *)
Lemma b7_cut_pcs :
  seg_text + B7_CLOSE = 0x884cc /\ seg_text + B7_UNK = 0x88508 /\ seg_text + B7_CALL = 0x885f8 /\
  seg_text + B7_KWOK = 0x88764 /\ seg_text + B7_NONAME = 0x88c88.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* the part every point of B7 carries: the cut's frame and objects (pf_base at the line scope), the line context,
   c and cur_name (pf_st0 at the line start), the line's length, and the loop's registers *)
Definition b7_core (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
(* the post of every point of B7's header chain: the line's step is r_header of the trimmed line *)
Definition b7_post (v : pfv) (cf : rconf) (nm : list Z) (o : nat) (ln : Z) : world SEGS -> config -> Prop :=
  pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln.

(* CLOSE (0x884cc): strchr found the ']' at ci (0x883bc) and the byte after it is the line's NUL (0x883e4 /
   0x883e8), so a0 still holds lp + ci and the header's body is about to be cut out of the line; s11 = 9 and
   s8 = 32 are the blanks of the later test (0x883c4 / 0x883c8). *)
Definition INV_CLOSE (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) (ci : nat) : Prop :=
  b7_core n v pos lyc Sc Wc rX memc mdc cf nm o ln d /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) /\
  hd0 (pf_tline (p_s v) o) = LBR /\
  strchr (pf_tline (p_s v) o) RBR = Some ci /\ nth (S ci) (pf_tline (p_s v) o) 0 = 0 /\
  pf_rg rX [(23, lp); (10, lp + Z.of_nat ci); (27, 9); (24, 32)].
Definition H_CLOSE (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci,
  INV_CLOSE n v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_CLOSE) rX memc mdc) (b7_post v cf nm o ln).

(* KWOK (0x88764): the body begins with "segment" read case-insensitively (strncasecmp at 0x88500 returned 0).
   s3 = bp is the body, s11 = 9 and s8 = 32 are the two blanks body[7] is tested against (0x88784, 0x88788). *)
Definition INV_KWOK (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (ci : nat) (bp : Z) : Prop :=
  b7_core n v pos lyc Sc Wc rX memc mdc cf nm o ln d /\
  strchr (pf_tline (p_s v) o) RBR = Some ci /\ nth (S ci) (pf_tline (p_s v) o) 0 = 0 /\
  strncasecmp (b7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 /\
  sa_str (rdW Wc memc) bp (b7_body (pf_tline (p_s v) o) ci) /\
  pf_inb (pf_F v pos + PF_O_BUF) bp (b7_body (pf_tline (p_s v) o) ci) /\
  pf_rg rX [(19, bp); (27, 9); (24, 32)].
Definition H_KWOK (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp,
  INV_KWOK n v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_KWOK) rX memc mdc) (b7_post v cf nm o ln).

(* UNK (0x88508): the F_unknown refusal's argument block. s3 = bp holds the body, the C string the refusal
   prints. The step is already decided: the caller hands the r_header equation. *)
Definition INV_UNK (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (bp : Z) (body : list Z) : Prop :=
  b7_core n v pos lyc Sc Wc rX memc mdc cf nm o ln d /\
  sa_str (rdW Wc memc) bp body /\ pf_inb (pf_F v pos + PF_O_BUF) bp body /\
  r_header cf nm (ln + 1) (pf_tline (p_s v) o) = (refuse cf (ln + 1) F_unknown [AS body], None, nm) /\
  pf_rg rX [(19, bp)].
Definition H_UNK (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d bp body,
  INV_UNK n v pos lyc Sc Wc rX memc mdc cf nm o ln d bp body ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_UNK) rX memc mdc) (b7_post v cf nm o ln).

(* NONAME (0x88c88): the empty-name refusal (`beqz a0` at 0x887ac taken); no variadic argument. *)
Definition INV_NONAME (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  b7_core n v pos lyc Sc Wc rX memc mdc cf nm o ln d /\
  r_header cf nm (ln + 1) (pf_tline (p_s v) o) = (refuse cf (ln + 1) F_noname [], None, nm).
Definition H_NONAME (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d,
  INV_NONAME n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_NONAME) rX memc mdc) (b7_post v cf nm o ln).

(* CALL (0x885f8): the shared `jal refuse` of the header refusals, a0 = c, a1 = lineno, a2 = the format,
   a3 = the string argument; its return is CLR 0x885fc, which stores NULL into cur's slot. The step's cur is
   NULL (CLR stores it).
   NOT b7_core: HREF (pf_pieces.v's INV_HREF) falls into CALL and carries no bound on the line's length, so
   CALL carries b7_core's four other conjuncts and not its `length (pf_line s o) < 512` (found by a
   B7 sub-lane, 2026-10-30; the refuse call does not read the line's length). UNK, which does carry
   b7_core, gives this weaker state by forgetting that conjunct. *)
Definition INV_CALL (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (f : list Z) (x : list Z) (xp : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln) /\
  (f = F_notclosed \/ f = F_after \/ f = F_outside \/ f = F_unknown) /\
  sa_str (rdW Wc memc) xp x /\ pf_inb (pf_F v pos + PF_O_BUF) xp x /\
  pf_rg rX [(10, p_c v); (11, ln + 1); (12, seg_litA_rc f); (13, xp)].
Definition H_CALL (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d f x xp,
  INV_CALL n v pos lyc Sc Wc rX memc mdc cf nm o ln d f x xp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7_CALL) rX memc mdc)
    (pf_postm B v (refuse cf (ln + 1) f [AS x], None, nm) o ln).

End e.
End f.
End d.

(** ** The four pieces, each at every ambient FP state, with the cuts a call can land on taken at every FP
    state (refuse returns at another one; strchr, strncasecmp, strlen and trim do not). *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_CLOSE (n : nat) : Prop := forall f1 : YK11.FPState, H_CLOSE (fx := f1) B n.
Definition HA_KWOK (n : nat) : Prop := forall f1 : YK11.FPState, H_KWOK (fx := f1) B n.
Definition HA_UNK (n : nat) : Prop := forall f1 : YK11.FPState, H_UNK (fx := f1) B n.
Definition HA_NONAME (n : nat) : Prop := forall f1 : YK11.FPState, H_NONAME (fx := f1) B n.
Definition HA_CALL (n : nat) : Prop := forall f1 : YK11.FPState, H_CALL (fx := f1) B n.

(* 0x885fc (CLR, 1 instruction) -> TAIL; 0x885f8 (CALL, the refuse call) -> CLR; 0x885ec-0x885f4 (HREF,
   3 instructions) -> CALL; 0x88508-0x8851c (UNK, 6) -> CALL; 0x887cc-0x887dc (REFTL, 5, its own refuse call)
   -> CLR; 0x88c88-0x88c9c (NONAME, 6, its own refuse call) -> CLR. *)
Definition B7_S_REF : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL B n -> H_CLR (fx := f0) B n) /\
    (HA_CLR B n -> H_CALL (fx := f0) B n) /\
    (HA_CLR B n -> H_REFTL (fx := f0) B n) /\
    (HA_CLR B n -> H_NONAME (fx := f0) B n) /\
    (HA_CALL n -> H_HREF (fx := f0) B n) /\
    (HA_CALL n -> H_UNK (fx := f0) B n).
(* 0x883b4-0x883f4 + 0x884a0-0x884a8 + the check stubs of B#8: strchr(lp, ']'), the trap T10, the check B#8 on
   close[1], the two refusals that jump to HREF. HDR -> CLOSE or HREF. *)
Definition B7_S_HDR : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_HREF B n -> HA_CLOSE n -> H_HDR (fx := f0) B n.
(* 0x884cc-0x88504 + the check stub of B#12: the check and the store of the NUL at the ']', the trap T13,
   trim(line + 1), strncasecmp(body, "segment", 7). CLOSE -> KWOK or UNK. *)
Definition B7_S_CLOSE : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_KWOK n -> HA_UNK n -> H_CLOSE (fx := f0) B n.
(* 0x88764-0x887c8 + the check stubs of B#20 and B#21: the trap T19, body[7], trim(body + 7), *name, strlen.
   KWOK -> UNK (body[7] is no blank), NONAME (the name is empty), SEG (a name of 1 to 15 bytes) or REFTL (16 or
   more). *)
Definition B7_S_KWOK : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    HA_UNK n -> HA_NONAME n -> HA_REFTL B n -> HA_SEG B n -> H_KWOK (fx := f0) B n.
End s.
