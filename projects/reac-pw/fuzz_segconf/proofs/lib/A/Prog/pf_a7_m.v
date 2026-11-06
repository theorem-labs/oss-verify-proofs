(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 84 of its 110 lines of code are new or changed and 492 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the INTERNAL cut statements of segment A7 of
   reac_segconf_parse_file's walk (segment A7's proof, 2026-10-30). Statement text only: nothing is
   proved here and no instruction is walked.

   A7 is the header branch. pf_pieces.v fixes its four outer cuts (HDR 0x87f6c, CLR 0x880fc, RS3 0x88100 and
   the exits TAIL 0x88068 / SEG 0x887a4). Between them the segment has four join points that more than one
   arm reaches, and splitting the walk at them is what lets the arms be proved apart. They are internal to
   A7: no other segment names them, and the whole of S_A7 is assembled from the five pieces below.

     FUN   0x88064 (+0x5ec)  `mv s4, zero`, then TAIL. The funnel of three of A7's four refusals: the call at
                             0x88060 falls into it, and 0x88360 (F_toolong) and 0x88798 (F_noname) jump to it.
                             s3 is the shadow base + 8 again on every arm that reaches it (the F_unknown arm,
                             which leaves the body in s3, goes to CLR / RS3 instead, where 0x88100 reloads it).
     CLOSE 0x880ac (+0x634)  the header's ']' was found at ci and nothing follows it: a0 = lp + ci.
     UNK   0x880e4 (+0x66c)  the F_unknown refusal site: s3 = the body. Two arms reach it, the keyword test at
                             0x880e0 and the blank test at 0x8830c.
     KWOK  0x882f0 (+0x878)  the keyword matched: s3 = the body, the walk now reads body[7].

   The post of every one of them is the post of H_HDR itself (the line's step is r_header of the whole
   trimmed line), as the plain-build walk owner's plain walk states its P4 lemmas: a piece does not re-state
   the step it has already decided, it carries the decision as a premise (H_UNK takes the r_header equation).

   The five pieces and the files that prove them:
     A7_S_FUN    HA_TAIL -> H_FUN                                   pf_a7_cr.v
     A7_S_UNK    (every FP state) H_CLR -> H_UNK                    pf_a7_u.v
     A7_S_KWOK   (ditto) H_FUN, H_UNK, HA_SEG -> H_KWOK             pf_a7_w3.v
     A7_S_CLOSE  (ditto) H_KWOK, H_UNK -> H_CLOSE                   pf_a7_w2.v
     A7_S_HDR    (ditto) H_FUN, H_CLOSE -> H_HDR                    pf_a7_w1.v
   and pf_a7.v chains them into `pf_a7_holds : S_A7 B` with pf_a7_cr.v's H_CLR and H_RS3. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a7_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The four internal cut pcs, as listing offsets *)
Definition A7_FUN : Z := AF_reac_segconf_parse_file + 0x5ec.    (* 0x88064 *)
Definition A7_CLOSE : Z := AF_reac_segconf_parse_file + 0x634.  (* 0x880ac *)
Definition A7_UNK : Z := AF_reac_segconf_parse_file + 0x66c.    (* 0x880e4 *)
Definition A7_KWOK : Z := AF_reac_segconf_parse_file + 0x878.   (* 0x882f0 *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* FUN (0x88064): a refusal has been made, c holds cf, the step's cur is NULL, and `mv s4, zero` is the only
   instruction before TAIL. Every register of the loop still holds (s3 among them: the arms that reach FUN
   never overwrite it, or reload it at 0x8832c). *)
Definition INV_FUN (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_FUN (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d, INV_FUN n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A7_FUN) rX memc mdc) (pf_postm B v (cf, None, nm) o ln).

(* CLOSE (0x880ac): strchr found the ']' at ci (0x87f74) and the byte after it is the line's NUL
   (0x87f90 / 0x87f94), so a0 still holds the ']' and the header's body is about to be cut out of the line.
   Everything else is INV_HDR's. *)
Definition INV_CLOSE (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) (ci : nat) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xb0, pf_cur_ptr (p_c v) cur)] /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) /\
  hd0 (pf_tline (p_s v) o) = LBR /\
  strchr (pf_tline (p_s v) o) RBR = Some ci /\ nth (S ci) (pf_tline (p_s v) o) 0 = 0 /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(20, 0x20); (25, 9); (23, lp); (10, lp + Z.of_nat ci)]).
Definition H_CLOSE (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci,
  INV_CLOSE n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ci ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A7_CLOSE) rX memc mdc)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* UNK (0x880e4): the F_unknown refusal site. s3 = bp holds the body, the C string the refusal prints; s3 is
   NOT the shadow base here, so the loop registers this cut names are only the four the refusal and CLR need.
   The step is already decided: the caller hands the r_header equation. *)
Definition INV_UNK (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (bp : Z) (body : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) bp body /\ pf_inb (pf_F v pos + PF_O_BUF) bp body /\
  r_header cf nm (ln + 1) (pf_tline (p_s v) o) = (refuse cf (ln + 1) F_unknown [AS body], None, nm) /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos); (19, bp)] ++ PF_RM v o ln).
Definition H_UNK (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d bp body,
  INV_UNK n v pos lyc Sc Wc rX memc mdc cf nm o ln d bp body ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A7_UNK) rX memc mdc)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* KWOK (0x882f0): the body begins with "segment" read case-insensitively (strncasecmp at 0x880dc returned 0).
   s3 = bp is the body, s9 = 9 and s4 = 0x20 are the two blanks body[7] is tested against (0x88308, 0x8830c). *)
Definition INV_KWOK (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) (ci : nat) (bp : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  strchr (pf_tline (p_s v) o) RBR = Some ci /\ nth (S ci) (pf_tline (p_s v) o) 0 = 0 /\
  strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 /\
  sa_str (rdW Wc memc) bp (a7_body (pf_tline (p_s v) o) ci) /\
  pf_inb (pf_F v pos + PF_O_BUF) bp (a7_body (pf_tline (p_s v) o) ci) /\
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos); (19, bp); (20, 0x20); (25, 9)] ++ PF_RM v o ln).
Definition H_KWOK (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci bp,
  INV_KWOK n v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci bp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A7_KWOK) rX memc mdc)
    (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).

End e.
End f.
End d.

(** ** The five pieces, each at every ambient FP state, with the cuts a call can land on taken at every FP
    state (refuse returns at another one; strchr, strncasecmp, strlen and trim do not). *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_FUN (n : nat) : Prop := forall f1 : YK11.FPState, H_FUN (fx := f1) B n.
Definition HA_CLOSE (n : nat) : Prop := forall f1 : YK11.FPState, H_CLOSE (fx := f1) B n.
Definition HA_UNK (n : nat) : Prop := forall f1 : YK11.FPState, H_UNK (fx := f1) B n.
Definition HA_KWOK (n : nat) : Prop := forall f1 : YK11.FPState, H_KWOK (fx := f1) B n.

(* 0x88064, 1 instruction: `mv s4, zero`, then TAIL. *)
Definition A7_S_FUN : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_TAIL B n -> H_FUN (fx := f0) B n.
(* 0x880e4-0x880f8, 6 instructions: the F_unknown refusal, then CLR. *)
Definition A7_S_UNK : Prop :=
  forall (f0 : YK11.FPState) (n : nat), (forall f1 : YK11.FPState, H_CLR (fx := f1) B n) ->
  H_UNK (fx := f0) B n.
(* 0x882f0-0x88364 + 0x88784-0x8879c + the two check stubs: body[7], trim(body + 7), the empty-name and
   over-long-name refusals, strlen. KWOK -> SEG, UNK (body[7] is no blank) or FUN (a refusal). *)
Definition A7_S_KWOK : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_FUN n -> HA_UNK n -> HA_SEG B n -> H_KWOK (fx := f0) B n.
(* 0x880ac-0x880e4 + its check stub: the store of the NUL at the ']', trim(line + 1), strncasecmp. *)
Definition A7_S_CLOSE : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_KWOK n -> HA_UNK n -> H_CLOSE (fx := f0) B n.
(* 0x87f6c-0x87fa4 + 0x8804c-0x88064 + its check stub: strchr(line, ']'), the two refusals that share the
   call at 0x88060. *)
Definition A7_S_HDR : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_FUN n -> HA_CLOSE n -> H_HDR (fx := f0) B n.
End s.
