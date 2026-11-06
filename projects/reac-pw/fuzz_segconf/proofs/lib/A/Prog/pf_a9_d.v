(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 115 of its 140 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the SHARED VOCABULARY of segment A9 of
   reac_segconf_parse_file's walk (lib/A/Prog/pf_pieces.v S_A9: KEY 0x87fac -> ROLE / MODEL / IGN / REF3 / TAIL,
   129 instructions, checks 9-11, 14, 15; calls strchr, 2 x trim, strlen, 4 x strcasecmp, refuse).
   Segment A9's proof, by the G3 walk owner, 2026-10-30. Statement text only: no instruction is walked here.

   THE FORM is cross_check_d.v's / chain_words_d.v's (origin/ossv/recipes 501c0d516c69): the cut points of the
   segment stated over the MACHINE state, not over a symbolic state, so each stretch file builds its own symbolic
   state; "from this cut the walk reaches S_A9's goal" as a9_from; one Prop per stretch (SA9_A .. SA9_E).

   THE CODE (dis/reac_segconf_parse_file.fuzz_segconf.asan.s, dis/g3.asan.ann.txt; reac_segconf.c:215-293):
     0x87fac KEY   a1 = '=', a0 = s7 = lp;  jal 0x43a28 strchr
     0x87fb8       ld s4, 0xb0(s1) (= cur); beqz a0 -> 0x88094 (no '=': F_neither, a2 = 0x216a0, j 0x881c4)
     0x87fc0       s8 = eq; check 9 (store1 at eq, 0x87fcc/0x88a34); sb zero,0(s8)
     0x87fd8       a0 = s7;  jal 0x890a8 trim         (trim(line): the key)
     0x87fe0       s7 = a0 = kp
     0x87fe4 K2    a0 = s8 + 1;  jal 0x890a8 trim     (trim(eq + 1): the value)
     0x87fec       s9 = a0 = vp0;  jal 0x43a0c strlen (strlen(v), a0 still vp0)
     0x87ff4 K3    a0 = n = |v|; bltu a0,2 -> 0x880a4 (ld s8,0x90(s1); j 0x8814c)
                   checks 10 (lb at vp0), 11 (lb at vp0+n-1), 14 (lb at vp0+n-1), 15 (store1 at vp0+n-1);
                   the quote test of R:78-86; on a strip: sb zero,0(vp0+n-1); s9 = vp0 + 1
     0x8814c K5    beqz s4 -> 0x881bc (cur = NULL: F_outside, a2 = 0x21700, j 0x881c4)
     0x88150       a1 = 0x21760 "role",   a0 = s7;  jal 0x43a1c strcasecmp; beqz -> 0x881d4 ROLE
     0x88164       a1 = 0x21800 "model",  a0 = s7;  jal 0x43a1c strcasecmp; beqz -> 0x8826c MODEL
     0x88178       a1 = 0x218e0 "ignore", a0 = s7;  jal 0x43a1c strcasecmp; beqz -> 0x88364 IGN
     0x8818c       a1 = 0x21960 "knock",  a0 = s7;  jal 0x43a1c strcasecmp; beqz -> 0x884f8 (F_knock,
                   a2 = 0x21980, a4 = s9 = val); else 0x881a0 (F_nokey, a2 = 0x21a40, a4 = s7 = key)
     0x88510 K9    a0 = s8 = c, a1 = s10 = lineno, a2 = the format, a3 = slot 0x50 = cur_name, a4 as above;
                   jal 0x88da4 refuse;  0x88514 j 0x88068 TAIL
     0x881c4 REF3  a0 = s8 = c, a1 = s10, a3 = s7, a2 = the format;  j 0x87e74 (A6's shared refuse call)

   THE STRETCHES (one file each):
     SA9_A  pf_a9_s1.v  KEY -> REF3 (no '=') or K2       strchr, check 9, the NUL store, trim #1
     SA9_B  pf_a9_s2.v  K2  -> K3                        trim #2, strlen
     SA9_C  pf_a9_s3.v  K3  -> K5                        the unquote block, checks 10, 11, 14, 15
     SA9_D  pf_a9_s4.v  K5  -> REF3 (cur = NULL), ROLE, MODEL, IGN or K9    4 x strcasecmp
     SA9_E  pf_a9_s5.v  K9  -> TAIL                      refuse
   Every internal cut is taken at the segment's own FP state fx (strchr / trim / strlen / strcasecmp keep it);
   only the refuse call of SA9_E changes it, and its TAIL exit is taken at every FP state (HA_TAIL). *)
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

(** ** The cut pcs, as listing offsets (BASE + A9_<k>; AF_reac_segconf_parse_file = 0x87a78) *)
Definition A9_K2 : Z := AF_reac_segconf_parse_file + 0x56c.   (* 0x87fe4 *)
Definition A9_K3 : Z := AF_reac_segconf_parse_file + 0x57c.   (* 0x87ff4 *)
Definition A9_K5 : Z := AF_reac_segconf_parse_file + 0x6d4.   (* 0x8814c *)
Definition A9_K9 : Z := AF_reac_segconf_parse_file + 0xa98.   (* 0x88510 *)
(* the two exits A9 reaches by a `j`: REF3 is A6's shared refuse call, TAIL is A5's line end *)
Definition A9_REF3 : Z := PF_REF3.
Definition A9_TAIL : Z := PF_TAIL.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(** ** The segment's context: INV_KEY's binders, packed (cross_check_d.v ccx) *)
Record a9x : Type := mkA9X {
  y_v : pfv;              (* the contract's bundle *)
  y_pos : Z;              (* the class-5 frame's position *)
  y_cf : rconf;           (* the reader's record at the line's start *)
  y_cur : option nat;     (* the current section *)
  y_nm : list Z;          (* cur_name's C string *)
  y_o : nat;              (* the line's offset in the text *)
  y_ln : Z;               (* the lines consumed before it *)
  y_d : list (list Z);    (* those lines *)
  y_lp : Z }.             (* the trimmed line's pointer in buf, at the cut KEY *)

(* the line A9 reads, the bytes of the text left, buf, cur as a pointer *)
Definition a9_line (x : a9x) : list Z := pf_tline (p_s (y_v x)) (y_o x).
Definition a9_k (x : a9x) : nat := length (skipn (y_o x) (p_s (y_v x))).
Definition a9_buf (x : a9x) : Z := pf_F (y_v x) (y_pos x) + PF_O_BUF.
Definition a9_cp (x : a9x) : Z := pf_cur_ptr (p_c (y_v x)) (y_cur x).
(* the key / value split of R:215-223, at the index ei of the '=' *)
Definition a9_key (x : a9x) (ei : nat) : list Z := r_trim (firstn ei (a9_line x)).
Definition a9_v0 (x : a9x) (ei : nat) : list Z := r_trim (skipn (S ei) (a9_line x)).
Definition a9_val (x : a9x) (ei : nat) : list Z := r_unquote (a9_v0 x ei).
(* what every cut of A9 must reach: H_KEY's post *)
Definition a9_goal (x : a9x) : world SEGS -> config -> Prop :=
  pf_postm B (y_v x) (r_key (y_cf x) (y_cur x) (y_nm x) (y_ln x + 1) (a9_line x)) (y_o x) (y_ln x).

(** ** What every cut of A9 carries (INV_KEY without its line string and its registers) *)
Definition a9_core (n : nat) (x : a9x) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  pf_base B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE /\
  pf_mid (y_v x) (y_o x) (y_ln x) (y_d x) n /\
  pf_st (y_v x) (y_pos x) (rdW Wc memc) (y_cf x) (y_cur x) (y_nm x) (a9_k x) /\
  pf_sl (rdW Wc memc) (pf_s1 (y_v x)) [(0xb0, a9_cp x)] /\
  (length (pf_line (p_s (y_v x)) (y_o x)) < 512)%nat /\
  hd0 (a9_line x) <> 0 /\ hd0 (a9_line x) <> LBR.

(* the registers A9 keeps unchanged from KEY to K5 (s8 holds the '=' pointer in between, so PF_RL's (24, c) is
   not among them): s2 = '#', s3 = SH + 8, s11 = SH, and the line's s5 = p', s10 = lineno *)
Definition A9_RC (x : a9x) : list (Z * Z) :=
  [(18, 0x23); (19, pf_SH (y_v x) (y_pos x) + 8); (27, pf_SH (y_v x) (y_pos x))] ++
  PF_RM (y_v x) (y_o x) (y_ln x).
(* a C string of buf, as trim, strlen, strcasecmp and refuse read it *)
Definition a9_inbuf (rd : reader) (x : a9x) (a : Z) (s : list Z) : Prop :=
  sa_str rd a s /\ pf_inb (a9_buf x) a s.

(** ** K2 (0x87fe4): the '=' is at ei, buf holds the key at kp and the rest of the line at eq + 1.
    s8 = eq = lp + ei (restored to c at 0x88008 / 0x8809c / 0x880a4), s7 = kp, s4 = cur.
    The key's bytes and its NUL end AT OR BELOW the '=' (trim #1 kept a sub-range of [lp, lp + ei)), so no
    later write of A9 -- trim #2's NUL at or above eq + 1, and the unquote store at vp0 + |v| - 1 -- can reach
    them. Without this conjunct the line "\"a\"=\"a\"" has kp = vp0 and the unquote store would destroy the
    key (found by stretch C's proof, 2026-10-30). *)
Definition INV_K2 (n : nat) (x : a9x) (ei : nat) (kp : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  a9_core n x lyc Sc Wc rX memc mdc /\
  strchr (a9_line x) EQ = Some ei /\
  a9_inbuf (rdW Wc memc) x kp (a9_key x ei) /\
  kp + Z.of_nat (length (a9_key x ei)) <= y_lp x + Z.of_nat ei /\
  a9_inbuf (rdW Wc memc) x (y_lp x + Z.of_nat ei + 1) (skipn (S ei) (a9_line x)) /\
  pf_rg rX (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp)]).

(** ** K3 (0x87ff4): both trims are done and strlen has answered. s9 = vp0, a0 = |v|.
    The key ends strictly below vp0 (vp0 >= eq + 1 = lp + ei + 1 > kp + |key|), which is what keeps the key
    whole across the unquote store of stretch C. *)
Definition INV_K3 (n : nat) (x : a9x) (ei : nat) (kp vp0 : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  a9_core n x lyc Sc Wc rX memc mdc /\
  strchr (a9_line x) EQ = Some ei /\
  a9_inbuf (rdW Wc memc) x kp (a9_key x ei) /\
  kp + Z.of_nat (length (a9_key x ei)) < vp0 /\
  a9_inbuf (rdW Wc memc) x vp0 (a9_v0 x ei) /\
  pf_rg rX (A9_RC x ++ [(24, y_lp x + Z.of_nat ei); (20, a9_cp x); (23, kp); (25, vp0);
                        (10, Z.of_nat (length (a9_v0 x ei)))]).

(** ** K5 (0x8814c): the key / value pair is built (the unquote is done), s8 is c again. *)
Definition INV_K5 (n : nat) (x : a9x) (ei : nat) (kp vp : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  a9_core n x lyc Sc Wc rX memc mdc /\
  strchr (a9_line x) EQ = Some ei /\
  a9_inbuf (rdW Wc memc) x kp (a9_key x ei) /\
  a9_inbuf (rdW Wc memc) x vp (a9_val x ei) /\
  pf_rg rX (PF_RL (y_v x) (y_pos x) ++ PF_RM (y_v x) (y_o x) (y_ln x) ++
            [(20, a9_cp x); (23, kp); (25, vp)]).

(** ** K9 (0x88510): the knock / no-key refusal's call. The two arms differ only in the format and in the
    string a4 points at (R:286 "%.24s" of the value, R:291 the key). *)
Definition a9_arg2 (x : a9x) (ei : nat) (f : list Z) (fa : Z) (w : list Z) : Prop :=
  (f = F_knock /\ fa = seg_litA_rc F_knock /\ w = a9_val x ei) \/
  (f = F_nokey /\ fa = seg_litA_rc F_nokey /\ w = a9_key x ei).
Definition INV_K9 (n : nat) (x : a9x) (ei gi : nat) (f : list Z) (fa wp : Z) (w : list Z)
  (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  a9_core n x lyc Sc Wc rX memc mdc /\
  y_cur x = Some gi /\
  strchr (a9_line x) EQ = Some ei /\
  a9_arg2 x ei f fa w /\
  a9_inbuf (rdW Wc memc) x wp w /\
  (* the step r_key takes on this arm, so that A9's goal is the refusal's post *)
  r_key (y_cf x) (y_cur x) (y_nm x) (y_ln x + 1) (a9_line x)
    = (refuse (y_cf x) (y_ln x + 1) f [AS (y_nm x); AS w], y_cur x, y_nm x) /\
  pf_rg rX (PF_RL (y_v x) (y_pos x) ++ PF_RM (y_v x) (y_o x) (y_ln x) ++
            [(20, a9_cp x); (10, p_c (y_v x)); (11, y_ln x + 1); (12, fa);
             (13, pf_F (y_v x) (y_pos x) + PF_O_CN); (14, wp)]).

(** ** "from this cut the walk reaches A9's goal" (chain_words_d.v cw_from) *)
Definition a9_from (pc : Z)
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (x : a9x) : Prop :=
  forall lyc Sc Wc rX memc mdc, P lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + pc) rX memc mdc) (a9_goal x).
Definition from_K2 (n : nat) : Prop := forall x ei kp, a9_from A9_K2 (INV_K2 n x ei kp) x.
Definition from_K3 (n : nat) : Prop := forall x ei kp vp0, a9_from A9_K3 (INV_K3 n x ei kp vp0) x.
Definition from_K5 (n : nat) : Prop := forall x ei kp vp, a9_from A9_K5 (INV_K5 n x ei kp vp) x.
Definition from_K9 (n : nat) : Prop :=
  forall x ei gi f fa wp w, a9_from A9_K9 (INV_K9 n x ei gi f fa wp w) x.

(** ** The five stretch statements *)
Definition SA9_A : Prop := forall n : nat, HA_REF3 B n -> from_K2 n -> H_KEY B n.
Definition SA9_B : Prop := forall n : nat, from_K3 n -> from_K2 n.
Definition SA9_C : Prop := forall n : nat, from_K5 n -> from_K3 n.
Definition SA9_D : Prop :=
  forall n : nat, HA_REF3 B n -> HA_ROLE B n -> HA_MODEL B n -> HA_IGN B n -> from_K9 n -> from_K5 n.
Definition SA9_E : Prop := forall n : nat, HA_TAIL B n -> from_K9 n.

(** ** The packing of H_KEY's binders: a9_core and the line string from INV_KEY *)
Lemma a9_of_KEY : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_KEY B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  let x := mkA9X v pos cf cur nm o ln d lp in
  a9_core n x lyc Sc Wc rX memc mdc /\
  a9_inbuf (rdW Wc memc) x lp (a9_line x) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(20, 0x20); (25, 9); (23, lp)]).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp
  (HB & HM & HS & HL & HLT & HSTR & HINB & HD0 & HDL & HRG).
cbn zeta. split; [|split; [split; [exact HSTR | exact HINB] | exact HRG]].
split; [exact HB|]. split; [exact HM|]. split; [exact HS|]. split; [exact HL|].
split; [exact HLT|]. split; [exact HD0 | exact HDL].
Qed.

End e.
End f.
End d.
