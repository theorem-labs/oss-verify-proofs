(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 148 of its 173 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the SHARED
   VOCABULARY of segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_pieces.v S_B9: KEY 0x883f8 -> ROLE /
   MODEL / IGN / REF3 / HREF / TAIL through KREF, and KREF 0x889a0 -> TAIL; 131 instructions, checks B#9, B#10,
   B#11, B#13, B#14, UBSan trap branches T11, T12, T14, T15, T16; calls strchr, 2 x trim, strlen, 4 x strcasecmp,
   refuse). The B9 segment lane of the image-B G3 walk owner, 2026-10-30. Statement text only: no instruction is walked here.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: the internal cuts of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_d.v (00819c5d72b2; A9's cuts K2 / K3 / K5 / K9 and the
   key-below-value conjunct the image-A A9 segment lane found), re-derived on image B's code: B keeps cur in slot 0xc0
   only (A: s4), B puts an internal cut after every call (so each stretch is one straight run to a call or an exit),
   and B's shared key refusal KREF is a cut of pf_pieces.v (A's K9 was internal).

   THE FORM is cross_check_d.v's / chain_words_d.v's (origin/ossv/recipes 501c0d516c69): the cut points of the
   segment stated over the MACHINE state, so each stretch file builds its own symbolic state; "from this cut the
   walk reaches S_B9's goal" as b9_from; one Prop per stretch (SB9_1 .. SB9_10; the KREF -> TAIL stretch is
   pf_pieces.v's second conjunct of S_B9 itself).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; reac_segconf.c:215-293):
     KEY 0x883f8  li a1,61; mv a0,s7 (lp); 0x88400 jal strchr
     J1  0x88404  beqz a0 -> 0x884ac (no '=': a2 = 0x216a0 F_neither, a0 = c (slot 0xc8), a1 = s6, a3 = s7 = lp;
                  j 0x882b4 = REF3). Else s8 = eq; check B#9 (store1 at eq); 0x8841c sb zero,0(s8); a0 = s7;
                  0x88424 jal trim                                   (trim(line) after *eq = 0: the key)
     J2  0x88428  beq s8,s10 -> unimp (T11, eq + 1 wraps); s7 = kp; a0 = s8 + 1; 0x88434 jal trim (trim(eq + 1))
     J3  0x88438  s3 = vp0; 0x8843c jal strlen (a0 = vp0)
     J4  0x88440  n = a0; the unquote of R:78-86 (n < 2: a5 = slot 0xc0, j K5; else check B#10 at vp0, a5 = slot
                 0xc0, v[0] = SQ / DQ, T12 / T14 (vp0 + n - 1 wraps), checks B#11 / B#13 at vp0 + n - 1, the strip:
                  T15, check B#14 (store1 at vp0 + n - 1), sb zero, T16 (vp0 + 1 wraps), s3 = vp0 + 1)
     K5  0x88570  beqz a5 -> 0x885e4 (cur = NULL: a2 = 0x21700 F_outside, falls into HREF 0x885ec, s7 = kp);
                  sd s3,112(s1) (val to slot 0x70); a1 = 0x21760 "role"; a0 = s7; 0x88584 jal strcasecmp
     J6  0x88588  beqz a0 -> ROLE 0x88630;   a1 = 0x21800 "model";  a0 = s7; 0x88598 jal strcasecmp
     J7  0x8859c  beqz a0 -> MODEL 0x886d4;  a1 = 0x218e0 "ignore"; a0 = s7; 0x885ac jal strcasecmp
     J8  0x885b0  beqz a0 -> IGN 0x887e0;    a1 = 0x21960 "knock";  a0 = s7; 0x885c0 jal strcasecmp
     J9  0x885c4  beqz a0 -> 0x88988 (knock: a2 = 0x21980, a0 = c, a1 = s6, a3 = slot 0x40 = cur_name,
                  a4 = slot 0x70 = val, falls into KREF); else nokey 0x885c8 (a2 = 0x21a40, a0 = c, a1 = s6,
                  a3 = slot 0x40, a4 = s7 = key; j 0x889a0 KREF)
     KREF 0x889a0 jal refuse; 0x889a4 j TAIL 0x88600            (pf_pieces.v's H_KREF; also B12's bad ignore)

   THE STRETCHES (one file each, pf_seg_B9_s<k>.v):
     SB9_1   KEY -> J1                       strchr
     SB9_2   J1  -> REF3 (no '=') or J2       check B#9, the NUL store, trim #1
     SB9_3   J2  -> J3                        T11, trim #2
     SB9_4   J3  -> J4                        strlen
     SB9_5   J4  -> K5                        the unquote block: B#10, B#11, B#13, B#14; T12, T14, T15, T16
     SB9_6   K5  -> HREF (cur = NULL) or J6   the val spill, strcasecmp "role"
     SB9_7   J6  -> ROLE or J7                strcasecmp "model"
     SB9_8   J7  -> MODEL or J8               strcasecmp "ignore"
     SB9_9   J8  -> IGN or J9                 strcasecmp "knock"
     SB9_10  J9  -> KREF                      the knock / nokey arguments
     S_B9's second conjunct: KREF -> TAIL (refuse, at every FP state).
   Every internal cut is taken at the segment's own FP state fx (strchr, trim, strlen and strcasecmp keep it);
   only refuse changes it, and KREF's TAIL exit is pf_pieces.v's HA_TAIL (every FP state).

   THE KEY STAYS BELOW THE VALUE (A9's finding, the image-A A9 segment lane, 2026-10-30): the key's bytes and its NUL end at
   or below the '=' (trim #1 keeps a sub-range of [lp, lp + ei)), and the value starts above it; so trim #2's NUL
   (at or above eq + 1) and the unquote store (at vp0 + |v| - 1 >= vp0 > eq) leave the key whole. J2 carries
   kp + |key| <= lp + ei, J3 / J4 carry kp + |key| < vp0. Without it the line DQ a DQ = DQ a DQ (key and value both
   quoted) would break the walk. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The internal cut pcs, as listing offsets (BASE + B9_<k>; AF_reac_segconf_parse_file = 0x3078, B's SegList) *)
Definition B9_J1 : Z := AF_reac_segconf_parse_file + 0x5cc.   (* 0x88404 strchr's return *)
Definition B9_J2 : Z := AF_reac_segconf_parse_file + 0x5f0.   (* 0x88428 trim #1's return *)
Definition B9_J3 : Z := AF_reac_segconf_parse_file + 0x600.   (* 0x88438 trim #2's return *)
Definition B9_J4 : Z := AF_reac_segconf_parse_file + 0x608.   (* 0x88440 strlen's return *)
Definition B9_K5 : Z := AF_reac_segconf_parse_file + 0x738.   (* 0x88570 the cur test *)
Definition B9_J6 : Z := AF_reac_segconf_parse_file + 0x750.   (* 0x88588 strcasecmp "role"'s return *)
Definition B9_J7 : Z := AF_reac_segconf_parse_file + 0x764.   (* 0x8859c strcasecmp "model"'s return *)
Definition B9_J8 : Z := AF_reac_segconf_parse_file + 0x778.   (* 0x885b0 strcasecmp "ignore"'s return *)
Definition B9_J9 : Z := AF_reac_segconf_parse_file + 0x78c.   (* 0x885c4 strcasecmp "knock"'s return *)
(* the cut after the k-th strcasecmp (k = 0 .. 3), and the literal it compared the key with *)
Definition B9_JC (k : nat) : Z := nth k [B9_J6; B9_J7; B9_J8; B9_J9] B9_J9.
Definition b9_lits : list (list Z) := [S_role; S_model; S_ignore; S_knock].
(* each pc at B's base seg_text (the excerpt's addresses) *)
Lemma b9_cut_pcs :
  seg_text + B9_J1 = 0x88404 /\ seg_text + B9_J2 = 0x88428 /\ seg_text + B9_J3 = 0x88438 /\
  seg_text + B9_J4 = 0x88440 /\ seg_text + B9_K5 = 0x88570 /\ seg_text + B9_J6 = 0x88588 /\
  seg_text + B9_J7 = 0x8859c /\ seg_text + B9_J8 = 0x885b0 /\ seg_text + B9_J9 = 0x885c4.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the literals' addresses the code forms (auipc / addi at 0x88578, 0x8858c, 0x885a0, 0x885b4; SegInstB) *)
Lemma b9_lit_addrs :
  seg_litA_rc S_role = 0x21760 /\ seg_litA_rc S_model = 0x21800 /\ seg_litA_rc S_ignore = 0x218e0 /\
  seg_litA_rc S_knock = 0x21960 /\ seg_litA_rc F_neither = 0x216a0 /\ seg_litA_rc F_outside = 0x21700 /\
  seg_litA_rc F_knock = 0x21980 /\ seg_litA_rc F_nokey = 0x21a40.
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

(** ** The segment's context: INV_KEY's binders, packed (cross_check_d.v ccx; A9's a9x) *)
Record b9x : Type := mkB9X {
  y_v : pfv;              (* the contract's bundle *)
  y_pos : Z;              (* the class-5 frame's position *)
  y_cf : rconf;           (* the reader's record at the line's start *)
  y_cur : option nat;     (* the current section *)
  y_nm : list Z;          (* cur_name's C string *)
  y_o : nat;              (* the line's offset in the text *)
  y_ln : Z;               (* the lines consumed before it *)
  y_d : list (list Z);    (* those lines *)
  y_lp : Z }.             (* the trimmed line's pointer in buf, at the cut KEY *)

(* the line B9 reads, the bytes of the text left, buf, cur as a pointer *)
Definition b9_line (x : b9x) : list Z := pf_tline (p_s (y_v x)) (y_o x).
Definition b9_k (x : b9x) : nat := length (skipn (y_o x) (p_s (y_v x))).
Definition b9_buf (x : b9x) : Z := pf_F (y_v x) (y_pos x) + PF_O_BUF.
Definition b9_cp (x : b9x) : Z := pf_cur_ptr (p_c (y_v x)) (y_cur x).
(* the key / value split of R:215-223, at the index ei of the '=' *)
Definition b9_key (x : b9x) (ei : nat) : list Z := r_trim (firstn ei (b9_line x)).
Definition b9_v0 (x : b9x) (ei : nat) : list Z := r_trim (skipn (S ei) (b9_line x)).
Definition b9_val (x : b9x) (ei : nat) : list Z := r_unquote (b9_v0 x ei).
(* what every cut of B9 must reach: H_KEY's post *)
Definition b9_goal (x : b9x) : world SEGS -> config -> Prop :=
  pf_postm B (y_v x) (r_key (y_cf x) (y_cur x) (y_nm x) (y_ln x + 1) (b9_line x)) (y_o x) (y_ln x).

(** ** What every cut of B9 carries (INV_KEY without its line string and its registers) *)
Definition b9_core (n : nat) (x : b9x) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  pf_base B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE /\
  pf_mid (y_v x) (y_o x) (y_ln x) (y_d x) n /\
  pf_st (y_v x) (y_pos x) (rdW Wc memc) (y_cf x) (y_cur x) (y_nm x) (b9_k x) /\
  (length (pf_line (p_s (y_v x)) (y_o x)) < 512)%nat /\
  hd0 (b9_line x) <> 0 /\ hd0 (b9_line x) <> LBR.

(* the registers no instruction of B9 writes (B9 writes s3, s7, s8 and argument registers only): s2 = '#',
   s5 = SH, s10 = -1, and the line's s9 = p', s6 = lineno (pf_pieces.v PF_RL, PF_RM) *)
Definition B9_R (x : b9x) : list (Z * Z) :=
  PF_RL (y_v x) (y_pos x) ++ PF_RM (y_v x) (y_o x) (y_ln x).
(* a C string of buf, as trim, strlen, strcasecmp and refuse read it *)
Definition b9_inbuf (rd : reader) (x : b9x) (a : Z) (s : list Z) : Prop :=
  sa_str rd a s /\ pf_inb (b9_buf x) a s.

(** ** J1 (0x88404): strchr has answered r = SegModel.strchr line '=' (a0 = NULL, or lp + ei). s7 = lp. *)
Definition INV_J1 (n : nat) (x : b9x) (r : option nat) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9_core n x lyc Sc Wc rX memc mdc /\
  b9_inbuf (rdW Wc memc) x (y_lp x) (b9_line x) /\
  strchr (b9_line x) EQ = r /\
  pf_rg rX (B9_R x ++ [(23, y_lp x); (10, match r with None => 0 | Some ei => y_lp x + Z.of_nat ei end)]).

(** ** J2 (0x88428): the '=' is at ei and holds the NUL, trim #1 has answered a0 = kp, the key at kp in buf, the
    rest of the line at eq + 1. s8 = eq = lp + ei. The key and its NUL end at or below the '=' (head comment). *)
Definition INV_J2 (n : nat) (x : b9x) (ei : nat) (kp : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9_core n x lyc Sc Wc rX memc mdc /\
  strchr (b9_line x) EQ = Some ei /\
  b9_inbuf (rdW Wc memc) x kp (b9_key x ei) /\
  kp + Z.of_nat (length (b9_key x ei)) <= y_lp x + Z.of_nat ei /\
  b9_inbuf (rdW Wc memc) x (y_lp x + Z.of_nat ei + 1) (skipn (S ei) (b9_line x)) /\
  pf_rg rX (B9_R x ++ [(24, y_lp x + Z.of_nat ei); (10, kp)]).

(** ** J3 (0x88438): trim #2 has answered a0 = vp0, the trimmed value at vp0 in buf. s7 = kp, s8 = eq. The key
    ends strictly below vp0 (vp0 >= eq + 1 > kp + |key|). *)
Definition INV_J3 (n : nat) (x : b9x) (ei : nat) (kp vp0 : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9_core n x lyc Sc Wc rX memc mdc /\
  strchr (b9_line x) EQ = Some ei /\
  b9_inbuf (rdW Wc memc) x kp (b9_key x ei) /\
  kp + Z.of_nat (length (b9_key x ei)) < vp0 /\
  b9_inbuf (rdW Wc memc) x vp0 (b9_v0 x ei) /\
  pf_rg rX (B9_R x ++ [(24, y_lp x + Z.of_nat ei); (23, kp); (10, vp0)]).

(** ** J4 (0x88440): strlen has answered a0 = |v0|; s3 = vp0, s7 = kp, s8 = eq (A9's K3). *)
Definition INV_J4 (n : nat) (x : b9x) (ei : nat) (kp vp0 : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9_core n x lyc Sc Wc rX memc mdc /\
  strchr (b9_line x) EQ = Some ei /\
  b9_inbuf (rdW Wc memc) x kp (b9_key x ei) /\
  kp + Z.of_nat (length (b9_key x ei)) < vp0 /\
  b9_inbuf (rdW Wc memc) x vp0 (b9_v0 x ei) /\
  pf_rg rX (B9_R x ++ [(24, y_lp x + Z.of_nat ei); (23, kp); (19, vp0);
                       (10, Z.of_nat (length (b9_v0 x ei)))]).

(** ** K5 (0x88570): the key / value pair is built (the unquote is done): s7 = kp, s3 = vp = the value's pointer,
    a5 = cur (loaded from slot 0xc0 at 0x88454 or 0x884c4). *)
Definition INV_K5 (n : nat) (x : b9x) (ei : nat) (kp vp : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9_core n x lyc Sc Wc rX memc mdc /\
  strchr (b9_line x) EQ = Some ei /\
  b9_inbuf (rdW Wc memc) x kp (b9_key x ei) /\
  b9_inbuf (rdW Wc memc) x vp (b9_val x ei) /\
  pf_rg rX (B9_R x ++ [(23, kp); (19, vp); (15, b9_cp x)]).

(** ** JC k (J6 .. J9, k = 0 .. 3): cur = Some gi, val in slot 0x70, the k-th strcasecmp of the key has answered
    in a0 (0 exactly when the key is the k-th literal under case folding), the earlier ones were not 0. s7 = kp. *)
Definition INV_JC (n : nat) (x : b9x) (ei : nat) (kp vp : Z) (gi k : nat) (lyc : alayout) (Sc : astate)
  (Wc : world SEGS) (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9_core n x lyc Sc Wc rX memc mdc /\
  y_cur x = Some gi /\
  strchr (b9_line x) EQ = Some ei /\
  b9_inbuf (rdW Wc memc) x kp (b9_key x ei) /\
  b9_inbuf (rdW Wc memc) x vp (b9_val x ei) /\
  pf_sl (rdW Wc memc) (pf_s1 (y_v x)) [(0x70, vp)] /\
  (forall j, (j < k)%nat -> strcasecmp (b9_key x ei) (nth j b9_lits []) <> 0) /\
  (getr rX 10 = w64 0 <-> strcasecmp (b9_key x ei) (nth k b9_lits []) = 0) /\
  pf_rg rX (B9_R x ++ [(23, kp)]).

(** ** "from this cut the walk reaches B9's goal" (chain_words_d.v cw_from) *)
Definition b9_from (pc : Z)
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (x : b9x) : Prop :=
  forall lyc Sc Wc rX memc mdc, P lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + pc) rX memc mdc) (b9_goal x).
Definition from_J1 (n : nat) : Prop := forall x r, b9_from B9_J1 (INV_J1 n x r) x.
Definition from_J2 (n : nat) : Prop := forall x ei kp, b9_from B9_J2 (INV_J2 n x ei kp) x.
Definition from_J3 (n : nat) : Prop := forall x ei kp vp0, b9_from B9_J3 (INV_J3 n x ei kp vp0) x.
Definition from_J4 (n : nat) : Prop := forall x ei kp vp0, b9_from B9_J4 (INV_J4 n x ei kp vp0) x.
Definition from_K5 (n : nat) : Prop := forall x ei kp vp, b9_from B9_K5 (INV_K5 n x ei kp vp) x.
Definition from_JC (n k : nat) : Prop :=
  forall x ei kp vp gi, b9_from (B9_JC k) (INV_JC n x ei kp vp gi k) x.

(** ** The ten stretch statements (exits at the segment's FP state fx; the composition instantiates pf_pieces.v's
    HA_ forms at fx) *)
Definition SB9_1 : Prop := forall n : nat, from_J1 n -> H_KEY B n.
Definition SB9_2 : Prop := forall n : nat, H_REF3 B n -> from_J2 n -> from_J1 n.
Definition SB9_3 : Prop := forall n : nat, from_J3 n -> from_J2 n.
Definition SB9_4 : Prop := forall n : nat, from_J4 n -> from_J3 n.
Definition SB9_5 : Prop := forall n : nat, from_K5 n -> from_J4 n.
Definition SB9_6 : Prop := forall n : nat, H_HREF B n -> from_JC n 0 -> from_K5 n.
Definition SB9_7 : Prop := forall n : nat, H_ROLE B n -> from_JC n 1 -> from_JC n 0.
Definition SB9_8 : Prop := forall n : nat, H_MODEL B n -> from_JC n 2 -> from_JC n 1.
Definition SB9_9 : Prop := forall n : nat, H_IGN B n -> from_JC n 3 -> from_JC n 2.
Definition SB9_10 : Prop := forall n : nat, H_KREF B n -> from_JC n 3.

(** ** The packing of H_KEY's binders: b9_core and the line string from INV_KEY *)
Lemma b9_of_KEY : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_KEY B n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  let x := mkB9X v pos cf cur nm o ln d lp in
  b9_core n x lyc Sc Wc rX memc mdc /\
  b9_inbuf (rdW Wc memc) x lp (b9_line x) /\
  pf_rg rX (B9_R x ++ [(23, lp)]).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp
  (HB & HM & HS & HL & HSTR & HINB & HD0 & HDL & HRG).
cbn zeta. split; [|split; [split; [exact HSTR | exact HINB] | unfold B9_R; rewrite <- app_assoc; exact HRG]].
split; [exact HB|]. split; [exact HM|]. split; [exact HS|]. split; [exact HL|].
split; [exact HD0 | exact HDL].
Qed.

(* H_KEY's post is b9_goal of the packed context *)
Lemma b9_goal_KEY : forall v pos cf cur nm o ln d lp,
  b9_goal (mkB9X v pos cf cur nm o ln d lp) =
  pf_postm B v (r_key cf cur nm (ln + 1) (pf_tline (p_s v) o)) o ln.
Proof. reflexivity. Qed.

End e.
End f.
End d.
