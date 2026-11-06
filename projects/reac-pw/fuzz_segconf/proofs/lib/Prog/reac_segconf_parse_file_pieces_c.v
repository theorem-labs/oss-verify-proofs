From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import refuse_c reac_segconf_parse_file_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_parse_file(c, text, label) (reac_segconf.c:120-296) cut into its 9 pieces and the line-loop
    invariant, plain build (image 3776ca44d75c; the unstripped twin 8dec0b814e6f):
    at 0x14cbc, 2204 bytes, 551 instructions, frame 0x3d0, saves ra and s0-s11 at sp + 0x3c8 ..
    0x368. Family F3. Statement text only: no piece is proved here, and
    pieces_give_contract (the whole function from its pieces) is stated, not proved. The whole-function contract is
    lib/Prog/reac_segconf_parse_file_c.v (REAC_SEGCONF_PARSE_FILE, PARSE_FILE_STACK, reader_pre,
    reac_segconf_parse_file_pre); H_ENTRY is it. The build-independent part (the saved-register record pf_sv, the
    line account pf_lctx / pf_line / pf_next / pf_tline, the counters' room pf_cnt, the provenance edit pf_prov_*, the
    role step pf_role_step, and the lemmas O1, O2, L_* as Props) is lib/Prog/pf_pieces_spec.v.

    The shape. One Prop per cut, H_<CUT>: for every machine at the cut's pc with the cut's
    facts, evt reaches the function's post computed from the cut's state (pf_ret / pf_fin: seg_env.ret_post_fp with
    the saved ra, the restored sp = sp + 0x3d0, the entry s0-s11 from the frame, a0 = c->n of the final state, W =
    the whole function's write list, c holding the final state). One Prop per piece, S_<PIECE>: its exit cuts imply
    its entry cut (a piece with several entries is the conjunction, one implication per entry). The loop's cuts and
    every cut inside a line take n, a bound on the length of the text left at the line's start: TAIL n leaves a rest
    shorter than n and goes to HEAD (pred n), so the pieces give H_HEAD n for every n by induction on n, then the
    contract by S_P1 (pieces_give_contract).

    The state at the cuts is the spine's (lib/Spec/SegModel.v): c holds rc (seg_spec.rconf_at), cur is option nat
    (None = NULL, Some i = &c->seg[i] = c + 356 i, pf_cur_ptr), cur_name (sp + 0x358, char[16]) holds the C string nm,
    the text is the C string s at t, the line starts at offset o (p = t + o), lineno = the number of lines consumed
    (pf_lctx: lines s = d ++ lines (skipn o s), ln = length d). The loop head's post is the function's post from
    r_lines (rc, cur, nm) ln (lines (skipn o s)); a cut inside a line has the post from r_lines (the line's remaining
    step) (ln + 1) (lines rest'), where the step is the spine's: r_line (LONG), r_header (HDR), r_key (KEY, ROLE,
    MODEL, IGN), pf_role_step (INTENT), refuse (the refusal sites), pf_prov_fin (the provenance sites), the cur_name
    copy (CNAME).

    The cuts (pc, piece that owns the code, who enters it):
    - ENTRY 0x14cbc (P1): the contract. DONE 0x1550c (P1): from P1 (empty text, `beqz` 0x14d68) and P2's tail.
    - HEAD 0x14dc4 (P2): from P1 and the tail's `bnez` 0x154b8. TAIL 0x154b4 (P2): from P2 (empty line, `beqz`
      0x14eb0), P3 (`j` 0x14e44), P4 (`j` 0x14f60), P5 (`j` 0x14f80), P9 (0x152b4, falls in after 0x154b0).
    - LONG 0x14e08 (P3): from P2. OUTS 0x14e40 (P3's refuse site): from P5 (0x15070). S9 0x14f7c (P5's site): from P7
      (0x153a8).
    - HDR 0x14ebc (P4), KEY 0x14ee0 (P5): from P2.
    - ROLE 0x15074 (P6), MODEL 0x150bc (P7), IGN 0x15154 (P8): from P5's strcasecmp tests (0x15000, 0x15014,
      0x15028). INTENT 0x151e8 (P6): P6's inner cut (O1).
    - KNOCK 0x15298 (P9): from P5 (0x1503c). KREF 0x152a0 (P9): from P6 (0x15294) and P8 (0x151d4). NOKEY 0x152b0
      (P9): from P5 (0x15058). PROV 0x154a8 (P9): from P6 (falls in at 0x154a4) and P8 (0x15444). PROVM 0x154ac (P9):
      from P7 (0x15300). CNAME 0x154b0 (P9): from P4 (0x15508).

    The pieces (counts: instructions / conditional branches / calls), the callee
    contracts each walk takes as premises, its call sites and where each argument comes from. Callee contracts:
    snprintf 0x19078 (snprintf_c.v: printf_env, the
    format in .rodata, the %s argument's slack); strchr 0x1eadc and strncasecmp 0x1ecc0 (commit
    d8911fcbf9ff); strlen 0x1ec30, memcpy 0x1e52c, memset 0x1e930, bcmp 0x1e42c (this directory's
    strlen_c.v, memcpy_c.v, memset_c.v, bcmp_c.v); strspn 0x1efcc and strcmp 0x1ebf8 (commit
    06702a5f1f22, strspn_c.v, strcmp_c.v); strcasecmp 0x1ea28; trim
    0x15660 and refuse 0x15558 (trim_c.v, refuse_c.v, family F2); reac_box_catalogue_by_token 0x15e04 and
    reac_box_catalogue 0x15dec (reac_box_catalogue_by_token_c.v, reac_box_catalogue_c.v). Every string argument in
    buf (sp + 0x158 .. 0x357), cur_name, known or low lies in the frame, above the callee's sp and apart from c; its
    slack lies in the frame bytes after it; every refuse call has rc_refused rc + 1 < 2^32 by pf_cnt.
    - P1 (entry, setup, return) 14cbc-14dc0, 1550c-15554; 85 / 3 / 1. ENTRY -> HEAD (text not empty) or DONE; DONE ->
      the return. 0x14d3c snprintf(c + 0x4080, 96, "%s" 0x104e0, label or "reac-pw.conf" 0x10463) (the label's
      placement: reac_segconf_parse_file_pre); c->gen++ (0x14d48); the spill slots (pf_spill) and cur_name = 16 zero
      bytes (0x14d60 / 0x14d64, nm = []); the head with o = 0, ln = 0, d = [], cur = None and rc = the spine's c1 of
      r_parse_file; n = length s.
    - P2 (line driver) 14dc4-14e04, 14e48-14eb8, 154b4-154bc; 49 / 13 / 4. HEAD -> LONG (len >= 512), HDR, KEY or
      TAIL (empty trimmed line); TAIL -> HEAD (pred n) or DONE. 0x14dd0 strchr(p, '\n'); 0x14df0 strlen(p) when nl =
      NULL (L_break_nl, L_next: s2 = nl + 1 or p + len); 0x14e58 memcpy(buf = sp + 0x158, at = p, len), len < 512
      (L_line_bytes, L_cstr_skipn); buf[len] = 0 (0x14e64); the strip_comment loop at 0x14e68 (invariant:
      k <= len, s5 = buf + k, a0 = -k, no comment start before k; L_strip); 0x14ea4 trim(buf) (trim_c.v; L_trim);
      lineno++ at 0x14e00 (lineno <= 65535 by pf_lctx); the tail's `lbu *p` / `bnez` (L_lines_step: lines rest = line
      :: lines rest').
    - P3 (long line) 14e08-14e44; 16 / 1 / 2. LONG -> TAIL; OUTS -> TAIL. 0x14e10 strspn(at, " \t\r" from sp + 0x40)
      on the rest of the text (O2_strspn_rest); at[lead] == '[' clears s6 (0x14e2c); 0x14e40 refuse(c, lineno, F_long
      0x10628 from sp + 0x38, 511) from LONG, or (c, lineno, F_outside, key) from OUTS.
    - P4 (header and seg_get) 14ebc-14edc, 14f44-14f60, 14f8c-14fc8, 15104-15150, 153ac-153c0, 153cc-1541c,
      15448-15488, 154c0-15508; 116 / 12 / 12. HDR -> TAIL (every header refusal, then `mv s6, zero` 0x14f5c) or
      CNAME. 0x14ec4 strchr(line, ']'); 0x14f58 refuse(c, lineno, F_notclosed 0x10397 / F_after 0x10657 (a3 = line)
      / F_unknown 0x108f7 (a3 = body)); `*close = 0` (0x14f8c); 0x14f94 trim(line + 1); 0x14fac strncasecmp(body,
      "segment" 0x10313, 7) and body[7] in {' ', '\t'} (s11 / s10); 0x15114 trim(body + 7); 0x15128 strlen(name);
      0x1514c refuse(c, lineno, F_toolong 0x102a9, name, 15) or (F_bound 0x10817, name, 32); 0x153bc refuse(c,
      lineno, F_noname 0x10441); the seg_get search loop at 0x153e0 (invariant: i <= n, s6 = c + 356 i, s8 = n - i,
      the names j < i differ from name) with 0x153e8 strcmp(c->seg[i].name, name); c->overflow++ (0x1540c) when n =
      32 (s10 = 32); 0x1546c memset(c + 356 n, 0, 356) and 0x15484 snprintf(c + 356 n, 16, "%s", name), n++
      (0x15458); seen_gen test (0x154c0) and 0x154e4 refuse(c, lineno, F_twice 0x105aa, name); seen_gen = gen
      (0x154f0); then CNAME.
    - P5 (key line) 14ee0-14f40, 14f64-14f88, 14fcc-15070; 77 / 11 / 9. KEY -> OUTS (cur = NULL), TAIL (no '='),
      ROLE, MODEL, IGN, KNOCK or NOKEY; S9 -> TAIL. 0x14ee8 strchr(line, '='); `*eq = 0` (0x14ef4); 0x14efc
      trim(line) -> key (s8); 0x14f08 trim(eq + 1) -> v; 0x14f10 strlen(v) and the inlined unquote (v[n-1] = 0,
      v++) -> val (s7); s9 borrowed for eq and set back to 512 on every path (0x14f28, 0x14f84, 0x14fd4); 0x14f78
      refuse(c, lineno, F_neither 0x10884, line); 0x14ffc / 0x15010 / 0x15024 / 0x15038 strcasecmp(key, "role"
      0x10298 / "model" 0x10811 / "ignore" 0x1054f / "knock" 0x102a3); the no-key branch sets a0-a4 (F_nokey 0x10680,
      cur_name, key).
    - P6 (role) 15074-150b8, 151d8-15294, 15304-15308, 153c4-153c8, 15420-15424, 1548c-154a4; 79 / 8 / 3. ROLE ->
      INTENT; INTENT -> KREF (F_badrole) or PROV (role = r, role_set = 1 at 0x15490 / 0x15498). The fold loop at
      0x15084 into low = sp + 0x50 (invariant: li < 63, low[0 .. li) = the fold of val[0 .. li); L_low with cap 64),
      low[k] = 0 (0x151e4); 0x151f4 / 0x1520c / 0x15224 bcmp(low, "auto" 0x1030e / "master" 0x10548 / "slave"
      0x1075c, 5 / 7 / 6) (bcmp_c.v with ls = LB, the 64 bytes INTENT names; O1_bcmp_lit); the tap / box word
      compares at 0x15258 / 0x15288 against the slots sp + 0x18 / 0x10 (O1_word_lit).
    - P7 (model) 150bc-15100, 152b8-15300, 1530c-153a8; 77 / 8 / 5. MODEL -> PROVM (by_token hit: model =
      snprintf_s 24 F_s [AS low], model_set = 1) or S9 (the refusal). The fold loop at 0x150cc into low = sp + 0x140
      (L_low with cap 24); 0x152c8 reac_box_catalogue_by_token(low); 0x152e8 snprintf(cur + 0x24, 24, "%s", low);
      0x15314 reac_box_catalogue(&ntok = sp + 0x48); the join loop at 0x15330 (invariant: ti < 11, s5 = ti + 1,
      s8 = tab + 296 ti, s9 = kn = length of the join so far <= 77; L_known) with 0x15364 snprintf(known + kn,
      240 - kn, "%s%s" 0x1031b, ti ? "|" 0x105f0 : "" 0x1038e, tab[ti].token), 11 times (known = sp + 0x50: the same
      bytes as role's low, their lifetimes apart); 0x153a4 refuse(c, lineno, F_badmodel 0x104e3, cur_name, val, known).
    - P8 (ignore) 15154-151d4, 15428-15444; 41 / 8 / 4. IGN -> KREF (F_badignore) or PROV (ignore = b, ignore_set =
      1 at 0x1542c / 0x15434). 0x15160 / 0x15178 / 0x151a0 / 0x151b4 strcasecmp(val, "yes" 0x1042f / "true" 0x10517 /
      "no" 0x10711 / "false" 0x1029d); "1" / "0" as val[0] and val[1] (SegModel.parse_bool's strcmp).
    - P9 (shared sites) 15298-152b4, 154a8-154b0; 11 / 0 / 2. KNOCK, KREF, NOKEY -> TAIL: 0x152b0 refuse(c, lineno,
      fmt, cur_name = sp + 0x358, val or key); PROV, PROVM, CNAME -> TAIL: 0x154b0 snprintf(field, 96, "%s",
      c->reading from sp + 0x28) or snprintf(cur_name, 16, "%s", name).

    Notes on the statement (each with the reason):
    - The counters. reader_pre's first text bounded c->refused only by 2^31, and refuse_pre asked for the same at
      every call, while one file can make 65535 refusals: fixed at
      commit 3e75bf1c5aa6 (the u32 bounds: reader_pre + 2^17, refuse_pre + 1). pf_cnt carries the
      room per byte left.
    - That cur_name holds seg[i].name is not a cut fact: the spine carries cur_name (nm) beside cur,
      as the C does, and no piece reads the relation.
    - DONE asks for the slot sp + 0x30 only: on the empty-text path the slots 8, 0x10, 0x18, 0x38 and 0x40 are not set
      yet (0x14d9c .. 0x14dbc come after the entry test 0x14d68).
    - The line start is not stated as "o = 0 or s[o - 1] = '\n'": pf_lctx's lines s = d ++ lines (skipn o s) carries
      it, and ln <= o gives the bound.
    - O2's bridge from spn_len (strspn_c.v) to SegModel.strspn_blank is a comment, not a
      Prop: this file does not import strspn_c.v, which defines spn_len. *)

(** ** This build's pcs and frame offsets *)
Definition PF_PC_HEAD : Z := 0x14dc4.
Definition PF_PC_TAIL : Z := 0x154b4.
Definition PF_PC_DONE : Z := 0x1550c.
Definition PF_PC_LONG : Z := 0x14e08.
Definition PF_PC_HDR : Z := 0x14ebc.
Definition PF_PC_KEY : Z := 0x14ee0.
Definition PF_PC_OUTS : Z := 0x14e40.
Definition PF_PC_S9 : Z := 0x14f7c.
Definition PF_PC_ROLE : Z := 0x15074.
Definition PF_PC_INTENT : Z := 0x151e8.
Definition PF_PC_MODEL : Z := 0x150bc.
Definition PF_PC_IGN : Z := 0x15154.
Definition PF_PC_KNOCK : Z := 0x15298.
Definition PF_PC_KREF : Z := 0x152a0.
Definition PF_PC_NOKEY : Z := 0x152b0.
Definition PF_PC_PROV : Z := 0x154a8.
Definition PF_PC_PROVM : Z := 0x154ac.
Definition PF_PC_CNAME : Z := 0x154b0.
Definition PF_SAVE : Z := 0x368.
Definition PF_NAMEBUF : Z := 0x358.
Definition PF_BUF : Z := 0x158.
Definition PF_LOW : Z := 0x50.
Definition PF_NSLOT : Z := 0x30.

(** ** What every cut after the prologue holds
    sp below is the cut's sp (bv_unsigned of the register): the entry sp is sp + PARSE_FILE_FRAME. The reader block c
    and its placement (reader_pre), printf's machine, the box-model table, the stack region [lo, entry sp) with the
    function's depth, mem_inv, and the 13 saved registers v. *)
Definition pf_env (m : word -> option byte) (fc : bv 32) (sp lo c : Z) (v : pf_sv) : Prop :=
  c <> 0 /\ c mod 16 = 0 /\ apart c SEG_C_SIZE lo (sp + PARSE_FILE_FRAME) /\ blk_noimg rsegs c SEG_C_SIZE /\
  printf_env m fc lo (sp + PARSE_FILE_FRAME) /\ cat_img rsegs m (sa_catalogue SA) /\
  stack_ok rsegs m lo (sp + PARSE_FILE_FRAME) PARSE_FILE_STACK /\ mem_inv rsegs m /\
  saved_at rsegs m (sp + PF_SAVE) (sv_list v).
(** The text: the C string s at t (never written: every edit is in buf), at most 65535 bytes, apart from the stack
    region and from c (reader_pre). *)
Definition pf_text (m : word -> option byte) (sp lo c t : Z) (s : list Z) : Prop :=
  t <> 0 /\ cstr_at rsegs m t s /\ (length s <= 65535)%nat /\
  apart t (Z.of_nat (length s) + 8) lo (sp + PARSE_FILE_FRAME) /\ apart t (cstr_span t s) c (c + SEG_C_SIZE).
(** The spill slots P1 fills before the loop and no piece changes (plain): sp + 8 &c->overflow,
    0x10 the "box\0" word, 0x18 the "tap\0" word, 0x20 &c->gen, 0x28 &c->reading, 0x30 &c->n, 0x38 F_long,
    0x40 " \t\r". *)
Definition pf_spill (m : word -> option byte) (sp c : Z) : Prop :=
  saved_at rsegs m (sp + 8)
    [Z_to_bv 64 (c + RC_OVERFLOW); Z_to_bv 64 PF_BOX_WORD; Z_to_bv 64 PF_TAP_WORD; Z_to_bv 64 (c + RC_GEN);
     Z_to_bv 64 (c + RC_READING); Z_to_bv 64 (c + RC_N); Z_to_bv 64 PF_STR_LONG; Z_to_bv 64 PF_STR_BLANKS].
(** The loop's registers (plain): s0 = c, s2 = p, s3 = lineno, the constants s1 = '#',
    s4 = ';', s10 = ' ' (also the bound 32 of seg_get), s11 = '\t'; s9 = 512 is stated beside it (P7's join loop
    borrows s9 and S9 puts it back), and s6 = cur. *)
Definition pf_regs (s0 s1 s2 s3 s4 s10 s11 : word) (c p ln : Z) : Prop :=
  s0 = Z_to_bv 64 c /\ s2 = Z_to_bv 64 p /\ s3 = Z_to_bv 64 ln /\
  s1 = Z_to_bv 64 HASH /\ s4 = Z_to_bv 64 SEMI /\ s10 = Z_to_bv 64 SP /\ s11 = Z_to_bv 64 TAB.
(** The cur_name buffer char[16] at a holds the C string nm (R:127; seg_spec.cstr_enc: the bytes after its NUL are
    not fixed). *)
Definition pf_nm_at (m : word -> option byte) (a : Z) (nm : list Z) : Prop :=
  exists f, bytes_at rsegs m a f /\ cstr_enc 16 nm f.
(** The reader's state at a cut: c holds rc, cur is an entry of it, the cur_name buffer holds nm, and the counters
    have room for the k text bytes left. *)
Definition pf_state (m : word -> option byte) (sp c : Z) (rc : rconf) (cur : option nat) (nm : list Z) (k : nat)
    : Prop :=
  rconf_at rsegs m c rc /\ pf_cur_ok rc cur /\ pf_nm_at m (sp + PF_NAMEBUF) nm /\ pf_cnt rc k.
(** At the head and the tail: a line starts at o (p = t + o), ln = length d lines have been read, and the rest of
    the text is the C string skipn o s at p (with the text's slack: L_cstr_skipn). *)
Definition pf_hctx (m : word -> option byte) (fc : bv 32) (sp lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (o : nat)
    (ln : Z) (d : list (list Z)) : Prop :=
  pf_env m fc sp lo c v /\ pf_text m sp lo c t s /\ pf_spill m sp c /\ pf_lctx s o ln d /\
  cstr_at rsegs m (t + Z.of_nat o) (skipn o s).
(** Inside a line that starts at o: lineno is ln + 1, and d counts this line too (the account at the next line's
    offset pf_next s o, where p already points). *)
Definition pf_ctx (m : word -> option byte) (fc : bv 32) (sp lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (o : nat)
    (ln : Z) (d : list (list Z)) (n : nat) : Prop :=
  pf_env m fc sp lo c v /\ pf_text m sp lo c t s /\ pf_spill m sp c /\
  (o < length s)%nat /\ (length (skipn o s) <= n)%nat /\ pf_lctx s (pf_next s o) (ln + 1) d.
(** A split key line (R:215-223): the '=' at ei of the trimmed line, key = trim of the bytes before it at kp, val =
    unquote of the trim of the bytes after it at vp, both C strings in buf. *)
Definition pf_kv (m : word -> option byte) (sp : Z) (line : list Z) (kp vp : Z) (key val : list Z) : Prop :=
  (exists ei : nat, strchr line EQ = Some ei /\ key = r_trim (firstn ei line) /\
                    val = r_unquote (r_trim (skipn (S ei) line))) /\
  cstr_at rsegs m kp key /\ pf_inb (sp + PF_BUF) kp key /\ cstr_at rsegs m vp val /\ pf_inb (sp + PF_BUF) vp val.

(** ** The function's post from a cut
    seg_env.ret_post_fp with the saved ra, the restored sp (the cut's sp + PARSE_FILE_FRAME), the entry s0-s11, a0 =
    c->n of the final state, W = the whole function's write list (its frame and its callees' frames below the entry
    sp, and RC_PARSE_W c), and c holding the final state rcf. *)
Definition pf_ret (v : pf_sv) (sp gp tp : word) (F : bvmap 5 word) (m : word -> option byte) (lo c : Z) (rcf : rconf)
    : machine_state -> Prop :=
  ret_post_fp (sv_ra v) (Z_to_bv 64 (bv_unsigned sp + PARSE_FILE_FRAME)) gp tp
    (sv_s0 v) (sv_s1 v) (sv_s2 v) (sv_s3 v) (sv_s4 v) (sv_s5 v) (sv_s6 v) (sv_s7 v) (sv_s8 v) (sv_s9 v) (sv_s10 v)
    (sv_s11 v) F
    (Z.of_nat (length (rc_seg rcf)))
    m
    ((bv_unsigned sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, bv_unsigned sp + PARSE_FILE_FRAME) :: RC_PARSE_W c)
    lo
    (fun m' => rconf_at rsegs m' c rcf).
(** The same from a state (rc, cur, cur_name) of the loop: its rconf. *)
Definition pf_fin (v : pf_sv) (sp gp tp : word) (F : bvmap 5 word) (m : word -> option byte) (lo c : Z)
    (st : rconf * option nat * list Z) : machine_state -> Prop :=
  pf_ret v sp gp tp F m lo c (fst (fst st)).

(** ** The cuts *)
(** ENTRY (the function's pc): exactly reac_segconf_parse_file_contract (premise and post). *)
Definition H_ENTRY : Prop := reac_segconf_parse_file_contract.

(** DONE (0x1550c, piece P1): the loop has ended (the tail's `*p == 0`, or an empty text at the entry test): `lw` c->n
    through the frame slot sp + 0x30 (it holds &c->n = c + 0x2c80 on both paths into DONE; the other spill slots may
    not be set yet on the empty-text path), the restores, `ret`. Post: the function's post from c's state rc. *)
Definition H_DONE : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c : Z) (rc : rconf),
    pf_env m fc (bv_unsigned sp) lo c v ->
    rconf_at rsegs m c rc ->
    bytes_at rsegs m (bv_unsigned sp + PF_NSLOT) (le8 (Z_to_bv 64 (c + RC_N))) ->
    evt rsegs
      (pf_ret v sp gp tp F m lo c rc)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_DONE) fc None m (seg_rom rsegs)).

(** HEAD (0x14dc4, piece P2): the line-loop head and the interface of the walk. A line starts at o
    (o < length s: the entry test and the tail's `bnez *p` saw a non-zero byte), p = t + o, ln = lineno = the
    number d of lines consumed; c holds rc, cur and the cur_name buffer nm are the spine's after those lines. The post
    is the function's post from r_lines (rc, cur, nm) ln (lines rest), rest = skipn o s. n bounds length rest (the
    measure: every pass takes at least one byte). The cut holds for every state (rc, cur, nm); the loop meets it
    with pf_spine rc0 lab d (the spine's state after the d lines consumed: L_r_lines_app, L_parse_start). *)
Definition H_HEAD (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
    pf_hctx m fc (bv_unsigned sp) lo v c t s o ln d ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    (o < length s)%nat ->
    (length (skipn o s) <= n)%nat ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat o) ln ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (rc, cur, nm) ln (lines (skipn o s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_HEAD) fc None m (seg_rom rsegs)).

(** TAIL (0x154b4, piece P2): a line has been read. o is the next line's offset (p = t + o, past the '\n' or at the
    text's end), ln and d count the lines read, c holds rc and (cur, nm) are the state after the line. The rest is
    shorter than n: the head it loops to is H_HEAD (pred n). *)
Definition H_TAIL (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
    pf_hctx m fc (bv_unsigned sp) lo v c t s o ln d ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    (length (skipn o s) < n)%nat ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat o) ln ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (rc, cur, nm) ln (lines (skipn o s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_TAIL) fc None m (seg_rom rsegs)).

(** S9 (0x14f7c, piece P5's shared site, entered from P7's model refusal `j 0x14f7c` at 0x153a8): as TAIL, but s9 holds
    the join loop's kn; `li s9, 512` puts the constant back, then `j` TAIL. *)
Definition H_S9 (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
    pf_hctx m fc (bv_unsigned sp) lo v c t s o ln d ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    (length (skipn o s) < n)%nat ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat o) ln ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (rc, cur, nm) ln (lines (skipn o s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_S9) fc None m (seg_rom rsegs)).

(** LONG (0x14e08, piece P3's entry from P2's `bltu len, 512` not taken): at = t + o in s7, len = length of the line in
    s8, len >= 512. The step is r_line's long branch.
    The mid-line cuts below share pf_ctx: the line starts at o (o < length s, length (skipn o s) <= n), lineno
    has been incremented (s3 = ln + 1, d = the lines read with this one), p = t + pf_next s o already points at the
    next line. Their post is the function's post from r_lines (the line's step) (ln + 1) (lines rest'), rest' =
    skipn (pf_next s o) s. *)
Definition H_LONG (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    s7 = Z_to_bv 64 (t + Z.of_nat o) ->
    s8 = Z_to_bv 64 (Z.of_nat (length (pf_line s o))) ->
    (512 <= length (pf_line s o))%nat ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_line rc cur nm (ln + 1) (pf_line s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_LONG) fc None m (seg_rom rsegs)).

(** HDR (0x14ebc, piece P4's entry): the line (len < 512) was copied into buf, its comment cut and trimmed; s7 = lp points
    at the trimmed line pf_tline s o in buf, whose first byte is '['. The step is r_header. *)
Definition H_HDR (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (lp : Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    (length (pf_line s o) < 512)%nat ->
    s7 = Z_to_bv 64 lp ->
    cstr_at rsegs m lp (pf_tline s o) ->
    pf_inb (bv_unsigned sp + PF_BUF) lp (pf_tline s o) ->
    hd0 (pf_tline s o) = LBR ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_header rc nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_HDR) fc None m (seg_rom rsegs)).

(** KEY (0x14ee0, piece P5's entry): as HDR, but the trimmed line is neither empty nor a header. The step is r_key. *)
Definition H_KEY (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (lp : Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    (length (pf_line s o) < 512)%nat ->
    s7 = Z_to_bv 64 lp ->
    cstr_at rsegs m lp (pf_tline s o) ->
    pf_inb (bv_unsigned sp + PF_BUF) lp (pf_tline s o) ->
    hd0 (pf_tline s o) <> 0 ->
    hd0 (pf_tline s o) <> LBR ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_key rc cur nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_KEY) fc None m (seg_rom rsegs)).

(** OUTS (0x14e40, piece P3's shared refuse site, entered from P5 by `j 0x14e40` at 0x15070): a key line outside any
    section (cur = NULL): refuse(c, lineno, F_outside, key) with the arguments in a0-a3, then `j` TAIL. *)
Definition H_OUTS (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (kp : Z) (key : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc None nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c None) ->
    a0 = Z_to_bv 64 c ->
    a1 = Z_to_bv 64 (ln + 1) ->
    a2 = Z_to_bv 64 PF_STR_OUTSIDE ->
    a3 = Z_to_bv 64 kp ->
    cstr_at rsegs m kp key ->
    pf_inb (bv_unsigned sp + PF_BUF) kp key ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) F_outside [AS key], None, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_OUTS) fc None m (seg_rom rsegs)).

(** ROLE (0x15074, piece P6's entry): key is "role".
    The key line has been split (pf_kv: the '=' at ei, key = s8, val = s7, both C strings in buf), cur = Some gi.
    The step is r_key in the branch the strcasecmp results select. *)
Definition H_ROLE (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (kp vp : Z) (key val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)) ->
    pf_kv m (bv_unsigned sp) (pf_tline s o) kp vp key val ->
    s8 = Z_to_bv 64 kp ->
    s7 = Z_to_bv 64 vp ->
    strcasecmp key S_role = 0 ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_ROLE) fc None m (seg_rom rsegs)).

(** MODEL (0x150bc, piece P7's entry): key is "model".
    The key line has been split (pf_kv: the '=' at ei, key = s8, val = s7, both C strings in buf), cur = Some gi.
    The step is r_key in the branch the strcasecmp results select. *)
Definition H_MODEL (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (kp vp : Z) (key val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)) ->
    pf_kv m (bv_unsigned sp) (pf_tline s o) kp vp key val ->
    s8 = Z_to_bv 64 kp ->
    s7 = Z_to_bv 64 vp ->
    strcasecmp key S_role <> 0 ->
    strcasecmp key S_model = 0 ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_MODEL) fc None m (seg_rom rsegs)).

(** IGN (0x15154, piece P8's entry): key is "ignore".
    The key line has been split (pf_kv: the '=' at ei, key = s8, val = s7, both C strings in buf), cur = Some gi.
    The step is r_key in the branch the strcasecmp results select. *)
Definition H_IGN (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (kp vp : Z) (key val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)) ->
    pf_kv m (bv_unsigned sp) (pf_tline s o) kp vp key val ->
    s8 = Z_to_bv 64 kp ->
    s7 = Z_to_bv 64 vp ->
    strcasecmp key S_role <> 0 ->
    strcasecmp key S_model <> 0 ->
    strcasecmp key S_ignore = 0 ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_IGN) fc None m (seg_rom rsegs)).

(** INTENT (0x151e8, piece P6's inner cut: the start of the inlined reac_role_intent_parse, after the fold loop and
    low[k] = 0). O1: the 64 bytes LB of low (sp + 0x50) are named, with their prefix r_low val 0 64 and its NUL; the
    bytes after it are what earlier lines left, and bcmp reads up to 7 of them. The step is stated against
    SegModel.role_intent_parse (pf_role_step).
    Plain: a0 = low already (set at 0x151dc, before the cut; the first bcmp at 0x151f4 reads it). *)
Definition H_INTENT (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (vp : Z) (val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)) ->
    a0 = Z_to_bv 64 (bv_unsigned sp + PF_LOW) ->
    s7 = Z_to_bv 64 vp ->
    cstr_at rsegs m vp val ->
    pf_inb (bv_unsigned sp + PF_BUF) vp val ->
    (exists LB : list byte, length LB = 64%nat /\ bytes_at rsegs m (bv_unsigned sp + PF_LOW) LB /\
       firstn (S (length (r_low val 0 64))) (zs LB) = r_low val 0 64 ++ [0]) ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (pf_role_step rc gi nm (ln + 1) val) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_INTENT) fc None m (seg_rom rsegs)).

(** KNOCK (0x15298, piece P9, entered from P5's knock branch): refuse(c, lineno, F_knock, cur_name, x = s7), TAIL. *)
Definition H_KNOCK (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (vp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    s7 = Z_to_bv 64 vp ->
    cstr_at rsegs m vp x ->
    pf_inb (bv_unsigned sp + PF_BUF) vp x ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) F_knock [AS nm; AS x], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_KNOCK) fc None m (seg_rom rsegs)).

(** KREF (0x152a0, piece P9, entered from P6 (bad role) and P8 (bad ignore) with the format in a2): refuse(c, lineno, f,
    cur_name, x = s7), TAIL. *)
Definition H_KREF (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (f : list Z) (fp vp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    In (f, fp) [(F_badrole, PF_STR_BADROLE); (F_badignore, PF_STR_BADIGNORE)] ->
    a2 = Z_to_bv 64 fp ->
    s7 = Z_to_bv 64 vp ->
    cstr_at rsegs m vp x ->
    pf_inb (bv_unsigned sp + PF_BUF) vp x ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) f [AS nm; AS x], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_KREF) fc None m (seg_rom rsegs)).

(** NOKEY (0x152b0, piece P9, entered from P5's no-key branch with the arguments in a0-a4): refuse(c, lineno, F_nokey,
    cur_name, key), TAIL. *)
Definition H_NOKEY (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (kp : Z) (key : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c cur) ->
    a0 = Z_to_bv 64 c ->
    a1 = Z_to_bv 64 (ln + 1) ->
    a2 = Z_to_bv 64 PF_STR_NOKEY ->
    a3 = Z_to_bv 64 (bv_unsigned sp + PF_NAMEBUF) ->
    a4 = Z_to_bv 64 kp ->
    cstr_at rsegs m kp key ->
    pf_inb (bv_unsigned sp + PF_BUF) kp key ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) F_nokey [AS nm; AS key], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_NOKEY) fc None m (seg_rom rsegs)).

(** PROV (0x154a8, piece P9, entered from P6 (role, falls in) and P8 (ignore, `j`)): a1 = 96 and a3 = &c->reading follow.
    c holds pf_prov_mid k rc gi (the value fields of seg[gi] stored, the file field not yet); a0 = the file field,
    a2 = "%s". The snprintf(field, 96, "%s", c->reading) gives pf_prov_fin k rc gi, then TAIL. *)
Definition H_PROV (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (k : pf_prov) (gi : nat),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c (pf_prov_mid k rc gi) (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)) ->
    a0 = Z_to_bv 64 (rseg_addr c gi + pf_prov_off k) ->
    a2 = Z_to_bv 64 PF_STR_S ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (pf_prov_fin k rc gi, Some gi, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_PROV) fc None m (seg_rom rsegs)).

(** PROVM (0x154ac, piece P9, entered from P7's hit with a1 = 96 set): a3 = &c->reading follows.
    c holds pf_prov_mid k rc gi (the value fields of seg[gi] stored, the file field not yet); a0 = the file field,
    a2 = "%s". The snprintf(field, 96, "%s", c->reading) gives pf_prov_fin k rc gi, then TAIL. *)
Definition H_PROVM (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (k : pf_prov) (gi : nat),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c (pf_prov_mid k rc gi) (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)) ->
    a0 = Z_to_bv 64 (rseg_addr c gi + pf_prov_off k) ->
    a1 = Z_to_bv 64 96 ->
    a2 = Z_to_bv 64 PF_STR_S ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (pf_prov_fin k rc gi, Some gi, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_PROVM) fc None m (seg_rom rsegs)).

(** CNAME (0x154b0, piece P9, entered from P4's accepted header): c already holds the state rc after the header (seen_gen
    stored, the repeated-name refusal made if any), cur = Some gi; snprintf(cur_name, 16, "%s", name) with the
    arguments in a0-a3 (name at most 15 bytes, in buf), then TAIL with nm' = snprintf_s 16 F_s [AS name]. *)
Definition H_CNAME (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (np : Z) (name : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn (pf_next s o) s)) ->
    pf_regs s0 s1 s2 s3 s4 s10 s11 c (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    s9 = Z_to_bv 64 512 ->
    s6 = Z_to_bv 64 (pf_cur_ptr c (Some gi)) ->
    a0 = Z_to_bv 64 (bv_unsigned sp + PF_NAMEBUF) ->
    a1 = Z_to_bv 64 16 ->
    a2 = Z_to_bv 64 PF_STR_S ->
    a3 = Z_to_bv 64 np ->
    cstr_at rsegs m np name ->
    pf_inb (bv_unsigned sp + PF_BUF) np name ->
    (length name <= 15)%nat ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (rc, Some gi, snprintf_s 16 F_s [AS name]) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_CNAME) fc None m (seg_rom rsegs)).

(** ** The pieces *)
(** P1, entry, setup and return: ENTRY -> HEAD or DONE; DONE -> the return (no exit). *)
Definition S_P1 : Prop :=
  H_DONE /\ ((forall n, H_HEAD n) -> H_DONE -> H_ENTRY).

(** P2, the line driver: HEAD -> LONG, HDR, KEY or TAIL (an empty line); TAIL -> HEAD (pred n) or DONE. *)
Definition S_P2 : Prop :=
  forall n : nat,
    (H_LONG n -> H_HDR n -> H_KEY n -> H_TAIL n -> H_HEAD n) /\ (H_HEAD (pred n) -> H_DONE -> H_TAIL n).

(** P3, the long line, and its shared refuse site: LONG -> TAIL; OUTS -> TAIL. *)
Definition S_P3 : Prop :=
  forall n : nat, (H_TAIL n -> H_LONG n) /\ (H_TAIL n -> H_OUTS n).

(** P4, the header and seg_get: HDR -> TAIL (every refusal, cur = NULL) or CNAME (accepted). *)
Definition S_P4 : Prop :=
  forall n : nat, H_TAIL n -> H_CNAME n -> H_HDR n.

(** P5, the key line: KEY -> OUTS, ROLE, MODEL, IGN, KNOCK, NOKEY or TAIL (no '='); S9 -> TAIL. *)
Definition S_P5 : Prop :=
  forall n : nat,
    (H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n -> H_TAIL n -> H_KEY n) /\
    (H_TAIL n -> H_S9 n).

(** P6, role: ROLE -> INTENT (the fold); INTENT -> KREF (bad role) or PROV. *)
Definition S_P6 : Prop :=
  forall n : nat, (H_INTENT n -> H_ROLE n) /\ (H_KREF n -> H_PROV n -> H_INTENT n).

(** P7, model: MODEL -> PROVM (a box model) or S9 (the refusal with the known list). *)
Definition S_P7 : Prop :=
  forall n : nat, H_PROVM n -> H_S9 n -> H_MODEL n.

(** P8, ignore: IGN -> KREF (bad ignore) or PROV. *)
Definition S_P8 : Prop :=
  forall n : nat, H_KREF n -> H_PROV n -> H_IGN n.

(** P9, the shared sites: KNOCK, KREF, NOKEY (refuse at 0x152b0) and PROV, PROVM, CNAME (snprintf at 0x154b0),
    each -> TAIL. *)
Definition S_P9 : Prop :=
  forall n : nat,
    (H_TAIL n -> H_KNOCK n) /\ (H_TAIL n -> H_KREF n) /\ (H_TAIL n -> H_NOKEY n) /\
    (H_TAIL n -> H_PROV n) /\ (H_TAIL n -> H_PROVM n) /\ (H_TAIL n -> H_CNAME n).

(** The whole function from its pieces (NOT proved here): strong induction on n gives H_HEAD n for every n (H_TAIL 0
    holds outright: its rest would be shorter than 0), then S_P1. *)
Definition pieces_give_contract : Prop :=
  S_P1 -> S_P2 -> S_P3 -> S_P4 -> S_P5 -> S_P6 -> S_P7 -> S_P8 -> S_P9 -> reac_segconf_parse_file_contract.
