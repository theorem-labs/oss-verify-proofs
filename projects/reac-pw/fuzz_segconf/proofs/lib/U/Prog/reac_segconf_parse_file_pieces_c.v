From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import refuse_c reac_segconf_parse_file_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_parse_file(c, text, label) (reac_segconf.c:120-296) cut into its 9 pieces and the line-loop
    invariant, UBSan build (image 1696d6c34ffd; the unstripped twin afc060e3cc9c):
    at 0x15248, 2616 bytes, 654 instructions, 96 conditional branches of which 34 go to the
    function's one `unimp` at 0x15c7c, frame 0x420, saves ra and s0-s11 at sp + 0x418 .. 0x3b8. Family F3.
    Statement text only: no piece is proved here, and pieces_give_contract (the whole
    function from its pieces) is stated, not proved. The whole-function contract is
    lib/U/Prog/reac_segconf_parse_file_c.v (REAC_SEGCONF_PARSE_FILE, PARSE_FILE_STACK, reader_pre,
    reac_segconf_parse_file_pre); H_ENTRY is it. The build-independent part (pf_sv, pf_lctx / pf_line / pf_next /
    pf_tline, pf_cnt, pf_prov_*, pf_role_step, and the lemmas O1, O2, L_* as Props) is lib/Prog/pf_pieces_spec.v.

    The shape is the plain twin's (lib/Prog/reac_segconf_parse_file_pieces_c.v, whose header says it in full): one
    Prop per cut, H_<CUT> (every machine at the cut with the cut's facts reaches the function's post computed from the
    cut's state: pf_ret / pf_fin, seg_env.ret_post_fp with the saved ra, sp + 0x420, the entry s0-s11, a0 = c->n of
    the final state, W the whole function's, c holding the final state); one Prop per piece, S_<PIECE> (its exit cuts
    imply its entry cut, one implication per entry); the measure n on the loop's cuts and every cut inside a line;
    the state in the spine's terms (rc in c, cur : option nat with &c->seg[i] = c + 356 i, cur_name at sp + 0x3a8,
    the text s at t, the line start o, lineno = the lines consumed). UBSan keeps c in the frame slot sp + 0x90 and cur
    in sp + 0x88 (DWARF breg2(144) / breg2(136)), not in registers.

    The cuts (pc, piece that owns the code, who enters it):
    - ENTRY 0x15248 (P1): the contract. DONE 0x15c30 (P1): from P1 (empty text, `beqz` 0x15310) and P2's tail.
    - HEAD 0x153a8 (P2): from P1 and the tail's `bnez` 0x156a8. TAIL 0x156a4 (P2): from P2 (empty line, `beqz`
      0x154c8), P3 (`j` 0x15444), P7 (`j` 0x15a6c), P9 (0x156a0 falls in; `j` 0x15904, 0x15b7c).
    - LONG 0x153f8 (P3): from P2. NEITHER 0x15440 (P3's refuse site): from P5 (0x1559c).
    - HDR 0x154d4 (P4), KEY 0x154fc (P5): from P2.
    - ROLE 0x156b0 (P6), MODEL 0x156f8 (P7), IGN 0x15798 (P8): from P5's strcasecmp tests (0x1562c, 0x15640,
      0x15654). INTENT 0x15834 (P6): P6's inner cut (O1).
    - OUTS 0x15688 (P9): from P5 (`beqz` cur, 0x15618). HREF 0x1569c (P9): from P4 (0x15584, 0x155e0). CLR 0x156a0
      (P9): from P4 (0x15794, 0x15a8c). KNOCK 0x158e8 (P9): from P5 (0x15668). KREF 0x158f0 (P9): from P6 (0x158e4)
      and P8 (0x15818). NOKEY 0x15900 (P9): from P5 (0x15684). PROV 0x15b70 (P9): from P6 (falls in at 0x15b6c) and
      P8 (0x15b44). PROVM 0x15b74 (P9): from P7 (0x15968). CNAME 0x15b78 (P9): from P4 (0x15c2c).

    The pieces (instructions / conditional branches [trap branches] / calls), their callee
    contracts, call sites and trap sites (each trap falls through by the premise named).
    Callee contracts: snprintf 0x19a14; strchr
    0x1f478 and strncasecmp 0x1f65c (commit d8911fcbf9ff); strlen 0x1f5cc, memcpy 0x1eec8,
    memset 0x1f2cc, bcmp 0x1edc8 (lib/U/Prog strlen_c.v, memcpy_c.v, memset_c.v, bcmp_c.v); strspn 0x1f968 and strcmp
    0x1f594 (commit 06702a5f1f22); strcasecmp 0x1f3c4;
    trim 0x15db4 and refuse 0x15c80 (lib/U/Prog trim_c.v, refuse_c.v, family F2); reac_box_catalogue_by_token 0x167a0
    and reac_box_catalogue 0x1677c (lib/U/Prog). Every string argument in buf (sp + 0x1a8 .. 0x3a7), cur_name, known or
    low lies in the frame, above the callee's sp and apart from c; every refuse call has rc_refused rc + 1 < 2^32 by
    pf_cnt. The pointer-overflow traps fall through because every pointer lies in the text block, buf, low or c, all
    away from 0, 1 and 2^64 - 1 (pf_text, stack_ok with sp + 0x420 <= 2^63 by printf_env, c + 16616 below the stack).
    - P1 (entry, setup, return) 15248-153a4, 15c30-15c7c; 108 / 5 [2] / 1. ENTRY -> HEAD or DONE; DONE -> the return.
      Traps 0x15284 (c == 0) and 0x15290 (c & 7): reader_pre's c <> 0 and c mod 16 = 0. 0x152e4 snprintf(c + 0x4080,
      96, "%s" 0x104e0, label or "reac-pw.conf" 0x10463); c->gen++ (0x152f0); the spill slots (pf_spill), sp + 0x88
      = 0 (cur = None), cur_name zeroed (0x15308 / 0x1530c, nm = []); the head with o = 0, ln = 0, d = [].
    - P2 (line driver) 153a8-153f4, 15448-154d0, 156a4-156ac; 58 / 17 [6] / 4. HEAD -> LONG, HDR, KEY or TAIL; TAIL
      -> HEAD (pred n) or DONE. 0x153b8 strchr(p, '\n'); 0x153d4 strlen(p) when nl = NULL; 0x15454 memcpy(buf = sp +
      0x1a8, at, len); buf[len] = 0 (0x1546c); the strip_comment loop at 0x15474 (a0 = buf + k, a1 = -k; L_strip);
      s4 = 9 (0x154b4); 0x154bc trim(buf). Traps 0x153c0 (nl == -1), 0x153dc (~p < len), 0x153ec (lineno + 1 <
      lineno: ln <= o <= 65535 by pf_lctx), 0x1545c (~buf < len, from the slot sp + 0x80), 0x1548c (p == 1), 0x1549c
      (p == -1).
    - P3 (long line) 153f8-15444; 20 / 2 [1] / 2. LONG -> TAIL; NEITHER -> TAIL. 0x15400 strspn(at, " \t\r" from
      sp + 0x78) on the rest of the text (O2_strspn_rest); at[lead] == '[' clears the cur slot (0x1542c); 0x15440
      refuse(c, lineno, F_long 0x10628 from sp + 0x70, 511) from LONG, or (c, lineno, F_neither, line) from NEITHER.
      Trap 0x1540c (~at < lead).
    - P4 (header and seg_get) 154d4-154f8, 15570-15584, 155a0-155e0, 15740-15794, 15a78-15b10, 15b80-15c2c; 138 / 20
      [8] / 11. HDR -> HREF (not closed, text after, unknown), CLR (too long, past the bound, no name) or CNAME.
      0x154dc strchr(line, ']'); `*close = 0` (0x155a0); 0x155ac trim(line + 1); 0x155c4 strncasecmp(body, "segment"
      0x10313, 7) and body[7] in {s4 = '\t', s1 = ' '}; 0x15758 trim(body + 7); 0x1576c strlen(name); 0x15790
      refuse(c, lineno, F_toolong 0x102a9, name, 15) or (F_bound 0x10817, name, 32); 0x15a88 refuse(c, lineno,
      F_noname 0x10441); the seg_get search loop at 0x15ac0 (invariant: s6 = 356 i, s9 = 11392 - 356 i, s4 = c + 356 i,
      the names j < i differ; the slot sp + 0x88 holds c->n during the search and gets cur back at 0x15bfc)
      with 0x15ad4 strcmp(c->seg[i].name, name); c->overflow++ (0x15b00); 0x15bb4 memset(c + 356 n, 0, 356) and
      0x15bcc snprintf(c + 356 n, 16, "%s", name), n++ (0x15b88); 0x15bf8 refuse(c, lineno, F_twice 0x105aa, name);
      seen_gen = gen (0x15c14). Traps 0x154e4 (close == -1), 0x155a4 (line == -1), 0x15744 (body > -8), 0x15ac0
      (array-bounds: i < n <= 32), 0x15ac8 (~c < 356 i, from the slot sp + 0x48), 0x15b8c (32 < n), 0x15b9c (~c <
      356 n), 0x15c04 (cur & 3: c mod 16 = 0, 356 = 4 * 89).
    - P5 (key line) 154fc-1556c, 15588-1559c, 155e4-15684; 76 / 16 [5] / 8. KEY -> NEITHER, OUTS (cur = NULL), ROLE,
      MODEL, IGN, KNOCK or NOKEY. 0x15504 strchr(line, '='); `*eq = 0` (0x15510); 0x15518 trim(line) -> key (s8);
      0x15528 trim(eq + 1); 0x15530 strlen(v) and the inlined unquote -> val (s7); 0x15628 / 0x1563c / 0x15650 /
      0x15664 strcasecmp(key, "role" / "model" / "ignore" / "knock"). Traps 0x1551c (eq == -1), 0x15558, 0x155ec,
      0x15600 (~v < n - 1), 0x1560c (v == -1).
    - P6 (role) 156b0-156f4, 1581c-158e4, 1596c-15970, 15a70-15a74, 15b14-15b18, 15b48-15b6c; 85 / 11 [3] / 3. ROLE
      -> INTENT; INTENT -> KREF (F_badrole) or PROV (role = r, role_set = s11 = 1 at 0x15b5c / 0x15b60). The fold loop
      at 0x156bc into low = sp + 0xa0 (L_low with cap 64), low[k] = 0 (0x15830); 0x15844 / 0x1585c / 0x15874 bcmp(low,
      "auto" / "master" / "slave", 5 / 7 / 6) (O1_bcmp_lit, ls = LB); the tap / box word compares at 0x158a8 / 0x158d8
      against the slots sp + 0x28 / 0x20 (O1_word_lit). Traps 0x156dc (q == -1), 0x15824 (~(sp + 0xa0) < li, from the
      slot sp + 0x40), 0x15b54 (cur & 3).
    - P7 (model) 156f8-1573c, 15908-15968, 15974-15a6c; 106 / 16 [8] / 5. MODEL -> PROVM (hit) or TAIL (the refusal).
      The fold loop at 0x15704 into low = sp + 0x190 (L_low with cap 24); 0x15924 reac_box_catalogue_by_token(low);
      0x15954 snprintf(cur + 0x24, 24, "%s", low); 0x1597c reac_box_catalogue(&ntok = sp + 0x98); the join loop at
      0x159b4 (s9 = ti, s6 = kn, s8 = tab + 296 ti; L_known) with 0x15a28 snprintf(known + kn, 240 - kn, "%s%s",
      ti ? "|" : "", tab[ti].token) (known = sp + 0xa0); 0x15a68 refuse(c, lineno, F_badmodel 0x104e3, cur_name, val,
      known). Traps 0x15724 (q == -1), 0x15910 (~(sp + 0x190) < li), 0x15934 (cur & 3), 0x159b4 (240 < kn: kn <= 77),
      0x159e4, 0x159e8, 0x15a00 (&tab[ti]: tab = 0x21468, ti <= 10), 0x15a08 (tab & 7: 0x21468 mod 8 = 0).
    - P8 (ignore) 15798-15818, 15b1c-15b44; 44 / 9 [1] / 4. IGN -> KREF (F_badignore) or PROV (ignore = b,
      ignore_set = 1 at 0x15b30 / 0x15b34). 0x157a4 / 0x157bc / 0x157e4 / 0x157f8 strcasecmp(val, "yes" / "true" /
      "no" / "false"). Trap 0x15b28 (cur & 3).
    - P9 (shared sites) 15688-156a0, 158e8-15904, 15b70-15b7c; 19 / 0 / 3. OUTS, HREF -> TAIL through 0x1569c
      refuse and `sd zero,0x88(sp)`; CLR -> TAIL; KNOCK, KREF, NOKEY -> TAIL through 0x15900 refuse(c, lineno, fmt,
      cur_name = sp + 0x3a8, val or key); PROV, PROVM, CNAME -> TAIL through 0x15b78 snprintf(field, 96, "%s",
      c->reading from sp + 0x50) or snprintf(cur_name, 16, "%s", name). No trap.

    Notes on the statement: as the plain twin's header says (the counters' bound, fixed at
    commit 3e75bf1c5aa6; cur_name = seg[i].name not a cut fact; the line start carried by
    pf_lctx; O2's spn_len bridge a comment). In this build DONE asks for the slot sp + 0x58 only (set at 0x152f8, before
    the entry test), and CLR does not fix the cur slot (on the bound refusal it still holds c->n from the search). *)

(** ** This build's pcs and frame offsets *)
Definition PF_PC_HEAD : Z := 0x153a8.
Definition PF_PC_TAIL : Z := 0x156a4.
Definition PF_PC_DONE : Z := 0x15c30.
Definition PF_PC_LONG : Z := 0x153f8.
Definition PF_PC_HDR : Z := 0x154d4.
Definition PF_PC_KEY : Z := 0x154fc.
Definition PF_PC_NEITHER : Z := 0x15440.
Definition PF_PC_OUTS : Z := 0x15688.
Definition PF_PC_HREF : Z := 0x1569c.
Definition PF_PC_CLR : Z := 0x156a0.
Definition PF_PC_ROLE : Z := 0x156b0.
Definition PF_PC_INTENT : Z := 0x15834.
Definition PF_PC_MODEL : Z := 0x156f8.
Definition PF_PC_IGN : Z := 0x15798.
Definition PF_PC_KNOCK : Z := 0x158e8.
Definition PF_PC_KREF : Z := 0x158f0.
Definition PF_PC_NOKEY : Z := 0x15900.
Definition PF_PC_PROV : Z := 0x15b70.
Definition PF_PC_PROVM : Z := 0x15b74.
Definition PF_PC_CNAME : Z := 0x15b78.
Definition PF_SAVE : Z := 0x3b8.
Definition PF_NAMEBUF : Z := 0x3a8.
Definition PF_BUF : Z := 0x1a8.
Definition PF_LOW : Z := 0xa0.
Definition PF_LOWM : Z := 0x190.
Definition PF_NSLOT : Z := 0x58.
Definition PF_CURSLOT : Z := 0x88.
Definition PF_CSLOT : Z := 0x90.

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
(** The word ~x (the no-wrap test operands UBSan keeps in the frame). *)
Definition pf_not (x : Z) : word := Z_to_bv 64 (- x - 1).
(** The spill slots P1 fills before the loop and no piece changes (UBSan): sp + 0x10
    &c->overflow, 0x18 sizeof c->seg (0x2c80, the array-bounds counter of seg_get), 0x20 the "box\0" word, 0x28
    the "tap\0" word, 0x30 ~(sp + 0x190), 0x38 &c->gen, 0x40 ~(sp + 0xa0), 0x48 ~c, 0x50 &c->reading, 0x58 &c->n;
    0x70 F_long, 0x78 " \t\r", 0x80 ~(sp + 0x1a8); 0x90 c. (0x60 / 0x68 are P7's join-loop flags, 0x88 is cur.) *)
Definition pf_spill (m : word -> option byte) (sp c : Z) : Prop :=
  saved_at rsegs m (sp + 0x10)
    [Z_to_bv 64 (c + RC_OVERFLOW); Z_to_bv 64 (RSEG_SIZE * 32); Z_to_bv 64 PF_BOX_WORD; Z_to_bv 64 PF_TAP_WORD;
     pf_not (sp + PF_LOWM); Z_to_bv 64 (c + RC_GEN); pf_not (sp + PF_LOW); pf_not c; Z_to_bv 64 (c + RC_READING);
     Z_to_bv 64 (c + RC_N)] /\
  saved_at rsegs m (sp + 0x70) [Z_to_bv 64 PF_STR_LONG; Z_to_bv 64 PF_STR_BLANKS; pf_not (sp + PF_BUF)] /\
  bytes_at rsegs m (sp + PF_CSLOT) (le8 (Z_to_bv 64 c)).
(** The loop's registers (UBSan): s2 = p, s3 = lineno, the constants s0 = ';', s1 = ' ' (also
    the bound 32 of seg_get), s5 = -1 (the pointer-overflow tests), s10 = '#', s11 = 1 (the p == 1 test and the
    *_set stores). c is in the frame slot sp + 0x90 (pf_spill), cur in sp + 0x88 (pf_curslot). *)
Definition pf_regs (s0 s1 s2 s3 s5 s10 s11 : word) (p ln : Z) : Prop :=
  s2 = Z_to_bv 64 p /\ s3 = Z_to_bv 64 ln /\ s0 = Z_to_bv 64 SEMI /\ s1 = Z_to_bv 64 SP /\
  s5 = Z_to_bv 64 (-1) /\ s10 = Z_to_bv 64 HASH /\ s11 = Z_to_bv 64 1.
(** cur in its frame slot sp + 0x88 (DWARF: cur at DW_OP_breg2(136)). *)
Definition pf_curslot (m : word -> option byte) (sp c : Z) (cur : option nat) : Prop :=
  bytes_at rsegs m (sp + PF_CURSLOT) (le8 (Z_to_bv 64 (pf_cur_ptr c cur))).
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

(** DONE (0x15c30, piece P1): the loop has ended (the tail's `*p == 0`, or an empty text at the entry test): `lw` c->n
    through the frame slot sp + 0x58 (it holds &c->n = c + 0x2c80 on both paths into DONE; the other spill slots may
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

(** HEAD (0x153a8, piece P2): the line-loop head and the interface of the walk. A line starts at o
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
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat o) ln ->
    pf_curslot m (bv_unsigned sp) c cur ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (rc, cur, nm) ln (lines (skipn o s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_HEAD) fc None m (seg_rom rsegs)).

(** TAIL (0x156a4, piece P2): a line has been read. o is the next line's offset (p = t + o, past the '\n' or at the
    text's end), ln and d count the lines read, c holds rc and (cur, nm) are the state after the line. The rest is
    shorter than n: the head it loops to is H_HEAD (pred n). *)
Definition H_TAIL (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
    pf_hctx m fc (bv_unsigned sp) lo v c t s o ln d ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    (length (skipn o s) < n)%nat ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat o) ln ->
    pf_curslot m (bv_unsigned sp) c cur ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (rc, cur, nm) ln (lines (skipn o s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_TAIL) fc None m (seg_rom rsegs)).

(** LONG (0x153f8, piece P3's entry from P2's `bltu len, 512` not taken): at = t + o in s7, len = length of the line in
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
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
    s7 = Z_to_bv 64 (t + Z.of_nat o) ->
    s8 = Z_to_bv 64 (Z.of_nat (length (pf_line s o))) ->
    (512 <= length (pf_line s o))%nat ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_line rc cur nm (ln + 1) (pf_line s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_LONG) fc None m (seg_rom rsegs)).

(** HDR (0x154d4, piece P4's entry): the line (len < 512) was copied into buf, its comment cut and trimmed; s7 = lp points
    at the trimmed line pf_tline s o in buf, whose first byte is '['. The step is r_header.
    UBSan: s4 = 9 ('\t', set at 0x154b4 and read by the body[7] test at 0x15750). *)
Definition H_HDR (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (lp : Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
    s4 = Z_to_bv 64 TAB ->
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

(** KEY (0x154fc, piece P5's entry): as HDR, but the trimmed line is neither empty nor a header. The step is r_key. *)
Definition H_KEY (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (lp : Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
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

(** NEITHER (0x15440, piece P3's shared refuse site, entered from P5 by `j 0x15440` at 0x1559c): a line with no '=':
    refuse(c, lineno, F_neither, line) with the arguments in a0-a3, then `j` TAIL (cur unchanged). *)
Definition H_NEITHER (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (lp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
    a0 = Z_to_bv 64 c ->
    a1 = Z_to_bv 64 (ln + 1) ->
    a2 = Z_to_bv 64 PF_STR_NEITHER ->
    a3 = Z_to_bv 64 lp ->
    cstr_at rsegs m lp x ->
    pf_inb (bv_unsigned sp + PF_BUF) lp x ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) F_neither [AS x], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_NEITHER) fc None m (seg_rom rsegs)).

(** OUTS (0x15688, piece P9, entered from P5's `beqz cur` at 0x15618): a key line outside any section (the slot
    sp + 0x88 holds 0): refuse(c, lineno, F_outside, key = s8), `sd zero` into the slot, TAIL. *)
Definition H_OUTS (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (kp : Z) (key : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc None nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c None ->
    s8 = Z_to_bv 64 kp ->
    cstr_at rsegs m kp key ->
    pf_inb (bv_unsigned sp + PF_BUF) kp key ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) F_outside [AS key], None, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_OUTS) fc None m (seg_rom rsegs)).

(** HREF (0x1569c, piece P9's shared refuse site, entered from P4 at 0x15584 and 0x155e0, and from P9's own OUTS):
    refuse(c, lineno, f, x) with the arguments in a0-a3, f one of the three header refusals (or F_outside), then
    `sd zero,0x88(sp)` (cur = NULL) and TAIL. The slot's old value is not read. *)
Definition H_HREF (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (f : list Z) (fp xp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc None nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    In (f, fp) [(F_notclosed, PF_STR_NOTCLOSED); (F_after, PF_STR_AFTER); (F_unknown, PF_STR_UNKNOWN);
                  (F_outside, PF_STR_OUTSIDE)] ->
    a0 = Z_to_bv 64 c ->
    a1 = Z_to_bv 64 (ln + 1) ->
    a2 = Z_to_bv 64 fp ->
    a3 = Z_to_bv 64 xp ->
    cstr_at rsegs m xp x ->
    pf_inb (bv_unsigned sp + PF_BUF) xp x ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) f [AS x], None, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_HREF) fc None m (seg_rom rsegs)).

(** CLR (0x156a0, piece P9, entered from P4 after the refusals at 0x15790 and 0x15a88): c already holds the state rc
    after the line's refusal; `sd zero,0x88(sp)` sets cur = NULL (the slot may hold c->n from the seg_get search),
    then TAIL. *)
Definition H_CLR (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc None nm (length (skipn (pf_next s o) s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (rc, None, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_CLR) fc None m (seg_rom rsegs)).

(** ROLE (0x156b0, piece P6's entry): key is "role".
    The key line has been split (pf_kv: the '=' at ei, key = s8, val = s7, both C strings in buf), cur = Some gi.
    The step is r_key in the branch the strcasecmp results select. *)
Definition H_ROLE (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (kp vp : Z) (key val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
    pf_kv m (bv_unsigned sp) (pf_tline s o) kp vp key val ->
    s8 = Z_to_bv 64 kp ->
    s7 = Z_to_bv 64 vp ->
    strcasecmp key S_role = 0 ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (r_key rc (Some gi) nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_ROLE) fc None m (seg_rom rsegs)).

(** MODEL (0x156f8, piece P7's entry): key is "model".
    The key line has been split (pf_kv: the '=' at ei, key = s8, val = s7, both C strings in buf), cur = Some gi.
    The step is r_key in the branch the strcasecmp results select. *)
Definition H_MODEL (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (kp vp : Z) (key val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
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

(** IGN (0x15798, piece P8's entry): key is "ignore".
    The key line has been split (pf_kv: the '=' at ei, key = s8, val = s7, both C strings in buf), cur = Some gi.
    The step is r_key in the branch the strcasecmp results select. *)
Definition H_IGN (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (kp vp : Z) (key val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
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

(** INTENT (0x15834, piece P6's inner cut: the start of the inlined reac_role_intent_parse, after the fold loop and
    low[k] = 0). O1: the 64 bytes LB of low (sp + 0xa0) are named, with their prefix r_low val 0 64 and its NUL; the
    bytes after it are what earlier lines left, and bcmp reads up to 7 of them. The step is stated against
    SegModel.role_intent_parse (pf_role_step). *)
Definition H_INTENT (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (vp : Z) (val : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
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

(** KNOCK (0x158e8, piece P9, entered from P5's knock branch): refuse(c, lineno, F_knock, cur_name, x = s7), TAIL. *)
Definition H_KNOCK (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (vp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
    s7 = Z_to_bv 64 vp ->
    cstr_at rsegs m vp x ->
    pf_inb (bv_unsigned sp + PF_BUF) vp x ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) F_knock [AS nm; AS x], cur, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_KNOCK) fc None m (seg_rom rsegs)).

(** KREF (0x158f0, piece P9, entered from P6 (bad role) and P8 (bad ignore) with the format in a2): refuse(c, lineno, f,
    cur_name, x = s7), TAIL. *)
Definition H_KREF (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (f : list Z) (fp vp : Z) (x : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
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

(** NOKEY (0x15900, piece P9, entered from P5's no-key branch with the arguments in a0-a4): refuse(c, lineno, F_nokey,
    cur_name, key), TAIL. *)
Definition H_NOKEY (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (kp : Z) (key : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c cur ->
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

(** PROV (0x15b70, piece P9, entered from P6 (role, falls in) and P8 (ignore, `j`)): a1 = 96 and a3 = &c->reading follow.
    c holds pf_prov_mid k rc gi (the value fields of seg[gi] stored, the file field not yet); a0 = the file field,
    a2 = "%s". The snprintf(field, 96, "%s", c->reading) gives pf_prov_fin k rc gi, then TAIL. *)
Definition H_PROV (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (k : pf_prov) (gi : nat),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c (pf_prov_mid k rc gi) (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
    a0 = Z_to_bv 64 (rseg_addr c gi + pf_prov_off k) ->
    a2 = Z_to_bv 64 PF_STR_S ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (pf_prov_fin k rc gi, Some gi, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_PROV) fc None m (seg_rom rsegs)).

(** PROVM (0x15b74, piece P9, entered from P7's hit with a1 = 96 set): a3 = &c->reading follows.
    c holds pf_prov_mid k rc gi (the value fields of seg[gi] stored, the file field not yet); a0 = the file field,
    a2 = "%s". The snprintf(field, 96, "%s", c->reading) gives pf_prov_fin k rc gi, then TAIL. *)
Definition H_PROVM (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (k : pf_prov) (gi : nat),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c (pf_prov_mid k rc gi) (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
    a0 = Z_to_bv 64 (rseg_addr c gi + pf_prov_off k) ->
    a1 = Z_to_bv 64 96 ->
    a2 = Z_to_bv 64 PF_STR_S ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (pf_prov_fin k rc gi, Some gi, nm) (ln + 1) (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PF_PC_PROVM) fc None m (seg_rom rsegs)).

(** CNAME (0x15b78, piece P9, entered from P4's accepted header): c already holds the state rc after the header (seen_gen
    stored, the repeated-name refusal made if any), cur = Some gi; snprintf(cur_name, 16, "%s", name) with the
    arguments in a0-a3 (name at most 15 bytes, in buf), then TAIL with nm' = snprintf_s 16 F_s [AS name]. *)
Definition H_CNAME (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
         (gi : nat) (np : Z) (name : list Z),
    pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn (pf_next s o) s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m (bv_unsigned sp) c (Some gi) ->
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

(** P3, the long line, and its shared refuse site: LONG -> TAIL; NEITHER -> TAIL. *)
Definition S_P3 : Prop :=
  forall n : nat, (H_TAIL n -> H_LONG n) /\ (H_TAIL n -> H_NEITHER n).

(** P4, the header and seg_get: HDR -> HREF (not closed, text after, unknown), CLR (the other refusals) or
    CNAME (accepted). *)
Definition S_P4 : Prop :=
  forall n : nat, H_HREF n -> H_CLR n -> H_CNAME n -> H_HDR n.

(** P5, the key line: KEY -> NEITHER, OUTS, ROLE, MODEL, IGN, KNOCK or NOKEY. *)
Definition S_P5 : Prop :=
  forall n : nat, H_NEITHER n -> H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n -> H_KEY n.

(** P6, role: ROLE -> INTENT (the fold); INTENT -> KREF (bad role) or PROV. *)
Definition S_P6 : Prop :=
  forall n : nat, (H_INTENT n -> H_ROLE n) /\ (H_KREF n -> H_PROV n -> H_INTENT n).

(** P7, model: MODEL -> PROVM (a box model) or TAIL (the refusal with the known list). *)
Definition S_P7 : Prop :=
  forall n : nat, H_PROVM n -> H_TAIL n -> H_MODEL n.

(** P8, ignore: IGN -> KREF (bad ignore) or PROV. *)
Definition S_P8 : Prop :=
  forall n : nat, H_KREF n -> H_PROV n -> H_IGN n.

(** P9, the shared sites: OUTS, HREF, CLR, KNOCK, KREF, NOKEY (refuse at 0x1569c / 0x15900) and PROV, PROVM,
    CNAME (snprintf at 0x15b78), each -> TAIL. *)
Definition S_P9 : Prop :=
  forall n : nat,
    (H_TAIL n -> H_OUTS n) /\ (H_TAIL n -> H_HREF n) /\ (H_TAIL n -> H_CLR n) /\
    (H_TAIL n -> H_KNOCK n) /\ (H_TAIL n -> H_KREF n) /\ (H_TAIL n -> H_NOKEY n) /\
    (H_TAIL n -> H_PROV n) /\ (H_TAIL n -> H_PROVM n) /\ (H_TAIL n -> H_CNAME n).

(** The whole function from its pieces (NOT proved here): strong induction on n gives H_HEAD n for every n (H_TAIL 0
    holds outright: its rest would be shorter than 0), then S_P1. *)
Definition pieces_give_contract : Prop :=
  S_P1 -> S_P2 -> S_P3 -> S_P4 -> S_P5 -> S_P6 -> S_P7 -> S_P8 -> S_P9 -> reac_segconf_parse_file_contract.
