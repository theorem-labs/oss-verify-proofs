(* reac_segconf_parse_file (reac_segconf.c:120-296; fuzz_segconf.asan 0x87a78, 4908 bytes, 1227 instructions; frame
   320 bytes, side-stack frame class 5): the contract of the ASan build's code, in plugin-hostd/fuzz_command's
   lib/A/Prog form (afn_pre at the entry, SRr of apost_baseF at the return: it reaches the printf wrappers).
   Functional content: the plain contract lib/Prog/reac_segconf_parse_file_c.v:13-70 (reader_pre :38-46,
   reac_segconf_parse_file_pre :48-56, the contract :58-70), restated over the ASan reader. The plain side's nine
   pieces S_P1 .. S_P9 (lib/Prog/reac_segconf_parse_file_pieces_c.v) are cuts of the plain image's machine at its
   pcs, not Gallina over the model; like the plain contract, this one names none of them (a walk's pieces are the
   walk's).
   What the code does (objdump of fuzz_segconf.asan, 0x87a78-0x88da0): the class-5 side-stack frame
   (`__asan_stack_malloc_5` at 0x87af0, a0 = 0x480 = 1152; object description at .rodata 0x17667: cur_name at
   frame offset 32 (16 bytes), buf 64 (512), low 640 (64), low146 736 (24), known 800 (240), ntok 1104 (8)); the
   shadow of its objects set inline and by `__asan_set_shadow_f8` / `__asan_set_shadow_00` (0x87b94, 0x87e20,
   0x88070, 0x88c20); snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf") (0x87ce8); c->gen++ (lw / sw
   of c + 0x40e0); memset(cur_name, 0, 16) (`__asan_memset` 0x87d4c); then (text <> NULL: the premise) the line
   loop over the text, one line per pass: strchr(p, '\n') (0x87de4) or strlen(p) (0x87e04), the >= 512 refusal
   with strspn(p, " \t\r") (0x87e34), the copy into buf (`__asan_memcpy` 0x87e90), strip_comment, trim, then the
   header branch (strchr ']', strncasecmp "segment", seg_get with strcmp, memset of a new entry at 0x88940 and
   snprintf of its name) or the key branch (strchr '=', trim, strlen, the strcasecmp dispatch on role / model /
   ignore / knock, the role branch's bcmp with auto / master / slave / tap / box, the model branch's
   reac_box_catalogue_by_token (0x88538), reac_box_catalogue (0x88634) and the join of the 11 tokens with
   snprintf "%s%s", the ignore branch's strcasecmp with yes / true / no / false, and the provenance snprintf of
   c->reading); the frame released by `__asan_stack_free_5` (0x88c10, a1 = 0x480); returns c->n. Its real-stack
   fallback (0x87b08-0x87b20) is not taken: the use-after-return flag is the record's constant as_uar_cell = 1.
   The post is the plain one: a0 = snd (SegModel.r_parse_file rcs s lab) and c holds fst (...).
   What it reads: the shadow base and the use-after-return flag through the GOT words as_got_shadow B (image A
   0xa2a50) and as_got_uar B (0xa2aa8), AR constants (lib/Reusable/YG0d.v AR_const_law), so the contract names
   neither; the c block; the text; the label; 35 literals of reac_segconf.c's module (PARSE_FILE_LITS, and
   refuse's); the box-model table and its 11 tokens; the stack-protector cells. What it writes: its frames, its
   callees' frames, and exactly seg_spec.RC_PARSE_W c (seg[32] and n, refusal[8] .. overflow, reading and gen):
   the plain write list without its stack range. The text is never written. No abort site
   (segA/evidence/program.asan.tsv line 19).
   ASAN FACTS ADDED over the plain contract:
   - the 41 inline checks (program.asan.tsv: _load1:19 _load4:8 _load8:1 _store1:6 _store4:7; error arms at
     0x88bb4 and 0x88c7c-0x88da0, segA/evidence/callsites.asan.tsv lines 282-324), by the object they test (shadow
     tests located by a script over the objdump): load4 / store4 of the block's int fields (gen at 0x87cec, overflow
     0x887fc, n 0x88be4, and a seg entry's model_set 0x88564, role 0x88844, role_set 0x8885c, ignore 0x888c0,
     ignore_set 0x888d8, seen_gen 0x889c0), killed by reader_pre's sa_addr rd c SEG_C_SIZE; load1 of the text
     (text[0] 0x87d50, the long line's at[lead] 0x87e40, the tail's *p 0x88074), killed by sa_addr rd t
     (length s + 1); load8 of tab[ti].token in the join loop (shadow byte at 0x8864c, error arm
     __asan_report_load8 0x88ccc), killed by sa_cat's sa_addr of the table; the other load1 / store1 checks are on
     buf, low and cur_name inside the class-5 frame this call takes and unpoisons itself (no caller premise).
   - the interceptors' ranges: strchr / strlen / strspn / memcpy on the rest of the text (sa_str rd t s with its
     slack, sa_addr rd t (length s + 1)); the snprintf destinations c->reading, a seg name, a model and a
     provenance field (in the block: sa_addr), cur_name and known (the frame); the label (sa_ostr, sa_addr, apart
     from c->reading by its read span seg_spec.cstr_span, where the plain contract took length + 8); every literal
     (sa_lit, PARSE_FILE_LITS); the tokens (sa_cat's sa_lit); strcmp's c->seg[i].name and the strcasecmp / bcmp
     operands in the block or the frame.
   - where each object lies: the block by sa_heap (malloc(0x40e8) at LLVMFuzzerTestOneInput 0x84f80); the text by
     sa_heap (fuzz_str's malloc(n + 1) at 0x850f4), apart from the block by cstr_span (the plain apart); the label
     in a live heap block, a live side-stack frame (main's class-3 frame) or the image (the .bss buffer longl, the
     literal "reac-pw.conf"), in the image case with its addressability at every AR state (see
     reac_segconf_parse_file_pre); the literals and the table by sa_lit / sa_cat (image objects).
   - NO keep clause (sa_kept) in the post: the class-5 frame, its shadow (also written by `__asan_set_shadow_00`
     and `_f8`) and the flag byte lie outside the stack window and the footprint, and the kit's
     astack_malloc_realizes keeps nothing of aowned B ly S, which holds the shadow of every image byte, so no keep
     clause over image shadow is provable from the walk's hypotheses. A caller re-derives an image object's
     shadow from the AR of the exit state (ajournal's first conjunct) through the record's pinned bytes.
   - the class-5 frame, with refuse's class-0 frame taken inside it: sa_room_n 2 S (sa_room S does not serve the
     nest: refuse asks sa_room at ITS entry, where this call's frame is already in frames S).
   - it reaches snprintf, and vsnprintf through refuse: apost_baseF, sa_frm0, sa_ssp rd gotw guard.
   - arodata_okP over the window RLO .. RHI: the string interceptors ask rt_rom_view (fuzz_command
     lib/A/Rt/RtDefs.v:145 at origin/ossv/recipes 501c0d516c69), which AR does not give.
   - EV_reac_segconf_parse_file = 0, post tail sa_noalloc.
   Call sites (callsites.asan.tsv lines 13, 337): LLVMFuzzerTestOneInput 0x851bc (every file but the last, with
   main's label buffer, longl or NULL) and reac_segconf_parse 0x891f0 (c, text, "reac-pw.conf").
   image A: A_reac_segconf_parse_file = 0x87a78; STK_reac_segconf_parse_file = 320 + 16 + Z.max STK_refuse
   (3 * ESTACK) (INFERENCE: the frame, the `andi sp,sp,-32` realignment at 0x87ab8, and the deepest callee window,
   refuse's or the printf wrappers'); RLO = 0xa14a0, RHI = 0xa3748 (readelf, fuzz_command's CmdGlob.v
   convention); cat = fuzz_catalogue 0xa18e0 (nm; .data.rel.ro); gotw = 0xa36d8, guard = 0x5ff078 (as
   refuse_c.v); lit, the 35 texts of PARSE_FILE_LITS in order: .str 0x21340 F_s, .str.1 0x21360 S_base, .str.2
   0x21380 " \t\r", .str.3 0x213a0 F_long, .str.4 0x21400 F_notclosed, .str.5 0x21440 F_after, .str.6 0x214a0
   S_segment, .str.7 0x214c0 F_unknown, .str.8 0x21520 F_noname, .str.9 0x21560 F_toolong, .str.10 0x215c0
   F_bound, .str.11 0x21620 F_twice, .str.12 0x216a0 F_neither, .str.13 0x21700 F_outside, .str.14 0x21760
   S_role, .str.15 0x21780 F_badrole, .str.16 0x21800 S_model, .str.17 0x21820 F_ss, .str.18 0x21840 "|",
   .str.19 0x21860 "", .str.20 0x21880 F_badmodel, .str.21 0x218e0 S_ignore, .str.22 0x21900 F_badignore,
   .str.23 0x21960 S_knock, .str.24 0x21980 F_knock, .str.25 0x21a40 F_nokey, .str.33 .. .str.37 0x21ae0 ..
   0x21b60 S_auto S_master S_slave S_tap S_box, .str.38 0x21b80 S_yes, .str.39 0x21ba0 S_true, .str.41 0x21bc0
   S_no, .str.42 0x21be0 S_false (the symbols this function's objdump lines name, deduplicated: 35; the bytes
   read from the pin, each equal to its SegModel text), then refuse's three (refuse_c.v).
   IMAGE-INDEPENDENT: no image module is Required; A_reac_segconf_parse_file, STK_reac_segconf_parse_file, RLO,
   RHI, lit, cat, gotw and guard are parameters.
   The WALK takes these as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626): rows 1-15 at e45889d6935a,
   rows 16-17 and the RtString forms of rows 6, 7, 10 in the accepted v1 5e0b8a44fdc):
     RtString.astrlen_realizes (row 16, strlen 0x43a0c, 3 sites); RtSeg.astrchr_realizes (pc) (row 6, accepted at
     commit 80d098bd1905, lib/A/Rt/RtSeg.v:72; strchr 0x43a28, 3 sites: c = 0x0a, 0x5d, 0x3d);
     RtString.astrspn_realizes (row 2, strspn 0x43a30, pc gotw guard); RtSeg.astrncasecmp_realizes (pc) (row 7,
     RtSeg.v:92 at 80d098bd1905; strncasecmp 0x43a20, n = 7); RtSeg.astrcasecmp_realizes (pc) (row 10, RtSeg.v:152
     at 80d098bd1905; strcasecmp 0x43a1c, 8 sites); RtString.astrcmp_realizes (row 17, strcmp 0x43a14);
     RtPFSeg.seg_asnprintf_realizes (row 4, commit 755e9278f8ff RtPFSeg.v:228; snprintf 0x43a64,
     7 sites);
     astack_malloc_realizes 5 (row 14, kit YG0d.v:293, `__asan_stack_malloc_5` 0x3ea2c);
     RtStack.astack_free_cls_realizes (row 15, `__asan_stack_free_5` 0x3ec38, class 5);
     and, from the image-A owner's frame (the interface's "Not in this layer"): the kit's abcmp_realizes (YG0d.v:361;
     bcmp 0x43a38, 5 sites), aintrin_realizes OCpy and OSet (kit YG0d.v:326,
     `__asan_memcpy` 0x558e0, `__asan_memset` 0x55d7c), aset_shadow_realizes at 0x00 and 0xf8 (fuzz_command's
     RtShadow form, as its answer_c.v takes it; `__asan_set_shadow_00` 0x589dc, `_f8` 0x58afc),
     stack_malloc_progressP (the class-5 frame is released by the CALL of `__asan_stack_free_5` at 0x88c10,
     a1 = 0x480, which is RtStack.astack_free_cls_realizes 5 above; the inline-release laws astack_free_law /
     frame_flag_lawP that classes 0, 1 and 3 use are not what this function's release runs - corrected after
     the G3 walk lane's contract review, note N1);
     and the program callees: refuse_contract (lib/A/Prog/refuse_c.v, 11 sites), trim_contract
     (lib/A/Prog/trim_c.v, 5 sites), reac_box_catalogue_by_token_contract and reac_box_catalogue_contract
     (the G2 contracts lane's lib/A/Prog files, over the same table premise sa_cat at cat).
   They are NOT premises of this contract: the statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/reac_segconf_parse_file_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* The literals parse_file passes to an interceptor or to refuse (reac_segconf.c's module), in the order of their
   symbols .str .. .str.42, then those of its callee refuse. [SP; TAB; CR] is the strspn set " \t\r" (SegModel's
   blank), [124] the join's separator "|" and [] its first, empty separator. *)
Definition PARSE_FILE_LITS : list (list Z) :=
[F_s; S_base; [SP; TAB; CR]; F_long; F_notclosed; F_after; S_segment; F_unknown; F_noname; F_toolong; F_bound;
 F_twice; F_neither; F_outside; S_role; F_badrole; S_model; F_ss; [124]; []; F_badmodel; S_ignore; F_badignore;
 S_knock; F_knock; F_nokey; S_auto; S_master; S_slave; S_tap; S_box; S_yes; S_true; S_no; S_false] ++
REFUSE_LITS.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What every caller of the reader's parse supplies, all but the label (the plain reader_pre,
   lib/Prog/reac_segconf_parse_file_c.v:40-46, over the reader rd = aview segs (w_H W) mem): c is the reader's
   block, a live heap block of 16616 bytes holding rcs, addressable, its counters far from 2 ^ 32 (at most 65536
   lines a call); the text is the C string s with its slack, at most 65535 bytes, in a heap block, its bytes and
   NUL addressable, and its read span apart from the block; printf's machine (the rounding mode and the
   stack-protector cells); the box-model table at cat; the literals. The plain stack_ok / apart from [lo, sp) /
   blk_noimg / mem_inv / cat_img conjuncts are afn_pre's, sa_heap's, sa_lit's and sa_cat's here.
   Outside the sections: reader_pre segs B lit cat gotw guard ly S rd c t rcs s. *)
Definition reader_pre (lit : list Z -> Z) (cat gotw guard : Z) (ly : alayout) (S : astate) (rd : reader)
(c t : Z) (rcs : rconf) (s : list Z) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_rconf rd c rcs /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
sa_addr rd c seg_spec.SEG_C_SIZE /\
rc_gen rcs + 1 < 2 ^ 32 /\ rc_refused rcs + 2 ^ 17 < 2 ^ 32 /\ rc_overflow rcs + 2 ^ 17 < 2 ^ 32 /\
t <> 0 /\ sa_str rd t s /\ (length s <= 65535)%nat /\
sa_heap B ly S t (Z.of_nat (length s) + 1) /\ sa_addr rd t (Z.of_nat (length s) + 1) /\
sa_disj t (seg_spec.cstr_span t s) c seg_spec.SEG_C_SIZE /\
sa_frm0 /\ sa_ssp rd gotw guard /\ sa_cat segs B rd cat /\
(forall x, In x PARSE_FILE_LITS -> sa_lit segs B rd (lit x) x).
(* The plain reac_segconf_parse_file_pre (lib/Prog/reac_segconf_parse_file_c.v:48-56) over the reader: reader_pre
   and the label, NULL or a C string of at most 65535 bytes in a live heap block, a live side-stack frame or the
   image, its bytes and NUL addressable, its read span apart from c->reading (the snprintf destination that reads
   it). In the image case the label's addressability is asked at EVERY AR state (sa_pinned), not only at the
   entry: parse_file calls `__asan_stack_malloc_5` (0x87af0) before the snprintf that reads the label (0x87ce8),
   and the kit's astack_malloc_realizes (lib/Reusable/YG0d.v:293-308) keeps no byte of aowned B ly S, which holds
   the shadow of every image byte (aowned's lm_zone shadow, YG0n.v:236-242); the allocator record pins an image
   global's shadow at every AR state (fuzz_command's route, its lib/A/Prog/CmdRecBase.v cmd_addressable_chk at
   501c0d516c69), so the walk re-derives it from the AR the runtime entry's post gives. A heap label's shadow is
   AR's shadow_ok at every state; a live frame's bytes and shadow are client bytes, which the entry keeps.
   The image case also pins the label's TAIL at every AR state (sa_pinned_tail): the one image label is the
   harness's .bss longl (image A 0x5de680, 121 bytes), whose slack 0x5de6f9..0x5de6ff is a .bss redzone, an owned
   static, so the journal does not keep it. That slack IS readable through seg_rom (the rw .bss segment is in
   segs; corrected 2026-10-30 after the plain / UBSan owner's review - an earlier version of this comment said it was
   not ROM), so the harness states it as sa_romtail and its walk gives this premise by
   SegABase.sa_pinned_tail_of_romtail (SegABase.v, the comment on sa_romtail; found by the G3 contracts lane).
   Outside the sections: reac_segconf_parse_file_pre segs B lit cat gotw guard ly S rd c t lp rcs s lab. *)
Definition reac_segconf_parse_file_pre (lit : list Z -> Z) (cat gotw guard : Z) (ly : alayout) (S : astate)
(rd : reader) (c t lp : Z) (rcs : rconf) (s : list Z) (lab : option (list Z)) : Prop :=
reader_pre lit cat gotw guard ly S rd c t rcs s /\
sa_ostr rd lp lab /\
match lab with
| Some l =>
    (length l <= 65535)%nat /\
    (sa_heap B ly S lp (Z.of_nat (length l) + 1) \/ sa_fframe ly S lp (Z.of_nat (length l) + 1) \/
     (sa_img segs B lp (Z.of_nat (length l) + 1) /\ sa_pinned segs B lp (Z.of_nat (length l) + 1) /\
      sa_pinned_tail segs B (lp + Z.of_nat (length l)))) /\
    sa_addr rd lp (Z.of_nat (length l) + 1) /\
    sa_disj lp (seg_spec.cstr_span lp l) (c + seg_spec.RC_READING) 96
| None => True
end.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_reac_segconf_parse_file : Z := 0.
Definition reac_segconf_parse_file_contract
(A_reac_segconf_parse_file STK_reac_segconf_parse_file RLO RHI : Z) (lit : list Z -> Z) (cat gotw guard : Z)
: Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c t lp : Z) (rcs : rconf) (s : list Z) (lab : option (list Z)),
afn_pre segs B STK_reac_segconf_parse_file ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 t -> 0 <= t < 2 ^ 64 ->
getr regs 12 = w64 lp -> 0 <= lp < 2 ^ 64 ->
reac_segconf_parse_file_pre lit cat gotw guard ly S (aview segs (w_H W) mem) c t lp rcs s lab ->
(* room for the class-5 side-stack frame and, inside it, refuse's class-0 frame *)
sa_room_n 2 S ->
st_nev S + EV_reac_segconf_parse_file <= EV_MAX ->
SRr segs W (cfg_at segs A_reac_segconf_parse_file regs mem md)
(apost_baseF segs B STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W c) regs ly S W mem md
  EV_reac_segconf_parse_file
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (snd (SegModel.r_parse_file rcs s lab)) /\
 sa_rconf (aview segs (w_H W') mem') c (fst (SegModel.r_parse_file rcs s lab)) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
