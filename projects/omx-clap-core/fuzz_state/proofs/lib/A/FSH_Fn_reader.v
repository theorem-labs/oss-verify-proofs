(* fs program part, READER group: the ASan contract of each reader function of fuzz_state.asan, in S0's U form
   ((internal path) sections 0-3; lib/A/FSH_Gen.v fpreU / fpostU / wkeep, lib/A/FSH_Base.v's fs.asan numerals
   and STK_f). rule 24: no function proved. STATEMENTS ONLY: one spec per function, no walk, no lemma.
   (No double-quote character appears in the comments of this file: Rocq lexes strings inside comments.)
   Machine names are written qualified, YK11.getr and YG0d.cfg_at (FSH_Fn_FORM.md shadowed-name rule): lib.Lib.PropExec's
   getr / mkst / seg_rom are loaded through the released lib/Prog modules this file Requires, and are never Imported.

   SPECS (entry = FSH_Base.A_<f>; source = preset_file.c, pf.c below, of omx-clap-core 246923f04ac0):
     pj_parse_spec           0x82eac  pf.c:296-309  SUCCESS form on the harness document (narrow)     walk: a Theorem Labs lane
     parse_value_spec k      0x82f9c  pf.c:277-294  level-indexed k = 0..2, narrow success form         walk: a Theorem Labs lane
     parse_items_spec k      0x84a04  pf.c:211-264  level-indexed k = 0..1, objects only (narrow)       walk: a Theorem Labs lane
     parse_string_spec       0x850b8  pf.c:117-181  PLAIN-BYTE CASE ONLY                                walk: a Theorem Labs lane
     pj_set_spec             0x838e8  pf.c:373-391  success form, key absent (append arm)               walk: a Theorem Labs lane
     grow_spec               0x83a48  pf.c:42-63    success form (every allocation granted)             walk: a Theorem Labs lane
     pj_free_spec k          0x83570  pf.c:334-350  level-indexed k = 0..2                              walk: a Theorem Labs lane
     pj_get_spec             0x83720  pf.c:352-362                                                       walk: a Theorem Labs lane
     pj_get_str_spec         0x83868  pf.c:364-369                                                       walk: a Theorem Labs lane
     pj_string_spec          0x83be4  pf.c:406-411  success form, plain arm 1 (fs.c:242-247 aborts else) walk: a Theorem Labs lane
     pj_object_spec          0x83c9c  pf.c:433-437                                                       walk: a Theorem Labs lane
   OUT of the port (narrow-form ruling, a Theorem Labs lane 20:29Z): hex4, put_utf8, literal, parse_number. On the harness
   document their call sites are dead: parse_string's escape branch (pf.c:142-171, the only callers of hex4 and
   put_utf8) needs a backslash in a string, and literal / parse_number (pf.c:289-292) need a value that is not a
   string or an object. FS_DOC_STRS excludes both.

   THE STATICS IN FP (owner's 21:23Z form change; S0 7dd4849273a lib/A/FSPstat.v). ajournal's image clause spares
   inFP FP, and fuzz/alloc.c's statics (g_fail_at, g_live, g_peak, g_count) are FS_PSTAT_FP. Every function that writes
   them, directly or through a callee, states its post with its block footprint ++ FS_PSTAT_FP. These are the eight
   specs that allocate or free: parse_string (fuzz_malloc 0x85180), pj_string (fuzz_strdup 0x83c40), pj_free
   (fuzz_free 0x83634 / 0x83668 / 0x83680 / 0x8369c), grow (fuzz_realloc 0x83af4 / 0x83b44), pj_set (grow 0x8395c,
   fuzz_strdup 0x83994) and, through those callees, parse_items (grow, parse_string), parse_value (parse_string,
   parse_items) and pj_parse (parse_value). pj_get (strcmp only), pj_get_str (pj_get only) and pj_object
   (__asan_memset only) reach no allocator (dis, both images, a Theorem Labs lane) and carry no FS_PSTAT_FP. The shared-kit FP
   clause (FP composition, RELOC's YCbq / YC85 port) is not stated here; walks that need it wait for that port.

   FS_DOC_STRS (PROVED, not a hypothesis): lib/A/Prog/FSDocStrs.v FS_DOC_STRS (c3ed10a9332 on this branch), for every
   body bs with bytes_ok bs: (i) STRUCTURE fs_doc_values (fs_doc (b64_enc bs)), every value of the document
   fs.c:237-248 builds is a string or an object; (ii) CHARACTERS fs_doc_strings (fs_doc (b64_enc bs)), every key and
   string is plain_bytes (no byte below 0x20, no 0x22, no 0x5c). The narrow forms of pj_parse,
   parse_value and parse_items take the two clauses as premises; parse_value states clause (i) explicitly; the caller
   discharges them with FSDocStrs.FS_DOC_STRS.

   NAMED HYPOTHESES the walks take (a missing premise is invisible to Print Assumptions), with owner:
     pjw_succ           owner WRITER (a Theorem Labs lane), a separately named Definition in lib/A/FSH_Fn_writer.v
                        pj_parse's text premises are its clauses (rd_text + zbytes_at of
                        wdoc t pr ++ [0]); discharged at pj_parse's caller check_round_trip A 0x82244 from the released
                        plain st15 -> st16 chain plus pjw_succ. NEVER a Section hypothesis.
     fuzz_malloc_spec, fuzz_free_spec, fuzz_strdup_spec, fuzz_realloc_spec
                        owner ALLOC (a Theorem Labs lane), U form (FSupoisonU fs_heads): parse_string (fuzz_malloc), pj_string
                        and pj_set (fuzz_strdup), grow (fuzz_realloc), pj_free (fuzz_free).
     FS_AREALLOC_A      owner ALLOC (a Theorem Labs lane), lib/A/FSH_ReallocModel.v (54d232882e6):
                        arealloc_realizes_all at __wrap_realloc 0x53078 / trace ipc 0x535b0 (the malloc_context_size
                        = 30 branch, a Theorem Labs lane's correction on the originals; not 0x53594), for grow's two
                        fuzz_realloc calls. Open there (a Theorem Labs lane owns the n < 64513 sizes).
     aintrin_realizesU OSet PC_memset (0x521bc), OCpy PC_memcpy (0x51d20)
                        FSupoisonU's ARU form of the donor's __asan_memset / __asan_memcpy contracts (donor-walked):
                        pj_parse, parse_items, pj_set, pj_free, pj_string, pj_object (memset); pj_set (memcpy).
     fs_strcmp_realizesU : astrcmp_realizesU segs B PC_strcmp (0x4265c; FsRt.fr_strcmp)
                        owner RUNTIME (a Theorem Labs lane): pj_get, hence pj_get_str and pj_set.
     fs_strlen_realizesU : astrlen_realizesU segs B PC_strlen (0x42654; FsRt.fr_strlen)
                        owner RUNTIME (a Theorem Labs lane): reached only inside fuzz_strdup (ALLOC's walk).
     bcmp (donor aa_bcmp, YG0d.v:542): NOT needed; its only reader caller is literal, which is out.
     astack_malloc_realizesU 0 and the class-0 stack-free law
                        FSupoisonU statement / RUNTIME: parse_value's class-0 fake frame (call 0x8300c). Open point
                        FSH_Fn_FORM.md 7.1: the donor's law bundle admits classes 1, 2 only.
     fs_img_facts segs B  S0 (FSH_Rt.v), the Section hypothesis IMG below.

   THE FAKE FRAME OF parse_value (FSH_Fn_FORM.md section 2, open point for every fake-frame function). parse_value tests
   the use-after-return flag (AR_const_law: the flag reads 1) and calls __asan_stack_malloc_0 at 0x8300c; the other path
   is the real-stack probe and fallback 0x83018-0x8303c, which writes the real stack's shadow and which AR forbids. The
   walk MUST show the class-0 frame is granted: count_cid 0 (frames S) < fs_frames 0 (YG0d.v:287). parse_value_spec k
   carries Z.of_nat (length (frames S)) <= FRL_parse_value k = 2 + k <= 4, so count_cid 0 (frames S) <= 4 < 2 ^ 14 =
   fs_frames 0 (YG00.v:558, kStackSizeLog 20). The premise propagates: at level k parse_value pushes one frame, and
   parse_items / parse_value at level k + 1 take FRL_parse_value (k + 1). It is NOT trivial in the way RUNTIME found for
   check_round_trip's class 3: parse_value recurses, so the bound is per level and grows by one each level.

   THE CALLER'S REAL-STACK OBJECT (FSH_Fn_FORM.md 3(a), as corrected 21:15Z). pj_parse keeps `struct pj_in`
   (pf.c:30-34; {p 0, end 8, depth 16}, 24 bytes) on its REAL stack at its entry sp - 48 (dis: 0x82eac
   `addi sp,sp,-0x30`, 0x82ed0-0x82ed8 the three stores at 0(sp), 8(sp), 0x10(sp), 0x82eec `mv a0,sp`; no fake frame).
   parse_value, parse_items and parse_string write it above their own sp. Their posts run the window to `ot` (fpostU
   with STK_f + (ot - spZ regs) and top ot) and give the slack back with wkeep, exempting the WHOLE object, n = 24
   (parse_items writes in->p at nine sites and in->depth at three: 0x84a90, 0x84eb8, 0x84f60).
   `ot` is 16-aligned (ajournal's astk_ok,
   YCbq.v:331-333 / :367): struct pj_in ends at pj_parse's sp - 24 (8 mod 16), so pj_parse passes ot = its sp - 16 and
   wkeep covers the extra 8 bytes. The window premises are rd_win: ot mod 16 = 0, q + 24 <= ot, ot <= ly_top ly and
   [sp, ot) present. No stack address is bounded by alloc_ceiling anywhere in this file: afn_pre's astk_ok gives
   alloc_ceiling <= ly_stk_lo ly <= spZ regs, so such a bound would make a spec vacuous.
   `struct pj` objects (56 bytes) are never on a real stack: check_round_trip's are in its class-3 fake frame (RUNTIME:
   stack_malloc3_contract, no zero arm), tree nodes in heap blocks. They are `pobj`, with no wkeep (rule 4).
   cstr_ok / zbytes_at (FSH_Gen.v, with their alloc_ceiling bounds) are cited only at heap or image addresses: the keys
   of pj_set / pj_get / pj_get_str and pj_string's s (.rodata literals of FS_RO_STRS, or the encoder's text block),
   pj_parse's text (pj_write's block). None is a stack address.

   CALL RETURN ADDRESSES (MEASURED: capstone 5.0.7 over the pinned fs.asan, sha256
   64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0, every jal / j of 0x80f1c..0x85ebc whose target is
   a lane function; each is a 4-byte jal, ra = call + 4). Listed per spec as callers (call -> ra) and allocating /
   freeing callees (call -> ra). No reader spec takes a CTX parameter or an `In (raZ regs :: spine ch) CTX` premise
   (owner's ruling 2026-10-29 05:05Z via a Theorem Labs lane: that premise is unsatisfiable in a reachable state, and here it
   only fed allocator calls' CTX clauses, which now rest on C5's universe-or-budget disjunct).

   Ported from: a Theorem Labs lane's lib/A/FMH_Fn.v (form, a working branch a1902517c68 via S0); S0 a working branch
   0433af44ccd (names and numerals); fs released plain contracts lib/Prog/{pj_parse,parse_value,parse_items,
   parse_string,pj_set,grow,pj_free,pj_get,pj_get_str,pj_string,pj_object}_c.v at c8557374ad2 (functional premises and
   posts, NAMED: PjStruct.pj_node / pj_fd / pj_hdr / pj_slots_at / pj_zero / pj_cbytes, PjIn.pj_in_ok, ReaderRes.*,
   pj_set_c.set_trace); inputs a Theorem Labs lane's slice/reader5-posts.md (pj_free, pj_get, pj_get_str, pj_string, pj_object;
   the pobj proposal), (internal path) section 4 (parse_string plain-byte post,
   plain_run), a Theorem Labs lane's state-port/pj_set-grow-shape.md (pj_set / grow shape and caller-object writes). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require
WriterSpec WriterValue ReaderRes PjStruct PjIn pj_set_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= image-free helpers ================= *)
(* allocator ticks of a reader run: each event of the released trace is charged the call it is, not the dearest call
   (FSH_Gen.v: EV_fuzz_malloc = 1, EV_fuzz_free = 1, EV_fuzz_realloc = 3). An EAlloc is a fuzz_malloc (through
   fuzz_strdup for a string), 1. An EGrow carries its OLD request m: m = 0 is a fuzz_realloc of NULL, which tail-calls
   fuzz_malloc (fs.asan fuzz_realloc 0x829e8 `beqz a0` at 0x82a10 -> 0x82a50 -> `j 0x828ac` = fuzz_malloc), 1, and its
   room premise is the p = 0 arm of fuzz_realloc_spec (FSH_Fn_alloc.v, paired with a working branch
   4fa86c2ed0b); m <> 0 is a true reallocation, which ticks three times, 3. An EFree is one fuzz_free, 1. An EFail is a
   refusal inside failing() before any tick (EV_check_reject_clean_starved, FSH_Gen.v:82), charged the dearest call as
   an upper bound. *)
Definition rd_ev (tr : list PjGrammar.ev) : Z :=
  fold_right (fun e s =>
    match e with
    | PjGrammar.EAlloc _ => EV_fuzz_malloc
    | PjGrammar.EGrow m _ => if Nat.eqb m 0 then EV_fuzz_malloc else EV_fuzz_realloc
    | PjGrammar.EFree _ => EV_fuzz_free
    | PjGrammar.EFail _ => EV_fuzz_realloc
    end + s) 0 tr.
(* live bytes a reader run may add at its peak: each event's request + HEAD (frees only lower it) *)
Definition rd_live (tr : list PjGrammar.ev) : Z :=
  fold_right (fun e s => Z.of_nat (PjGrammar.esize e) + HEAD + s) 0 tr.
(* every request (HEAD + n, fuzz/alloc.c:28) fits the allocator's MALLOC_MAX (YG00.v:38) *)
Definition rd_sizes_ok (tr : list PjGrammar.ev) : Prop :=
  Forall (fun e => Z.of_nat (PjGrammar.esize e) + HEAD < MALLOC_MAX) tr.
(* a reader block (a, k) of a tree's block list (user pointer, request) is the ASan block (a - HEAD, k + HEAD) with the
   user-poisoned head (a - HEAD, HEAD) (fs_rblock, FSH_Gen.v) *)
Definition rd_heads (D : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b - HEAD, HEAD)) D.
Definition rd_hblocks (D : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b - HEAD, snd b + HEAD)) D.
Definition rd_sum (D : list (Z * Z)) : Z := fold_right (fun b s => snd b + s) 0 D.
(* U with the heads H removed, the rest in order (each fuzz_free removes its head as U1 ++ U2, FSupoisonU
   ARU_unpoison_any) *)
Definition hd_in (H : list (Z * Z)) (h : Z * Z) : bool :=
  existsb (fun g => (fst g =? fst h) && (snd g =? snd h)) H.
Definition udrop (U H : list (Z * Z)) : list (Z * Z) := filter (fun h => negb (hd_in H h)) U.
(* one fuzz_realloc (old, n) answering new: a NULL old goes to fuzz_malloc and only appends the new head; else the old
   head leaves U (disown) and the new one is appended (own) *)
Definition ugrow1 (U U' : list (Z * Z)) (old new : Z) : Prop :=
  (old = 0 /\ U' = U ++ [(new - HEAD, HEAD)]) \/
  (old <> 0 /\ exists U1 U2, U = U1 ++ (old - HEAD, HEAD) :: U2 /\ U' = U1 ++ U2 ++ [(new - HEAD, HEAD)]).
(* grow's allocation events (pf.c:48-58: realloc kids to 56 * cap', then keys to 8 * cap' for an object; the plain
   pj_set_c.set_trace's grow prefix, any type) *)
Definition grow_tr (ty n cap : Z) : list PjGrammar.ev :=
  if n =? cap then
    PjGrammar.EGrow (Z.to_nat (56 * cap)) (Z.to_nat (56 * ReaderRes.cap2 cap)) ::
    (if ty =? 6 then [PjGrammar.EGrow (Z.to_nat (8 * cap)) (Z.to_nat (8 * ReaderRes.cap2 cap))] else [])
  else [].
(* grow's result (plain grow_c.v:58-90, success arms only: every allocation is granted under `quiet`): the new kids /
   keys k' y', the new cap', the blocks freed (Dold) and made (Dnew) and the heads U -> U'. Type 6 is PJ_OBJECT
   (PjTree.tag); 56 = sizeof(struct pj), 8 = sizeof(char * ) *)
Definition grow_res (ty n cap kids keys k' y' cap' : Z) (Dold Dnew U U' : list (Z * Z)) : Prop :=
  (n < cap /\ k' = kids /\ y' = keys /\ cap' = cap /\ Dold = [] /\ Dnew = [] /\ U' = U) \/
  (n = cap /\ cap' = ReaderRes.cap2 cap /\
   Dold = ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap /\
   4096 + HEAD <= k' /\ k' mod 16 = 0 /\
   (ty = 6 -> 4096 + HEAD <= y' /\ y' mod 16 = 0) /\ (ty <> 6 -> y' = keys) /\
   Dnew = (k', 56 * cap') :: (if ty =? 6 then [(y', 8 * cap')] else []) /\
   exists Um, ugrow1 U Um kids k' /\ (if ty =? 6 then ugrow1 Um U' keys y' else U' = Um)).
(* parse_string's plain-byte case (a Theorem Labs lane section 4): the Q bytes after the opening quote at p are plain
   (FSH_Gen.plain_byte, the predicate of FS_DOC_STRS (ii): >= 0x20, not 0x22, not 0x5c) and the next byte is
   the closing quote (0x22 = 34); the run is what the copy holds *)
Definition plain_run (tb : list byte) (text len p Q : Z) : Prop :=
  0 <= Q /\ p + 1 + Q < text + len /\
  nth_error tb (Z.to_nat (p + 1 + Q - text)) = Some (Z_to_bv 8 34) /\
  (forall i, 0 <= i < Q -> exists c : byte,
     nth_error tb (Z.to_nat (p + 1 + i - text)) = Some c /\ plain_byte (bv_unsigned c)).
Definition run_at (tb : list byte) (text p Q : Z) : list Z :=
  ReaderRes.zb (firstn (Z.to_nat Q) (skipn (Z.to_nat (p + 1 - text)) tb)).
(* ticks and live bytes of the fixed-shape calls *)
Definition EV_pj_string : Z := EV_fuzz_strdup.                (* one fuzz_strdup, pf.c:410 *)
Definition EV_pj_free (D : list (Z * Z)) : Z := EV_fuzz_free * Z.of_nat (length D).
                                                              (* one fuzz_free per block; fuzz_free (NULL) returns
                                                                 before free (dis 0x82d54 `beqz a0`) *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
(* the image facts (FSH_Rt.v): a stated interface, proved once for fs's TfibB *)
Hypothesis IMG : fs_img_facts segs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= shared data premises ================= *)
(* a caller object in a live fake frame: the donor's afobj (cgif_file lib/YC20.v:86-89) verbatim; fs's raw core has no
   YC20.v and FSH_YC20.v copies only in_roP / arodata_okP / apost_base, so it is restated here *)
Definition fs_afobj (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
  (exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
     frame_addr ly cid pos <= p /\ p + n <= frame_addr ly cid pos + fs_frame_bytes cid) /\
  p mod 8 = 0 /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n.
(* where a `struct pj` (56 bytes) lives, the ONE placement predicate of the lane (a Theorem Labs lane's proposal, the ASan form
   of plain ReaderRes.rplace): in a live fake frame (check_round_trip's doc, state, v, back) or inside a live heap block
   past its 16-byte head (a kid), 8-aligned, addressable, writable *)
Definition pobj (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (v : Z) : Prop :=
  (fs_afobj ly S W mem v 56 \/
   ((exists b m, In (b, m) (ablocks B ly S) /\ b + HEAD <= v /\ v + 56 <= b + req_size m) /\
    v mod 8 = 0 /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56)) /\
  (forall i, 0 <= i < 56 -> writable_at segs (rdW W mem) (v + i)).
(* every block of a tree's list is a live reader block with its head user-poisoned (FSH_Gen.v fs_rblock) *)
Definition rd_blocks_ok (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (D : list (Z * Z)) : Prop :=
  forall a k, In (a, k) D -> fs_rblock segs B ly S W mem a k.
(* a tree node v holding t with blocks D, whose block relation is the live list UL (plain pj_node with lblk = lin) *)
Definition rnode (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (UL : list (Z * Z))
  (v : Z) (t : PjTree.jv) (D : list (Z * Z)) : Prop :=
  PjStruct.pj_node segs (rdW W mem) (fun a k => In (a, k) UL) v t D /\ rd_blocks_ok ly S W mem UL /\ incl D UL.
Definition rtree (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (v : Z) (t : PjTree.jv) (D : list (Z * Z)) : Prop :=
  rnode ly S W mem D v t D.
(* the text the reader parses: pjw_succ's block clauses (WRITER FSH_Fn_writer.v): a live reader block of cap bytes at
   text, the text shorter than it *)
Definition rd_text (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (text len tcap : Z) : Prop :=
  4096 + HEAD <= text /\ fs_rblock segs B ly S W mem text tcap /\ len < tcap.
(* the raised window of a callee that writes pj_parse's struct pj_in at q (24 bytes, above its sp): ot is 16-aligned
   and above the object, at most the stack top, and [sp, ot) is present; these and afn_pre's astk_ok at sp are what
   ajournal's astk_ok (STK + (ot - sp)) ly ot and window clause need (YCbq.v:331-333, :366-367) *)
Definition rd_win (regs : bvmap 5 word) (ly : alayout) (W : world segs) (mem : word -> option byte) (q ot : Z) : Prop :=
  spZ regs <= q /\ q + 24 <= ot /\ ot mod 16 = 0 /\ ot <= ly_top ly /\
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a).
(* n bytes at src are now at dst (plain grow_c.v:31-32 `moved`, over the ASan view) *)
Definition rd_moved (W W' : world segs) (mem mem' : word -> option byte) (src dst n : Z) : Prop :=
  forall i, 0 <= i < n -> mbyte segs (rdW W' mem') (dst + i) = mbyte segs (rdW W mem) (src + i).
(* pj_get's and pj_get_str's answers: plain pj_get_c.v:12-26 pj_get_hit / pj_get_res and pj_get_str_c.v:12-27
   pj_get_str_res, restated over `segs` because the released ones are fixed at the PLAIN image's rsegs (Img0), so they
   cannot be named over the ASan image; the text is otherwise theirs *)
Definition rd_get_hit (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : Z) (members : list (list Z * PjTree.jv))
  (D : list (Z * Z)) (kname : list Z) (z : Z) : Prop :=
  exists i v kids Di,
    nth_error members i = Some (kname, v) /\
    (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) /\
    PjStruct.pj_u64 segs m (o + 24) kids /\ z = kids + 56 * Z.of_nat i /\
    PjStruct.pj_node segs m lblk z v Di /\ incl Di D.
Definition rd_get_res (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : Z) (t : PjTree.jv) (D : list (Z * Z))
  (kname : list Z) (z : Z) : Prop :=
  match t with
  | PjTree.JObj members =>
      (forall nm u, In (nm, u) members -> nm <> kname) /\ z = 0 \/ rd_get_hit m lblk o members D kname z
  | _ => z = 0
  end.
Definition rd_get_str_res (m : word -> option byte) (lblk : Z -> Z -> Prop) (o : Z) (t : PjTree.jv)
  (D : list (Z * Z)) (kname : list Z) (z : Z) : Prop :=
  match t with
  | PjTree.JObj members =>
      (forall nm u, In (nm, u) members -> nm <> kname) /\ z = 0 \/
      exists i v kids,
        nth_error members i = Some (kname, v) /\
        (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) /\
        PjStruct.pj_u64 segs m (o + 24) kids /\
        match v with
        | PjTree.JStr s => PjStruct.pj_u64 segs m (kids + 56 * Z.of_nat i + 16) z /\
                           exists n, PjStruct.pj_cstr segs m lblk z n s /\ In (z, n) D
        | _ => z = 0
        end
  | _ => z = 0
  end.

(* ================= pj_parse (A 0x82eac), SUCCESS form on the harness document ================= *)
(* pf.c:296-309. Template: plain pj_parse_c.v:27-69, the `Some t` arm only (rule: pj_parse's only caller,
   check_round_trip fs.c:252, aborts otherwise). Its text is pj_write's output of a document t of depth <= 2
   (check_round_trip_stages_b.v:188-190 crt_doc_ok) satisfying FS_DOC_STRS; then json_read (wdoc t pr) = Some t
   (PjRoundTrip.G9) and the run's events are PjRoundTrip.ttrace t (jr_value_wdoc). struct pj_in is on its own real
   stack (inside [sp - STK_pj_parse, sp)); `out` (check_round_trip's back, class-3 fake frame) is written whole.
   Callers: check_round_trip 0x82244 -> 0x82248. Allocating / freeing callees: parse_value 0x82ef4 -> 0x82ef8 (level 0,
   window top ot = sp - 16); pj_free 0x82f78 -> 0x82f7c is the failure exit, dead here. __asan_memset 0x82ee8. *)
Definition pj_parse_spec : Prop :=
  forall ly S U W regs mem md ch t0 len out tcap (t : PjTree.jv) (pr : bool) live peak cnt fail,
  let tr := PjRoundTrip.ttrace t in
  fpreU segs B STK_pj_parse ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  YK11.getr regs 10 = w64 t0 -> YK11.getr regs 11 = w64 len -> YK11.getr regs 12 = w64 out ->
  (* the text: pjw_succ's clauses *)
  rd_text ly S W mem t0 len tcap -> zbytes_at segs W mem t0 (WriterValue.wdoc t pr ++ [0]) ->
  Z.of_nat (length (WriterValue.wdoc t pr)) = len ->
  (* the document: well formed, depth <= 2, FS_DOC_STRS (i) and (ii) *)
  PjRoundTrip.pj_wf ReaderRes.jr_strtod t -> (PjTree.depth t <= 2)%nat ->
  FSDocStrs.fs_doc_values t -> FSDocStrs.fs_doc_strings t ->
  (* the result object *)
  pobj ly S W mem out -> (out + 56 <= spZ regs - STK_pj_parse \/ spZ regs <= out) ->
  (out + 56 <= t0 - HEAD \/ t0 + tcap <= out) ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S + rd_ev tr <= EV_MAX -> blocks_bytes S + rd_live tr <= LIVE_MAX ->
  SRr segs W (YG0d.cfg_at segs A_pj_parse regs mem md)
    (fun W' c' => exists D Da,
       Permutation Da D /\
       fpostU segs B STK_pj_parse (spZ regs) ([(out, out + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md (rd_ev tr)
         (U ++ rd_heads Da)
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
            rtree ly' S' W' mem' out t D /\ rd_sum D = PjGrammar.held tr /\ (length D <= length tr)%nat /\
            pobj ly' S' W' mem' out /\
            rd_text ly' S' W' mem' t0 len tcap /\ zbytes_at segs W' mem' t0 (WriterValue.wdoc t pr ++ [0]) /\
            (exists peak', peak <= peak' /\
               fs_glob segs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail)) W' c').

(* ================= parse_value (A 0x82f9c), level k = 0..2, narrow success form ================= *)
(* pf.c:277-294. Template: plain parse_value_c.v:25-66 (`Some (t, r)` arm). Level k: k parse_value levels above,
   the value u of depth <= 2 - k is written at indent k, after the white space ws (the colon separator leaves one
   space before a member value); in->depth = k. FS_DOC_STRS's STRUCTURE clause is stated explicitly: u and every value
   in it is a string or an object, so parse_value dispatches only to parse_string (0x22, 0x831cc) and parse_items
   (0x7b, 0x832f4), and literal (0x83310), parse_number's fuzz_malloc (0x833cc) / __asan_memcpy (0x83400) and strtod
   (0x8343c) are dead.
   Class-0 fake frame 0x8300c: see the header; the frames premise is what discharges count_cid 0 (frames S) <
   fs_frames 0. Window: struct pj_in at q in pj_parse's frame, top ot (rd_win), wkeep over [sp, ot) except [q, q + 24).
   Callers: pj_parse 0x82ef4 -> 0x82ef8 (k = 0); parse_items 0x84d98 -> 0x84d9c (level k + 1).
   Allocating callees: parse_string 0x831cc -> 0x831d0; parse_items 0x832f4 -> 0x832f8 (k <= 1);
   __asan_stack_malloc_0 0x8300c -> 0x83010. *)
Definition parse_value_spec (k : nat) : Prop :=
  forall ly S U W regs mem md ch q ot v text len p (tb : list byte) tcap (u : PjTree.jv) (pr : bool)
    (ws rest : list Z) live peak cnt fail,
  let tr := PjRoundTrip.ttrace u in
  let wt := concat (WriterValue.wvpieces u pr (Z.of_nat k)) in
  (k <= 2)%nat ->
  fpreU segs B (STK_parse_value (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v ->
  PjIn.pj_in_ok segs (rdW W mem) q text len p (Z.of_nat k) tb -> rd_win regs ly W mem q ot ->
  (* the frame chain at q, which parse_string's C5 chain premise reads at the 0x831cc call (and parse_items'
     at its key call). Right arm (k = 0, caller pj_parse): q is this function's entry sp, and the chain at q
     is built by the prologue's saved ra / s0, so only the NEXT pointer s0 needs a bound. Left arm (k >= 1,
     caller parse_items): q lies above spZ regs and the chain is stated in the entry memory; s0Z regs = q there
     (parse_items' `mv s0, a0` 0x84a5c, s0 callee-saved, `mv a0, s0` 0x84d94), so the chain at the entry s0, which
     this function's own callees' fpreU extend, IS that chain (a Theorem Labs lane, 12:4xZ). In both, every
     record's NEXT pointer is a stop or >= q + 40, so its words (nfp - 8, nfp - 16 >= q + 24) lie outside
     struct pj_in [q, q + 24), which the walk writes. fp-chain records are (fp, ra, nfp), YG00.v:368-374. *)
  (q = spZ regs /\ (bad_next q (ly_top ly) (s0Z regs) = true \/ q + 40 <= s0Z regs) \/
   spZ regs + 16 <= q /\ s0Z regs = q /\ exists chq, achain ly (aview segs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
     Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  rd_text ly S W mem text len tcap ->
  (* the bytes at in->p: white space, then the writer's text of u *)
  ReaderRes.rest_at tb text p = ws ++ wt ++ rest -> Forall (fun c => PjGrammar.ws c = true) ws ->
  (* FS_DOC_STRS (i) STRUCTURE, explicit (= FSDocStrs.fs_doc_values u) *)
  (forall x, In x (u :: FSDocStrs.jv_vals u) -> FSDocStrs.str_or_obj x) ->
  (* FS_DOC_STRS (ii) CHARACTERS *)
  FSDocStrs.fs_doc_strings u ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod u -> (PjTree.depth u <= 2 - k)%nat ->
  (* the value object, zeroed by the caller (pj_parse's memset, parse_items' memset of the kid) *)
  pobj ly S W mem v -> PjStruct.pj_zero segs (rdW W mem) v ->
  (v + 56 <= spZ regs - STK_parse_value (2 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S + rd_ev tr <= EV_MAX -> blocks_bytes S + rd_live tr <= LIVE_MAX ->
  SRr segs W (YG0d.cfg_at segs A_parse_value regs mem md)
    (fun W' c' => exists D Da,
       Permutation Da D /\
       fpostU segs B (STK_parse_value (2 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md
         (rd_ev tr) (U ++ rd_heads Da)
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\
            PjIn.pj_in_ok segs (rdW W' mem') q text len (p + Z.of_nat (length ws) + Z.of_nat (length wt))
              (Z.of_nat k) tb /\
            wkeep segs W W' mem mem' (spZ regs) ot q 24 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
            rtree ly' S' W' mem' v u D /\ rd_sum D = PjGrammar.held tr /\ (length D <= length tr)%nat /\
            pobj ly' S' W' mem' v /\
            rd_text ly' S' W' mem' text len tcap /\
            (exists peak', peak <= peak' /\
               fs_glob segs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail)) W' c').

(* ================= parse_items (A 0x84a04), level k = 0..1, objects only ================= *)
(* pf.c:211-264. Template: plain parse_items_c.v:27-70 (`Some (t, r)` arm, o = true). Called by parse_value at level
   k with in->p at '{' (123) and in->depth = k; it raises in->depth to k + 1 for the members (pf.c:214), whose values
   it parses with parse_value at level k + 1, and lowers it back at '}'. Narrow: the object flag is 1 (no array on the
   harness document, FS_DOC_STRS (i)); keys and values are plain strings or objects, so its failure exits (fuzz_free
   0x84ecc, the ':' check) are dead. Frames: one more than parse_value at level k (its own class-0 frame).
   Callers: parse_value 0x832f4 -> 0x832f8. Allocating / freeing callees: grow 0x84b68 -> 0x84b6c and
   0x84e60 -> 0x84e64; parse_string 0x84c4c -> 0x84c50 (keys); parse_value 0x84d98 -> 0x84d9c; __asan_memset 0x84d78;
   fuzz_free 0x84ecc -> 0x84ed0 dead. *)
Definition parse_items_spec (k : nat) : Prop :=
  forall ly S U W regs mem md ch q ot v text len p (tb : list byte) tcap (ms : list (list Z * PjTree.jv))
    (pr : bool) (rest : list Z) live peak cnt fail,
  let tr := PjRoundTrip.ttrace (PjTree.JObj ms) in
  let wt := concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) in
  (k <= 1)%nat ->
  fpreU segs B (STK_parse_items (1 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok segs (rdW W mem) q text len p (Z.of_nat k) tb -> rd_win regs ly W mem q ot ->
  (* the frame chain at q for parse_string's C5 chain premise at the key call 0x84c4c and for parse_value
     (k + 1)'s left arm. Left arm only: the one caller, parse_value, always has its sp below q. Every record's
     NEXT pointer is a stop or >= q + 40, so the chain's words lie outside struct pj_in [q, q + 24). *)
  spZ regs + 16 <= q -> (exists chq, achain ly (aview segs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
    Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq) ->
  rd_text ly S W mem text len tcap ->
  ReaderRes.rest_at tb text p = wt ++ rest ->
  FSDocStrs.fs_doc_values (PjTree.JObj ms) -> FSDocStrs.fs_doc_strings (PjTree.JObj ms) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms) -> (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat ->
  pobj ly S W mem v -> PjStruct.pj_zero segs (rdW W mem) v ->
  (v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v) -> (v + 56 <= text - HEAD \/ text + tcap <= v) ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  rd_sizes_ok tr -> live + rd_live tr < 2 ^ 64 ->
  st_nev S + rd_ev tr <= EV_MAX -> blocks_bytes S + rd_live tr <= LIVE_MAX ->
  SRr segs W (YG0d.cfg_at segs A_parse_items regs mem md)
    (fun W' c' => exists D Da,
       Permutation Da D /\
       fpostU segs B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md
         (rd_ev tr) (U ++ rd_heads Da)
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\
            PjIn.pj_in_ok segs (rdW W' mem') q text len (p + Z.of_nat (length wt)) (Z.of_nat k) tb /\
            wkeep segs W W' mem mem' (spZ regs) ot q 24 /\
            Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
            rtree ly' S' W' mem' v (PjTree.JObj ms) D /\ rd_sum D = PjGrammar.held tr /\
            (length D <= length tr)%nat /\ pobj ly' S' W' mem' v /\
            rd_text ly' S' W' mem' text len tcap /\
            (exists peak', peak <= peak' /\
               fs_glob segs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail)) W' c').

(* ================= parse_string (A 0x850b8), PLAIN-BYTE CASE ONLY ================= *)
(* pf.c:117-181. Template: the third disjunct of plain parse_string_c.v:64-68, with decode = identity on a run
   without '\' (a Theorem Labs lane section 4). One fuzz_malloc of Q + 1 (0x85180), the copy loop, the NUL, in->p := p + Q + 2
   (0x85620); the new block's head joins U (rule 1: U' = U ++ [(a - 16, 16)]). The scan-None, decode-None (fuzz_free
   0x855b8) and refused-allocation arms are unreachable under the premises and dropped; hex4 (0x85494) and put_utf8
   (0x854cc) are not reached. Needs no runtime hypothesis; one allocator hypothesis, fuzz_malloc_spec (ALLOC).
   Window: struct pj_in at q in pj_parse's REAL frame (rd_win), wkeep over [sp, ot) except [q, q + 24).
   Callers: parse_value 0x831cc -> 0x831d0 (values); parse_items 0x84c4c -> 0x84c50 (keys).
   Allocating callees: fuzz_malloc 0x85180 -> 0x85184 (fuzz_free 0x855b8 -> 0x855bc dead). *)
Definition parse_string_spec : Prop :=
  forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q live peak cnt fail,
  fpreU segs B STK_parse_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  (* the fp chain fuzz_malloc's fpreU reads at the call 0x85180 (YCbq.v:341): s0 = q (0x850fc `mv s0, a0`, the only s0
     write before it), so the chain runs from q - 8, q - 16 upwards in pj_parse's frame; stated on fpreU's entry view.
     spZ regs + 16 <= q keeps those words above [spZ regs - FRAME_parse_string, spZ regs), which the prologue overwrites
     before the call, so the walk carries the entry chain to the call (rd_win gives only spZ regs <= q) *)
  (exists chq, achain ly (aview segs (w_H W) (unpoison U mem)) (spZ regs - FRAME_parse_string) q chq) ->
  spZ regs + 16 <= q ->
  YK11.getr regs 10 = w64 q ->
  PjIn.pj_in_ok segs (rdW W mem) q text len p d tb -> rd_win regs ly W mem q ot ->
  rd_text ly S W mem text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
  plain_run tb text len p Q ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail 1 ->
  Q + 1 + HEAD < MALLOC_MAX -> live + Q + 1 < 2 ^ 64 ->
  st_nev S + EV_fuzz_malloc <= EV_MAX -> blocks_bytes S + (Q + 1 + HEAD) <= LIVE_MAX ->
  SRr segs W (YG0d.cfg_at segs A_parse_string regs mem md)
    (fun W' c' => exists a,
       fpostU segs B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP regs ly S U W mem md EV_fuzz_malloc
         (U ++ [(a - HEAD, HEAD)])
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 a /\ 4096 + HEAD <= a /\
            ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] /\
            fs_rblock segs B ly' S' W' mem' a (Q + 1) /\
            PjStruct.pj_cbytes segs (rdW W' mem') a (run_at tb text p Q) /\
            PjIn.pj_in_ok segs (rdW W' mem') q text len (p + Q + 2) d tb /\
            wkeep segs W W' mem mem' (spZ regs) ot q 24 /\
            rd_text ly' S' W' mem' text len tcap /\
            fs_glob segs W' mem' (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail) W' c').

(* ================= grow (A 0x83a48), success form ================= *)
(* pf.c:42-63. Template: plain grow_c.v:34-90, success arms (n < cap; n = cap with every realloc granted). MEASURED
   (pj_set-grow-shape.md section 4): the released walk plus eight shadow checks; no fake frame; it writes through v
   only, at v + 0x18 (kids, 0x83b08), v + 0x20 (keys, 0x83b54) and v + 0x30 (cap, 0x83b64): FP is exactly those 24
   bytes ([v + 24, v + 40) and [v + 48, v + 56), as plain grow_c.v:16-19) plus the old kids / keys blocks, which
   fuzz_realloc frees. v is a pobj (check_round_trip's doc / state, or a heap kid under parse_items): no wkeep.
   Callers: pj_set 0x8395c -> 0x83960; parse_items 0x84b68 -> 0x84b6c and 0x84e60 -> 0x84e64.
   Allocating callees: fuzz_realloc 0x83af4 -> 0x83af8 (kids) and 0x83b44 -> 0x83b48 (keys, objects only). *)
Definition grow_spec : Prop :=
  forall ly S U W regs mem md ch v ty num str kids keys n cap live peak cnt fail,
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk ty keys cap in
  fpreU segs B STK_grow ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 v ->
  pobj ly S W mem v -> (v + 56 <= spZ regs - STK_grow \/ spZ regs <= v) ->
  PjStruct.pj_hdr segs (rdW W mem) v ty num str kids keys n cap ->
  PjStruct.pj_slots_at (fun a k => In (a, k) Dold0) ty kids keys n cap ->
  rd_blocks_ok ly S W mem Dold0 -> PjStruct.pj_apart Dold0 v -> incl (rd_heads Dold0) U ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail (Z.of_nat (length (grow_tr ty n cap))) ->
  (* live counts the live reader blocks' requests, and obj's own arrays are among them: fuzz_realloc's
     p <> 0 arm needs the old block's request k <= live (FSH_Fn_alloc.v), which nothing else here gives.
     Measured by the grow walk at 0x83af4 (k = 56 * cap) and 0x83b44 (k = 8 * cap, live already shifted
     by the first realloc). rd_sum [] = 0, so the cap = 0 path (p = 0) is unaffected. *)
  rd_sum Dold0 <= live ->
  (n = cap -> 56 * ReaderRes.cap2 cap + HEAD < MALLOC_MAX) -> live + rd_live (grow_tr ty n cap) < 2 ^ 64 ->
  st_nev S + rd_ev (grow_tr ty n cap) <= EV_MAX -> blocks_bytes S + rd_live (grow_tr ty n cap) <= LIVE_MAX ->
  SRr segs W (YG0d.cfg_at segs A_grow regs mem md)
    (fun W' c' => exists k' y' cap' Dold Dnew U',
       grow_res ty n cap kids keys k' y' cap' Dold Dnew U U' /\
       fpostU segs B STK_grow (spZ regs)
         ([(v + 24, v + 40); (v + 48, v + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP)
         regs ly S U W mem md (rd_ev (grow_tr ty n cap)) U'
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\
            Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B ly S ++ rd_hblocks Dnew) /\
            PjStruct.pj_hdr segs (rdW W' mem') v ty num str k' y' n cap' /\
            PjStruct.pj_slots_at (fun a k => In (a, k) (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk ty y' cap'))
              ty k' y' n cap' /\
            rd_blocks_ok ly' S' W' mem' (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk ty y' cap') /\
            rd_moved W W' mem mem' kids k' (56 * cap) /\ (ty = 6 -> rd_moved W W' mem mem' keys y' (8 * cap)) /\
            pobj ly' S' W' mem' v /\
            (exists peak', peak <= peak' /\
               fs_glob segs W' mem' (live + PjGrammar.held (grow_tr ty n cap)) peak'
                 (cnt + Z.of_nat (length (grow_tr ty n cap))) fail)) W' c').

(* ================= pj_set (A 0x838e8), success form, the key absent ================= *)
(* pf.c:373-391. Template: plain pj_set_c.v:32-108, the second disjunct (key absent, every allocation granted).
   Narrow: the key is absent from obj (fs.c:242-246 sets six distinct keys, three per object), so the hit path
   (pj_free (old) 0x8392c, memcpy over old) is dead, and under `quiet` the failure tail (pj_free (val) 0x83968) is
   dead. MEASURED (pj_set-grow-shape.md section 3): the released walk plus five shadow checks; no fake frame; it writes
   obj + 0x28 (n, 0x83a10), obj->keys[n] (heap, 0x839e4), obj->kids[n] (56 bytes, __asan_memcpy 0x8393c) and *val
   (56 bytes, __asan_memset 0x8394c); grow writes obj + 0x18 / 0x20 / 0x30. FP: [o + 24, o + 56) (kids, keys, n, cap),
   all of val, and the old kids / keys blocks (written at slot n, or freed by grow). obj and val are pobj
   (check_round_trip's class-3 frame; rule 4): no wkeep.
   Callers: check_round_trip 0x82150 -> 0x82154, 0x8217c -> 0x82180, 0x821a8 -> 0x821ac, 0x821d4 -> 0x821d8,
   0x821fc -> 0x82200, 0x82214 -> 0x82218. Allocating / freeing callees: grow 0x8395c -> 0x83960;
   fuzz_strdup 0x83994 -> 0x83998; pj_get 0x83920 -> 0x83924 (strcmp); pj_free 0x8392c -> 0x83930 and
   0x83968 -> 0x8396c dead. *)
Definition pj_set_spec : Prop :=
  forall ly S U W regs mem md ch o k w (ms : list (list Z * PjTree.jv)) (tv : PjTree.jv) D Dw num str kids keys n cap
    (kname : list Z) live peak cnt fail,
  let klen := Z.of_nat (length kname) in
  let tr := pj_set_c.set_trace n cap klen in
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap in
  fpreU segs B STK_pj_set ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 o -> YK11.getr regs 11 = w64 k -> YK11.getr regs 12 = w64 w ->
  (* obj: an object node with its header *)
  rtree ly S W mem o (PjTree.JObj ms) D -> pobj ly S W mem o ->
  PjStruct.pj_hdr segs (rdW W mem) o 6 num str kids keys n cap -> cap <= 2 ^ 54 -> incl (rd_heads Dold0) U ->
  (* val: any node, apart from obj (plain pj_set_c.v:42-45) *)
  rtree ly S W mem w tv Dw -> pobj ly S W mem w ->
  (forall bk, In bk Dw -> ~ In bk D) -> (forall x, w <= x < w + 56 -> ~ PjStruct.pj_foot o D x) ->
  PjStruct.pj_apart Dw o ->
  (o + 56 <= spZ regs - STK_pj_set \/ spZ regs <= o) -> (w + 56 <= spZ regs - STK_pj_set \/ spZ regs <= w) ->
  (* the key: a C string kept by the caller, apart from both trees (plain pj_set_c.v:47-51), and absent *)
  cstr_ok segs W mem k kname -> cstr_kept B ly S U k kname ->
  (forall x, k <= x < k + klen + 1 -> ~ PjStruct.pj_foot o D x /\ ~ PjStruct.pj_foot w Dw x) ->
  ~ In kname (map fst ms) ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail (Z.of_nat (length tr)) ->
  (* obj's own arrays are among the live reader blocks counted by live; pj_set hands this to grow
     unchanged (same obj, same live - pj_get and the stage B run do not touch the statics), and grow
     needs it for fuzz_realloc's p <> 0 arm (k <= live). rd_sum [] = 0, so cap = 0 is unaffected. *)
  rd_sum Dold0 <= live ->
  klen + 1 + HEAD < MALLOC_MAX -> (n = cap -> 56 * ReaderRes.cap2 cap + HEAD < MALLOC_MAX) ->
  live + rd_live tr < 2 ^ 64 ->
  st_nev S + rd_ev tr <= EV_MAX -> blocks_bytes S + rd_live tr <= LIVE_MAX ->
  SRr segs W (YG0d.cfg_at segs A_pj_set regs mem md)
    (fun W' c' => exists k' y' cap' Dold Dnew Dr Do Ug a,
       grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug /\
       Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ (a, klen + 1) :: Dr ++ Dw) /\
       fpostU segs B STK_pj_set (spZ regs)
         ([(o + 24, o + 56); (w, w + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP)
         regs ly S U W mem md (rd_ev tr) (Ug ++ [(a - HEAD, HEAD)])
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\ 4096 + HEAD <= a /\
            Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B ly S ++ rd_hblocks (Dnew ++ [(a, klen + 1)])) /\
            rtree ly' S' W' mem' o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do /\
            PjStruct.pj_zero segs (rdW W' mem') w /\
            pobj ly' S' W' mem' o /\ pobj ly' S' W' mem' w /\ cstr_ok segs W' mem' k kname /\
            (exists peak', peak <= peak' /\
               fs_glob segs W' mem' (live + PjGrammar.held tr) peak' (cnt + Z.of_nat (length tr)) fail)) W' c').

(* ================= pj_free (A 0x83570), level k = 0..2 ================= *)
(* pf.c:334-350. Template: plain pj_free_c.v:26-44. Level k: k pj_free frames above (self call 0x83608), the tree is
   freeable at depth 2 - k (PjStruct.pj_fd; a pj_node tree of depth <= 2 is pj_fd at its depth, PjStruct.pj_node_fd).
   One fuzz_free per block of D; each removes its head from U (U' = udrop U (rd_heads D), rule 1); v is zeroed
   (__asan_memset 0x836ac). v is a pobj: no wkeep (rule 4).
   Callers: check_round_trip 0x822b0 -> 0x822b4 (back), 0x822b8 -> 0x822bc (doc); pj_free 0x83608 -> 0x8360c (level
   k + 1); pj_parse 0x82f78 and pj_set 0x8392c / 0x83968 are dead (success forms).
   Freeing callees: fuzz_free 0x83634 -> 0x83638, 0x83668 -> 0x8366c, 0x83680 -> 0x83684, 0x8369c -> 0x836a0. *)
Definition pj_free_spec (k : nat) : Prop :=
  forall ly S U W regs mem md ch v D live peak cnt fail,
  (k <= 2)%nat ->
  fpreU segs B (STK_pj_free (2 - k)) ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 v ->
  (v = 0 /\ D = [] \/
   v <> 0 /\ PjStruct.pj_fd segs (rdW W mem) (fun a n => In (a, n) D) (2 - k) v D /\ pobj ly S W mem v /\
   (v + 56 <= spZ regs - STK_pj_free (2 - k) \/ spZ regs <= v)) ->
  rd_blocks_ok ly S W mem D -> incl (rd_heads D) U ->
  fs_glob segs W mem live peak cnt fail -> rd_sum D <= live ->
  st_nev S + EV_pj_free D <= EV_MAX ->
  SRr segs W (YG0d.cfg_at segs A_pj_free regs mem md)
    (fpostU segs B (STK_pj_free (2 - k)) (spZ regs) ((v, v + 56) :: ablocks_fp (rd_hblocks D) ++ FS_PSTAT_FP)
       regs ly S U W mem md
       (EV_pj_free D) (udrop U (rd_heads D))
       (fun ly' S' W' regs' mem' md' =>
          Permutation (ablocks B ly S) (rd_hblocks D ++ ablocks B ly' S') /\
          (v <> 0 -> PjStruct.pj_zero segs (rdW W' mem') v /\ pobj ly' S' W' mem' v) /\
          fs_glob segs W' mem' (live - rd_sum D) peak cnt fail)).

(* ================= pj_get (A 0x83720) ================= *)
(* pf.c:352-362. Template: plain pj_get_c.v:28-51 (answer rd_get_res, the segs-generic pj_get_res). No allocation,
   no write outside its frame: U' = U, FP = [], 0 ticks. The strcmp interceptor reads each key and the needle
   (fs_strcmp_realizesU, RUNTIME). o is check_round_trip's back (fake frame), pj_get_str's argument (a heap kid), or
   pj_set's obj; UL is the caller's live block list (a superset of D).
   Callers: check_round_trip 0x82258 -> 0x8225c; pj_get_str 0x83880 -> 0x83884; pj_set 0x83920 -> 0x83924.
   Runtime callee: strcmp 0x837d0 -> 0x837d4.
   The needle k carries cstr_kept beside cstr_ok, in pj_set_spec's shape (R1 kept-buffer ruling, integrator 23:08Z; the
   B pair states it the same way). *)
Definition pj_get_spec : Prop :=
  forall ly S U W regs mem md ch o k (kname : list Z) (t : PjTree.jv) D UL live peak cnt fail,
  fpreU segs B STK_pj_get ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 o -> YK11.getr regs 11 = w64 k ->
  (o = 0 \/ rnode ly S W mem UL o t D /\ pobj ly S W mem o) ->
  cstr_ok segs W mem k kname -> cstr_kept B ly S U k kname ->
  fs_glob segs W mem live peak cnt fail ->
  SRr segs W (YG0d.cfg_at segs A_pj_get regs mem md)
    (fpostU segs B STK_pj_get (spZ regs) [] regs ly S U W mem md 0 U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ cstr_ok segs W' mem' k kname /\ cstr_kept B ly' S' U k kname /\
          fs_glob segs W' mem' live peak cnt fail /\
          (o = 0 /\ YK11.getr regs' 10 = w64 0 \/
           o <> 0 /\ rnode ly' S' W' mem' UL o t D /\
           exists z, YK11.getr regs' 10 = w64 z /\ rd_get_res (rdW W' mem') (fun a n => In (a, n) UL) o t D kname z))).

(* ================= pj_get_str (A 0x83868) ================= *)
(* pf.c:364-369. Template: plain pj_get_str_c.v:29-52 (answer rd_get_str_res). Calls pj_get only.
   Callers: check_round_trip 0x82264 -> 0x82268. Callee: pj_get 0x83880 -> 0x83884.
   The needle k carries cstr_kept beside cstr_ok, as in pj_get_spec (R1 kept-buffer ruling). *)
Definition pj_get_str_spec : Prop :=
  forall ly S U W regs mem md ch o k (kname : list Z) (t : PjTree.jv) D UL live peak cnt fail,
  fpreU segs B STK_pj_get_str ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 o -> YK11.getr regs 11 = w64 k ->
  (o = 0 \/ rnode ly S W mem UL o t D /\ pobj ly S W mem o) ->
  cstr_ok segs W mem k kname -> cstr_kept B ly S U k kname ->
  fs_glob segs W mem live peak cnt fail ->
  SRr segs W (YG0d.cfg_at segs A_pj_get_str regs mem md)
    (fpostU segs B STK_pj_get_str (spZ regs) [] regs ly S U W mem md 0 U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ cstr_ok segs W' mem' k kname /\ cstr_kept B ly' S' U k kname /\
          fs_glob segs W' mem' live peak cnt fail /\
          (o = 0 /\ YK11.getr regs' 10 = w64 0 \/
           o <> 0 /\ rnode ly' S' W' mem' UL o t D /\
           exists z, YK11.getr regs' 10 = w64 z /\ rd_get_str_res (rdW W' mem') (fun a n => In (a, n) UL) o t D kname z))).

(* ================= pj_string (A 0x83be4), success form ================= *)
(* pf.c:406-411. Template: plain pj_string_c.v:26-56, arm 1 only (fs.c:242-247 aborts on any other). memset of v
   (0x83c14), type 4 = PJ_STRING (PjTree.tag), str := fuzz_strdup of s, or of the empty literal FS_RO_STRS 0x21020 when
   s is NULL (0x83c40).
   The new block's head joins U (rule 1). v is a pobj (check_round_trip's v): no wkeep (rule 4).
   Callers: check_round_trip 0x82138 -> 0x8213c, 0x82164 -> 0x82168, 0x82190 -> 0x82194, 0x821bc -> 0x821c0,
   0x821e4 -> 0x821e8. Allocating callees: fuzz_strdup 0x83c40 -> 0x83c44. *)
Definition pj_string_spec : Prop :=
  forall ly S U W regs mem md ch v s (cs : list Z) live peak cnt fail,
  let n := Z.of_nat (length cs) + 1 in
  fpreU segs B STK_pj_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 v -> YK11.getr regs 11 = w64 s ->
  pobj ly S W mem v -> (v + 56 <= spZ regs - STK_pj_string \/ spZ regs <= v) ->
  (s = 0 /\ cs = [] \/
   s <> 0 /\ cstr_ok segs W mem s cs /\ cstr_kept B ly S U s cs /\ (s + n <= v \/ v + 56 <= s)) ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail 1 ->
  n + HEAD < MALLOC_MAX -> live + n < 2 ^ 64 ->
  st_nev S + EV_pj_string <= EV_MAX -> blocks_bytes S + (n + HEAD) <= LIVE_MAX ->
  SRr segs W (YG0d.cfg_at segs A_pj_string regs mem md)
    (fun W' c' => exists a,
       fpostU segs B STK_pj_string (spZ regs) ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md EV_pj_string
         (U ++ [(a - HEAD, HEAD)])
         (fun ly' S' W' regs' mem' md' =>
            YK11.getr regs' 10 = w64 0 /\ 4096 + HEAD <= a /\
            ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, n + HEAD)] /\
            rtree ly' S' W' mem' v (PjTree.JStr cs) [(a, n)] /\ pobj ly' S' W' mem' v /\
            fs_glob segs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c').

(* ================= pj_object (A 0x83c9c) ================= *)
(* pf.c:433-437. Template: plain pj_object_c.v:10-26 (its post: type 6 = PJ_OBJECT, the rest zero, i.e. the empty
   object node). memset of v (0x83cc4); no allocation: U' = U, 0 ticks. v is a pobj: no wkeep (rule 4).
   Callers: check_round_trip 0x82120 -> 0x82124 (doc), 0x82128 -> 0x8212c (state). *)
Definition pj_object_spec : Prop :=
  forall ly S U W regs mem md ch v live peak cnt fail,
  fpreU segs B STK_pj_object ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 v ->
  pobj ly S W mem v -> (v + 56 <= spZ regs - STK_pj_object \/ spZ regs <= v) ->
  fs_glob segs W mem live peak cnt fail ->
  SRr segs W (YG0d.cfg_at segs A_pj_object regs mem md)
    (fpostU segs B STK_pj_object (spZ regs) [(v, v + 56)] regs ly S U W mem md 0 U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\
          rtree ly' S' W' mem' v (PjTree.JObj []) [] /\ pobj ly' S' W' mem' v /\
          fs_glob segs W' mem' live peak cnt fail)).

End c.
