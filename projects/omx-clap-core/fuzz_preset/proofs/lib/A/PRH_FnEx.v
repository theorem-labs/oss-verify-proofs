(* fuzz_preset, program part (the kit's ex texts): the ASan contract TEXTS of the harness's expected-text parser and its
   tree comparison (fuzz_preset.c @8f3e7e1a07 :92-356): same, ex_value (with ex_number and ex_items inlined), ex_string,
   ex_word, ex_hex4, ex_utf8 and ex_ws (out of line in image B only; image A inlines it), in cgif's per-function form
   (cgif_file lib/YC21.v:33-66; the fm port's FMH_Fn.v:101-180), as lib/A/PRH_FnAlloc.v states it: fpre (YCbqG's afn_pre_x +
   the read-only view), argument registers, the alloc.c ledger (PRH_Base.v prh_ledger, restated with the same values:
   none of these functions reaches the allocator or writes a static, the internal file calls-A.tsv / the internal file calls-B.tsv), and SRr to the return
   address. Every conclusion is `srealizes` through SRr (lib/Reusable/YA0n.v:38-41).
   IMAGE-PARAMETRIC: segments pa_segs, entries pa_sigma AS_<fn>, frames STK_<fn> (PRH_Base.v; STK_ex_value's per-level
   frame carries the 16 bytes of its `andi sp, sp, -32` realignment, pi_frame since d1737d5887e). No image constant.
   ALLOCATOR-PARAMETRIC: ARx is an explicit argument.
   FUNCTIONAL CONTENT: preset's released plain contracts lib/Prog/{ex_value,ex_string,ex_word,ex_hex4,same}_c.v,
   restated (their pure models only: PjGrammar.jr_value / jr_string / scan / skip / hex4 / utf8 with ReaderRes.jr_strtod,
   = plain ex_value_c.ex_sm; PRH_Reader.v's pj_nodeR / pj_footR, the kit's one tree predicate, over
   mrestrict (w_H W) mem with lblk prh_lin Lam; PjTree.jv).
   No plain lemma is cited. ex_utf8 HAS NO RELEASED PLAIN CONTRACT: its text is stated from fuzz_preset.c :157-183
   (the four RFC 3629 arms) = PjGrammar.utf8 for cp < 2 ^ 21, and checked against both images' bodies (A 0x84764, B
   0x84b54: frame 16, one ASan-checked `sb` per byte written, a0 = the byte count). Every pc here is at the #102 pin.
   THE CALLER'S CURSOR. `struct ex` (p +0, end +8, depth +16 int, scratch +24, differs +32 int; 40 bytes) lives on
   check_as_written's real stack (A 0x82010 `addi a0, sp, 8`; no fake frame there), above the entry sp of every
   function here that writes it (ex_value at every nesting, ex_string, ex_word, ex_ws), and ex_hex4's out-parameter
   is ex_string's stack slot (A 0x84178 / 0x841f0, B 0x844a8 / 0x84544: sp + 36, sp + 32). The plain journal keeps
   every byte above the entry sp, so these texts take the kit's caller-window post fpostW / fpostWF over fwin d (FMH
   readings_spec's form): the written caller cells are IN FP, every other byte of [sp, sp + d) is kept, and each arm
   states the written cells' values (or that they are unchanged).
   THE SCRATCH is check_as_written's __wrap_malloc (size + 1) block (A 0x81ff4): an allocator block outside Lam, so
   the FP of ex_value / ex_string / ex_utf8 names its bytes. The text bytes `data` lie in an allocator block too (the
   plain check_as_written's caw_inside, ablocks for blocks L A).
   WHERE A BYTE LIVES (prhex_inblk, prhex_home): a byte read or written AFTER an intervening program call needs a home
   whose shadow facts survive the call's journal: a live allocator block outside its hidden head (AR_laws_x's
   alx_shadow), a live fake frame (ajournal_x keeps a frame's bytes and their shadow), or the real stack above the
   entry sp (alx_zshadow, YCbqG ea24ad37a3c: the head of zero_shadow_ranges is [ly_stk_lo, ly_stk_hi), YG0n.v:188-189,
   and astk_ok with fwin puts the caller's cells there). These are laws a walk cites, not premises of these texts.
   Runtime calls (strlen, strcmp, bcmp, __asan_memcpy, strtod) keep every byte off their stack window and written cells
   (abcmp_realizes YG0d.v:383, aintrin_realizes :347, YStrtodRowX.v:377-379), so no home is asked for those bytes.
   NAMED GAPS (runtime shapes these texts' walks need, not stated here):
   - EX-STRTOD-END: ex_value calls musl strtod (scratch, &end) with `end` in its own class-1 fake frame (frame + 32,
     A 0x83310 frame_alloc_1 (96)). OWNED AND PROVED: lib/Reusable/YStrtodRowX.v @ 5a1376f3c69 (the leaf-lemma author), whose
     strtod_site_x (:347) carries the single agreed entry name aj_memnorm (:344) and whose astrtod_realizes_x (:354)
     states this call site: *e = s + c in a live fake frame, fa0 = bits, errno and its window may change, frm_zero,
     fs0-fs11 kept.
   - EX-LIT-SHADOW: ex_value passes ex_word the literals "true" / "false" / "null" (.rodata .str.N); ex_word's
     cstr_ok premise at those call sites needs their shadow, i.e. each literal in as_zero_shadow B (in_zs) or another
     image fact; the literal addresses are image facts of the walk, not premises of tex_value_specX. The premise
     STANDS: ex_word's first call is strlen (A 0x84578, B 0x84920), whose call rule (YGcallMx aj_strlen_at_x) asks
     first_byte, src_ok, amem_range8, range_addressable and shadow_hull_vis over len + 1 and the tail granule visible
     - cstr_ok's conjuncts (the S8b walk, measured on the rule). The reader `literal` takes cstr_ok for the same reason: it
     calls strlen, then bcmp (PRH_FnReader.v:320-324; lib/A/Prog/literal_inst.v:18-20). So only the
     literals' SHADOW is the gap, not the whole premise. CLOSED 2026-10-29: a walk discharges ex_word's cstr_ok at a
     literal by PRH_Base.cstr_ok_ro (the S1 owner's YGcallRoStr.ro_cstr_x), its image premise decided by
     YGcallRoStr.ro_str_check / ro_str_check_ok (vm_compute); the literal's shadow is ro_str_img's, no named hypothesis.
   - EX-FRAME-1: ex_value's frame_alloc_1 must return a frame (the 96-byte alloca + 4096-byte probe arm runs only on a
     NULL return): tex_value_specX asks count_cid 1 (frames S) + S n <= fs_frames 1, astack_malloc_realizes 1's own
     premise at every nesting (YG0d.v:297-300).
   - EX-WS-A: ex_ws has no symbol in image A (inlined); tex_ws_specX is image B's (town_specX's case).
   - EX-HBLK-SHADOW (= the Pj part's G-Pj1): the tree's nodes below the root, its key arrays and its strings lie in live
     harness blocks, whose base is a hidden head (in Hp), so AR_laws_x's alx_shadow does not cover them. Their user
     bytes' shadow comes from the instance's head-shadow law (the allocator-model owner's AR_head_shadow_cf: shadow 0 on [a + cf_head,
     a + req_size n)). The walks need it for the nested ex_value / same calls' root shadow (prhex_tree's
     range_addressable of a kid) and for the strcmp / bcmp reads of a node's strings and number bits. No text premises
     it (the Pj part's convention).
   - H_EXV_SCR_RANGE (ex_value's strcmp(v->str, in->scratch), A 0x8397c; MEASURED a CANNOT from the kit's laws): the
     engine's strcmp rule asks YGcfStr.amem_range8 over each string, whose high-memory start bound
     kHighMemBeg + 15 <= p does not follow for the scratch: prhex_inblk scr (len + 1) is check_as_written's block,
     outside Lam, with no hidden head, and the blocks law admits a block at exactly kHighMemBeg (CfParamsPreset.v:98's
     preset_place_ok is only the ASan owner's counting condition, no lower bound). The walk carries ONE marked hypothesis at
     that site, `H_EXV_SCR_RANGE : YGcfStr.amem_range8 scr (Z.of_nat (length cs) + 1)`, whose DISCHARGE is
     the allocator-model owner's block_amem_range8_cf (lib/Reusable/YGcfBlockRange.v: the chunk extent lies in one app region and the
     user pointer is the chunk base + ck_rz with ck_rz >= 16, so a high user pointer is >= kHighMemBeg + 16). If ARcf
     cannot give it, it goes to the A top's open list (the kit owner). cstr_ok and amem_range8 are NOT widened for it.
   room: room_live_cf (PRH_Base.v, owned by the allocator-model owner), room_cf at none (no function here calls the allocator, so each
   post carries room_live_cf S -> room_live_cf S'); margins removed.
   Statements only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure model ---- *)

(* the grammar's reading of a value at nesting d (plain ex_value_c.v:20-21 ex_V, its ex_sm being ReaderRes.jr_strtod):
   None when the grammar refuses, else the tree and the rest of the text *)
Definition prhex_V (d : Z) (xs : list Z) : option (PjTree.jv * list Z) :=
  fst (fst (PjGrammar.jr_value ReaderRes.jr_strtod (Z.to_nat d) xs [])).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- where bytes live, unchanged cells, the cursor ---- *)

(* [a, a + n) inside a live allocator block, outside its head when the head is hidden (the plain caw_inside over
   ablocks, check_as_written_c.v:39-40) *)
Definition prhex_inblk (ly : alayout) (S : astate) (Hp : list Z) (a n : Z) : Prop :=
  exists b m, In (b, m) (ablocks B ly S) /\ b <= a /\ a + n <= b + m /\ (In b Hp -> b + cf_head <= a).

(* a tree node's home: inside a live harness block (a kid), inside a live fake frame (LLVMFuzzerTestOneInput's doc), or
   on the real stack above the entry sp (a caller's local) *)
Definition prhex_home (ly : alayout) (S : astate) (Lam : list (Z * Z)) (regs : bvmap 5 word) (p n : Z) : Prop :=
  (exists b m, In (b, m) Lam /\ b <= p /\ p + n <= b + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= p /\
     p + n <= frame_addr ly cid pos + fs_frame_bytes cid) \/
  (spZ regs <= p /\ p + n <= ly_stk_hi ly).

(* a tree at p: the plain representation (lblk = the harness blocks), its root at home, the root's 56 bytes
   addressable, and the root's 56-byte HULL VISIBLE (every shadow byte of the granules [p, p + 56) present in the view;
   the memnorm-runner author's fact HVHULL, commit da73e1570f87 lib/A/Prog/S8aNumber.v:62-64, which
   its ev_number arm needs at ex_value's mid states and which no kit law gives: CONSUMER: the memnorm-runner author). Every home
   supplies it: a Lam block by alx_hshadow (field 14) / AR_shadow_law, a fake frame by alx_frames (its shadow present),
   the real stack by alx_zshadow_byte. *)
Definition prhex_tree (ly : alayout) (S : astate) (Lam : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (p : Z) (t : PjTree.jv) (D : list (Z * Z)) : Prop :=
  PRH_Reader.pj_nodeR segs (rdW W mem) (prh_lin Lam) p t D /\ prhex_home ly S Lam regs p 56 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 56 /\
  shadow_hull_vis (aview segs (w_H W) mem) p 56.

(* the n bytes at a unchanged from (W, mem) to (W', mem') (a cell in FP that an arm does not write) *)
Definition prhex_same (W : world segs) (mem : word -> option byte) (W' : world segs) (mem' : word -> option byte)
  (a n : Z) : Prop :=
  forall z, a <= z < a + n -> aview segs (w_H W') mem' z = aview segs (w_H W) mem z.

(* the struct ex cursor at q (fuzz_preset.c :117-123) *)
Definition prhex_cur (W : world segs) (mem : word -> option byte) (q p e dep scr dl : Z) : Prop :=
  val_mem segs (rdW W mem) q 8 p /\ val_mem segs (rdW W mem) (q + 8) 8 e /\
  val_mem segs (rdW W mem) (q + 16) 4 dep /\ val_mem segs (rdW W mem) (q + 24) 8 scr /\
  val_mem segs (rdW W mem) (q + 32) 4 dl.

(* the entry frame chain survives any change of [q, q + n): fpre's achain read through any reader that agrees with
   the entry view outside [q, q + n). ex_value writes in->p / depth / differs and then makes program calls (ex_string,
   ex_word, ex_ws in B, itself), whose call rule (aj_call_xWF) takes achain at the call from ex_value's own record
   down to this entry chain (the S8a walk's S8aDisp, measured). The form holds in both callers without fixing the chain's
   direction: from check_as_written s0 holds rc (no frame pointer, A 0x81fd0), so achain's left disjunct, ch = [],
   reads nothing; from ex_value every record lies in an ex_value frame BELOW check_as_written's sp, so below q. *)
Definition prhex_ch_apart (ly : alayout) (W : world segs) (mem : word -> option byte) (regs : bvmap 5 word)
  (ch : list (Z * Z * Z)) (q n : Z) : Prop :=
  forall rd' : reader, (forall a, ~ (q <= a < q + n) -> rd' a = aview segs (w_H W) mem a) ->
  achain ly rd' (spZ regs) (s0Z regs) ch.

(* ---- the leaves ---- *)

(* ex_hex4 (fuzz_preset.c :136-155; plain ex_hex4_c.v): the four bytes at p as a hex number; on success *out = it
   (one 4-byte store), else nothing written. out is the caller's (ex_string's) stack slot above the entry sp, so the
   post is the caller-window one with [out, out + 4) in FP. The bytes are a window of the text (ex_string checks four
   remain). *)
Definition tex_hex4_specX : Prop :=
  forall ly S Hp W regs mem md ch (p out d : Z) (bs : list Z) Lam peak cnt fail ran most own,
  fpre B ARx STK_ex_hex4 ly S Hp W regs mem md ch ->
  getr regs 10 = w64 p -> getr regs 11 = w64 out ->
  src_rd W mem p bs -> prhex_inblk ly S Hp p 4 -> length bs = 4%nat ->
  out mod 4 = 0 -> spZ regs <= out -> out + 4 <= spZ regs + d -> fwin ly W regs mem d ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_ex_hex4) regs mem md)
    (fpostWm B ARx SK STK_ex_hex4 d [(out, out + 4)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       match PjGrammar.hex4 bs with
       | Some v => getr regs' 10 = w64 0 /\ val_mem segs (rdW W' mem') out 4 v
       | None => getr regs' 10 = w64 (-1) /\ prhex_same W mem W' mem' out 4
       end)).

(* ex_utf8 (fuzz_preset.c :157-183; NO released plain contract, stated from the source): cp as UTF-8 (RFC 3629) at o,
   returning the byte count. For cp < 2 ^ 21 the C arms are PjGrammar.utf8 cp byte for byte (and the register a1 is
   w64 cp: bit 31 clear, so the int sign extension changes nothing). o is the scratch (inside an allocator block), so
   its bytes are the footprint. *)
Definition tex_utf8_specX : Prop :=
  forall ly S Hp W regs mem md ch (o cp : Z) Lam peak cnt fail ran most own,
  let k := Z.of_nat (length (PjGrammar.utf8 cp)) in
  fpre B ARx STK_ex_utf8 ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 0 <= cp < 2 ^ 21 ->
  wdest_ok B STK_ex_utf8 ly S W regs mem o k -> prhex_inblk ly S Hp o k ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_ex_utf8) regs mem md)
    (fpostm B ARx SK STK_ex_utf8 [(o, o + k)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ getr regs' 10 = w64 k /\ bytes_at W' mem' o (PjGrammar.utf8 cp) /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* ex_ws (fuzz_preset.c :130-134; out of line in image B only, B 0x84274; inlined in A): in->p past the whitespace
   (PjGrammar.ws: space, tab, newline, carriage return) before in->end. B's UBSan traps ask q 8-aligned, p non-null
   and no wrap. Writes in->p only (in FP). *)
Definition tex_ws_specX : Prop :=
  forall ly S Hp W regs mem md ch (q x0 i0 d : Z) (x : list Z) Lam peak cnt fail ran most own,
  let len := Z.of_nat (length x) in
  fpre B ARx STK_ex_ws ly S Hp W regs mem md ch ->
  getr regs 10 = w64 q ->
  val_mem segs (rdW W mem) q 8 (x0 + i0) -> val_mem segs (rdW W mem) (q + 8) 8 (x0 + len) -> q mod 8 = 0 ->
  spZ regs <= q -> q + 16 <= spZ regs + d -> fwin ly W regs mem d ->
  src_rd W mem x0 x -> (0 < len -> prhex_inblk ly S Hp x0 len) -> len <= 3 * 2 ^ 20 -> 0 <= i0 <= len ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_ex_ws) regs mem md)
    (fpostWm B ARx SK STK_ex_ws d [(q, q + 8)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ val_mem segs (rdW W' mem') q 8
         (x0 + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat i0) x)))) /\
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* ex_word (fuzz_preset.c :322-332; plain ex_word_c.v): strlen (word), then bcmp (in->p, word, len) when len bytes
   remain; on a match in->differs = 1 when v is a node of another type, and in->p += len, returning 0; else -1 and
   nothing written. Only runtime calls intervene, so the entry shadow facts of the word, the text and v->type serve.
   B's UBSan traps ask q and v 8-aligned. FP: in->p and in->differs. *)
Definition tex_word_specX : Prop :=
  forall ly S Hp W regs mem md ch (q w ty v t x0 i0 d : Z) (wl x : list Z) Lam peak cnt fail ran most own,
  let len := Z.of_nat (length x) in
  let hit := Z.of_nat (length wl) <= len - i0 /\ firstn (length wl) (skipn (Z.to_nat i0) x) = wl in
  fpre B ARx STK_ex_word ly S Hp W regs mem md ch ->
  getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
  cstr_ok W mem w wl -> 0 <= ty <= 2 ->
  (* the tag pointer is a machine address (the kit owner's ruling, on the walk-identity check's S8aWord counterexample 1:
     v = 2 ^ 64 with a3 = 0 takes the NULL arm, and the post then demanded a store at q + 32 the binary never
     makes; the frame-window clause of cstr_ok does not subsume it) *)
  0 <= v /\ v + 4 <= 2 ^ 47 ->
  val_mem segs (rdW W mem) q 8 (x0 + i0) -> val_mem segs (rdW W mem) (q + 8) 8 (x0 + len) -> q mod 8 = 0 ->
  spZ regs <= q -> q + 36 <= spZ regs + d -> fwin ly W regs mem d ->
  src_rd W mem x0 x -> prhex_inblk ly S Hp x0 len -> len <= 3 * 2 ^ 20 -> 0 <= i0 <= len ->
  (v <> 0 -> val_mem segs (rdW W mem) v 4 t /\ 0 <= t < 2 ^ 32 /\ v mod 8 = 0 /\
     range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 4 /\
     (v + 4 <= spZ regs - STK_ex_word \/ spZ regs <= v)) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_ex_word) regs mem md)
    (fpostWm B ARx SK STK_ex_word d [(q, q + 8); (q + 32, q + 36)] regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       ((hit /\ getr regs' 10 = w64 0 /\ val_mem segs (rdW W' mem') q 8 (x0 + i0 + Z.of_nat (length wl)) /\
         ((v <> 0 /\ t <> ty /\ val_mem segs (rdW W' mem') (q + 32) 4 1) \/
          ((v = 0 \/ t = ty) /\ prhex_same W mem W' mem' (q + 32) 4)))
        \/
        (~ hit /\ getr regs' 10 = w64 (-1) /\ prhex_same W mem W' mem' q 8 /\
         prhex_same W mem W' mem' (q + 32) 4)))).

(* ex_string (fuzz_preset.c :185-239; plain ex_string_c.v): the string whose opening quote is at in->p, decoded into
   the scratch (calls ex_hex4, ex_utf8); 0 with in->p past the closing quote and the decoded bytes NUL-terminated at
   the scratch, or -1 with in->p unchanged and scratch bytes written. The text and the scratch are read / written
   after program calls, so both lie in allocator blocks; the scratch is apart from the text and the cursor (plain
   ex_string_c.v:23-24). FP: the scratch and in->p. *)
Definition tex_string_specX : Prop :=
  forall ly S Hp W regs mem md ch (q x0 i0 scr d : Z) (x : list Z) Lam peak cnt fail ran most own,
  let len := Z.of_nat (length x) in
  let xs := skipn (Nat.succ (Z.to_nat i0)) x in
  fpre B ARx STK_ex_string ly S Hp W regs mem md ch ->
  getr regs 10 = w64 q ->
  val_mem segs (rdW W mem) q 8 (x0 + i0) -> val_mem segs (rdW W mem) (q + 8) 8 (x0 + len) ->
  val_mem segs (rdW W mem) (q + 24) 8 scr -> q mod 8 = 0 ->
  spZ regs <= q -> q + 32 <= spZ regs + d -> fwin ly W regs mem d ->
  src_rd W mem x0 x -> prhex_inblk ly S Hp x0 len -> len <= 3 * 2 ^ 20 -> 0 <= i0 < len ->
  wdest_ok B STK_ex_string ly S W regs mem scr (len + 1) -> prhex_inblk ly S Hp scr (len + 1) ->
  (scr + len + 1 <= x0 \/ x0 + len <= scr) -> (scr + len + 1 <= q \/ q + 40 <= scr) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_ex_string) regs mem md)
    (fpostWm B ARx SK STK_ex_string d [(scr, scr + len + 1); (q, q + 8)] regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       match fst (fst (PjGrammar.jr_string xs [])) with
       | None => getr regs' 10 = w64 (-1) /\ prhex_same W mem W' mem' q 8
       | Some (s, rest) => getr regs' 10 = w64 0 /\
           (exists c, PjGrammar.scan xs = Some c /\ rest = skipn (Nat.succ c) xs /\
              val_mem segs (rdW W' mem') q 8 (x0 + i0 + Z.of_nat c + 2)) /\
           bytes_at W' mem' scr (s ++ [0])
       end)).

(* ---- the recursive two ---- *)

(* ex_value at nesting n (fuzz_preset.c :334-356, with ex_number :243-264 and ex_items :266-320 inlined; plain
   ex_value_c.v): the value at in->p by the grammar at depth dep = in->depth, compared with the tree at v (NULL:
   none); 0 with in->p past it, in->depth back at dep and in->differs set exactly when it was set or v's tree is not
   the one read; -1 when the grammar refuses (in->p, in->depth <= 33 and in->differs moved, scratch bytes written).
   It may still nest n times (plain ex_value_K's 33 - dep frames: 32 - dep <= n). It reaches musl strtod (fpostWF;
   the entry rounding mode is 0, as plain ex_value_c.v:75 frm0 asks) and takes one class-1 fake frame per nesting
   (frame_alloc_1 (96)), released before it returns. FP: the scratch, in->p, in->depth, in->differs; the scratch is
   apart from the text and the cursor, the tree from the scratch, the cursor, the stack window and errno (plain
   ex_value_c.v:69-72). *)
Definition tex_value_specX (n : nat) : Prop :=
  forall ly S Hp W regs mem md ch (q v x0 i0 dep dl scr d : Z) (x : list Z) (t : PjTree.jv) (D : list (Z * Z))
    Lam peak cnt fail ran most own,
  let len := Z.of_nat (length x) in
  fpre B ARx (STK_ex_value n) ly S Hp W regs mem md ch ->
  (* THE MEMORY IS NORMAL AT ENTRY (the walk controller's measurement, the kit owner's ruling (a)): ex_value reaches musl
     strtod, whose row consumes it, and ev_mid's memnorm conjunct has NO other source - until now only the comment at
     :38 named it. YAkMemnorm.memnorm segs mem (the engine file YAkMemnorm.v:41, blob 96c72061b4d4 at
     commit e47394d004f6: the same body as YAjMemnorm.memnorm, `mem_inv /\ task_mem`), over
     the FULL overlay, never the at-main restricted view. SPELLED OVER YAkMemnorm on the CONVERSION argument (the kit owner's
     ruling): the S1 owner's YGcallMxmn rows and engine leaves state over it, so the one conversion
     (YAkMemnormJ.memnorm_kit_j) is at the at-main seed, not at every allocator call. The OVERRIDE argument was measured
     and does NOT apply to the kit: the kit of record's own closure already holds all three lia overrides (LiaTwx2,
     YM03, YM05), with or without either memnorm file. SUPPLIERS, both proved: image A's AjMemnormMainA.v and image B's
     YjMemnormMainB.tfib_memnorm_at_main_B (the image-B memnorm owner, commit b757f238656), threaded down the
     call chain check_as_written <- LLVMFuzzerTestOneInput. THE KEEP ACROSS THIS CALL is this post's m-form: fpostWFm
     adds PRH_Base.fQmn's `memnorm segs mem -> memnorm segs mem'` (PRH_Base.v:1465-1469, :1510-1513); across a RUNNER
     SEGMENT a walk keeps it by YSRrMemnorm.srr_inv_laws_memnorm_k (lib/Reusable/YSRrMemnorm.v:30; lib/A/Prog/S8aWord.v
     :20-22). State today: seeded (both images, proved), kept across m-form calls and across runner segments. *)
  YAkMemnorm.memnorm segs mem ->
  frm_zero (@YK11.fp_csr fx) ->
  count_cid 1 (frames S) + Z.of_nat (Nat.succ n) <= fs_frames 1 ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v ->
  prhex_cur W mem q (x0 + i0) (x0 + len) dep scr dl -> q mod 8 = 0 -> prhex_ch_apart ly W mem regs ch q 40 ->
  spZ regs <= q -> q + 40 <= spZ regs + d -> fwin ly W regs mem d ->
  src_rd W mem x0 x -> (0 < len -> prhex_inblk ly S Hp x0 len) -> len <= 3 * 2 ^ 20 -> 0 <= i0 <= len ->
  0 <= dep <= 32 -> 32 <= dep + Z.of_nat n -> (dl = 0 \/ dl = 1) ->
  wdest_ok B (STK_ex_value n) ly S W regs mem scr (len + 1) -> prhex_inblk ly S Hp scr (len + 1) ->
  (scr + len + 1 <= x0 \/ x0 + len <= scr) -> (scr + len + 1 <= q \/ q + 40 <= scr) ->
  (v = 0 \/
   prhex_tree ly S Lam W regs mem v t D /\ Forall (fun ak => 0 < fst ak) D /\
   (forall z, PRH_Reader.pj_footR v D z ->
      ~ (scr <= z < scr + len + 1) /\ ~ (q <= z < q + 40) /\ ~ (spZ regs - STK_ex_value n <= z < spZ regs) /\
      ~ (as_errno B <= z < as_errno B + 4))) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_ex_value) regs mem md)
    (fpostWFm B ARx SK (STK_ex_value n) d [(scr, scr + len + 1); (q, q + 8); (q + 16, q + 20); (q + 32, q + 36)]
       regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       (* THE HULL USE, by route (b), the threaded allocator hull premise that the texts implement
          (lib/Spec/PresetHullBudget.v): no allocator call and a fake frame only, so both meters are kept
          (st_secs S' = st_secs S); check_as_written's free AFTER ex_value reads its admission off this *)
       PresetHullBudget.hull_used S S' [] /\
        (* ex_value is the ONE non-allocating text whose post cannot say S' = S: its body takes a fake frame
           (__asan_stack_malloc_1, class 1) and releases it, so S' is S with st_fs changed. It makes NO
           allocator call, so the run position is KEPT, in the same implication form as room_live_cf: the walk
           closes it by PRH_Base.iface_room_pos_set_fs / _stack_free (true by conversion). The kit owner's ruling
           (a) gives S' = S to the other 21 non-allocating texts; this one takes (b) and this is why. *)
        (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
           PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
           PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\ exists r p' dep' dl',
          getr regs' 10 = w64 r /\
          prhex_cur W' mem' q (x0 + p') (x0 + len) dep' scr dl' /\ (dl' = 0 \/ dl' = 1) /\
          Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
          prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
          match prhex_V dep (skipn (Z.to_nat i0) x) with
          | None => r = -1 /\ 0 <= p' <= len /\ dep <= dep' <= 33
          | Some (u, rest) => r = 0 /\ p' = len - Z.of_nat (length rest) /\ dep' = dep /\
              (dl' = 1 <-> dl = 1 \/ (v <> 0 /\ t <> u))
          end)).

(* same at nesting n (fuzz_preset.c :92-113; plain same_c.v): 1 when the trees at pa and pb are equal, else 0; it reads
   both (strcmp on strings and keys, bcmp on the 8 bytes of a number) and writes only its frame; it nests at most
   depth ta times (plain same_k ta = SAME_FS * (depth ta + 1)). The trees are restated after, as the plain post does;
   their footprints are apart from the stack window, the only bytes same writes (R1). *)
Definition tsame_specX (n : nat) : Prop :=
  forall ly S Hp W regs mem md ch (pa pb : Z) (ta tb : PjTree.jv) (Da Db : list (Z * Z)) Lam peak cnt fail ran most own,
  fpre B ARx (STK_same n) ly S Hp W regs mem md ch ->
  (* THE LIVE REAL STACK ABOVE sp, GUARDED (the kit owner's ruling, 2026-10-29, on the S1 owner's wording): when the root
     pa is at or above sp, the live real stack [sp, ly_top) is present (the S1 owner's engine leaf
     YGcallStackUp.astack_up_x, lib/Reusable/YGcallStackUp.v 136e8c774182, engine set s1b f027ed1fab66, taken by path;
     the B' walker's F25). This premise is CONVERTIBLE to the conclusion of the engine's YGcallStackUp.astack_up_guard_x
     (`astack_up_x segs ly W (spZ regs) mem -> (spZ regs <= pa -> forall a, spZ regs <= a < ly_top ly ->
     apresent (w_H W) mem a)`) with astack_up_x unfolded - convertible, not syntactically identical - so a caller
     holding the unguarded astack_up_x discharges it by astack_up_guard_x. The GUARD makes the premise FREE at every
     call site: the S1 owner's stack-up reviewer
     read every `same` call site on A' (check_no_overread +1500 / +1520, check_round_trip
     +0x5f0, round_trip_text +0x348 and the recursive call) and the B' walker's reviewer did the same on B'. At all of them
     `spZ regs <= pa` is FALSE: every root lies below alloc_ceiling <= ly_stk_lo <= the callee's sp (a fake-frame local
     or a Lam block). So ONE text changes and NO caller text and no harness-entry conjunct changes. That is VERIFY's
     rule-2 half for this text; for rule 1 the leaf carries its own negative control, stack_zone_presence_false (the
     UNGUARDED zone-presence law is false). The B' walk proves this text: lib/B/Prog/SameB_walk.v same_holds_B (:1997). *)
  (spZ regs <= pa -> YGcallStackUp.astack_up_x segs ly W (spZ regs) mem) ->
  getr regs 10 = w64 pa -> getr regs 11 = w64 pb ->
  prhex_tree ly S Lam W regs mem pa ta Da -> prhex_tree ly S Lam W regs mem pb tb Db ->
  (PjTree.depth ta <= n)%nat ->
  (forall z, PRH_Reader.pj_footR pa Da z -> ~ (spZ regs - STK_same n <= z < spZ regs)) ->
  (forall z, PRH_Reader.pj_footR pb Db z -> ~ (spZ regs - STK_same n <= z < spZ regs)) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr segs W (cfg_at segs (pa_sigma AS_same) regs mem md)
    (fpostm B ARx SK (STK_same n) [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ (ta = tb /\ getr regs' 10 = w64 1 \/ ta <> tb /\ getr regs' 10 = w64 0) /\
       PRH_Reader.pj_nodeR segs (rdW W' mem') (prh_lin Lam) pa ta Da /\
       PRH_Reader.pj_nodeR segs (rdW W' mem') (prh_lin Lam) pb tb Db /\
       (* same ALLOCATES NOTHING (no allocator call, no fake frame: STK_same is its own real-stack frames and the
          strcmp wrapper), so the allocator state is unchanged, STATED (the slice walker's counterexample: with ablocks
          alone kept, an S' whose quarantine differs from S would satisfy the post, and iface_room_pos's quar_fifo_cf
          hist S' then fails for every hist, so check_no_overread's post was unprovable past its same calls) *)
       Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

End c.
