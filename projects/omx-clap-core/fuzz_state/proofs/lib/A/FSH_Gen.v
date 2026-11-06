(* fs program part, the IMAGE-GENERIC half of the statement base: every definition here is generic in segs / B and in the
   build's numerals (those it needs are parameters), so it is stated ONCE and serves both builds. The numerals and the
   names instantiated at them are per build: lib/A/FSH_Base.v, FSH_Rt.v, FSH_Harness.v over fs.asan and lib/B/FSH_*.v
   over fs.asan-ubsan (FSH_Fn_FORM.md section 0). Definitions only (rule 24: no function proved); the one lemma,
   fpost_ot_sp, relates two of these definitions.
   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Base.v, FMH_Rt.v, FMH_Fn.v (a working branch
   e48bf3cce32, with the FMH_* text of 706affbdbe6, 3e0aa997be6, 137702429de and a1902517c68: stk_sh0 out of the
   contracts, str_homeA / cstr_kept, image facts out of fpre, reader blocks with n > 0); donor
   proofs/cgif/cgif_file_fuzzer/lib (YCbq.v:331-370 astk_ok / afn_pre / ajournal, YG0d.v:225-283 acall_pre / ecall_pre,
   YG0d.v:311-326 dest_ok / aintrin_realizes, YC20.v:43-48, :90-96 via FSH_YC20.v; A/ACes.v:164 the raised window of
   rd_entry). Design: a Theorem Labs lane's design/HARNESS.md, design/POISON.md. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20.
(* fs's released pure models (lib/Spec, lib/Prog), Required (not copied) so lane files can name them qualified:
   PjTree (jv, depth), PjGrammar / PjRoundTrip (the reader's grammar, pj_wf, ttrace), WriterSpec (b64_enc, b64_dec,
   b64c, esc, hexd, wstr, newcap), WriterSpecFacts, WriterApp (the writer's buffer state), WriterValue (wvpieces, wdoc),
   B64Canon (b64_strip), HState (b64_alloc_bound, in_window), ReaderRes (jr_strtod, fregs_kept, rd_cells),
   check_round_trip_stages_b (crt_doc :48-49, crt_doc_ok :188-190: depth <= 2, 15 parse allocations). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts WriterApp WriterValue
  B64Canon HState ReaderRes check_round_trip_stages_b.
Import ListNotations.
Local Open Scope Z_scope.
(* IMPLICIT-INSTANCE GUARD (CRT 22:0xZ, a Theorem Labs lane 22:13Z). S0's specs take {SK : YI16.sink_head} (the musl ofl_head cell of
   the build being walked). Reusable/YI5b.v:12 declares `#[global] Instance src0_sink_head` = the PLAIN build's ofl_head,
   so any file that loads YI5b and leaves SK to inference elaborates against the plain image, green and vacuous. YI5b is
   Required here only to name it; the removal is #[global] so that it holds wherever this file is loaded, including
   files that load FSH_Gen without importing it (this Require is what would otherwise bring the instance in). Every
   S0 / lane site passes SK explicitly: build A `@... AE2k.tfib_sink_head` (ofl_head 0x5fb628), build B
   `@... FSH_Base.fsB_sink_head` (0x5fbb28). The ASan instance A/AE2k.v:45 tfib_sink_head is removed in
   lib/{A,B}/FSH_Harness.v, the S0 files that reach AE2k. Measured: with these removals a bare use leaves ?SK
   unresolved ("no type class instance found"). Other implicit classes of S0's specs: FPState and RunCeil have no global
   instance in lib/ (only #[local] fx0 copies); lib_shape has #[global] ff_lib_shape (Reusable/YI0a.v:55, cgif's
   file shape) and checksum_shape (ZTraceSpec.v:14, fs's plain shape, the one fs_lib_contract_x is meant for), neither
   in this file's load closure.
   NOT a third instance (a Theorem Labs lane 22:2xZ, measured 2026-10-28 by a scratch with the U chain loaded first, then the S0 imports of
   a B context): lib/U/Reusable/YI5b.v:12 `#[global] Instance src0_sink_head` is an instance of
   lib.U.Reusable.YI16.sink_head, which U/Reusable/YI16.v:11 declares as its OWN Class, a constant distinct from the
   lib.Reusable.YI16.sink_head S0's specs take (`eq_refl : RC.sink_head = UC.sink_head` fails). With it loaded,
   `Definition _ : lib.Reusable.YI16.sink_head := _` still fails, while `_ : lib.U.Reusable.YI16.sink_head` resolves to it.
   It cannot fill S0's SK, so it is not removed here: removing it would only break U-side elaboration (the UBSan plain
   chain) in files that load both chains. `YI5b.src0_sink_head` below resolves to lib.Reusable.YI5b's (Locate). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- program constants (source; the same in both builds) ---- *)
Definition SIZE_MAXZ : Z := 2 ^ 64 - 1.
Definition HEAD : Z := 16.                             (* fuzz/alloc.c:28 *)
Definition PRESET_FILE_MAX_BYTES : Z := 3 * 2 ^ 20.    (* preset_file.h:61; fs.c:323 returns before any allocation above *)
(* reader allocation calls (failing(): g_count + 1, alloc.c:33-39) one LLVMFuzzerTestOneInput call makes, at most, from the
   released plain contracts: check_no_overread 3 (check_no_overread_c.v:52), the main decode 1 (fs.c:327-333),
   check_reject_clean_starved 2 (check_reject_clean_starved_c.v:51), check_round_trip CRT_ALLOCS = 68
   (check_round_trip_c.v:17, :54). ENTRY 23:35Z: accepted-path callee increments 84 - the callee posts on the accepted
   path force cno 3 + decode_ff 1 + crt 78 + starved 2 = 84, above the 74 this estimate gave; 96 leaves slack. *)
Definition FS_CNT_LIB : Z := 96.
(* the shared core's per-call event bound: fs keeps cgif's EV_LIB = 2000 (A/ACfn.v:23) against the Theorem Labs core's
   EV_MAX = 11776 (Reusable/YG00.v:38, from a Theorem Labs lane d834f9653ac via a working branch 5e580eb5ab5): 4 * 2000 + 3 = 8003 <= 11776
   (the driver's 4 calls, A/AD1r.v:582). *)
Definition FS_EV_LIB : Z := 2000.
(* allocator ticks (one per malloc, one per free, YG00.v:233, :540; a realloc 3 in cgif_rgb's model, lib/YG0f.v:15-21
   realloc_tree: free NULL; malloc; free) per call, at most, where they do not depend on a tree (source counts,
   FsProgramPart.md sections 2-3; the tree-dependent ones, pj_parse / pj_free / pj_set / pj_write / parse_* /
   write_value / put, are the lanes'). ESTIMATED from source. *)
Definition EV_fuzz_malloc : Z := 1.
Definition EV_fuzz_free : Z := 1.
Definition EV_fuzz_realloc : Z := 3.                   (* p = 0: the tail call to fuzz_malloc, 1 *)
Definition EV_fuzz_strdup : Z := 1.
Definition EV_past_nul : Z := 1.
Definition EV_preset_base64_encode : Z := 1.
Definition EV_preset_base64_decode : Z := 2.           (* malloc; free on refusal (pf.c:608, :643) *)
Definition EV_check_no_overread : Z := 12.             (* 6 malloc + 6 free *)
Definition EV_check_as_written : Z := 4.               (* want, six: 2 malloc + 2 free *)
Definition EV_check_reject_clean_starved : Z := 0.     (* both reader allocations fail in failing() before malloc *)
Definition EV_check_round_trip : Z := 2 * 36 + 3 * 2.  (* 36 malloc + 36 free + at most 2 realloc *)
Definition FS_EV_LLVMF : Z := 2 * 46 + 3 * 2.          (* accepted text: 46 malloc + 46 free + at most 2 realloc *)
(* live request bytes one call may add: peak 30,149,357 < 2^25 (FsProgramPart.md section 3), under LIVE_LIB = 2^33 *)
Definition FS_LIVE_LLVMF : Z := 2 ^ 25.
Definition LIVE_check_no_overread : Z := 2 ^ 24.       (* its own peak 16,515,183 (FsProgramPart.md section 3) *)
Definition LIVE_check_round_trip : Z := 2 ^ 25.

(* ---- stack each runtime contract asks below the call's sp (fm FMH_Base.v convention) ---- *)
Definition STK_RT_STR : Z := 2 * ESTACK.      (* strlen, strcmp, memchr (donor astrnlen_realizes YG0d.v:404; fm FMH_Base.v:87);
                                                 one name for the string family *)
Definition STK_RT_MEMCHR : Z := STK_RT_STR.
Definition STK_RT_BCMP : Z := 2 * ESTACK.     (* donor abcmp_realizes, YG0d.v:355 *)
Definition STK_RT_PRINTF : Z := 3 * ESTACK.   (* fm a Theorem Labs lane: snprintf .. printf_core + the strnlen interceptor *)
Definition STK_RT_INTRIN : Z := ESTACK.       (* __asan_memcpy / __asan_memset / __asan_set_shadow_f5: ecall_pre
                                                 (YG0d.v:281-282, :319) *)
Definition STK_RT_MEMCPY : Z := STK_RT_INTRIN.
Definition STK_RT_MEMSET : Z := STK_RT_INTRIN.
Definition STK_RT_FAKE : Z := ESTACK.         (* __asan_stack_malloc_*: ecall_pre (YG0d.v:286) *)
Definition STK_RT_POISON : Z := ESTACK.       (* __asan_(un)poison_memory_region: ecall_pre (YG0d.v:285-291) needs
                                                 ly_stk_lo + ESTACK <= sp at the call, as for STK_RT_FAKE; the old 64
                                                 (a Theorem Labs lane's design/POISON.md section 7) does not meet it (a Theorem Labs lane's
                                                 B own lane, 07:50Z). Only B STK_own changes value (96 -> 4128); every
                                                 other user is a zmaxl that also holds STK_RT_ALLOC = ASTACK. *)
Definition STK_RT_ALLOC : Z := ASTACK.        (* malloc / free: acall_pre (YG0d.v:229-230); NOT realloc's (below) *)
Definition STK_RT_REALLOC : Z := ASTACK + 0x8a0.
                                              (* realloc: ASTACK + its own runtime prefix 0x8a0 (interceptor 0x7f0 +
                                                 unwind 0x70 + asan_realloc 0x10 + Reallocate 0x30), which sits ABOVE
                                                 the inner Allocate / Deallocate whose contracts need ly_bot < sp_callee
                                                 (AllocG.v:75, DeallocG.v:81; ReallocG.v:121 RSTACK); FSupoisonRealloc's
                                                 arealloc_realizesU takes `ly_bot ly + 0x8a0 < spZ regs` (a Theorem Labs lane
                                                 e0461c947a1; ruled by a Theorem Labs lane 2026-10-29T08:04Z). *)
(* strtod: the released plain walk's stack, lib/Prog/strtod_c.v:13 STRTOD_K (same musl code in fs.asan,
   FsExtraSources.md 2.3; ESTIMATED for the ASan walk). Its only call (parse_value) is unreachable on fs's document, whose
   leaves are strings (check_round_trip_stages_b.v:48-49 crt_doc); kept so the bound covers the code. *)
Definition STK_RT_STRTOD : Z := 8928.
(* the stack probe of the six fake-frame functions' real-stack fallback (FSH_Base.v, FRAME_ / PROBE_) *)
Definition PROBE_PAGE : Z := 4096.
Definition zmaxl (l : list Z) : Z := fold_right Z.max 0 l.

(* ---- fake frames live at a call (the donor's per-spec premise `Z.of_nat (length (frames S)) <= N`, cgif lib/YC21.v:38;
   ajournal keeps frames S' = frames S at return, YCbq.v:354); a spec's N = the fake-frame functions above it on the
   harness's call path (FSH_Fn_FORM.md section 2) ---- *)
Definition FRL_LLVMF : Z := 0.                (* tfib_lib_pre_x: frames S = [] (A/ACfn.v:40) *)
Definition FRL_CHECK : Z := 1.                (* called by LLVMFuzzerTestOneInput: its class-0 frame *)
Definition FRL_CRT_CALLEE : Z := 2.           (* called (transitively) by check_round_trip outside parse_value *)
Definition FRL_parse_value (k : Z) : Z := 2 + k.   (* parse_value at level k: k parse_value frames above it *)
Definition FRL_MAX : Z := 7.                  (* the donor's bound; fs's deepest is FRL_parse_value 2 + 1 = 5 *)

(* no reader allocation fails in the next k: g_fail_at = SIZE_MAX and g_count stays far from it (fm FMH_Fn.v) *)
Definition quiet (cnt fail k : Z) : Prop := fail = SIZE_MAXZ /\ 0 <= cnt /\ cnt + k < 2 ^ 63.

(* ---- pure models of runtime answers (fm FMH_Rt.v; find_idx of fm's ManifestModel restated) ---- *)
(* the first index of c in l *)
Definition first_at (l : list Z) (c : Z) (j : nat) : Prop :=
  (j < length l)%nat /\ nth j l 0 = c /\ ~ In c (firstn j l).
Fixpoint zfind (c : Z) (l : list Z) : option nat :=
  match l with [] => None | x :: t => if x =? c then Some O else option_map S (zfind c t) end.
(* memchr (p, c, n) reads up to and including the first c, or all n bytes *)
Definition mchr_len (c : Z) (l : list Z) : Z :=
  match zfind c l with Some k => Z.of_nat k + 1 | None => Z.of_nat (length l) end.
(* strcmp (s1, s2) = 0 for NUL-free l1, l2: the strings are equal (C compares up to the first NUL) *)
Definition str_eq (l1 l2 : list Z) : Prop := l1 = l2.
(* strncmp / strncasecmp (fm's; fs links neither, carried so the string family stays one text) *)
Definition strn_eq (k : nat) (l1 l2 : list Z) : Prop := firstn k (l1 ++ [0]) = firstn k (l2 ++ [0]).
Definition lc (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
Definition strncase_eq (k : nat) (l1 l2 : list Z) : Prop :=
  map lc (firstn k (l1 ++ [0])) = map lc (firstn k (l2 ++ [0])).

(* ---- snprintf formats: literal runs, %s, %.*s (fm), %c and %04x (fs's put_string, pf.c:498, :506) ---- *)
Inductive fpiece : Type := FLit (l : list Z) | FStr | FPStr | FChr | FHex4.
Fixpoint fmt_bytes (ps : list fpiece) : list Z :=
  match ps with
  | [] => []
  | FLit l :: ps' => l ++ fmt_bytes ps'
  | FStr :: ps' => [37; 115] ++ fmt_bytes ps'
  | FPStr :: ps' => [37; 46; 42; 115] ++ fmt_bytes ps'
  | FChr :: ps' => [37; 99] ++ fmt_bytes ps'
  | FHex4 :: ps' => [37; 48; 52; 120] ++ fmt_bytes ps'
  end.
(* "%04x" of v < 2^16: four lowercase hex digits (fs's WriterSpec.hexd, the digit of WriterSpec.esc) *)
Definition hex4z (v : Z) : list Z :=
  map WriterSpec.hexd [v / 4096 mod 16; v / 256 mod 16; v / 16 mod 16; v mod 16].

(* the FP registers a callee keeps (fs plain lib/Prog/ReaderRes.v:99-101). On the ASan side the FP state is the Section's
   fx throughout: strtod, the only FP code fs's target code calls, is unreachable on fs's document (FSH_Fn_FORM.md
   section 1). *)
Definition fregs_kept (f f' : YK11.FPState) : Prop := ReaderRes.fregs_kept f f'.

(* ---- the narrow form of fs's document, shared by WRITER and READER (owner 21:26Z). Definitions only, byte-for-byte
   from a working branch f995a01189d: plain_byte / plain_bytes from lib/A/FSW_writer_model.v:17-18 and
   jv_plain from lib/A/FSH_Fn_writer.v:121-131. Under plain_bytes put_string's escape arms (the two-char escapes and the
   \u%04x snprintf at A 0x85d04 / B 0x86214) are unreachable, which is why fs's snprintf walk left the port; READER's
   FS_DOC_STRS discharges the premise for the document fs.c:237-248 builds. FSW_writer_model.v's lemmas
   (plain_not_special, spieces_run_plain, spieces_plain, wstr_plain, wstr_plain_length, wstr_plain_mem) use only these
   two definitions and WriterSpec's special / spieces / wstr, so that file keeps its lemmas and imports this one
   (it then depends on the ASan core through FSH_Gen; if a kit-free model file is wanted, these three definitions move
   to a leaf file unchanged). ---- *)
Definition plain_byte (c : Z) : Prop := 32 <= c /\ c <> 34 /\ c <> 92.
Definition plain_bytes (bs : list Z) : Prop := Forall plain_byte bs.
Fixpoint jv_plain (t : PjTree.jv) {struct t} : Prop :=
  match t with
  | PjTree.JStr s => plain_bytes s
  | PjTree.JArr items =>
      (fix go (l : list PjTree.jv) {struct l} : Prop :=
         match l with [] => True | u :: r => jv_plain u /\ go r end) items
  | PjTree.JObj members =>
      (fix go (l : list (list Z * PjTree.jv)) {struct l} : Prop :=
         match l with [] => True | (k, u) :: r => plain_bytes k /\ jv_plain u /\ go r end) members
  | _ => True
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the per-function wrappers in U FORM (all program-part lanes, 20:41Z): every fs function runs with live user-poisoned
   heads (fuzz_malloc poisons a 16-byte head per block), so the pre is afn_preU (afn_pre read through ARU, as FSupoisonU's
   acall_preU reads acall_pre) and the post fpostU gives the heads back as U'. fpostU takes the window top sp0 as a
   parameter, as the donor's ajournal does (YCbq.v:348; A/ACfn.v:50 passes spZ regs, A/ACes.v:164 rd_entry a raised one):
   a callee that writes a caller's real-stack object above its sp (pj_write's pj_out, pj_parse's struct pj_in,
   parse_string's slot hex4 writes) passes window size STK_f + (ot - spZ regs) and top ot, and gives the slack back with
   wkeep. The U = [] forms fpre / fpost (the donor's afn_pre / apost_base) are corollaries: fpreU_of_pre, fpost_of_U. *)
Definition afn_preU (STK : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
  afn_pre segs B STK ly S W regs (unpoison U mem) md ch /\ upoison_ok B ly S U /\ upoisoned segs W mem U.
Definition fpostU (STK sp0 : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S (U : list (Z * Z)) W mem md (k : Z)
  (U' : list (Z * Z))
  (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal segs B STK sp0 FP ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' k /\
    upoison_ok B ly' S' U' /\ upoisoned segs W' mem' U' /\
    aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
(* a Theorem Labs lane's apost_baseU (FMH_Base.v) is fpostU at sp0 = spZ regs, in a Theorem Labs lane's argument order *)
Definition apost_baseU (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z) (U U' : list (Z * Z))
  (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fpostU STK (spZ regs) FP regs ly S U W mem md k U' Q.
(* the donor's apost_base, and its window-relative form (no user poison) *)
Definition fpost (STK : Z) (FP : list (Z * Z)) regs ly S W mem md (k : Z)
  (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  apost_base segs B STK FP regs ly S W mem md k Q.
Definition fpost_ot (STK ot : Z) (FP : list (Z * Z)) regs ly S W mem md (k : Z)
  (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal segs B (STK + (ot - spZ regs)) ot FP ly S W mem md [] ly' S' W' mem' md' k /\
    aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
Lemma fpost_ot_sp : forall STK FP regs ly S W mem md k Q W' c',
  fpost_ot STK (spZ regs) FP regs ly S W mem md k Q W' c' <-> fpost STK FP regs ly S W mem md k Q W' c'.
Proof. intros. unfold fpost_ot, fpost, apost_base. rewrite Z.sub_diag, Z.add_0_r. reflexivity. Qed.
Lemma fpost_of_U : forall STK FP regs ly S W mem md k Q W' c',
  fpostU STK (spZ regs) FP regs ly S [] W mem md k [] Q W' c' -> fpost STK FP regs ly S W mem md k Q W' c'.
Proof.
intros STK FP regs ly S W mem md k Q W' c' (ly' & S' & regs' & mem' & md' & Ec & J & _ & _ & R & HQ).
exists ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact J|]. split; [exact R | exact HQ].
Qed.
(* the keep conjunct of a window-relative post, shared by WRITER and READER (text of WRITER's
   working branch 4b4015d615 lib/A/FSH_Fn_writer.v:124, unchanged): every byte of [s, ot) outside the caller's object
   [o, o + n) keeps its value and its writability (pj_out n = 32; struct pj_in per READER) *)
Definition wkeep (W W' : world segs) (mem mem' : word -> option byte) (s ot o n : Z) : Prop :=
  forall a, s <= a < ot -> ~ (o <= a < o + n) ->
    mbyte segs (rdW W' mem') a = mbyte segs (rdW W mem) a /\
    (writable_at segs (rdW W mem) a <-> writable_at segs (rdW W' mem') a).

(* ecall_pre (YG0d.v:277) with STK bytes of present stack, as abcmp_realizes asks (YG0d.v:355) *)
Definition ecall_pre_k (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
  ecall_pre segs B ly S W regs mem md /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).
(* ecall_preU (FSupoison.v) with STK bytes of stack *)
Definition ecall_preU_k (STK : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ecall_preU segs B ly S U W regs mem md /\ ly_stk_lo ly + STK <= spZ regs /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).
(* ecall_preU_k at any K gives FSupoison's ecall_preU (whose ecall_pre has the ESTACK window); ecall_pre_k K gives
   ecall_preU_k K at U = [] *)
Lemma ecall_preU_k_ecall_preU : forall K ly S U W regs mem md,
  ecall_preU_k K ly S U W regs mem md -> ecall_preU segs B ly S U W regs mem md.
Proof. intros K ly S U W regs mem md H. exact (proj1 H). Qed.
Lemma ecall_preU_k_nil : forall K ly S W regs mem md,
  ecall_pre_k K ly S W regs mem md -> ecall_preU_k K ly S [] W regs mem md.
Proof.
intros K ly S W regs mem md (H & L & P). split; [exact (proj2 (ecall_preU_nil segs B ly S W regs mem md) H)|].
split; [exact L | exact P].
Qed.



(* ---- C strings and byte windows ---- *)
(* the bytes l (no NUL) then a NUL at p, as the walk reads them *)
Definition cstr (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p (l ++ [0]) /\ Forall (fun c => c <> 0) l.
(* what a runtime string reader needs of it: every byte up to the NUL addressable (the interceptor's range check), the
   rest of the 8-byte word holding the NUL visible (musl's word reads; donor astrnlen_realizes, YG0d.v:401-412), the
   8-byte word at p in amem_range (the Bz walks' region_in_mem needs p + 7, RUNTIME-str I_consts.v:20) and a length under
   2 ^ 32 (istrlen_spec, I_strlen.v:110; fs's strings are under 3 MiB).
   VACUITY (audit 2026-10-28): `p + len + 1 <= alloc_ceiling` is FALSE of a real-stack pointer, since astk_ok gives
   alloc_ceiling <= ly_stk_lo ly <= spZ regs - STK (YCbq.v:331-333, alloc_ceiling 0x7fff7f800000 YK06.v:13). It is KEPT
   because no fs string argument is a real-stack address on a live path: every string fs passes to strlen / strcmp /
   memchr / bcmp is in a reader block, in the image, or in a GRANTED FAKE FRAME (put_string's `esc` = its class-0 frame
   + 0x20, strlen at A 0x85d0c / B 0x8621c), and a fake frame lies below alloc_ceiling: owned_extents holds
   (ly_F ly, kFakeStackSize) (YG0f.v:294) and layout_ok's lo_app (YG0f.v:318) puts it in in_app, whose bound is
   `lo + len <= ASAN_CEIL` (YG0f.v:276); frame_addr ly cid pos = ly_F ly + offset (YG0f.v:339). The one real-stack case is
   the fallback object taken when __asan_stack_malloc_* answers NULL, which also writes the real frame's stack shadow and
   so is excluded by AR anyway (FSH_Fn_FORM.md section 2). If a walk ever takes that path, this bound (and wdest_ok's and
   src_rd's) must become the donor's `<= 2 ^ 63` (YG0d.v:320, :324, :406) with the donor's frame premise
   `forall a, p <= a <= p + len -> ~ (spZ regs - STK_RT_STR <= a < spZ regs)` (abcmp_realizes' form, YG0d.v:359-360).
   CEILING BOUND = THE BYTES UP TO THE NUL (a Theorem Labs lane 2026-10-29T05:04Z, option (c); was `+ 8`): its one consumer,
   FSstrlen.v cstr_off_frame (the string lies below the walk's stack window), needs only p + len + 1. musl strlen's word
   reads past the NUL (fs.asan 0x99070: byte steps to 8-alignment, then aligned `ld` words, 0x990c4-0x990dc) stay inside
   the aligned word holding the NUL, which the LAST conjunct makes visible and amem_range (len + 8) places in app memory;
   for a heap string they also stay below alloc_ceiling, since alloc_ceiling (0x7fff7f800000) is 8-aligned and the block
   ends at or below it. The `+ 8` form was unprovable for a string that fills its heap block (CRT, a Theorem Labs lane 04:56Z). *)
Definition cstr_ok (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  cstr W mem p l /\ 4096 <= p /\ p + Z.of_nat (length l) + 1 <= alloc_ceiling /\
  Z.of_nat (length l) + 1 < 2 ^ 32 /\
  amem_range p (Z.of_nat (length l) + 8) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l) + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l) + 1) /\
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview segs (w_H W) mem a <> None).
(* a byte window [p, p + length l) holding l, each visible (fm FMH_Base.v bytes_at; renamed: YP03.v has a bytes_at) *)
Definition zbytes_at (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  garr8 segs (rdW W mem) p l.
(* a destination the walk may write n bytes at (donor dest_ok, YG0d.v:311, with an STK window) *)
Definition wdest_ok (STK : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (d n : Z) : Prop :=
  0 <= d /\ d + n <= alloc_ceiling /\ amem_range d n /\   (* snprintf's dest is put_string's `esc`, in its granted fake
     frame (A 0x85d04, B 0x86214), which is below alloc_ceiling (cstr_ok's note); `~ aowned` holds of it because a live
     frame's bytes are aclient_byte (YG0n.v:229-241) *)
  (forall a, d <= a < d + n -> writable_at segs (rdW W mem) a /\ ~ aowned B ly S a /\ ~ (spZ regs - STK <= a < spZ regs)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n).
(* a byte window the code copies from (memcpy source, aintrin_realizes OCpy premises, YG0d.v:317-326) *)
Definition src_rd (W : world segs) (mem : word -> option byte) (p : Z) (l : list Z) : Prop :=
  zbytes_at W mem p l /\ 4096 <= p /\ p + Z.of_nat (length l) + 8 <= alloc_ceiling /\   (* fs's memcpy sources include
     fake-frame objects: put's src is put_string's `esc` (A 0x842b0 under 0x85d1c, B 0x845dc under 0x8622c) and pj_set's
     src is check_round_trip's local &state in its class-3 frame (A 0x8393c, B 0x83b30); both below alloc_ceiling *)
  amem_range p (Z.of_nat (length l)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l)) /\
  (0 < Z.of_nat (length l) -> shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l))).

(* ---- fuzz/alloc.c's statics (alloc.c:30) at the build's cells gl gp gc gf (fm fm_glob); FSH_Base.v fs_glob ---- *)
Definition fs_glob_at (gl gp gc gf : Z) (W : world segs) (mem : word -> option byte) (live peak cnt fail : Z) : Prop :=
  val_mem segs (rdW W mem) gl 8 live /\ val_mem segs (rdW W mem) gp 8 peak /\
  val_mem segs (rdW W mem) gc 8 cnt /\ val_mem segs (rdW W mem) gf 8 fail /\
  0 <= live <= peak /\ peak < 2 ^ 64 /\ 0 <= cnt < 2 ^ 64 /\ 0 <= fail < 2 ^ 64.
(* a reader block (fuzz/alloc.c own :41-49): the asan block (p - 16, n + 16) is live, its head holds n, n > 0 (a Theorem Labs lane
   a1902517c68: the granule after the head is in the block, as the poison walks ask); while live its 16-byte head is
   user-poisoned, (p - 16, 16) in U *)
Definition fs_rblock (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
  In (p - HEAD, n + HEAD) (ablocks B ly S) /\ p mod 16 = 0 /\ 0 < n /\
  val_mem segs (rdW W mem) (p - HEAD) 8 n.

(* the shadow of the STACK reads 0. AR gives it: ARm's am_zshadow (YG0n.v:217) covers zero_shadow_ranges, whose head is the
   stack (YG0n.v:187-190). Not a contract premise (a Theorem Labs lane 706affbdbe6): derive it from AR where needed. No shadow-zero
   fact over fs's .data / .bss is stated: fs registers 34 asan globals with poisoned redzones (A/AF0m.v:278-279). *)
Definition stk_sh0 (W : world segs) (mem : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> aview segs (w_H W) mem (shadow_addr a) = Some 0.

(* where a string the caller keeps across a program call lives (relro rlo..rhi): inside a live block, avoiding every range
   of the poison set U (no byte on a user-poisoned head, FSH_Rt.v cstr_kept), or in read-only image bytes that are not
   runtime-owned. A callee's ajournal keeps both (a Theorem Labs lane G3, G5). *)
Definition str_homeA_at (rlo rhi : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (p n : Z) : Prop :=
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= p /\ p + n <= b + m /\
     forall r, In r U -> p + n <= fst r \/ fst r + snd r <= p) \/
  (forall a, p <= a < p + n -> in_roP segs rlo rhi a /\ ~ Exists (in_zr a) (as_owned_static B) /\
     ~ (as_errno B <= a < as_errno B + 4)).
(* the stack-protector cells musl's printf_core reads: the .got slot gcan holds can, and can holds a value *)
Definition fs_canary_at (gcan can : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  exists cval, val_mem segs (rdW W mem) gcan 8 can /\ val_mem segs (rdW W mem) can 8 cval /\ 0 <= cval < 2 ^ 64.
(* the premise every fs function takes besides its own: the donor's afn_pre and the relro / rom view (it rides through
   ajournal's image clause); image facts come from fs_img_facts (FSH_Rt.v), a Theorem Labs lane 3e0aa997be6 *)
Definition fpre_at (rlo rhi STK : Z) ly S (W : world segs) regs mem md ch : Prop :=
  afn_pre segs B STK ly S W regs mem md ch /\ arodata_okP segs rlo rhi B (aview segs (w_H W) mem).
Definition fpreU_at (rlo rhi STK : Z) ly S (U : list (Z * Z)) (W : world segs) regs mem md ch : Prop :=
  afn_preU STK ly S U W regs mem md ch /\ arodata_okP segs rlo rhi B (aview segs (w_H W) mem).
Lemma fpreU_of_pre : forall rlo rhi STK ly S W regs mem md ch,
  fpre_at rlo rhi STK ly S W regs mem md ch -> fpreU_at rlo rhi STK ly S [] W regs mem md ch.
Proof.
intros rlo rhi STK ly S W regs mem md ch (H & R). split; [|exact R].
split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs.
Qed.

(* ---- (c) user-poisoned heads live across allocator calls (FSH_Fn_FORM.md section 3c; (internal path) items 9-10,
   P1-P4): fs keeps reader blocks live across later reader allocations (grow's realloc of keys while keys[0]'s head is
   poisoned, pf.c:51-57, :224-233), so at fs's malloc / free / realloc calls U <> []. a Theorem Labs lane's FMupoison covers allocator
   calls only at U = [] (ARU_nil). The named predicate for the U fs carries is FSupoisonU.fs_heads (a Theorem Labs lane,
   a working branch c811a33348d: every range the 16-byte head at the start of a live block), with ARU_free_outside
   for free sites and the allocator / runtime contracts in ARU form there (P1, P3); P2 (unpoison anywhere) is proved
   there; the realloc leaf is ALLOC's (FSH_ReallocModel.v). Not restated here. ---- *)

(* ---- runtime contracts in the donor's per-call form (YG0d.v:317-419: ecall_pre, argument registers, range premises on
   aview, SRr to the return address with AR kept, callee-saved registers kept, same_but_materialized, a memory frame).
   Generic in pc; FSH_Rt.v instantiates them at the build's entries. U = [] forms (fm FMH_Rt.v); the ARU twins of the
   walks fs runs while heads are poisoned live in a Theorem Labs lane's FSupoisonU-style files (FSH_Fn_FORM.md section 4). ---- *)
(* the post of a call that writes nothing but its stack window: return to ra, AR kept, a0 = v with R v *)
Definition rt_post_ro (STK : Z) ly S W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
(* the same with user-poisoned ranges U live across the call *)
Definition rt_post_roU (STK : Z) ly S (U : list (Z * Z)) W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W (unpoison U mem') md' /\ upoisoned segs W mem' U /\
    aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* strlen interceptor (fs.asan __interceptor_strlen 0x426e4, REAL = musl strlen 0x99070): ASAN_READ_RANGE (s, len + 1) *)
Definition astrlen_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x (l : list Z),
  ecall_pre_k STK_RT_STR ly S W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> cstr_ok W mem x l ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = Z.of_nat (length l))).

(* strcmp interceptor (fs.asan 0x42c10): compares itself up to the first difference or NUL at i, then READ_STRING (s1, i + 1),
   (s2, i + 1); fs uses only = 0 / <> 0 (fs.c:296, :301; pf.c:359) *)
Definition astrcmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y (l1 l2 : list Z),
  ecall_pre_k STK_RT_STR ly S W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y ->
  cstr_ok W mem x l1 -> cstr_ok W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> str_eq l1 l2)).

(* the U forms of strlen / strcmp (Theorem Labs lanes, 20:41Z; FMH_Rt.astrstr_realizes' form): fs calls both while
   reader heads are poisoned; the U = [] forms above are their corollaries, proved here *)
Definition astrlen_realizesU (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md x (l : list Z),
  ecall_preU_k STK_RT_STR ly S U W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> cstr_ok W mem x l ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_roU STK_RT_STR ly S U W regs mem md (fun v => v = Z.of_nat (length l))).
Definition astrcmp_realizesU (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md x y (l1 l2 : list Z),
  ecall_preU_k STK_RT_STR ly S U W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y ->
  cstr_ok W mem x l1 -> cstr_ok W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_roU STK_RT_STR ly S U W regs mem md (fun v => v = 0 <-> str_eq l1 l2)).
Lemma rt_post_ro_of_U : forall K ly S W regs mem md R W' c',
  rt_post_roU K ly S [] W regs mem md R W' c' -> rt_post_ro K ly S W regs mem md R W' c'.
Proof.
intros K ly S W regs mem md R W' c' (EW & regs' & mem' & md' & v & Ec & HAR & _ & Rest).
split; [exact EW|]. exists regs', mem', md', v. split; [exact Ec|]. split; [exact HAR | exact Rest].
Qed.
Lemma astrlen_realizes_of_U : forall pc, astrlen_realizesU pc -> astrlen_realizes pc.
Proof.
intros pc HU ly S W regs mem md x l Hpre Hrom Hx Hl.
eapply SRr_mono; [exact (HU ly S [] W regs mem md x l (ecall_preU_k_nil _ _ _ _ _ _ _ Hpre) Hrom Hx Hl)|].
intros W' c' _ H. exact (rt_post_ro_of_U _ _ _ _ _ _ _ _ _ _ H).
Qed.
Lemma astrcmp_realizes_of_U : forall pc, astrcmp_realizesU pc -> astrcmp_realizes pc.
Proof.
intros pc HU ly S W regs mem md x y l1 l2 Hpre Hrom Hx Hy H1 H2.
eapply SRr_mono; [exact (HU ly S [] W regs mem md x y l1 l2 (ecall_preU_k_nil _ _ _ _ _ _ _ Hpre) Hrom Hx Hy H1 H2)|].
intros W' c' _ H. exact (rt_post_ro_of_U _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* strchr interceptor (fm's; fs.asan has no strchr call: preset_base64_decode's strchr (pf.c:626) is compiled to memchr) *)
Definition astrchr_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x c (l : list Z),
  ecall_pre_k STK_RT_STR ly S W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 c -> 0 < c < 256 -> cstr_ok W mem x l ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md
      (fun v => (v = 0 /\ ~ In c l) \/ (exists j, first_at l c j /\ v = x + Z.of_nat j))).

(* strncmp / strncasecmp interceptors (fm's; fs links neither) *)
Definition astrncmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y n (l1 l2 : list Z),
  ecall_pre_k STK_RT_STR ly S W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  cstr_ok W mem x l1 -> cstr_ok W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> strn_eq (Z.to_nat n) l1 l2)).
Definition astrncasecmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y n (l1 l2 : list Z),
  ecall_pre_k STK_RT_STR ly S W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  cstr_ok W mem x l1 -> cstr_ok W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> strncase_eq (Z.to_nat n) l1 l2)).

(* memchr (p, c, n) interceptor (fs.asan 0x43e30, REAL = musl memchr 0x98924): READ_RANGE (p, r ? r - p + 1 : n), any byte
   c: fs calls memchr (data, 0, size) (fuzz_strnlen, LLVMFuzzerTestOneInput A 0x81020 / B 0x81090; data is the driver's
   input block or FS_EMPTY) and memchr (g_b64, c, 65) (preset_base64_decode A 0x848f8 / B 0x84d4c: pf.c:626's strchr
   compiled to memchr; g_b64 is .rodata); fm's form has c = 0 only. Neither argument is a stack address, so the
   alloc_ceiling bound is satisfiable at both sites (cstr_ok's vacuity note). *)
Definition amemchr_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x c n (l : list Z),
  ecall_pre_k STK_RT_STR ly S W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 c -> 0 <= c < 256 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  zbytes_at W mem x l -> Z.of_nat (length l) = n -> 4096 <= x -> x + n <= alloc_ceiling ->
  amem_range x (n + 8) ->   (* the 8-byte word reads past the last byte, RUNTIME-str ruling *)
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (mchr_len c l) ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x (mchr_len c l)) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md
      (fun v => match zfind c l with None => v = 0 | Some k => v = x + Z.of_nat k end)).
(* the U form (preset_base64_decode runs with reader heads poisoned); the U = [] form is its corollary *)
Definition amemchr_realizesU (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md x c n (l : list Z),
  ecall_preU_k STK_RT_STR ly S U W regs mem md -> rom_view segs W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 c -> 0 <= c < 256 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  zbytes_at W mem x l -> Z.of_nat (length l) = n -> 4096 <= x -> x + n <= alloc_ceiling ->
  amem_range x (n + 8) ->   (* the 8-byte word reads past the last byte, RUNTIME-str ruling *)
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (mchr_len c l) ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x (mchr_len c l)) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_roU STK_RT_STR ly S U W regs mem md
      (fun v => match zfind c l with None => v = 0 | Some k => v = x + Z.of_nat k end)).
Lemma amemchr_realizes_of_U : forall pc, amemchr_realizesU pc -> amemchr_realizes pc.
Proof.
intros pc HU ly S W regs mem md x c n l Hpre Hrom Hx Hc Hc' Hn Hn' Hb Hl Hx1 Hx2 Hr Ha Hv.
eapply SRr_mono;
  [exact (HU ly S [] W regs mem md x c n l (ecall_preU_k_nil _ _ _ _ _ _ _ Hpre) Hrom Hx Hc Hc' Hn Hn' Hb Hl Hx1 Hx2 Hr Ha Hv)|].
intros W' c' _ H. exact (rt_post_ro_of_U _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* the output of the format pieces over the vararg register values (a3..a7); each %s / %.*s string a C string that does
   not overlap the destination [d, d + n); %c a byte; %04x a value below 2^16 *)
Fixpoint frender (W : world segs) (mem : word -> option byte) (d n : Z) (ps : list fpiece) (args : list Z)
  (out : list Z) : Prop :=
  match ps with
  | [] => out = []
  | FLit l :: ps' => exists out', out = l ++ out' /\ frender W mem d n ps' args out'
  | FStr :: ps' =>
      match args with
      | p :: args' => exists s out', cstr_ok W mem p s /\ (p + Z.of_nat (length s) + 1 <= d \/ d + n <= p) /\
          out = s ++ out' /\ frender W mem d n ps' args' out'
      | [] => False
      end
  | FPStr :: ps' =>
      match args with
      | k :: p :: args' => exists s out', 0 <= k < 2 ^ 31 /\ cstr_ok W mem p s /\
          (p + Z.of_nat (length s) + 1 <= d \/ d + n <= p) /\
          out = firstn (Z.to_nat k) s ++ out' /\ frender W mem d n ps' args' out'
      | _ => False
      end
  | FChr :: ps' =>
      match args with
      | v :: args' => exists out', 0 <= v < 256 /\ out = v :: out' /\ frender W mem d n ps' args' out'
      | [] => False
      end
  | FHex4 :: ps' =>
      match args with
      | v :: args' => exists out', 0 <= v < 2 ^ 16 /\ out = hex4z v ++ out' /\ frender W mem d n ps' args' out'
      | [] => False
      end
  end.

(* snprintf interceptor (fs.asan __interceptor_snprintf 0x45f48 -> vsnprintf 0x45b58: printf_common's %s checks, REAL =
   musl vsnprintf 0x982e4, then WRITE_RANGE (str, min (size, res + 1))) for the formats fmts of the build; the output fits;
   over ARU (fs's put_string runs while reader heads are poisoned). The image facts musl's printf_core reads: rom_view
   (formats, word constants) and the stack-protector cells gcan / can. *)
Definition asnprintf_realizes_at (fmts : list (Z * list fpiece)) (gcan can : Z) (pc : Z) : Prop :=
  forall ly S (U : list (Z * Z)) W regs mem md d sz f (ps : list fpiece) (out : list Z),
  ecall_preU_k STK_RT_PRINTF ly S U W regs mem md -> rom_view segs W mem -> fs_canary_at gcan can W mem ->
  getr regs 10 = w64 d -> getr regs 11 = w64 sz -> getr regs 12 = w64 f ->
  In (f, ps) fmts -> cstr_ok W mem f (fmt_bytes ps) ->
  frender W mem d sz ps (map (fun r : Z => bv_unsigned (getr regs (Z_to_bv 5 r))) [13; 14; 15; 16; 17]) out ->
  Z.of_nat (length out) + 1 <= sz < 2 ^ 31 ->
  wdest_ok STK_RT_PRINTF ly S W regs mem d (Z.of_nat (length out) + 1) ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       AR segs B ly S W (unpoison U mem') md' /\ upoisoned segs W mem' U /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (Z.of_nat (length out)) /\
       zbytes_at W mem' d (out ++ [0]) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length out) + 1) ->
          ~ (spZ regs - STK_RT_PRINTF <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* the image facts the build's code and runtime calls take, as one constant fact about B (a Theorem Labs lane 3e0aa997be6 /
   137702429de fm_img_facts): rom_view, the stack-protector cells, cstr_ok and the non-owned read-only home of every
   read-only string strs and format fmts, and (ALLOC a Theorem Labs lane, 21:36Z) that the journal footprint of fuzz/alloc.c's
   statics is not runtime-owned. The last one is what lets a static store keep AR: AR_frame_law (YG0d.v:438-445) and
   AR_owned_image_law (:473-474) let a walk change an image byte only where it is not owned, and nothing else about B
   says the four cells are not. It is a fact about B alone, so it is the first conjunct, with the projection
   fs_pstat_not_owned; the final instance proves it for fs's TfibB from Tfib_owned_static (the donor's pattern,
   A/AD1u.v:26 owned_off) - NOT here, and note A/AB01.v, A/AB03.v are relocated, not yet regenerated.
   The same conjunct also says no FS_PSTAT_FP cell is an errno cell: the image-byte laws of YCbq.v:361 / 828 carve
   out `as_errno B` beside the owned statics, so a static store keeps AR only when its address is outside both.
   `pstat` is the build's FS_PSTAT_FP (lib/A/FSPstat.v, lib/B/FSPstat.v), a parameter because this file is image-generic;
   FSH_Rt.v instantiates it. The rest follows from AR and the relro view at every state; lanes take the build's
   fs_img_facts (FSH_Rt.v) as a Section hypothesis. *)
(* U = [] in the two str_homeA_at below: the table strings and formats are image bytes, never in a heap block
   (YCbq.v blk_img), so they are homed by the read-only arm and the block arm's poison clause is idle here. *)
Definition fs_img_facts_at (rlo rhi gcan can : Z) (strs : list (Z * list Z)) (fmts : list (Z * list fpiece))
  (pstat : list (Z * Z)) : Prop :=
  (forall a, inFP pstat a -> ~ Exists (in_zr a) (as_owned_static B) /\
                             ~ (as_errno B <= a < as_errno B + 4)) /\
  (forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
   arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
   rom_view segs W mem /\ fs_canary_at gcan can W mem /\
   Forall (fun r => cstr_ok W mem (fst r) (snd r) /\
                    str_homeA_at rlo rhi ly S [] (fst r) (Z.of_nat (length (snd r)) + 1)) strs /\
   (forall f ps, In (f, ps) fmts -> cstr_ok W mem f (fmt_bytes ps) /\
                 str_homeA_at rlo rhi ly S [] f (Z.of_nat (length (fmt_bytes ps)) + 1))).
Lemma fs_pstat_not_owned : forall rlo rhi gcan can strs fmts pstat,
  fs_img_facts_at rlo rhi gcan can strs fmts pstat ->
  forall a, inFP pstat a -> ~ Exists (in_zr a) (as_owned_static B).
Proof. intros rlo rhi gcan can strs fmts pstat H. exact (fun a Ha => proj1 (proj1 H a Ha)). Qed.
End c.
